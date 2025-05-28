import ast
import re

import tokenize
from io import StringIO
from collections import defaultdict
from operator import attrgetter
import json
from typing import Any
import itertools
import re

class DataflowRef:
    __slots__ = ['start_pos','end_pos','name','cell_id','cell_tag', 'is_ambiguous']

    def __init__(self, start_pos=None, end_pos=None, name=None, cell_id=None, cell_tag=None, is_ambiguous=False):
        self.start_pos = start_pos
        self.end_pos = end_pos
        self.name = name
        self.cell_id = cell_id
        self.cell_tag = cell_tag
        self.is_ambiguous = is_ambiguous
        
    @classmethod
    def fromstrstr(cls, s):
        return cls(**json.loads(json.loads(s)))

    def strstr(self):
        return json.dumps(json.dumps({
            'name': self.name,
            'cell_id': self.cell_id,
            'cell_tag': self.cell_tag,
            'is_ambiguous': self.is_ambiguous,
        }))

    def __str__(self):
        return self.to_str()

    def to_str(self, persistent=True, use_tags=True):
        if persistent:
            return f'{self.name}${self.cell_id}'
        else:
            if not self.is_ambiguous:
                return self.name
            elif self.cell_tag is not None and use_tags:
                return f'{self.name}${self.cell_tag}'
            else:
                return f'{self.name}${self.cell_id}'

    def __repr__(self):
        return f'DataflowRef({self.start_pos}, {self.end_pos}, {self.name}, {self.cell_id}, {self.cell_tag}, {self.is_ambiguous})'

def identifier_replacer(ref):
    return f"__dfvar__[{ref.strstr()}]"

def ref_replacer(ref):
    return f"_oh['{ref.cell_id}']['{ref.name}']"

def dollar_replacer(ref):
    return ref.to_str(persistent=True, use_tags=False)

def dollar_disp_replacer(ref):
    return ref.to_str(persistent=False, use_tags=True)
    
def dollar_disp_no_tag_replacer(ref):
    return ref.to_str(persistent=False, use_tags=False)

def run_replacer(s, refs, replace_f):
    code_arr = s.splitlines()
    for ref in sorted(refs, key=attrgetter('end_pos'), reverse=True):
        # FIXME improve error handling
        assert ref.start_pos[0] == ref.end_pos[0]

        line = code_arr[ref.start_pos[0] - 1]
        code_arr[ref.start_pos[0] - 1] = \
            line[:ref.start_pos[1]] + replace_f(ref) + line[ref.end_pos[1]:]
    return '\n'.join(code_arr)    

def refs_to_dict(refs):
    identifier_refs = defaultdict(set)
    for ref in refs:
        identifier_refs[ref.name].add(ref.cell_id)
    return dict(identifier_refs)

def is_ambiguous(name, cell_id, output_tags):
    return (name not in output_tags 
        or len(output_tags[name]) > 1
        or cell_id not in output_tags[name])

def ground_refs(s, dataflow_state, execution_count, replace_f=ref_replacer, input_tags={}, output_tags={}, cell_refs=None):
    updates = []

    class DataflowLinker(ast.NodeVisitor):
        def __init__(self):
            super().__init__()
            self.scope = [set()]
            self.updates = []

        def visit_Name(self, node):
            # FIXME what to do with del?
            if isinstance(node.ctx, ast.Store):
                # print("STORE", name.id, file=sys.__stdout__)
                self.scope[-1].add(node.id)
            elif isinstance(node.ctx, ast.Del):
                self.scope[-1].discard(node.id)
            elif isinstance(node.ctx, ast.Load) and all(node.id not in s for s in self.scope):
                # FIXME this isn't quite right if we run for any cell
                # as sometimes, we may want to retarget a cell
                if cell_refs is not None and node.id in cell_refs:
                    cell_ids = cell_refs[node.id]
                    assert len(cell_ids) == 1, "Multiple cell references found for unambiguous ref!"
                    cell_id = cell_ids[0]
                    self._create_dataflow_ref(node, cell_id, is_ambiguous=is_ambiguous(node.id, cell_id, output_tags))
                elif dataflow_state.has_external_link(node.id, execution_count):
                    cell_id = dataflow_state.get_external_link(node.id, execution_count)
                    self._create_dataflow_ref(node, cell_id, is_ambiguous=is_ambiguous(node.id, cell_id, output_tags))

            self.generic_visit(node)

        def _create_dataflow_ref(self, node, cell_id, is_ambiguous=False):
            ref = DataflowRef(
                start_pos=(node.lineno, node.col_offset),
                end_pos=(node.end_lineno, node.end_col_offset),
                name=node.id,
                cell_id=cell_id,
                cell_tag=input_tags.get(cell_id, None),
                is_ambiguous=is_ambiguous,
            )
            self.updates.append(ref)

        # need to make sure we visit right side before left!
        def visit_Assign(self, node):
            self.visit(node.value)
            for target in node.targets:
                self.visit(target)

        # FIXME we should rewrite augmented assignments to
        # deal with c += 12 where c is referencing another
        # cell's output
        def visit_AugAssign(self, node):
            self.visit(node.value)
            self.visit(node.target)

        def visit_AnnAssign(self, node):
            if node.value:
                self.visit(node.value)
            self.visit(node.annotation)
            self.visit(node.target)
        
        def process_function(self, node, add_name=True):
            if add_name:
                self.scope[-1].add(node.name)
            func_args = set()
            for a in itertools.chain(node.args.args, node.args.posonlyargs, node.args.kwonlyargs):
                func_args.add(a.arg)
            self.scope.append(func_args)
            retval = self.generic_visit(node)
            self.scope.pop()
            return retval

        def visit_FunctionDef(self, node):
            return self.process_function(node)

        def visit_AsyncFunctionDef(self, node):
            return self.process_function(node)

        def visit_Lambda(self, node):
            return self.process_function(node, add_name=False)

        def visit_ClassDef(self, node):
            self.scope[-1].add(node.name)
            self.scope.append(set())
            retval = self.generic_visit(node)
            self.scope.pop()
            return retval

        def process_import(self, node):
            for alias in node.names:
                if alias.asname:
                    self.scope[-1].add(alias.asname)
                else:
                    self.scope[-1].add(alias.name)
            self.generic_visit(node)

        def visit_Import(self, node):
            self.process_import(node)

        def visit_ImportFrom(self, node):
            self.process_import(node)

        def visit_ExceptHandler(self, node):
            self.scope.append(set())
            if node.name:
                self.scope[-1].add(node.name)
            retval = self.generic_visit(node)
            self.scope.pop()
            return retval

        def process_elt_comp(self, node):
            self.scope.append(set())
            for generator in node.generators:
                self.visit(generator)
            self.visit(node.elt)
            self.scope.pop()

        def visit_ListComp(self, node):
            self.process_elt_comp(node)

        def visit_SetComp(self, node):
            self.process_elt_comp(node)

        def visit_GeneratorExp(self, node):
            self.process_elt_comp(node)

        def visit_DictComp(self, node):
            self.scope.append(set())
            for generator in node.generators:
                self.visit(generator)
            self.visit(node.key)
            self.visit(node.value)
            self.scope.pop()

        def visit_NamedExpr(self, node):
            self.visit(node.value)
            self.visit(node.target)

    tree = ast.parse(s)
    linker = DataflowLinker()
    linker.visit(tree)
    
    return run_replacer(s, linker.updates, replace_f)

def convert_dollar(s, dataflow_state, execution_count, replace_f=ref_replacer, input_tags={}, output_tags={}):
    input_tags_rev = {id: tag for tag, id in input_tags.items()}

    def positions_mesh(end, start):
        return end[0] == start[0] and end[1] == start[1]

    updates = []
    s_stream = StringIO(s)

    dollar_pos = None
    var_name = None
    ref_qualifier = None
    cell_ref = ""
    last_token = None
    just_started = False

    """
    References can look like:
      * df or df$tag or df$f1f1f1
    """
    for t in tokenize.generate_tokens(s_stream.readline):
        if t.string == '$':
            if last_token is not None and positions_mesh(last_token.end, t.start):
                dollar_pos = last_token.start, t.end
                var_name = last_token.string
                just_started = True
        elif dollar_pos is not None:
            if t.type == 2 and positions_mesh(dollar_pos[1], t.start): # NUMBER
                t_string = t.string
                t_end = t.end
                while (
                    not re.match(r"[0-9a-f]+$", t_string)
                    and (t_end[0] > t.start[0] or t_end[1] > t.start[1])
                    and t_end[1] > 0
                ):
                    t_string = t_string[:-1]
                    t_end = (t_end[0], t_end[1] - 1)
                cell_ref += t_string
                dollar_pos = dollar_pos[0], t_end
                just_started = False
            elif t.type == 1 and positions_mesh(dollar_pos[1], t.start): # NAME
                cell_ref += t.string
                dollar_pos = dollar_pos[0], t.end                
                just_started = False
            else: # DONE
                if cell_ref in input_tags_rev:
                    cell_tag = cell_ref
                    cell_id = input_tags_rev[cell_ref]
                else:
                    cell_tag = None
                    cell_id = cell_ref

                updates.append(DataflowRef(
                    start_pos=dollar_pos[0],
                    end_pos=dollar_pos[1],
                    name=var_name,
                    cell_id=cell_id,
                    cell_tag=cell_tag,
                    is_ambiguous=is_ambiguous(var_name, cell_id, output_tags)
                ))
                dollar_pos = None
                var_name = None
                ref_qualifier = None
                cell_ref = ""
                last_token = None
                just_started = False
                if t.type == 1: # NAME
                    last_token = t
        elif t.type == 1: # NAME
            last_token = t

    # print("UPDATES:", updates)
    return run_replacer(s, updates, replace_f)

def convert_identifier(s, replace_f=ref_replacer):
    class DataflowReplacer(ast.NodeVisitor):
        def __init__(self):
            self.updates = []
            super().__init__()

        def visit_Subscript(self, node):
            if (isinstance(node.value, ast.Name) and node.value.id == '__dfvar__'):
                ref = DataflowRef(
                    start_pos=(node.lineno, node.col_offset),
                    end_pos=(node.end_lineno, node.end_col_offset),
                    **json.loads(node.slice.value), 
                )
            
                self.updates.append(ref)
            self.generic_visit(node)

    tree = ast.parse(s)
    linker = DataflowReplacer()
    linker.visit(tree)

    return run_replacer(s, linker.updates, replace_f), refs_to_dict(linker.updates)