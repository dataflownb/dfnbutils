import ast
import ast_comments
from io import StringIO
from .constants import DEFAULT_ID_LENGTH
from ..refs import (
    DataflowRef, identifier_replacer, ref_replacer,
    run_replacer, convert_dollar, convert_identifier,
    DataflowLinker as RefLinker, underscore_replacer
)
import tokenize
import json
from typing import Any
import itertools
import asttokens
import astor
import builtins
import re


ref_uuids = set()

def convert_output_tags(code, output_tags, uuid, uuids_in_nb):
    def update_identifier(identifier, scope, imported_library = False):
        #case for imported library
        if imported_library:
            return identifier + f' as {identifier}_{uuid}'
        
        #check local scopes
        if len(scope) > 1:
            #checking local scopes
            for scope_vars in scope[:0:-1]:
                if identifier in scope_vars:
                    return identifier
                
        #check if identifier already converted      
        for id in uuids_in_nb:
            if id in identifier:
                ref_uuids.add(id)
                return identifier
            
        #special case: not available in 3.12.2 but available in 3.10
        if identifier == 'get_ipython':
            return identifier
        
        return identifier if identifier in dir(builtins) else f"{identifier}_{uuid}"
    
    class DFconvertDataflowLinker(RefLinker):
        def visit_Name(self, node):
            if isinstance(node.ctx, ast.Store):
                self.scope[-1].add(node.id)
                node.id = update_identifier(node.id, self.scope)
            elif isinstance(node.ctx, ast.Del):
                self.scope[-1].discard(node.id)
            elif isinstance(node.ctx, ast.Load):
                if node.id != 'Out':
                    node.id = update_identifier(node.id, self.scope)
            self.generic_visit(node)

        def visit_Subscript(self, node):
            if isinstance(node.value, ast.Name) and node.value.id == 'Out':
                if isinstance(node.slice, ast.Index) and isinstance(node.slice.value, ast.Str):
                    subscript_value = node.slice.value.s
                    new_id = f'Out_{subscript_value}'
                    if len(new_id) > 7 and new_id[:8] in uuids_in_nb:
                        ref_uuids.add(new_id[:8])
                        node.value = ast.Name(id=new_id, ctx=ast.Load())
            self.generic_visit(node)

        def process_import(self, node):
            for index, alias in enumerate(node.names):
                if alias.asname:
                    self.scope[-1].add(alias.asname)
                    node.names[index].asname = update_identifier(alias.asname, self.scope)
                else:
                    self.scope[-1].add(alias.name)
                    node.names[index].name = update_identifier(alias.name, self.scope, True)
            self.generic_visit(node)
        
        def process_function(self, node, add_name=True):
            if add_name:
                self.scope[-1].add(node.name)
                node.name = update_identifier(node.name, self.scope)
            func_args = set()
            for a in itertools.chain(node.args.args, node.args.posonlyargs, node.args.kwonlyargs):
                func_args.add(a.arg)
            self.scope.append(func_args)
            retval = self.generic_visit(node)
            self.scope.pop()
            return retval

        def visit_ClassDef(self, node):
            self.scope[-1].add(node.name)
            node.name = update_identifier(node.name, self.scope)
            self.scope.append(set())
            retval = self.generic_visit(node)
            self.scope.pop()
            return retval

        def visit_ExceptHandler(self, node):
            self.scope.append(set())
            if node.name:
                self.scope[-1].add(node.name)
                node.name = update_identifier(node.name, self.scope)
            retval = self.generic_visit(node)
            self.scope.pop()
            return retval

    tree = ast_comments.parse(code)
    linker = DFconvertDataflowLinker(dataflow_state=None, execution_count=None, output_tags={}, cell_refs={}, reversion=False, display_code=False)
    
    linker.visit(tree)
    return ast_comments.unparse(tree)

def transform_out_refs(csource,cast):
    offset = 0
    #Depth first traversal otherwise offset won't be accurate
    for node in asttokens.util.walk(cast.tree):
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == 'Out':
            start, end = node.first_token.startpos + offset, node.last_token.endpos + offset
            #new_id = re.sub('Out\[[\"|\']?([0-9A-Fa-f]{' + str(DEFAULT_ID_LENGTH) + '})[\"|\']?\]', r'Out_\1', csource[start:end])
            new_id = re.sub(r'Out\[(?:["\']?)?([0-9A-Fa-f]{' + str(DEFAULT_ID_LENGTH) + r'})(?:["\']?)?\]', r'Out_\1', csource[start:end])
            csource = csource[:start] + new_id + csource[end:]
            ref_uuids.add(new_id[4:])
            offset = offset + (len(new_id) - (end - start))
    return csource

def transform_last_node(csource,cast,exec_count):
    if isinstance(exec_count,int):
        exec_count = ("{0:#0{1}x}".format(int(exec_count),8))[2:]
    if len(cast.tree.body) > 0 and isinstance(cast.tree.body[-1], ast.Expr):
        expr_val = cast.tree.body[-1].value
        if isinstance(expr_val, ast.Tuple):
            tuple_eles = []
            named_flag = False
            out_exists = False
            for idx, elt in enumerate(expr_val.elts):
                if isinstance(elt, ast.Name):
                    named_flag = True
                    tuple_eles.append(ast.Name(elt.id, ast.Store))
                else:
                    out_exists = True
                    tuple_eles.append(ast.Name('Out_' + str(exec_count) + '['+str(idx)+']', ast.Store))
            if (named_flag):
                nnode = ast.Assign([ast.Tuple(tuple_eles, ast.Store)], expr_val)
                tuple_content = astor.to_source(expr_val).strip()[1:-1]
                out_assign = f'Out_{exec_count} = [{tuple_content}]\n' if out_exists else ''
                ast.fix_missing_locations(nnode)
                start,end = cast.tree.body[-1].first_token.startpos, cast.tree.body[-1].last_token.endpos
                csource = csource[:start] + out_assign + astor.to_source(nnode) + csource[end:]
    return csource

def out_assign(csource,cast,exec_count,tags):
    #This is a special case where an a,3 type assignment happens
    tag_flag = bool([True if exec_count in (tag[:DEFAULT_ID_LENGTH] for tag in tags) else False].count(True))

    if len(cast.tree.body) > 0 and isinstance(cast.tree.body[-1], ast.Expr) and isinstance(cast.tree.body[-1].value, ast.Call):
        return csource, []

    if tag_flag:
        if isinstance(cast.tree.body[-1], ast.Assign):
            new_node = ast.Name('Out_' + str(exec_count), ast.Store)
            nnode = cast.tree.body[-1]
            out_targets = nnode.targets.pop()
            nnode.targets.append(new_node)
            ast.fix_missing_locations(nnode)
            start, end = cast.tree.body[-1].first_token.startpos, cast.tree.body[-1].last_token.endpos
            csource = csource[:start] + astor.to_source(nnode) + csource[end:]
            return csource, out_targets
    if len(cast.tree.body) < 1:
        return csource, []
    if isinstance(cast.tree.body[-1],ast.Expr):
        expr_val = cast.tree.body[-1].value
        nnode = ast.Assign([ast.Name('Out_' + str(exec_count), ast.Store)], expr_val)
        ast.fix_missing_locations(nnode)
        start, end = cast.tree.body[-1].first_token.startpos, cast.tree.body[-1].last_token.endpos
        csource = csource[:start] + astor.to_source(nnode) + csource[end:]
    elif isinstance(cast.tree.body[-1],ast.Assign):
        new_node = ast.Name('Out_'+str(exec_count),ast.Store)
        nnode = cast.tree.body[-1]
        nnode.targets.append(new_node)
        ast.fix_missing_locations(nnode)
        start, end = cast.tree.body[-1].first_token.startpos, cast.tree.body[-1].last_token.endpos
        csource = csource[:start] + astor.to_source(nnode) + csource[end:]
    return csource, []