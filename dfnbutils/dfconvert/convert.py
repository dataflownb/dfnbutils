import ast
import astor
import asttokens
import re
import uuid as uuidlib
from collections import OrderedDict
from IPython.core.inputtransformer2 import TransformerManager
from . import make_ipy
from .topological import topological
from .display_cell import display_variable_cell
from .constants import DEFAULT_ID_LENGTH, DF_CELL_PREFIX

def _transform_outrefs(source_code):
    # Changes Out[aaa] and Out["aaa"] to Out_aaa
    pattern = r'Out\[["|\']?([0-9A-Fa-f]{' + str(DEFAULT_ID_LENGTH) + r'})["|\']?\]'
    return re.sub(pattern, r'Out_\1', source_code)

def _replace_export_id(input_string):
    pattern = r'\[([a-zA-Z0-9]+)\]\[(\d+)\]'
    return re.sub(pattern, r'Out_\1[\2]', input_string)

def convert_notebook(notebook, md_above=False, full_transform=False, out_mode=False):
    cell_template = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": []
    }

    try:
        code_cells_ref = dict()
        non_code_cells_ref = OrderedDict()
        downlinks = dict()
        nb_output_tags = dict()
        non_code_cells_block = dict()
        non_code_cells_seq = dict()
        transformer_manager = TransformerManager()
        latest_non_code_cell = None

        # Separate code and non-code cells
        for cell in notebook['cells']:
            output_tags = []
            cell_id = cell['id'].split('-')[0]

            if cell['cell_type'] != "code":
                non_code_cells_seq[cell_id] = []
                if latest_non_code_cell and not non_code_cells_block[latest_non_code_cell]:
                    del non_code_cells_block[latest_non_code_cell]
                    non_code_cells_seq[cell_id] += non_code_cells_seq[latest_non_code_cell] + [non_code_cells_ref[latest_non_code_cell]]
                    del non_code_cells_seq[latest_non_code_cell]

                latest_non_code_cell = cell_id
                non_code_cells_ref[cell_id] = cell
                non_code_cells_block[cell_id] = set()

            else:
                if latest_non_code_cell and cell['source']:
                    non_code_cells_block[latest_non_code_cell].add(cell_id)

                for output in cell.get('outputs', []):
                    if output.get('metadata') and output['metadata'].get('output_tag'):
                        output_tags.append(output['metadata']['output_tag'])

                    if 'execution_count' in output and output.get('output_type') in ['stream', 'display_data', 'error', 'update_display_data', 'clear_output']:
                        del output['execution_count']

                nb_output_tags[cell_id] = output_tags
                code_cells_ref[cell_id] = [cell]

        # Process each code cell
        for uuid, cells in code_cells_ref.items():
            cell = cells[0]
            make_ipy.ref_uuids = set()

            # Apply transformers
            persistent_code = cell['metadata']['dfmetadata']['persistentCode']    
            code = transformer_manager.transform_cell(persistent_code)
            code = make_ipy.convert_dollar(code, {}, '', replace_f=make_ipy.identifier_replacer)
            code = make_ipy.convert_identifier(code, make_ipy.underscore_replacer, {})
            code = make_ipy.convert_output_tags(code, nb_output_tags.get(uuid, []), uuid, code_cells_ref.keys())

            cast = asttokens.ASTTokens(code, parse=True)
            code = make_ipy.transform_out_refs(code, cast)

            if full_transform:
                code = _transform_outrefs(code)

            cast = asttokens.ASTTokens(code, parse=True)
            code = make_ipy.transform_last_node(code, cast, uuid)

            # Handle output assignments
            valid_tags = [output['metadata']['output_tag'] for output in cell.get('outputs', []) if 'metadata' in output and 'output_tag' in output['metadata']]
            cast = asttokens.ASTTokens(code, parse=True)
            code, out_targets = make_ipy.out_assign(code, cast, uuid, valid_tags)

            code_cells_ref[uuid][0]['source'] = code.strip()

            if out_mode:
                tree = ast.parse(cell['source'])
                if out_targets:
                    if isinstance(out_targets, ast.Tuple):
                        for elt in out_targets.elts:
                            new_cell = dict(cell_template)
                            new_cell['source'] = DF_CELL_PREFIX + str(astor.to_source(elt)).rstrip()
                            code_cells_ref[uuid].append(new_cell)

                if tree.body and isinstance(tree.body[-1], ast.Assign) and isinstance(tree.body[-1].targets, list):
                    for count, target in enumerate(tree.body[-1].targets):
                        if (len(tree.body[-1].targets) == count + 1) and isinstance(target, ast.Name) and len(code_cells_ref[uuid]) == 1:
                            new_cell = dict(cell_template)
                            new_cell['source'] = DF_CELL_PREFIX + target.id
                            code_cells_ref[uuid].append(new_cell)
                        if isinstance(target, ast.Tuple):
                            for elt in target.elts:
                                if isinstance(elt, ast.Name):
                                    new_cell = dict(cell_template)
                                    new_cell['source'] = DF_CELL_PREFIX + elt.id
                                    code_cells_ref[uuid].append(new_cell)

            else:
                # Wrap exported variables into display_variables
                exported_variables = ""

                if nb_output_tags.get(uuid):
                    variable_items = []
                
                    for val in nb_output_tags[uuid]:
                        is_uuid_in_val = uuid in val
                        is_external_ref = len(val) < 8 or val[:8] not in code_cells_ref.keys() or uuid != val[:8]
                
                        if is_external_ref:
                            if is_uuid_in_val:
                                tag = _replace_export_id(val)
                                variable_items.append(f'"{tag}": {tag}')
                            else:
                                variable_items.append(f'"{val}_{uuid}": {val}_{uuid}')
                
                    if variable_items:
                        exported_variables = "{ " + ", ".join(variable_items) + " }"


                if len(exported_variables) > 3:
                    code += f'\ndisplay_variables({exported_variables})'
                elif f'Out_{uuid}' in code:
                    code += f'\ndisplay_variables({{"Out_{uuid}": Out_{uuid}}})'

                code_cells_ref[uuid][0]['source'] = code

            downlinks[uuid] = list(make_ipy.ref_uuids)

        # Topologically sort cells based on dependencies
        sorted_order = list(topological(downlinks))
        ordered_cells = []

        if md_above:
            ordered_cells.extend(non_code_cells_ref.values())

        for cell_id in reversed(sorted_order):
            if not md_above:
                for id_, code_ids in non_code_cells_block.items():
                    if cell_id in code_ids:
                        if non_code_cells_seq.get(id_):
                            ordered_cells.extend(non_code_cells_seq[id_])
                        ordered_cells.append(non_code_cells_ref[id_])
                        del non_code_cells_block[id_]
                        break
            ordered_cells.extend(code_cells_ref[cell_id])

        if not md_above:
            ordered_cells.extend(non_code_cells_ref[id_] for id_ in non_code_cells_block.keys())

        notebook['cells'] = ordered_cells if out_mode else display_variable_cell + ordered_cells

        # Standardize kernel metadata
        if 'metadata' in notebook and 'kernelspec' in notebook['metadata']:
            notebook['metadata']['kernelspec']['display_name'] = "Python 3 (ipykernel)"
            notebook['metadata']['kernelspec']['name'] = "python3"
            del notebook['metadata']['dfnotebook']
            del notebook['metadata']['enable_tags']
        
        #clearing the existing metadata and execution count from code cells.
        final_cells = []
        for cell in notebook['cells']:
            cell['id'] = str(uuidlib.uuid4()) # assign new cell ids
            if cell['cell_type'] == "code":
                cell['metadata'] = {}
                cell['execution_count'] = None
                final_cells.append(cell)
            else:
                final_cells.append(cell)
        
        notebook['cells'] = final_cells
        return notebook

    except Exception as e:
        return ''