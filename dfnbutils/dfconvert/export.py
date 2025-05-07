import json
import os
from .convert import convert_notebook

def convert_dfnotebook(notebook, in_fname, out_fname = None, md_above=False, full_transform=False, out_mode=False):
    if out_fname == None or len(out_fname.strip()) == 0:
        base_name = os.path.splitext(os.path.basename(in_fname))[0]
        out_fname_file = base_name + '_ipy' + '.ipynb'
        out_fname = os.path.join(os.path.dirname(in_fname), out_fname_file)
    nb = convert_notebook(notebook, md_above=md_above, full_transform=full_transform, out_mode=out_mode)
    if len(nb) == 0:
        print("Error occured, please check the notebook and try again.")
    else:
        with open(out_fname, 'w') as json_file:
            json.dump(nb, json_file)