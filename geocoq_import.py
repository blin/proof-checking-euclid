import json
import glob

from geocoq_rpl import process_parse_tree, Top

parse_tree_paths = glob.glob("build/*_parse_tree.json")

bad_path = "lemma_planeseparation"
process_parse_tree(json.load(open(f"build/{bad_path}_parse_tree.json")))

for p in parse_tree_paths:
    print(p)
    process_parse_tree(json.load(open(p)))
