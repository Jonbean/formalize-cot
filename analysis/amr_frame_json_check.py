#!/usr/bin/env python3
"""amr_frame_json_check.py

Scans `amr-frame-50-gemini-2.5-flash` subfolders for JSON files and performs
three tasks for each JSON file's last successful round:

1) Extract axioms/theorems that are "original" — i.e. they appear
    immediately below a line that starts with
    "-- natural language description: <sentence>" (these correspond to the
    statements matching the provided natural language description).
2) Extract predefined declarations — declarations that appear in the
    header/initial part of each JSON file (before the first natural-language
    description). These are typically structure definitions and setup axioms.
3) Extract axioms/theorems that are "externally introduced" — declarations
    that are neither original nor predefined.

Additionally, compute, for each ORIGINAL THEOREM, the percentage of
externally introduced axioms/theorems that occur in its proof (i.e.
used_externals_count / total_externals_count * 100).

Output: prints a summary and writes `amr_frame_json_check_results.json`.

Usage: run from workspace root:
    python amr_frame_json_check.py

"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

"""Configuration:
By default this script will analyze one or more model output folders (method
paths) under the repository. In `main()` we configure a list of
`(method_path, method_name)` to process; each will produce its own
`amr_frame_json_check_results_<prefix>.json` file where `<prefix>` is a
sanitized combination of the method name and folder name.
"""

BASE_DIR = "../data/output"
DECL_RE = re.compile(r"^\s*(axiom|theorem)\s+([A-Za-z0-9_']+)")
NL_RE = re.compile(r"^\s*--\s*natural language description:\s*(.*)", re.IGNORECASE)
WORD_RE_TEMPLATE = r"\b{}\b"


def read_json_lines(path):
    """Read JSONL file and return list of parsed JSON objects."""
    objects = []
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        obj = json.loads(line)
                        objects.append(obj)
                    except json.JSONDecodeError:
                        continue
    except Exception as e:
        print(f"Error reading {path}: {e}")
        return []
    return objects


def find_last_successful_round(json_objects):
    """Find the last round where 'error' field is empty.
    
    Returns the lean_code from the last successful round, or None if no successful round found.
    """
    last_round_events = []
    
    for obj in json_objects:
        if obj.get("event") == "round-end":
            error = obj.get("error", "")
            if not error or error.strip() == "":
                # This round is successful
                lean_code = obj.get("lean_code", "")
                return lean_code
    
    return None


def find_declarations(lines):
    """Find all axiom/theorem declarations and classify as original or external.

    Returns lists of dicts: declarations, originals, externals.
    Each dict: {name, kind, start, end, block}
    """
    decls = []
    # find indexes of declarations
    for i, ln in enumerate(lines):
        m = DECL_RE.match(ln)
        if m:
            kind = m.group(1)
            name = m.group(2)
            decls.append((i, kind, name))

    # compute blocks: from decl start until next decl or EOF
    decl_blocks = []
    for idx, (start, kind, name) in enumerate(decls):
        end = len(lines)
        if idx + 1 < len(decls):
            end = decls[idx + 1][0]
        block = "".join(lines[start:end]).rstrip()
        decl_blocks.append({
            "name": name,
            "kind": kind,
            "start": start,
            "end": end,
            "block": block,
        })

    originals = []
    externals = []
    predefined = []

    # map decl index to decl dict for easy lookup
    decl_by_index = {d["start"]: d for d in decl_blocks}
    decl_starts = sorted(decl_by_index.keys())

    # find all NL comment line indices
    nl_indices = [i for i, ln in enumerate(lines) if NL_RE.match(ln)]

    marked_original_starts = set()

    # Declarations that appear before the first NL are predefined
    if nl_indices:
        first_nl = nl_indices[0]
        for s in decl_starts:
            if s < first_nl:
                predefined.append(decl_by_index[s])
            else:
                break
    else:
        # No NL comments: everything is predefined
        for s in decl_starts:
            predefined.append(decl_by_index[s])

    # For each NL comment, find the first declaration after it and mark original
    for nl_i in nl_indices:
        # find decl start >= nl_i
        candidate = None
        for s in decl_starts:
            if s >= nl_i:
                candidate = s
                break
        if candidate is not None:
            # avoid marking the same decl twice
            if candidate not in marked_original_starts:
                d = dict(decl_by_index[candidate])
                d["nl_sentence"] = NL_RE.match(lines[nl_i]).group(1).strip()
                originals.append(d)
                marked_original_starts.add(candidate)

    # remaining declarations not in predefined or originals are externals
    for s in decl_starts:
        if any(d["start"] == s for d in predefined):
            continue
        if s in marked_original_starts:
            continue
        externals.append(decl_by_index[s])
    
    return decl_blocks, originals, predefined, externals


def analyze_file(path):
    """Analyze a JSON file from amr-frame-50-gemini-2.5-flash folder."""
    json_objects = read_json_lines(path)
    
    # Find last successful round
    lean_code = find_last_successful_round(json_objects)
    
    if lean_code is None:
        return {
            "file": path,
            "successful": False,
            "originals": [],
            "predefined": [],
            "externals": [],
            "original_theorems_analysis": {
                "total_original_theorems": 0,
                "total_externals": 0,
                "details": [],
            },
            "summary": {
                "total_declarations": 0,
                "total_axioms": 0,
                "total_theorems": 0,
            }
        }
    
    # Split lean_code into lines and find declarations
    lines = lean_code.split("\n")
    decl_blocks, originals, predefined, externals = find_declarations(lines)
    external_names = [d["name"] for d in externals]
    
    # Only consider original theorems for the new percentage metric
    original_theorems = [d for d in originals if d["kind"] == "theorem"]
    theorems_info = []
    total_externals = len(external_names)
    
    # For each original theorem, compute how many of the external declarations
    # are referenced in its block and the percentage relative to total_externals.
    if original_theorems:
        # prepare regexes for external names and for all declaration names
        ext_word_res = [(name, re.compile(WORD_RE_TEMPLATE.format(re.escape(name)))) for name in external_names]
        all_decl_names = [d2["name"] for d2 in decl_blocks]
        all_word_res = [(name, re.compile(WORD_RE_TEMPLATE.format(re.escape(name)))) for name in all_decl_names]
        
        for d in original_theorems:
            block = d["block"]
            # only consider proof text after the first ":= by" marker
            proof_pos = block.find(":= by")
            if proof_pos >= 0:
                proof_text = block[proof_pos + len(":= by") :]
            else:
                proof_text = ""
            
            used_all = set()
            for name, cre in all_word_res:
                if cre.search(proof_text):
                    used_all.add(name)
            
            used_externals = set()
            for name, cre in ext_word_res:
                if cre.search(proof_text):
                    used_externals.add(name)
            
            used_count = len(used_externals)
            total_used = len(used_all)
            percent_external_used = (used_count / total_used * 100.0) if total_used > 0 else 0.0
            
            theorems_info.append({
                "name": d["name"],
                "used_externals_count": used_count,
                "used_externals": sorted(used_externals),
                "total_used_count": total_used,
                "percent_of_externals_used": percent_external_used,
            })

    total_original_theorems = len(original_theorems)
    
    return {
        "file": path,
        "successful": True,
        "originals": originals,
        "predefined": predefined,
        "externals": externals,
        "original_theorems_analysis": {
            "total_original_theorems": total_original_theorems,
            "total_externals": total_externals,
            "details": theorems_info,
        },
        "summary": {
            "total_declarations": len(decl_blocks),
            "total_axioms": sum(1 for d in decl_blocks if d["kind"] == "axiom"),
            "total_theorems": sum(1 for d in decl_blocks if d["kind"] == "theorem"),
        },
    }


def find_json_files(base_dir):
    """Find all JSON files under base_dir (recursive)."""
    results = []
    for root, dirs, files in os.walk(base_dir):
        for fn in files:
            if fn.endswith(".json"):
                results.append(os.path.join(root, fn))
    return sorted(results)


def _sanitize(s: str) -> str:
    """Sanitize a string to be used in filenames: lower, alnum/_ only."""
    import re
    s = s.strip().lower()
    s = re.sub(r"[^a-z0-9]+", "_", s)
    s = s.strip("_")
    return s


def _make_output_prefix(method_path: str, method_name: str) -> str:
    """Construct a reasonable output prefix for a method.

    Avoids duplicating the method name when it already appears in
    the folder name.
    """
    last_seg = Path(method_path).name
    nm = method_name.strip().lower().replace(' ', '').replace('-', '').replace('_', '')
    ls = last_seg.strip().lower().replace(' ', '').replace('-', '').replace('_', '')
    if nm and nm in ls:
        prefix_base = last_seg
    else:
        prefix_base = f"{method_name}_{last_seg}"
    return _sanitize(prefix_base)


def run_method_analysis(method_path: str, method_name: str):
    """Run the existing analysis for every JSON under `method_path` and
    write a per-method results file.
    """
    mp = Path(method_path)
    if not mp.exists():
        print(f"Warning: method path does not exist: {mp}")
        return None

    files = find_json_files(str(mp))
    if not files:
        print(f"No JSON files found under {mp}")
        return None

    results = {}
    successful_count = 0
    for f in files:
        try:
            res = analyze_file(f)
            # store path relative to the method root for clarity
            rel = os.path.relpath(f, start=str(mp))
            results[rel] = res

            if res["successful"]:
                successful_count += 1
                s = res["summary"]
                ota = res.get("original_theorems_analysis", {})
                print(f"{method_name}/{rel}: {s['total_theorems']} theorems, {ota.get('total_original_theorems', 0)} original theorems")
            else:
                print(f"{method_name}/{rel}: No successful round found")
        except Exception as e:
            print(f"Error analyzing {f}: {e}")

    prefix = _make_output_prefix(str(mp), method_name)
    out_path = f"amr_json_external_axiom_check_results_{prefix}.json"
    with open(out_path, "w", encoding="utf-8") as out:
        json.dump(results, out, indent=2)

    print(f"\nDetailed results written to {out_path}")
    print(f"Total files analyzed: {len(files)}")
    print(f"Successful files: {successful_count}")
    return out_path


def main():
    # Configure the list of (method_path, method_name) to analyze. Add or
    # remove entries as needed; each method will produce its own results file.
    methods = [
        ('../data/output/AMR-Frame-GPT5mini', 'AMR-Frame'),
        ('../data/output/AMR-Role-GPT5mini', 'AMR-Role'),
        ('../data/output/autof1-GPT5mini', 'autof1'),
        ('../data/output/autof2-GPT5mini', 'autof2'),
    ]

    for method_path, method_name in methods:
        print("\n" + "#" * 60)
        print(f"Processing method: {method_name} -> {method_path}")
        print("#" * 60 + "\n")
        run_method_analysis(method_path, method_name)


if __name__ == "__main__":
    main()
