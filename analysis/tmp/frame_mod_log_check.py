#!/usr/bin/env python3
"""frame_mod_log_check.py

Scans `Modified-CoT-In-Lean-AMR-Frame` subfolders for files named
`log_AMR-Frame_rationale-*.txt` and performs three tasks for each log file:

1) Extract axioms/theorems that are "original" — i.e. they appear
    immediately below a line that starts with
    "-- natural language description: <sentence>" (these correspond to the
    statements matching the provided natural language description).
2) Extract predefined declarations — declarations that appear in the
    header/initial part of each log file (before the first natural-language
    description). These are typically structure definitions and setup axioms.
3) Extract axioms/theorems that are "externally introduced" — declarations
    that are neither original nor predefined.

Additionally, compute, for each ORIGINAL THEOREM, the percentage of
externally introduced axioms/theorems that occur in its proof (i.e.
used_externals_count / total_externals_count * 100).

Output: prints a summary and writes `frame_mod_log_check_results.json`.

Usage: run from workspace root:
    python frame_mod_log_check.py

"""

import os
import re
import json
from collections import defaultdict

BASE_DIR = "Modified-CoT-In-Lean-AMR-Frame"
BASE_DIR = "../../data/output/openai-o3-result-modified"  # adjust as needed
LOG_PATTERN = re.compile(r"log_AMR-Frame_rationale-.*\.txt$")
DECL_RE = re.compile(r"^\s*(axiom|theorem)\s+([A-Za-z0-9_']+)")
NL_RE = re.compile(r"^\s*--\s*natural language description:\s*(.*)", re.IGNORECASE)
WORD_RE_TEMPLATE = r"\b{}\b"
ERROR_KEYWORDS = [
    "unknown tactic",
    "unexpected token",
    "unsolved goals",
    "invoke error",
    "invoke setup/exception",
    "error",
    "exception",
    "unexpected",
    "unsolved",
    "time exceed",
    "failed",
    "traceback",
    "line",
]

def _line_looks_like_error(line: str) -> bool:
    s = line.strip().lower()
    if not s:
        return False
    # allow non-error messages like 'invoke finished' or timing/info lines
    if s.startswith("invoke finished"):
        return False
    # if any known error keyword appears, treat as error
    for kw in ERROR_KEYWORDS:
        if kw in s:
            return True
    return False


def read_lines(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.readlines()


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


def theorem_uses_externals(lines, decl_blocks, external_names):
    """Detect whether each theorem uses any external name in its proof.

    Returns list of theorem dicts {name, uses_external: bool, used_externals: [names]}
    """
    theorems = []
    ext_set = set(external_names)
    # prepare regexes for quick search
    ext_word_res = [(name, re.compile(WORD_RE_TEMPLATE.format(re.escape(name)))) for name in external_names]

    for d in decl_blocks:
        if d["kind"] != "theorem":
            continue
        # For a theorem, inspect its block (which contains the proof if present)
        block = d["block"]
        used = set()
        for name, cre in ext_word_res:
            if cre.search(block):
                used.add(name)
        theorems.append({
            "name": d["name"],
            "uses_external": len(used) > 0,
            "used_externals": sorted(used),
        })
    return theorems


def analyze_file(path):
    lines = read_lines(path)
    # Split into rounds (lines starting with '---round') and pick the last
    # successful round. A round is successful if the section after
    # '---error message---' contains no non-empty lines.
    round_starts = [i for i, ln in enumerate(lines) if ln.strip().startswith("---round")]
    successful = False
    successful_round = None
    if not round_starts:
        # No rounds: file is only successful if it has "---error message---" marker
        # No rounds: if there is no '---error message---' marker, consider successful.
        # Otherwise check any error markers' tails for error-like lines.
        err_positions = [i for i, ln in enumerate(lines) if ln.strip().startswith("---error message---")]
        if not err_positions:
            successful = False
            use_lines = lines
        else:
            successful = False
            for pos in err_positions:
                tail = lines[pos + 1 :]
                if not any(_line_looks_like_error(ln) for ln in tail):
                    successful = True
                    successful_round = (0, len(lines))
                    break
            use_lines = lines
    else:
        round_starts.append(len(lines))
        successful_round_idx = None
        successful_rounds = []
        for r in range(len(round_starts) - 1):
            s = round_starts[r]
            e = round_starts[r + 1]
            round_lines = lines[s:e]
            # find '---error message---' in this round
            err_idx = None
            for j, ln in enumerate(round_lines):
                if ln.strip().startswith("---error message---"):
                    err_idx = j
                    break
            if err_idx is None:
                successful = True
                successful_rounds.append((s, e))
            else:
                tail = round_lines[err_idx + 1 :]
                # consider the round successful if the tail contains no error-like lines
                if not any(_line_looks_like_error(ln) for ln in tail):
                    successful = True
                    successful_rounds.append((s, e))
        # if multiple successful rounds, pick the last one
        if successful_rounds:
            successful_round = successful_rounds[-1]
            s, e = successful_round
            use_lines = lines[s:e]
        else:
            use_lines = lines

    decl_blocks, originals, predefined, externals = find_declarations(use_lines)
    external_names = [d["name"] for d in externals]
    # Only consider original theorems for the new percentage metric
    original_theorems = [d for d in originals if d["kind"] == "theorem"]
    theorems_info = []
    total_externals = len(external_names)
    # For each original theorem, compute how many of the external declarations
    # are referenced in its block and the percentage relative to total_externals.
    percent_external_used = 0.0
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
    if not successful:  
        # print(f"Analyzed {path}: successful")
        print(percent_external_used)
    return {
        "file": path,
        "originals": originals,
        "predefined": predefined,
        "externals": externals,
        "successful": successful,
        "successful_round": {"start": successful_round[0], "end": successful_round[1]} if successful_round is not None else None,
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


def find_log_files(base_dir=BASE_DIR):
    results = []
    for root, dirs, files in os.walk(base_dir):
        for fn in files:
            if LOG_PATTERN.search(fn):
                results.append(os.path.join(root, fn))
    return sorted(results)


def main():
    files = find_log_files()
    if not files:
        print("No log files found under", BASE_DIR)
        return

    results = {}
    for f in files:
        try:
            res = analyze_file(f)
            # store relative path key
            rel = os.path.relpath(f)
            results[rel] = res
            # brief console summary per file
            s = res["summary"]
            ota = res.get("original_theorems_analysis", {})
            # print(f"{rel}: {s['total_theorems']} theorems, {ota.get('total_original_theorems',0)} original theorems (details in JSON)")
        except Exception as e:
            print(f"Error analyzing {f}: {e}")

    # write JSON
    out_path = "frame_mod_log_check_results.json"
    with open(out_path, "w", encoding="utf-8") as out:
        json.dump(results, out, indent=2)

    print(f"Detailed results written to {out_path}")


if __name__ == "__main__":
    main()
