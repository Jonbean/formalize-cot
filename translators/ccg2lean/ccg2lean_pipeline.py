#!/usr/bin/env python3
# ccg2lean_pipeline.py
# Multi-sentence -> depccg (ccg2lambda FOL) -> Lean 4 files
# - Supports JSON list-of-lists of {idx,text,PIT,...}
# - Ordered emission, PIT -> {axiom, lemma, theorem}, shared decls per chain
# - NL comments per statement; optional-knowledge comment for lemma/theorem

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from typing import Dict, List, Tuple, Optional, Set

# ---------- config / env quieting ----------
os.environ.setdefault("PYTHONWARNINGS", "ignore")
os.environ.setdefault("TF_CPP_MIN_LOG_LEVEL", "3")

# ---------- depccg runners ----------

XML_START_RE = re.compile(
    rb"<\?xml|<\s*(root|document|corpus|sentences|jigg)\b", re.IGNORECASE
)
# Heuristics to recognize a real formula (has a quantifier or a call or parentheses structure)
_FORMULA_LIKE = re.compile(r"(∀|∃|\bforall\b|\bexists\b|\(|\)|[A-Za-z_][A-Za-z0-9_]*\s*\()")
_FAILED_TOKEN = re.compile(r"\bFAILED!?(\b|$)")

def _looks_like_formula(s: str) -> bool:
    if not s or _FAILED_TOKEN.search(s):
        return False
    if s.strip().upper() == "FAILED!":
        return False
    if s.count("(") and s.count(")") and s.count("(") == s.count(")"):
        pass  # ok
    # the rest as before...
    if not _FORMULA_LIKE.search(s):
        return False
    letters = re.sub(r"[^A-Za-z]", "", s)
    return len(letters) > 0

def _extract_xml_payload(raw: bytes) -> bytes:
    m = XML_START_RE.search(raw)
    return raw[m.start():] if m else b""

def run_depccg_xml(sentences: List[str], model="elmo", annotator="spacy") -> ET.Element:
    cmd = [
        "depccg_en", "-m", model, "--annotator", annotator,
        "--tokenize", "--format", "jigg_xml_ccg2lambda",
    ]
    p = subprocess.run(
        cmd,
        input=("\n".join(sentences) + "\n").encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    out, err = p.stdout, p.stderr
    if p.returncode != 0:
        sys.stderr.write(err.decode("utf-8", "ignore"))
        raise RuntimeError("depccg_en failed (non-zero exit). See stderr above.")
    payload = _extract_xml_payload(out)
    if not payload:
        sys.stderr.write("[info] No XML start found on stdout; will try text fallback.\n")
        raise ET.ParseError("No XML payload")
    try:
        return ET.fromstring(payload.decode("utf-8"))
    except ET.ParseError as e:
        sys.stderr.write(f"[info] XML parse failed: {e}. Will try text fallback.\n")
        raise

# def run_depccg_text(sentences: List[str], model="elmo", annotator="spacy") -> List[str]:
#     """Ask depccg for plain ccg2lambda output and heuristically harvest one FOL per sentence."""
#     cmd = ["depccg_en", "-m", model, "--annotator", annotator, "--tokenize", "--format", "ccg2lambda"]
#     p = subprocess.run(
#         cmd,
#         input=("\n".join(sentences) + "\n").encode("utf-8"),
#         stdout=subprocess.PIPE,
#         stderr=subprocess.PIPE,
#     )
#     if p.returncode != 0:
#         sys.stderr.write(p.stderr.decode("utf-8", "ignore"))
#         raise RuntimeError("depccg_en failed in text mode.")
#     lines = [ln.rstrip() for ln in p.stdout.decode("utf-8", "ignore").splitlines()]

#     # Group blocks separated by blank lines
#     blocks, cur = [], []
#     for ln in lines:
#         if not ln.strip():
#             if cur:
#                 blocks.append(" ".join(cur)); cur = []
#         else:
#             cur.append(ln.strip())
#     if cur: blocks.append(" ".join(cur))

#     # From each block, keep the substring that looks like a formula
#     FOL_START = re.compile(
#         r"(forall|exists|all|some|\bnot\b|\band\b|\bor\b|->|[-&|()]|[A-Za-z_][A-Za-z0-9_:\-]*\s*\([^()]*\))"
#     )
#     fols: List[str] = []
#     for blk in blocks:
#         blk = re.sub(r"\bID=\d+[^A-Za-z(]+", " ", blk)
#         m = FOL_START.search(blk)
#         if m:
#             fols.append(blk[m.start():].strip())
#     return fols

_BLOCK_SPLIT_ID = re.compile(r"(?=^ID=\d+\b)", re.M)
_LOG_CAND = re.compile(r"(FAILED!\s*)?log probability=([-\d\.eE]+)\s+(.*?)(?=(?:FAILED!\s*)?log probability=|$)", re.S)

def _split_depccg_text_output(raw_text: str) -> List[str]:
    """Split depccg text output into blocks, one per input sentence."""
    text = raw_text.strip()
    if not text:
        return []
    if "ID=" in text:
        # Split at beginnings of lines "ID=<num>"
        parts = _BLOCK_SPLIT_ID.split(text)
        blocks = [p.strip() for p in parts if p.strip()]
        return blocks
    # fallback: blank-line delimitation
    parts = re.split(r"\n\s*\n+", text)
    return [p.strip() for p in parts if p.strip()]

_FOL_START_PROPER = re.compile(
    r"(∀|∃|\bforall\b|\bexists\b|\bnot\b|\band\b|\bor\b|\(|[A-Za-z_][A-Za-z0-9_:\-]*\s*\()",
    re.S
)


def _extract_best_formula_from_block(block: str) -> Optional[str]:
    """
    Pick highest-prob NON-FAILED candidate whose body looks like a formula.
    If none, return None (caller can decide how to handle failures).
    """
    cands = []
    for m in _LOG_CAND.finditer(block):
        failed = bool(m.group(1))
        prob = float(m.group(2))
        body = (m.group(3) or "").strip()
        m2 = _FOL_START_PROPER.search(body)
        if m2:
            body = body[m2.start():].strip()
        cands.append((failed, prob, body))

    # Prefer non-FAILED with valid body
    good = [(f,p,b) for (f,p,b) in cands if (not f) and _looks_like_formula(b)]
    if good:
        return max(good, key=lambda t: t[1])[2]

    # Then consider "failed" entries that still have a valid-looking formula body
    okish = [(f,p,b) for (f,p,b) in cands if _looks_like_formula(b)]
    if okish:
        return max(okish, key=lambda t: t[1])[2]

    # No candidates we trust
    return None


def run_depccg_text_multi(sentences: List[str], model="elmo", annotator="spacy") -> List[str]:
    """
    Robust text-mode: single depccg call -> split into blocks -> pick best candidate per block.
    If count mismatches number of inputs, fallback to one-by-one calls.
    """
    cmd = ["depccg_en", "-m", model, "--annotator", annotator, "--tokenize", "--format", "ccg2lambda"]
    p = subprocess.run(
        cmd,
        input=("\n".join(sentences) + "\n").encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if p.returncode != 0:
        sys.stderr.write(p.stderr.decode("utf-8", "ignore"))
        raise RuntimeError("depccg_en failed in text mode.")

    text = p.stdout.decode("utf-8", "ignore")
    blocks = _split_depccg_text_output(text)
    fols = []
    for b in blocks:
        f = _extract_best_formula_from_block(b)
        if f:
            fols.append(f)

    if len(fols) == len(sentences):
        return fols

    # Fallback: run per sentence for guaranteed 1:1 extraction
    sys.stderr.write(f"[info] Text-mode block mismatch ({len(fols)} vs {len(sentences)}). Falling back to per-sentence runs.\n")
    per_fols: List[str] = []
    for s in sentences:
        p1 = subprocess.run(
            cmd,
            input=(s + "\n").encode("utf-8"),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if p1.returncode != 0:
            sys.stderr.write(p1.stderr.decode("utf-8", "ignore"))
            continue
        f = _extract_best_formula_from_block(p1.stdout.decode("utf-8", "ignore"))
        if f:
            per_fols.append(f)
        else:
            per_fols.append("")  # keep alignment; caller will truncate later
    return per_fols
# ---------- FOL harvesting from XML (per sentence, preserve order) ----------

def _local(tag: str) -> str:
    if tag.startswith("{"):
        return tag.split("}", 1)[1]
    if ":" in tag:
        return tag.split(":", 1)[1]
    return tag

def _first_formula_in(el: ET.Element) -> Optional[str]:
    for d in el.iter():
        if _local(d.tag).lower().endswith("sem"):
            txt = (d.text or "").strip()
            if txt:
                return txt
    for d in el.iter():
        for k, v in d.attrib.items():
            if k.lower() in {"sem", "ccg2lambda", "formula", "lf"} and v.strip():
                return v.strip()
    for d in el.iter():
        if _local(d.tag).lower() in {"lf", "logic"} and (d.text or "").strip():
            return d.text.strip()
    return None

def extract_fols_per_sentence_from_xml(doc: ET.Element, num_inputs: int) -> List[str]:
    sents = [el for el in doc.iter() if _local(el.tag).lower() == "sentence"]
    fols: List[str] = []
    for s in sents:
        f = _first_formula_in(s)
        if f: fols.append(f)
    if len(fols) != num_inputs:
        flat: List[str] = []
        for el in doc.iter():
            if _local(el.tag).lower().endswith("sem"):
                txt = (el.text or "").strip()
                if txt: flat.append(txt)
        if len(flat) >= num_inputs:
            fols = flat[:num_inputs]
    return fols

# ---------- FOL -> Lean mapping ----------

CALL_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_:\-]*)\s*\(([^()]*)\)")
EQ_FUNC_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_:\-]*)\s*\(\s*([A-Za-z0-9_]+)\s*\)\s*=\s*([A-Za-z0-9_]+)")
EQ_FUNC_REV_RE = re.compile(r"([A-Za-z0-9_]+)\s*=\s*([A-Za-z_][A-Za-z0-9_:\-]*)\s*\(\s*([A-Za-z0-9_]+)\s*\)")

def is_event_var(v: str) -> bool:
    return v.startswith("e")  # heuristic: e, e0, e1, ...

def sort_of_var(v: str) -> str:
    return "ε" if is_event_var(v) else "ι"

RESERVED: Set[str] = {
    "all", "some", "if", "then", "else", "match", "with", "end",
    "theorem", "lemma", "axiom", "by", "have", "let", "in",
    "Type", "Sort", "Prop", "fun", "True", "False", "Eq",
    "and", "or", "not", "forall", "exists"
}

# Names that conflict with Lean/Core/Std/Mathlib symbols in practice
CONFLICTING: Set[str] = {
    "Acc",  # well-founded accessibility
    "Or", "And", "Not", "Iff", "Eq",  # capitalized propositional constants
}

def clean_name(name: str) -> str:
    name = name.lstrip("_")
    name = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not name:
        return "P"
    if name[0].isdigit():
        name = f"n_{name}"
    if name in CONFLICTING:
        name = f"nl_{name}"        # rename away from clashes
    if name in RESERVED:
        name = f"p_{name}"
    return name

def tokenize_calls(f: str) -> List[Tuple[str, List[str]]]:
    calls = []
    tmp = f
    while True:
        m = CALL_RE.search(tmp)
        if not m: break
        name = clean_name(m.group(1))
        args = [a.strip() for a in m.group(2).split(",") if a.strip()]
        calls.append((name, args))
        tmp = tmp[:m.start()] + " " * (m.end()-m.start()) + tmp[m.end():]
    return calls

def infer_signatures(formulas: List[str]) -> Dict[str, Tuple[str, ...]]:
    sig: Dict[str, Tuple[str, ...]] = {}
    for fol in formulas:
        for m in EQ_FUNC_RE.finditer(fol):
            f, a, b = clean_name(m.group(1)), m.group(2), m.group(3)
            sig[f] = (sort_of_var(a), sort_of_var(b))
        for m in EQ_FUNC_REV_RE.finditer(fol):
            a, f, b = m.group(1), clean_name(m.group(2)), m.group(3)
            sig[f] = (sort_of_var(b), sort_of_var(a))
    QUANTIFIERS = {"forall", "exists", "all", "some"}
    for fol in formulas:
        for name, args in tokenize_calls(fol):
            if name in QUANTIFIERS:
                continue
            if name in sig and len(sig[name]) == 2 and sig[name][-1] in ("ι", "ε"):
                continue
            sorts = tuple(sort_of_var(a) for a in args) + ("Prop",)
            if name in sig:
                if len(sig[name]) != len(sorts):
                    if len(sorts) > len(sig[name]):
                        sig[name] = sorts
            else:
                sig[name] = sorts
    return sig

# ccg2lambda variants: words and symbols
KW = [
    (r"\bforall\b", "∀"), (r"\ball\b", "∀"),
    (r"\bexists\b", "∃"), (r"\bsome\b", "∃"),
    (r"\bnot\b", "¬"),
    (r"\band\b", "∧"), (r"\bor\b", "∨"),
    (r"->", "→"),
    (r"\|", "∨"), (r"&", "∧"),
]

# support depccg variants that emit: forall x., all x., exists x., some x.
QF_RE = re.compile(r"\b(forall|all|exists|some)\b\s*([A-Za-z0-9_]+)\s*[\.:\)]")

def annotate_binders(s: str) -> str:
    def rep(m):
        q, v = m.group(1), m.group(2)
        sym = "∀" if q in {"forall", "all"} else "∃"
        sort = "ε" if is_event_var(v) else "ι"
        return f"{sym} ({v} : {sort}), "
    return QF_RE.sub(rep, s)

# Turn unary '-' (as used by some ccg2lambda outputs) into '¬'
NEG_UNARY_RE = re.compile(r'(^|[^0-9A-Za-z_])-\s*(?=(∀|∃|\(|[A-Za-z_]))')
def normalize_unary_negation(s: str) -> str:
    return NEG_UNARY_RE.sub(r'\1¬', s)

def to_curried_apps(s: str) -> str:
    out = s
    while True:
        m = CALL_RE.search(out)
        if not m: break
        name = clean_name(m.group(1))
        args = [a.strip() for a in m.group(2).split(",") if a.strip()]
        out = out[:m.start()] + (name + (" " + " ".join(args) if args else "")) + out[m.end():]
    return out

TRUE_PATTERNS = [
    (re.compile(r"\(\s*True\s*∧\s*"), "("),
    (re.compile(r"\s*∧\s*True\s*\)"), ")"),
    (re.compile(r"\bTrue\s*∧\s*"), ""),
    (re.compile(r"\s*∧\s*True\b"), ""),
    (re.compile(r"\bTrue\s*→\s*"), ""),
]
def prune_trivial_true(s: str) -> str:
    prev = None
    out = s
    while prev != out:
        prev = out
        for rx, repl in TRUE_PATTERNS:
            out = rx.sub(repl, out)
        out = re.sub(r"\(\s*\)", "", out)
        out = re.sub(r"\s+", " ", out).strip()
    return out

def normalize_glyphs(s: str) -> str:
    # normalize common unicode math symbols to ascii-ish tokens
    s = s.replace("×", "mul")
    s = s.replace("÷", "div")
    s = s.replace("−", "-")    # unicode minus -> ascii hyphen
    return s

def fol_to_lean_prop(f: str) -> str:
    s = normalize_glyphs(f)  # NEW

    # existing steps follow...
    s = annotate_binders(s)
    for a, b in KW:
        s = re.sub(a, b, s)
    s = s.replace(".(", "(").replace(").", ")")
    s = re.sub(r"\s*\.\s+", " ", s)
    s = normalize_unary_negation(s)
    s = to_curried_apps(s)
    s = prune_trivial_true(s)
    s = re.sub(r"\s+", " ", s).strip()
    return s

# ---------- Lean emission ----------

PRELUDE_CORE = """\
-- Lean core only (no Mathlib)
-- open Classical  -- uncomment if you actually need classical logic

universe u
axiom ι : Type u   -- individuals
axiom ε : Type u   -- events
"""

PRELUDE_MATHLIB = """\
import Mathlib.Logic.Basic
open Classical

universe u
axiom ι : Type u   -- individuals
axiom ε : Type u   -- events
"""
def select_prelude(kind: str) -> str:
    k = (kind or "core").lower()
    return PRELUDE_MATHLIB if k == "mathlib" else PRELUDE_CORE

def decl_from_sig(name: str, sig: Tuple[str, ...]) -> str:
    if not sig:
        return f"axiom {name} : Prop"
    if sig[-1] == "Prop":
        return f"axiom {name} : " + (" → ".join(sig[:-1]) + " → Prop" if len(sig) > 1 else "Prop")
    return f"axiom {name} : " + " → ".join(sig)

# ---------- PIT mapping & IO ----------

LABEL_MAP = {
    # map many PITs to axioms
    "premise": "axiom",
    "assumption": "axiom",
    "definition": "axiom",
    "new definition": "axiom",
    "new-definition": "axiom",
    "def": "axiom",
    "fact": "axiom",
    "rule": "axiom",
    "explicit-knowledge-claim": "axiom",
    "implicit assumption resurfacing": "axiom",
    "implicit-assumption-resurfacing": "axiom",
    "axiom": "axiom",

    "lemma": "lemma",

    "conclusion": "theorem",
    "theorem": "theorem",
    "thm": "theorem",
    "negated-theorem": "negated-theorem",
}

def norm_label(label: Optional[str]) -> str:
    if not label: return "axiom"
    key = label.strip().lower()
    return LABEL_MAP.get(key, "axiom")

def load_sequences_from_json_multi(path: pathlib.Path) -> List[List[Dict]]:
    """Load list-of-lists; each inner list is a sequence of statements dicts."""
    raw = path.read_text(encoding="utf-8")
    data = json.loads(raw)
    if not isinstance(data, list):
        raise ValueError("Top-level JSON must be a list (of sequences).")
    sequences: List[List[Dict]] = []
    for i, seq in enumerate(data, 1):
        if not isinstance(seq, list):
            raise ValueError(f"Sequence {i} is not a list.")
        items: List[Dict] = []
        for j, d in enumerate(seq, 1):
            if not isinstance(d, dict):
                raise ValueError(f"Item {i}.{j} is not an object.")
            txt = d.get("text")
            pit = d.get("PIT") or d.get("label")
            if not txt:
                raise ValueError(f"Item {i}.{j} missing 'text'.")
            items.append({
                "text": txt.strip(),
                "pit": pit,
                "label": norm_label(pit),
                "name": d.get("name"),
                "negated": (str(pit).strip().lower() == "negated-theorem"),
                "idx": d.get("idx", j-1),
            })
        sequences.append(items)
    return sequences

def default_name(kind: str, seq_idx: int, item_idx: int) -> str:
    base = {"axiom": "axiom", "lemma": "lemma"}.get(kind, "theorem")
    return f"{base}_{seq_idx}_{item_idx}"

# ---------- Free constant harvesting (pronouns etc.) ----------

FREE_INDIV_RE = re.compile(r"\b_[A-Za-z][A-Za-z0-9_]*\b")

def harvest_free_individuals(formulas: List[str]) -> List[str]:
    names: Set[str] = set()
    for f in formulas:
        for m in FREE_INDIV_RE.finditer(f):
            names.add(m.group(0))
    return sorted(names)

# ---------- Build Lean from items (one sequence) ----------

def build_lean_from_items(items: List[Dict], all_formulas: List[str], seq_no: int) -> str:
    """
    Build a Lean file for one sequence of items, preserving order even if a sentence parse fails.

    Changes vs. older version:
    - We DO NOT drop items with failed parses.
    - For each item we compute a prop (if available); otherwise we emit a placeholder Prop and
      make the axiom/lemma/theorem refer to that placeholder so the file still compiles.
    - Shared declarations (predicate/function signatures, free individuals) are inferred ONLY
      from successfully parsed formulas, to avoid pollution from junk.
    """

    # 1) Per-item Lean proposition strings, aligned 1:1 with items (None on parse failure)
    props: List[Optional[str]] = []
    for fol in all_formulas:
        props.append(fol_to_lean_prop(fol) if (fol and fol.strip()) else None)

    # 2) Assign stable names if missing (order-preserving)
    for k, it in enumerate(items, 1):
        if not it.get("name"):
            it["name"] = default_name(it["label"], seq_no, k)

    # 3) Shared declarations inferred ONLY from successful formulas
    ok_formulas = [fol for fol in all_formulas if (fol and fol.strip())]
    sigs = infer_signatures(ok_formulas)
    decls = "\n".join(sorted(decl_from_sig(n, sigs[n]) for n in sigs))

    # Free individual constants like _they
    free_inds = harvest_free_individuals(ok_formulas)
    free_decl = "\n".join(f"axiom {n} : ι" for n in free_inds)

    # 4) Emit statements in the original order.
    #    On failure: declare a placeholder Prop and make the statement reference it.
    stmts: List[str] = []
    for it, prop in zip(items, props):
        kind = it["label"]
        name = clean_name(it["name"])
        nl = it["text"].replace("\n", " ").strip()

        header = [f"-- NL: {nl}"]
        tagline = f"-- [{kind}] {name}"
        if kind in {"lemma", "theorem"}:
            header.append("-- [Optional knowledge insertion point: extra axioms may be added here if needed]")
        header.append(tagline)

        if prop:  # normal case
            if kind == "axiom":
                code = f"axiom {name} : {prop}"
            elif kind == "lemma":
                code = f"lemma {name} : {prop} := by\n  sorry"
            else:
                if it.get("negated", False):
                    code = f"theorem {name} : ¬({prop}) := by\n  sorry"
                else:
                    code = f"theorem {name} : {prop} := by\n  sorry"
        else:
            # parse failed for this item -> keep order with a compilable placeholder
            placeholder = f"{name}_Prop"
            if kind == "axiom":
                code = (
                    f"-- [parse failed: no usable formula from depccg]\n"
                    f"axiom {placeholder} : Prop\n"
                    f"axiom {name} : {placeholder}"
                )
            elif kind == "lemma":
                code = (
                    f"-- [parse failed: no usable formula from depccg]\n"
                    f"axiom {placeholder} : Prop\n"
                    f"lemma {name} : {placeholder} := by\n  sorry"
                )
            else:  # theorem
                code = (
                    f"-- [parse failed: no usable formula from depccg]\n"
                    f"axiom {placeholder} : Prop\n"
                    f"theorem {name} : {placeholder} := by\n  sorry"
                )

        stmts.append("\n".join(header + [code]))

    # 5) Assemble file: boilerplate at top, then free constants, shared decls, then statements
    sections = [PRELUDE]  # if you added a prelude selector, use: select_prelude(args.prelude)
    if free_decl:
        sections.append(free_decl)
    if decls:
        sections.append(decls)
    sections.append("\n\n".join(stmts) if stmts else "-- (no statements parsed)")
    return "\n\n".join(sections) + "\n"

# ---------- CLI ----------

def main():
    ap = argparse.ArgumentParser(description="Rationale chains -> depccg (ccg2lambda FOL) -> Lean 4 files.")
    src = ap.add_mutually_exclusive_group(required=False)
    src.add_argument("--json-multi", help="JSON list-of-lists of {idx,text,PIT,...}. One Lean file per inner list.")
    # (legacy modes still available)
    src.add_argument("-i", "--input", help="LEGACY: text file with one sentence per line (default: stdin)")
    src.add_argument("--json", help="LEGACY: JSON/NDJSON of items: {text, label?, name?, negated?}")

    ap.add_argument("--labels", help="LEGACY: labels file (one label per line) for --input mode")
    ap.add_argument("-o", "--out", default="sentences.lean", help="LEGACY: single output filename")
    ap.add_argument("--outdir", default="lean_out", help="When --json-multi is used, write files here (default: lean_out)")
    ap.add_argument("--basename", default="seq", help="Base name for generated files with --json-multi (default: seq)")
    ap.add_argument("--model", default="elmo", help="depccg model (default: elmo)")
    ap.add_argument("--annotator", default="spacy", help="depccg annotator (default: spacy)")
    ap.add_argument("--prelude", default="core", choices=["core","mathlib"],
                help="Prelude to use (default: core). core = no imports; mathlib = import Mathlib.Logic.Basic")
    args = ap.parse_args()

    # New multi-JSON mode
    if args.json_multi:
        sequences = load_sequences_from_json_multi(pathlib.Path(args.json_multi))
        outdir = pathlib.Path(args.outdir); outdir.mkdir(parents=True, exist_ok=True)
        for i, items in enumerate(sequences, 1):
            sentences = [it["text"] for it in items]
            if not sentences: 
                sys.stderr.write(f"[warn] Sequence {i} is empty; skipping.\n"); continue
            # depccg per sequence
            try:
                xml = run_depccg_xml(sentences, args.model, args.annotator)
                fols = extract_fols_per_sentence_from_xml(xml, num_inputs=len(sentences))
                if len(fols) != len(sentences):
                    sys.stderr.write(f"[info] XML mismatch in seq {i}; trying text fallback.\n")
                    fols = run_depccg_text_multi(sentences, args.model, args.annotator)
            except Exception:
                fols = run_depccg_text_multi(sentences, args.model, args.annotator)
            if not fols:
                sys.stderr.write(f"[warn] No formulas found for sequence {i}; skipping.\n"); continue
            if len(fols) != len(sentences):
                sys.stderr.write(f"[warn] Found {len(fols)} formulas for {len(sentences)} sentences in seq {i}; truncating to min.\n")
            n = min(len(fols), len(sentences))
            lean_src = build_lean_from_items(items[:n], fols[:n], seq_no=i)
            out_path = outdir / f"{args.basename}_{i:03d}.lean"
            out_path.write_text(lean_src, encoding="utf-8")
            print(f"Wrote {out_path}")
        return

    # ---------- Legacy single-output paths (kept for back-compat) ----------

    def norm_label_legacy(label: Optional[str]) -> str:
        return norm_label(label)

    def load_items_from_json(path: pathlib.Path) -> List[Dict]:
        raw = path.read_text(encoding="utf-8").strip()
        items: List[Dict] = []
        try:
            obj = json.loads(raw)
            if isinstance(obj, dict): obj = [obj]
            if isinstance(obj, list): items = obj
        except json.JSONDecodeError:
            items = [json.loads(ln) for ln in raw.splitlines() if ln.strip()]
        out = []
        for i, it in enumerate(items, 1):
            text = it.get("text") or it.get("sentence")
            if not text:
                raise ValueError(f"JSON item {i} missing 'text'.")
            out.append({
                "text": text.strip(),
                "label": norm_label_legacy(it.get("label")),
                "name": it.get("name"),
                "negated": bool(it.get("negated", False)),
            })
        return out

    def load_items_from_plain(sent_path: Optional[pathlib.Path], labels_path: Optional[pathlib.Path]) -> List[Dict]:
        if sent_path:
            sentences = [s.strip() for s in sent_path.read_text(encoding="utf-8").splitlines() if s.strip()]
        else:
            sentences = [s.strip() for s in sys.stdin.read().splitlines() if s.strip()]
        if not sentences:
            sys.exit("No sentences provided.")
        if labels_path and labels_path.exists():
            labels = [norm_label_legacy(s) for s in labels_path.read_text(encoding="utf-8").splitlines()]
            if len(labels) < len(sentences):
                labels += ["axiom"] * (len(sentences) - len(labels))
            else:
                labels = labels[:len(sentences)]
        else:
            labels = ["axiom"] * len(sentences)
        items = []
        for i, (txt, lab) in enumerate(zip(sentences, labels), 1):
            neg = (lab == "negated-theorem")
            base = lab if lab != "negated-theorem" else "theorem"
            items.append({"text": txt, "label": base, "name": None, "negated": neg})
        return items

    if args.json:
        items = load_items_from_json(pathlib.Path(args.json))
    else:
        sent_path = pathlib.Path(args.input) if args.input else None
        labels_path = pathlib.Path(args.labels) if args.labels else None
        items = load_items_from_plain(sent_path, labels_path)

    sentences = [it["text"] for it in items]
    if not sentences:
        sys.exit("No sentences provided.")

    # per-sentence formulas
    try:
        xml = run_depccg_xml(sentences, args.model, args.annotator)
        fols = extract_fols_per_sentence_from_xml(xml, num_inputs=len(sentences))
        if len(fols) != len(sentences):
            sys.stderr.write("[info] XML did not yield one formula per sentence; trying text fallback.\n")
            fols = run_depccg_text_multi(sentences, args.model, args.annotator)
    except Exception:
        fols = run_depccg_text_multi(sentences, args.model, args.annotator)
    if not fols:
        sys.exit("No formulas found (XML or text).")
    if len(fols) != len(sentences):
        sys.stderr.write(f"[warn] Found {len(fols)} formulas for {len(sentences)}; truncating to min.\n")
    n = min(len(fols), len(sentences))
    # Adapt items for single-output build
    seq_items = []
    for k, it in enumerate(items[:n], 1):
        seq_items.append({
            "text": it["text"], "label": it["label"], "name": it.get("name"),
            "negated": it.get("negated", False)
        })
    lean_src = build_lean_from_items(seq_items, fols[:n], seq_no=1)
    pathlib.Path(args.out).write_text(lean_src, encoding="utf-8")
    print(f"Wrote {args.out}")

if __name__ == "__main__":
    main()