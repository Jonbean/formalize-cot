#!/usr/bin/env python3
"""
Scan a shared dir for JSON files named like:
  "COT DATASET SAMPLES - {key_name}_{non_keyname}.json"

Derive key_name (substring after the fixed prefix and before the first "_"),
create /out_base/{key_name} if needed, and (placeholder) run your processing.

Example:
  "COT DATASET SAMPLES - AbE_sss.json" -> out dir: /data/runs/AbE
"""

from __future__ import annotations
import argparse
import logging
import os
from pathlib import Path
import sys
import json
from propbank_interface import PropbankCatalogue
from amr2lean_batch_role_centric import AMR2LeanBatch as amr2lean_role
from amr2lean_batch_frame_centric import AMR2LeanBatch as amr2lean_frame

DEFAULT_PREFIX = "COT DATASET SAMPLES - "

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Prepare per-key output directories from shared JSON files.")
    p.add_argument("--shared-dir", required=True, type=Path,
                   help="Directory containing the JSON files.")
    p.add_argument("--out-base", required=True, type=Path,
                   help="Base directory under which per-key output dirs are created.")
    p.add_argument("--prefix", default=DEFAULT_PREFIX,
                   help=f"Fixed filename prefix (default: {DEFAULT_PREFIX!r}).")
    p.add_argument("--glob", default="*.json",
                   help="Glob to select input files (default: *.json).")
    p.add_argument("--dry-run", action="store_true",
                   help="Show what would be done without running the processing step.")
    p.add_argument("--f-or-r", default='r', help="role centric or frame centric translation")
    p.add_argument("-v", "--verbose", action="count", default=0,
                   help="Increase verbosity (-v, -vv).")

    return p.parse_args()

def setup_logging(verbosity: int) -> None:
    level = logging.WARNING
    if verbosity == 1:
        level = logging.INFO
    elif verbosity >= 2:
        level = logging.DEBUG
    logging.basicConfig(format="[%(levelname)s] %(message)s", level=level)

def extract_key_name(filename: str, prefix: str) -> str | None:
    """
    From 'COT DATASET SAMPLES - AbE_sss.json' with prefix = 'COT DATASET SAMPLES - ',
    return 'AbE'. If the pattern doesn't match, return None.
    """
    if not filename.startswith(prefix):
        return None
    tail = filename[len(prefix):]       # e.g., 'AbE_sss.json'
    # key_name is before the first underscore in tail
    try:
        idx = tail.index("_")
    except ValueError:
        return None
    key = tail[:idx].strip()
    return key or None

def ensure_dir(path: Path) -> None:
    if path.exists() and not path.is_dir():
        raise RuntimeError(f"Path exists but is not a directory: {path}")
    path.mkdir(parents=True, exist_ok=True)

def main() -> int:
    args = parse_args()
    setup_logging(args.verbose)

    shared_dir: Path = args.shared_dir
    out_base: Path = args.out_base
    prefix: str = args.prefix
    pattern: str = args.glob

    if not shared_dir.is_dir():
        logging.error("Shared dir does not exist or is not a directory: %s", shared_dir)
        return 2

    # Make sure the base output directory exists
    try:
        ensure_dir(out_base)
    except Exception as e:
        logging.error("Failed to ensure out_base: %s (%s)", out_base, e)
        return 2

    files = sorted(shared_dir.glob(pattern))
    if not files:
        logging.warning("No files matched %r in %s", pattern, shared_dir)

    processed = 0
    skipped = 0
    pb_catalog = PropbankCatalogue("/Users/jonzcai/Documents/ComputerScience/NLP/data/datasets/propbank-frames/frames/")

    for path in files:
        fname = path.name
        key = extract_key_name(fname, prefix)
        if key is None:
            logging.info("Skip: does not match prefix/pattern: %s", fname)
            skipped += 1
            continue

        out_dir = out_base / key

        try:
            ensure_dir(out_dir)
        except Exception as e:
            logging.error("Cannot create output dir %s for %s: %s", out_dir, fname, e)
            skipped += 1
            continue

        logging.info("Input: %s", path)
        logging.info("Output dir: %s", out_dir)

        if args.dry_run:
            processed += 1
            continue

        with open(str(path), 'r') as f:
            data = json.load(f)
            for idx, rationale in enumerate(data):


                batch = amr2lean_role(pb_catalog, import_semantic_gadgets=False, label_map=None, shorter_variant=True, include_nl_comment=True)
                if args.f_or_r == 'f':
                    batch = amr2lean_frame(pb_catalog, import_semantic_gadgets=False, label_map=None, include_nl_comment=True)
                    
                lean_code = batch.translate_many(rationale)
                saving_path = os.path.join(out_dir, 'rationale-'+str(idx)+'.lean')
                with open(saving_path , 'w') as g:
                    g.write(lean_code)

        processed += 1


    logging.warning("Done. processed=%d, skipped=%d", processed, skipped)
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nInterrupted.", file=sys.stderr)
        sys.exit(130)