#!/usr/bin/env python3
"""
Formalization Test Module

This module evaluates Lean code files for syntactic correctness using the lean_interact library.
It traverses a two-level folder structure, evaluates each .lean file, and records any 
compilation errors to a CSV file for later diagnosis.

Usage:
    python formalization-test.py --folder <path_to_lean_folder> [--output <output_csv>] [--lean-version <version>]

Example:
    python formalization-test.py --folder ./lean_code --output errors.csv --lean-version v4.12.0
"""

import argparse
import csv
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Optional

try:
    from lean_interact import LeanREPLConfig, LeanServer, Command
except ImportError:
    print("Error: lean_interact is not installed. Install it with: pip install lean-interact")
    sys.exit(1)


# Default Lean version - lean_interact supports versions between v4.8.0-rc1 and v4.26.0-rc2
DEFAULT_LEAN_VERSION = "v4.23.0"

# Supported Lean version range for reference
SUPPORTED_LEAN_VERSIONS = {
    "min": "v4.8.0-rc1",
    "max": "v4.26.0-rc2",
    "recommended": ["v4.23.0", "v4.24.0", "v4.25.0", "v4.26.0-rc2", "v4.12.0"]
}


def find_lean_files(root_folder: str, max_depth: int = 2) -> list[tuple[str, str, str]]:
    """
    Find all .lean files in the given directory up to the specified depth.
    
    The folder structure is expected to be:
        root_folder/
        └── level1_folder/
            └── level2_folder/
                └── file.lean
    
    Args:
        root_folder: Path to the root folder containing Lean code
        max_depth: Maximum depth to search for .lean files (default: 2)
    
    Returns:
        List of tuples containing (full_path, relative_folder, filename)
    """
    lean_files = []
    root_path = Path(root_folder).resolve()
    
    if not root_path.exists():
        raise FileNotFoundError(f"Folder not found: {root_folder}")
    
    if not root_path.is_dir():
        raise NotADirectoryError(f"Not a directory: {root_folder}")
    
    for dirpath, _, filenames in os.walk(root_path):
        current_path = Path(dirpath)
        # Calculate depth relative to root
        try:
            rel_path = current_path.relative_to(root_path)
            depth = len(rel_path.parts)
        except ValueError:
            depth = 0
        
        # Only process files within max_depth
        if depth <= max_depth:
            for filename in filenames:
                if filename.endswith('.lean'):
                    full_path = current_path / filename
                    # Get the relative folder path from root
                    rel_folder = str(rel_path) if depth > 0 else "."
                    lean_files.append((str(full_path), rel_folder, filename))
    
    return lean_files


def create_lean_server(lean_version: str, verbose: bool = False) -> LeanServer:
    """
    Create and configure a Lean server instance.
    
    Args:
        lean_version: The Lean version to use (e.g., 'v4.12.0')
        verbose: Whether to enable verbose output
    
    Returns:
        Configured LeanServer instance
    """
    config = LeanREPLConfig(
        lean_version=lean_version,
        verbose=verbose
    )
    return LeanServer(config)


def evaluate_lean_file(server: LeanServer, file_path: str) -> dict:
    """
    Evaluate a Lean file for syntactic correctness.
    
    Args:
        server: The Lean server instance
        file_path: Path to the Lean file to evaluate
    
    Returns:
        Dictionary containing evaluation results with keys:
        - success: bool
        - messages: list of messages/warnings
        - errors: list of error messages
        - sorries: list of sorry locations (incomplete proofs)
        - env: environment ID if successful
    """
    result = {
        "success": False,
        "messages": [],
        "errors": [],
        "sorries": [],
        "env": None,
        "raw_result": None
    }
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            code = f.read()
        
        if not code.strip():
            result["success"] = True
            result["messages"].append("Empty file")
            return result
        
        command = Command(cmd=code)
        response = server.run(command)
        result["raw_result"] = response
        
        # Process the response - lean_interact returns different response types
        # Handle different response formats
        if hasattr(response, 'messages') and response.messages:
            for msg in response.messages:
                if hasattr(msg, 'severity'):
                    if msg.severity == 'error':
                        error_text = format_message(msg)
                        result["errors"].append(error_text)
                    else:
                        result["messages"].append(format_message(msg))
                else:
                    result["messages"].append(str(msg))
        
        if hasattr(response, 'sorries') and response.sorries:
            result["sorries"] = [format_sorry(s) for s in response.sorries]
        
        if hasattr(response, 'env'):
            result["env"] = response.env
        
        # Determine success based on errors
        if hasattr(response, 'error') and response.error:
            result["errors"].append(str(response.error))
            result["success"] = False
        elif result["errors"]:
            result["success"] = False
        else:
            result["success"] = True
            
    except FileNotFoundError:
        result["errors"].append(f"File not found: {file_path}")
    except UnicodeDecodeError as e:
        result["errors"].append(f"Encoding error: {str(e)}")
    except Exception as e:
        result["errors"].append(f"Evaluation error: {str(e)}")
    
    return result


def format_message(msg) -> str:
    """Format a Lean message for display."""
    parts = []
    if hasattr(msg, 'pos') and msg.pos:
        parts.append(f"[Line {msg.pos.get('line', '?')}:{msg.pos.get('column', '?')}]")
    if hasattr(msg, 'severity'):
        parts.append(f"({msg.severity})")
    if hasattr(msg, 'data'):
        parts.append(str(msg.data))
    elif hasattr(msg, 'message'):
        parts.append(str(msg.message))
    else:
        parts.append(str(msg))
    return " ".join(parts)


def format_sorry(sorry) -> str:
    """Format a sorry location for display."""
    if hasattr(sorry, 'pos'):
        return f"Sorry at line {sorry.pos.get('line', '?')}"
    return str(sorry)


def save_results_to_csv(
    results: list[dict],
    output_file: str,
    lean_version: str
) -> tuple[int, int]:
    """
    Save evaluation results to a CSV file.
    
    Args:
        results: List of evaluation result dictionaries
        output_file: Path to the output CSV file
        lean_version: The Lean version used for evaluation
    
    Returns:
        Tuple of (total_files, failed_files)
    """
    # CSV headers for comprehensive diagnosis
    headers = [
        "code_folder",
        "file_name", 
        "full_path",
        "status",
        "error_count",
        "error_messages",
        "warning_count",
        "warnings",
        "sorry_count",
        "sorries",
        "lean_version",
        "evaluation_timestamp"
    ]
    
    timestamp = datetime.now().isoformat()
    total_files = len(results)
    failed_files = 0
    
    with open(output_file, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        
        for result in results:
            status = "PASS" if result["eval_result"]["success"] else "FAIL"
            if not result["eval_result"]["success"]:
                failed_files += 1
            
            row = {
                "code_folder": result["folder"],
                "file_name": result["filename"],
                "full_path": result["full_path"],
                "status": status,
                "error_count": len(result["eval_result"]["errors"]),
                "error_messages": " | ".join(result["eval_result"]["errors"]) if result["eval_result"]["errors"] else "",
                "warning_count": len(result["eval_result"]["messages"]),
                "warnings": " | ".join(result["eval_result"]["messages"]) if result["eval_result"]["messages"] else "",
                "sorry_count": len(result["eval_result"]["sorries"]),
                "sorries": " | ".join(result["eval_result"]["sorries"]) if result["eval_result"]["sorries"] else "",
                "lean_version": lean_version,
                "evaluation_timestamp": timestamp
            }
            writer.writerow(row)
    
    return total_files, failed_files


def save_errors_only_to_csv(
    results: list[dict],
    output_file: str,
    lean_version: str
) -> tuple[int, int]:
    """
    Save only failed evaluations to a CSV file.
    
    Args:
        results: List of evaluation result dictionaries
        output_file: Path to the output CSV file
        lean_version: The Lean version used for evaluation
    
    Returns:
        Tuple of (total_files, failed_files)
    """
    headers = [
        "code_folder",
        "file_name",
        "full_path", 
        "error_count",
        "error_messages",
        "sorry_count",
        "sorries",
        "lean_version",
        "evaluation_timestamp"
    ]
    
    timestamp = datetime.now().isoformat()
    total_files = len(results)
    failed_results = [r for r in results if not r["eval_result"]["success"]]
    
    with open(output_file, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        
        for result in failed_results:
            row = {
                "code_folder": result["folder"],
                "file_name": result["filename"],
                "full_path": result["full_path"],
                "error_count": len(result["eval_result"]["errors"]),
                "error_messages": " | ".join(result["eval_result"]["errors"]) if result["eval_result"]["errors"] else "",
                "sorry_count": len(result["eval_result"]["sorries"]),
                "sorries": " | ".join(result["eval_result"]["sorries"]) if result["eval_result"]["sorries"] else "",
                "lean_version": lean_version,
                "evaluation_timestamp": timestamp
            }
            writer.writerow(row)
    
    return total_files, len(failed_results)


def run_evaluation(
    target_folder: str,
    output_csv: str = "compilation_errors.csv",
    lean_version: str = DEFAULT_LEAN_VERSION,
    verbose: bool = False,
    errors_only: bool = True,
    max_depth: int = 2
) -> dict:
    """
    Run the full evaluation pipeline.
    
    Args:
        target_folder: Path to the folder containing Lean files
        output_csv: Path for the output CSV file
        lean_version: Lean version to use
        verbose: Enable verbose output
        errors_only: If True, only save errors to CSV; otherwise save all results
        max_depth: Maximum folder depth to search
    
    Returns:
        Dictionary with evaluation summary
    """
    print(f"=" * 60)
    print(f"Lean Formalization Test")
    print(f"=" * 60)
    print(f"Target folder: {target_folder}")
    print(f"Lean version: {lean_version}")
    print(f"Output CSV: {output_csv}")
    print(f"Max search depth: {max_depth}")
    print(f"-" * 60)
    
    # Find all Lean files
    print("Searching for .lean files...")
    try:
        lean_files = find_lean_files(target_folder, max_depth=max_depth)
    except (FileNotFoundError, NotADirectoryError) as e:
        print(f"Error: {e}")
        return {"success": False, "error": str(e)}
    
    if not lean_files:
        print("No .lean files found in the target folder.")
        return {"success": False, "error": "No .lean files found"}
    
    print(f"Found {len(lean_files)} .lean file(s)")
    print(f"-" * 60)
    
    # Initialize Lean server
    print(f"Initializing Lean server (version {lean_version})...")
    try:
        server = create_lean_server(lean_version, verbose=verbose)
    except Exception as e:
        print(f"Error initializing Lean server: {e}")
        return {"success": False, "error": f"Server initialization failed: {e}"}
    
    print("Lean server ready.")
    print(f"-" * 60)
    
    # Evaluate each file
    results = []
    for i, (full_path, folder, filename) in enumerate(lean_files, 1):
        print(f"[{i}/{len(lean_files)}] Evaluating: {folder}/{filename}...", end=" ")
        
        eval_result = evaluate_lean_file(server, full_path)
        results.append({
            "full_path": full_path,
            "folder": folder,
            "filename": filename,
            "eval_result": eval_result
        })
        
        if eval_result["success"]:
            print("✓ PASS")
        else:
            print(f"✗ FAIL ({len(eval_result['errors'])} error(s))")
            if verbose:
                for err in eval_result["errors"]:
                    print(f"    → {err}")
    
    print(f"-" * 60)
    
    # Save results to CSV
    print(f"Saving results to {output_csv}...")
    if errors_only:
        total, failed = save_errors_only_to_csv(results, output_csv, lean_version)
    else:
        total, failed = save_results_to_csv(results, output_csv, lean_version)
    
    # Summary
    passed = total - failed
    pass_rate = (passed / total * 100) if total > 0 else 0
    
    print(f"=" * 60)
    print(f"EVALUATION SUMMARY")
    print(f"=" * 60)
    print(f"Total files evaluated: {total}")
    print(f"Passed: {passed} ({pass_rate:.1f}%)")
    print(f"Failed: {failed} ({100 - pass_rate:.1f}%)")
    print(f"Results saved to: {output_csv}")
    print(f"=" * 60)
    
    return {
        "success": True,
        "total_files": total,
        "passed": passed,
        "failed": failed,
        "pass_rate": pass_rate,
        "output_csv": output_csv,
        "results": results
    }


def list_supported_versions():
    """Print information about supported Lean versions."""
    print("Supported Lean versions by lean_interact:")
    print(f"  Minimum: {SUPPORTED_LEAN_VERSIONS['min']}")
    print(f"  Maximum: {SUPPORTED_LEAN_VERSIONS['max']}")
    print(f"  Recommended: {', '.join(SUPPORTED_LEAN_VERSIONS['recommended'])}")


def main():
    """Main entry point for CLI usage."""
    parser = argparse.ArgumentParser(
        description="Evaluate Lean code files for syntactic correctness",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --folder ./lean_code
  %(prog)s --folder ./lean_code --output errors.csv --lean-version v4.12.0
  %(prog)s --folder ./lean_code --all-results --verbose
  %(prog)s --list-versions
        """
    )
    
    parser.add_argument(
        "--folder", "-f",
        type=str,
        help="Path to the folder containing Lean code files"
    )
    
    parser.add_argument(
        "--output", "-o",
        type=str,
        default="compilation_errors.csv",
        help="Output CSV file path (default: compilation_errors.csv)"
    )
    
    parser.add_argument(
        "--lean-version", "-l",
        type=str,
        default=DEFAULT_LEAN_VERSION,
        help=f"Lean version to use (default: {DEFAULT_LEAN_VERSION})"
    )
    
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose output"
    )
    
    parser.add_argument(
        "--all-results", "-a",
        action="store_true",
        help="Save all results (not just errors) to CSV"
    )
    
    parser.add_argument(
        "--max-depth", "-d",
        type=int,
        default=2,
        help="Maximum folder depth to search for .lean files (default: 2)"
    )
    
    parser.add_argument(
        "--list-versions",
        action="store_true",
        help="List supported Lean versions and exit"
    )
    
    args = parser.parse_args()
    
    if args.list_versions:
        list_supported_versions()
        return
    
    if not args.folder:
        parser.error("--folder is required unless using --list-versions")
    
    summary = run_evaluation(
        target_folder=args.folder,
        output_csv=args.output,
        lean_version=args.lean_version,
        verbose=args.verbose,
        errors_only=not args.all_results,
        max_depth=args.max_depth
    )
    
    # Exit with appropriate code
    if not summary.get("success"):
        sys.exit(1)
    elif summary.get("failed", 0) > 0:
        sys.exit(2)  # Some files failed compilation
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()

