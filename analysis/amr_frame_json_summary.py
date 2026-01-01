#!/usr/bin/env python3
"""amr_frame_json_summary.py

Generates a summary report from amr_frame_json_check_results.json.
Provides statistics on successful files, declarations, and external usage patterns.

Output: prints summary and writes `amr_frame_json_summary_report.txt`.
"""

import json
from collections import Counter
from statistics import mean, median

def generate_summary_report():
    """Generate summary report from the results JSON."""
    with open('amr_json_external_axiom_check_results_amr_frame_gpt5mini.json', 'r') as f:
        data = json.load(f)
    
    # Filter for successful files
    successful_files = {k: v for k, v in data.items() if v.get('successful')}
    unsuccessful_files = {k: v for k, v in data.items() if not v.get('successful')}
    
    # Statistics
    total_files = len(data)
    successful_count = len(successful_files)
    success_rate = (successful_count / total_files * 100) if total_files else 0
    
    report = []
    report.append("=" * 80)
    report.append("AMR-FRAME JSON ANALYSIS SUMMARY REPORT")
    report.append("=" * 80)
    report.append("")
    
    report.append("OVERALL STATISTICS:")
    report.append("-" * 40)
    report.append(f"Total JSON files analyzed: {total_files}")
    report.append(f"Successful files (last round error-free): {successful_count}")
    report.append(f"Unsuccessful files: {len(unsuccessful_files)}")
    report.append(f"Success rate: {success_rate:.1f}%")
    report.append("")
    
    if successful_count == 0:
        report.append("No successful files found. Skipping detailed analysis.")
        return "\n".join(report)
    
    # Declaration statistics
    report.append("DECLARATION STATISTICS (successful files only):")
    report.append("-" * 40)
    
    total_decls = [v['summary']['total_declarations'] for v in successful_files.values()]
    total_axioms = [v['summary']['total_axioms'] for v in successful_files.values()]
    total_theorems = [v['summary']['total_theorems'] for v in successful_files.values()]
    predefined_counts = [len(v['predefined']) for v in successful_files.values()]
    original_counts = [len(v['originals']) for v in successful_files.values()]
    external_counts = [len(v['externals']) for v in successful_files.values()]
    
    report.append(f"Total declarations per file:")
    report.append(f"  Average: {mean(total_decls):.1f}")
    report.append(f"  Median: {median(total_decls):.1f}")
    report.append(f"  Min: {min(total_decls)}, Max: {max(total_decls)}")
    report.append("")
    
    report.append(f"Axioms per file:")
    report.append(f"  Average: {mean(total_axioms):.1f}")
    report.append(f"  Median: {median(total_axioms):.1f}")
    report.append("")
    
    report.append(f"Theorems per file:")
    report.append(f"  Average: {mean(total_theorems):.1f}")
    report.append(f"  Median: {median(total_theorems):.1f}")
    report.append("")
    
    report.append(f"Predefined declarations per file:")
    report.append(f"  Average: {mean(predefined_counts):.1f}")
    report.append(f"  Median: {median(predefined_counts):.1f}")
    report.append("")
    
    report.append(f"Original declarations per file:")
    report.append(f"  Average: {mean(original_counts):.1f}")
    report.append(f"  Median: {median(original_counts):.1f}")
    report.append("")
    
    report.append(f"External declarations per file:")
    report.append(f"  Average: {mean(external_counts):.1f}")
    report.append(f"  Median: {median(external_counts):.1f}")
    report.append("")
    
    # Original theorems analysis
    report.append("ORIGINAL THEOREM ANALYSIS:")
    report.append("-" * 40)
    
    original_theorem_counts = [v['original_theorems_analysis']['total_original_theorems'] 
                               for v in successful_files.values()]
    original_theorem_total = sum(original_theorem_counts)
    
    report.append(f"Total original theorems across all successful files: {original_theorem_total}")
    report.append(f"Average original theorems per file: {mean(original_theorem_counts):.1f}")
    report.append("")
    
    # External usage patterns
    report.append("EXTERNAL USAGE PATTERNS:")
    report.append("-" * 40)
    
    all_external_percentages = []
    theorem_with_externals = 0
    theorem_without_externals = 0
    
    for file_result in successful_files.values():
        for theorem_info in file_result['original_theorems_analysis']['details']:
            percent = theorem_info['percent_of_externals_used']
            all_external_percentages.append(percent)
            if theorem_info['used_externals_count'] > 0:
                theorem_with_externals += 1
            else:
                theorem_without_externals += 1
    
    if all_external_percentages:
        report.append(f"Theorems using external declarations: {theorem_with_externals}")
        report.append(f"Theorems NOT using external declarations: {theorem_without_externals}")
        report.append("")
        report.append(f"Percentage of externals used per theorem (when used):")
        report.append(f"  Average: {mean(all_external_percentages):.1f}%")
        report.append(f"  Median: {median(all_external_percentages):.1f}%")
        report.append(f"  Min: {min(all_external_percentages):.1f}%, Max: {max(all_external_percentages):.1f}%")
    
    report.append("")
    report.append("=" * 80)
    
    return "\n".join(report)


def main():
    report = generate_summary_report()
    print(report)
    
    with open('amr_json_summary_report.txt', 'w') as f:
        f.write(report)
    
    print(f"\nReport written to amr_json_summary_report.txt")


if __name__ == "__main__":
    main()
