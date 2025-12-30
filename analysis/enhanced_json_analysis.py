#!/usr/bin/env python3
"""
Enhanced JSON Log Analysis Script for FormalizeCoT Project

This script analyzes JSON files in three folders:
- amr-frame-50-gemini-2.5-flash
- auto-50-gemini-2.5-flash
- auto2-50-gemini-2.5-flash

Each JSON file contains round-indexed data. The script computes:
- Overall statistics
- Round analysis (max rounds, success rate per round)
- Error type classification
- Method comparison

Outputs:
- enhanced_analysis_report.txt
- enhanced_analysis_results.json
"""

import os
import json
from pathlib import Path
from collections import Counter, defaultdict

class EnhancedJSONAnalyzer:
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.methods = {
            # 'Auto': 'autof-50-gemini-2.5-flash',
            # 'Auto2': 'autof2-50-gemini-2.5-flash',
            'AMR-Frame': '../data/output/AMR-Frame-GPT5mini',
            # 'AMR-Role': '../data/output/AMR-Role-GPT5mini',
            # 'AMR-Role': 'amr-role-50-gemini-2.5-flash'
        }
        self.results = {}

    def analyze_json_file(self, file_path: Path) -> dict:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
        except Exception as e:
            return {
                'file_path': str(file_path),
                'has_meaningful_content': False,
                'content_length': 0,
                'error': str(e),
                'rounds': [],
                'max_rounds': 0,
                'success_round': None,
                'error_type': 'file_read_error'
            }

        rounds = []
        last_error = None
        last_success = None
        immediate_failures = 0
        failed_after_rounds = 0
        successes = 0

        for idx, line in enumerate(lines):
            try:
                obj = json.loads(line)
            except Exception:
                continue
            
            # Check for preflight status
            if 'preflight_ok' in obj and obj['preflight_ok'] is False:
                immediate_failures = 1
                break  # Skip further analysis for this file

            elif 'event' in obj and obj['event'] == 'round-end':
                round_num = int(obj.get('round', idx + 1))
                lean_code = obj.get('lean_code', '')
                error = obj.get('error', '')
                has_error = bool(error and error.strip())
                rounds.append({
                    'round_number': round_num,
                    'lean_code': lean_code,
                    'error': error,
                    'has_error': has_error
                })
                if not has_error:
                    last_success = round_num
                    successes = 1
                    failed_after_rounds = 0
                else:
                    last_error = error
                    failed_after_rounds = 1

        # if immediate_failures:
        #     successes = 0
        #     last_error = None
        #     last_success = None
        #     failed_after_rounds = 0



        max_rounds = len(rounds)
        success_round = last_success
        # if success_round:
        #     print(f"Success at round {success_round} for file {file_path}")
        error_type = self.classify_error_type(rounds, last_error)
        has_meaningful_content =  False if immediate_failures else True
        content_length = sum(len(r['lean_code']) for r in rounds if r['lean_code'])
        
        if successes + immediate_failures + failed_after_rounds != 1:
            print("Debug Info:")
            print(f"successes: {successes}, immediate_failures: {immediate_failures}, failed_after_rounds: {failed_after_rounds}")
            print(f"Warning: No outcomes recorded for file {file_path}.")
            var = input("Please check the file and press Enter to continue...")

        return {
            'file_path': str(file_path),
            'has_meaningful_content': has_meaningful_content,
            'content_length': content_length,
            'error': None,
            'rounds': rounds,
            'max_rounds': max_rounds,
            'success_round': success_round,
            'error_type': error_type,
            'immediate_failures': immediate_failures,
            'failed_after_rounds': failed_after_rounds,
            'successes': successes
        }

    def classify_error_type(self, rounds, last_error):
        if not rounds:
            return 'no_rounds'
        if rounds and not rounds[-1]['has_error']:
            return 'success'
        if last_error:
            err = last_error.lower()
            if 'unknown identifier' in err:
                return 'unknown_identifier'
            if 'unsolved goals' in err:
                return 'unsolved_goals'
            if 'type mismatch' in err:
                return 'type_mismatch'
            if 'failed to synthesize' in err:
                return 'synthesis_failed'
            if 'failed to prove' in err:
                return 'proof_failed'
            if 'lean system' in err:
                return 'lean_system_check_failed'
            if 'server_error' in err or 'error code: 500' in err:
                return 'server_error'
        return 'other_error'

    def analyze_method(self, method_name: str, method_path: str) -> dict:
        method_dir = self.base_path / method_path
        if not method_dir.exists():
            print(f"Method directory not found: {method_dir}")
            return {}
        json_files = list(method_dir.glob('**/*.json'))  # Analyze all JSON files in subdirectories
        file_analyses = []
        for file_path in json_files:
            analysis = self.analyze_json_file(file_path)
            file_analyses.append(analysis)
        
        meaningful_files = [f for f in file_analyses if f['has_meaningful_content']]
        meaningful_percentage = (len(meaningful_files) / len(file_analyses)) * 100 if file_analyses else 0
        content_lengths = [f['content_length'] for f in file_analyses if f['content_length'] > 0]
        avg_length = sum(content_lengths) / len(content_lengths) if content_lengths else 0
        sorted_lengths = sorted(content_lengths)
        median_length = sorted_lengths[len(sorted_lengths)//2] if sorted_lengths else 0
        round_stats = self.analyze_rounds(file_analyses)
        error_stats = self.analyze_error_types(file_analyses)
        
        # total_examples = sum(f['immediate_failures'] + f['failed_after_rounds'] + f['successes'] for f in file_analyses)
        total_examples = len(file_analyses)
        return {
            'method_name': method_name,
            'total_files': len(file_analyses),
            'meaningful_files': len(meaningful_files),
            'meaningful_percentage': meaningful_percentage,
            'file_analyses': file_analyses,
            'content_lengths': content_lengths,
            'avg_content_length': avg_length,
            'median_content_length': median_length,
            'min_content_length': min(content_lengths) if content_lengths else 0,
            'max_content_length': max(content_lengths) if content_lengths else 0,
            'round_stats': round_stats,
            'error_stats': error_stats,
            'total_examples': total_examples
        }

    def analyze_rounds(self, file_analyses):
        round_counts = Counter()
        success_by_round = defaultdict(int)
        total_by_round = defaultdict(int)
        max_rounds_distribution = Counter()
        for analysis in file_analyses:
            max_rounds = analysis['max_rounds']
            success_round = analysis['success_round']
            max_rounds_distribution[max_rounds] += 1
            if max_rounds > 0:
                round_counts[max_rounds] += 1
                for round_num in range(1, max_rounds + 1):
                    total_by_round[round_num] += 1
                    if success_round == round_num:
                        success_by_round[round_num] += 1
        success_rates_by_round = {}
        for round_num in total_by_round:
            if total_by_round[round_num] > 0:
                success_rates_by_round[round_num] = (success_by_round[round_num] / total_by_round[round_num]) * 100
        return {
            'round_counts': dict(round_counts),
            'max_rounds_distribution': dict(max_rounds_distribution),
            'success_by_round': dict(success_by_round),
            'total_by_round': dict(total_by_round),
            'success_rates_by_round': success_rates_by_round
        }

    def analyze_error_types(self, file_analyses):
        error_type_counts = Counter()
        immediate_failures = 0
        failed_after_rounds = 0
        successes = 0
        for analysis in file_analyses:
            error_type = analysis['error_type']
            error_type_counts[error_type] += 1
            immediate_failures += analysis.get('immediate_failures', 0)
            failed_after_rounds += analysis.get('failed_after_rounds', 0)
            successes += analysis.get('successes', 0)
        return {
            'error_type_counts': dict(error_type_counts),
            'immediate_failures': immediate_failures,
            'failed_after_rounds': failed_after_rounds,
            'successes': successes
        }

    def analyze_all_methods(self):
        for method_name, method_path in self.methods.items():
            print(f"\nAnalyzing {method_name} method...")
            self.results[method_name] = self.analyze_method(method_name, method_path)

    def generate_enhanced_report(self) -> str:
        report = []
        report.append("=" * 80)
        report.append("ENHANCED FORMALIZE COT LOG ANALYSIS REPORT")
        report.append("=" * 80)
        report.append("")
        report.append("OVERALL STATISTICS:")
        report.append("-" * 40)
        for method_name, result in self.results.items():
            if result:
                report.append(f"{method_name}:")
                report.append(f"  Total log files: {result['total_files']}")
                report.append(f"  Files with meaningful content: {result['meaningful_files']}")
                report.append(f"  Meaningful content percentage: {result['meaningful_percentage']:.2f}%")
                report.append(f"  Average content length: {result['avg_content_length']:.0f} characters")
                report.append(f"  Total examples: {result['total_examples']}")
                report.append("")
        report.append("ROUND ANALYSIS:")
        report.append("-" * 40)
        for method_name, result in self.results.items():
            if result and 'round_stats' in result:
                round_stats = result['round_stats']
                report.append(f"\n{method_name} Round Statistics:")
                report.append("  Max rounds per problem:")
                for rounds, count in sorted(round_stats['max_rounds_distribution'].items()):
                    percentage = (count / result['total_files']) * 100
                    report.append(f"    {rounds} rounds: {count} problems ({percentage:.1f}%)")
                if round_stats['success_rates_by_round']:
                    report.append("  Success rate by round:")
                    for round_num in sorted(round_stats['success_rates_by_round'].keys()):
                        success_rate = round_stats['success_rates_by_round'][round_num]
                        total_attempts = round_stats['total_by_round'].get(round_num, 0)
                        report.append(f"    Round {round_num}: {success_rate:.1f}% ({round_stats['success_by_round'].get(round_num, 0)}/{total_attempts})")
        report.append("\nERROR TYPE ANALYSIS:")
        report.append("-" * 40)
        for method_name, result in self.results.items():
            if result and 'error_stats' in result:
                error_stats = result['error_stats']
                report.append(f"\n{method_name} Error Statistics:")
                report.append("  Error types:")
                for error_type, count in error_stats['error_type_counts'].items():
                    percentage = (count / result['total_files']) * 100
                    report.append(f"    {error_type}: {count} ({percentage:.1f}%)")
                report.append("  Summary:")
                report.append(f"    Immediate failures: {error_stats['immediate_failures']}")
                report.append(f"    Failed after rounds: {error_stats['failed_after_rounds']}")
                report.append(f"    Successes: {error_stats['successes']}")
        report.append("\nMETHOD COMPARISON:")
        report.append("-" * 40)
        comparison_data = []
        for method_name, result in self.results.items():
            if result and 'error_stats' in result:
                error_stats = result['error_stats']
                success_rate = (error_stats['successes'] / result['total_files']) * 100 if result['total_files'] else 0
                round_stats = result['round_stats']
                avg_rounds = sum(round_stats['max_rounds_distribution'].keys()) / len(round_stats['max_rounds_distribution']) if round_stats['max_rounds_distribution'] else 0
                comparison_data.append({
                    'method': method_name,
                    'success_rate': success_rate,
                    'avg_rounds': avg_rounds,
                    'immediate_failures': error_stats['immediate_failures'],
                    'failed_after_rounds': error_stats['failed_after_rounds']
                })
        comparison_data.sort(key=lambda x: x['success_rate'], reverse=True)
        report.append(f"{'Method':<12} {'Success Rate':<12} {'Avg Rounds':<12} {'Immediate Fail':<15} {'Failed After Rounds':<20}")
        report.append("-" * 80)
        for data in comparison_data:
            report.append(f"{data['method']:<12} {data['success_rate']:<12.1f} {data['avg_rounds']:<12.1f} "
                        f"{data['immediate_failures']:<15} {data['failed_after_rounds']:<20}")
        report.append("\nFINAL RECOMMENDATIONS:")
        report.append("-" * 40)
        if comparison_data:
            best_method = comparison_data[0]
            report.append(f"Best performing method: {best_method['method']}")
            report.append(f"  Success rate: {best_method['success_rate']:.1f}%")
            report.append(f"  Average rounds: {best_method['avg_rounds']:.1f}")
            report.append(f"  Immediate failures: {best_method['immediate_failures']}")
            report.append(f"  Failed after rounds: {best_method['failed_after_rounds']}")
        return "\n".join(report)

    def save_enhanced_results(self):
        json_results = {}
        for method_name, result in self.results.items():
            if result:
                json_results[method_name] = {
                    'method_name': result['method_name'],
                    'total_files': result['total_files'],
                    'meaningful_files': result['meaningful_files'],
                    'meaningful_percentage': result['meaningful_percentage'],
                    'avg_content_length': result['avg_content_length'],
                    'median_content_length': result['median_content_length'],
                    'min_content_length': result['min_content_length'],
                    'max_content_length': result['max_content_length'],
                    'content_lengths': result['content_lengths'],
                    'round_stats': result['round_stats'],
                    'error_stats': result['error_stats'],
                    'total_examples': result['total_examples']
                }
        with open('./enhanced_analysis_results.json', 'w') as f:
            json.dump(json_results, f, indent=2)

    def run_analysis(self):
        print("Starting Enhanced FormalizeCOT JSON Log Analysis...")
        print("=" * 60)
        self.analyze_all_methods()
        report = self.generate_enhanced_report()
        print(report)
        with open('./enhanced_analysis_report.txt', 'w') as f:
            f.write(report)
        self.save_enhanced_results()
        print("\nEnhanced analysis complete!")
        print("Files generated:")
        print("- enhanced_analysis_report.txt: Enhanced summary report")
        print("- enhanced_analysis_results.json: Enhanced numerical results")

def main():
    base_path = "./"
    analyzer = EnhancedJSONAnalyzer(base_path)
    analyzer.run_analysis()

if __name__ == "__main__":
    main()