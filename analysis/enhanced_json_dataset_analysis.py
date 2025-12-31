#!/usr/bin/env python3
"""
Enhanced JSON Dataset Analysis Script for FormalizeCoT Project

This script analyzes JSON files in amr-frame-50-gemini-2.5-flash folder
organized by datasets (aqua, gsm8k, math, prontoqa, worldtree).

Each JSON file contains round-indexed data in JSONL format. The script computes:
- Overall statistics per dataset
- Round analysis (max rounds, success rate per round)
- Error type classification
- Dataset comparison

Outputs:
- enhanced_json_dataset_report.txt
- enhanced_json_dataset_results.json
"""

import os
import json
from pathlib import Path
from collections import Counter, defaultdict

class EnhancedJSONDatasetAnalyzer:
    def __init__(self, base_path: str, method_path: str = '../data/output/AMR-Frame-GPT5mini', method_name: str = 'AMR-Frame'):
        self.base_path = Path(base_path)
        self.method_name = method_name
        # method_path may be passed relative to base_path
        self.method_path = Path(method_path)
        self.results = {}

        # Detect datasets automatically from subfolders under the method path
        self.datasets = self._detect_datasets()

        # Output filename prefix (sanitize method name and method path last segment)
        def _sanitize(s: str) -> str:
            import re
            s = s.strip().lower()
            s = re.sub(r"[^a-z0-9]+", "_", s)
            s = s.strip("_")
            return s

        last_seg = self.method_path.name
        # avoid duplicating method name when it already appears in last_seg
        nm = self.method_name.strip().lower().replace(' ', '').replace('-', '').replace('_', '')
        ls = last_seg.strip().lower().replace(' ', '').replace('-', '').replace('_', '')
        if nm and nm in ls:
            prefix_base = last_seg
        else:
            prefix_base = f"{self.method_name}_{last_seg}"

        self.output_prefix = _sanitize(prefix_base)

    def analyze_json_file(self, file_path: Path) -> dict:
        """Analyze a single JSON file (JSONL format)."""
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

        max_rounds = len(rounds)
        success_round = last_success
        error_type = self.classify_error_type(rounds, last_error)
        has_meaningful_content = False if immediate_failures else True
        content_length = sum(len(r['lean_code']) for r in rounds if r['lean_code'])
        
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
        """Classify the type of error encountered."""
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

    def analyze_dataset(self, dataset: str) -> dict:
        """Analyze all JSON files in a specific dataset."""
        dataset_dir = (self.base_path / self.method_path / dataset).resolve()
        if not dataset_dir.exists():
            print(f"Dataset directory not found: {dataset_dir}")
            return {}
        
        json_files = list(dataset_dir.glob('*.json'))
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
        
        return {
            'method_name': self.method_name,
            'dataset': dataset,
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
            'error_stats': error_stats
        }

    def analyze_rounds(self, file_analyses):
        """Analyze round statistics across files."""
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
        """Analyze error type statistics."""
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

    def analyze_all_datasets(self):
        """Analyze all datasets."""
        for dataset in self.datasets:
            print(f"Analyzing {self.method_name} - {dataset} ...")
            self.results[dataset] = self.analyze_dataset(dataset)

    def generate_report(self) -> str:
        """Generate comprehensive analysis report."""
        report = []
        report.append("=" * 80)
        report.append("ENHANCED FORMALIZE COT JSON DATASET ANALYSIS REPORT")
        report.append(f"Method: {self.method_name}")
        report.append("=" * 80)
        report.append("")
        
        report.append("OVERALL STATISTICS BY DATASET:")
        report.append("-" * 40)
        
        # Summary table
        report.append(f"{'Dataset':<12} {'Total':<8} {'Success':<8} {'Fail Imm':<10} {'Fail Rnd':<10} {'Success %':<10}")
        report.append("-" * 60)
        
        for dataset in self.datasets:
            result = self.results.get(dataset)
            if not result or result['total_files'] == 0:
                report.append(f"{dataset:<12} No data.")
                continue
            
            error_stats = result['error_stats']
            success_rate = (error_stats['successes'] / result['total_files']) * 100 if result['total_files'] else 0
            report.append(f"{dataset:<12} {result['total_files']:<8} {error_stats['successes']:<8} "
                        f"{error_stats['immediate_failures']:<10} {error_stats['failed_after_rounds']:<10} "
                        f"{success_rate:<10.1f}%")
        
        report.append("")
        report.append("DETAILED ANALYSIS BY DATASET:")
        report.append("=" * 80)
        
        for dataset in self.datasets:
            result = self.results.get(dataset)
            if not result or result['total_files'] == 0:
                report.append(f"\n{dataset}: No data.\n")
                continue
            
            report.append(f"\n{dataset.upper()}:")
            report.append("-" * 40)
            report.append(f"Total JSON files: {result['total_files']}")
            report.append(f"Files with meaningful content: {result['meaningful_files']}")
            report.append(f"Meaningful content percentage: {result['meaningful_percentage']:.2f}%")
            report.append(f"Average content length: {result['avg_content_length']:.0f} characters")
            report.append(f"Median content length: {result['median_content_length']:.0f} characters")
            
            report.append("\nRound Analysis:")
            round_stats = result['round_stats']
            report.append("  Max rounds per problem:")
            for rounds, count in sorted(round_stats['max_rounds_distribution'].items()):
                percentage = (count / result['total_files']) * 100
                report.append(f"    {rounds} rounds: {count} problems ({percentage:.1f}%)")
            
            if round_stats['success_rates_by_round']:
                report.append("  Success rate by round:")
                for round_num in sorted(round_stats['success_rates_by_round'].keys()):
                    success_rate = round_stats['success_rates_by_round'][round_num]
                    total_attempts = round_stats['total_by_round'].get(round_num, 0)
                    successes = round_stats['success_by_round'].get(round_num, 0)
                    report.append(f"    Round {round_num}: {success_rate:.1f}% ({successes}/{total_attempts})")
            
            error_stats = result['error_stats']
            report.append("\nError Analysis:")
            report.append("  Error types:")
            for error_type, count in sorted(error_stats['error_type_counts'].items(), key=lambda x: x[1], reverse=True):
                percentage = (count / result['total_files']) * 100
                report.append(f"    {error_type}: {count} ({percentage:.1f}%)")
            
            report.append("  Summary:")
            report.append(f"    Immediate failures: {error_stats['immediate_failures']}")
            report.append(f"    Failed after rounds: {error_stats['failed_after_rounds']}")
            report.append(f"    Successes: {error_stats['successes']}")
        
        report.append("\n" + "=" * 80)
        report.append("DATASET COMPARISON:")
        report.append("-" * 40)
        
        comparison_data = []
        for dataset in self.datasets:
            result = self.results.get(dataset)
            if result and result['total_files'] > 0:
                error_stats = result['error_stats']
                success_rate = (error_stats['successes'] / result['total_files']) * 100
                round_stats = result['round_stats']
                avg_rounds = sum(r * c for r, c in round_stats['max_rounds_distribution'].items()) / sum(round_stats['max_rounds_distribution'].values()) if round_stats['max_rounds_distribution'] else 0
                comparison_data.append({
                    'dataset': dataset,
                    'total_files': result['total_files'],
                    'success_rate': success_rate,
                    'avg_rounds': avg_rounds,
                    'immediate_failures': error_stats['immediate_failures'],
                    'failed_after_rounds': error_stats['failed_after_rounds'],
                    'successes': error_stats['successes']
                })
        
        comparison_data.sort(key=lambda x: x['success_rate'], reverse=True)
        report.append(f"{'Dataset':<12} {'Total':<8} {'Success %':<12} {'Avg Rounds':<12} {'Imm Fail':<10} {'Failed Rnd':<12}")
        report.append("-" * 80)
        for data in comparison_data:
            report.append(f"{data['dataset']:<12} {data['total_files']:<8} {data['success_rate']:<12.1f} "
                        f"{data['avg_rounds']:<12.1f} {data['immediate_failures']:<10} {data['failed_after_rounds']:<12}")
        
        report.append("\nRECOMMENDATIONS:")
        report.append("-" * 40)
        if comparison_data:
            best = comparison_data[0]
            worst = comparison_data[-1]
            report.append(f"Best performing dataset: {best['dataset']}")
            report.append(f"  Success rate: {best['success_rate']:.1f}%")
            report.append(f"  Average rounds: {best['avg_rounds']:.1f}")
            report.append(f"  Total files: {best['total_files']}")
            report.append(f"\nChallenging dataset: {worst['dataset']}")
            report.append(f"  Success rate: {worst['success_rate']:.1f}%")
            report.append(f"  Average rounds: {worst['avg_rounds']:.1f}")
            report.append(f"  Total files: {worst['total_files']}")
        
        return "\n".join(report)

    def save_results(self):
        """Save detailed results to JSON."""
        json_results = {
            'method_name': self.method_name,
            'method_path': str(self.method_path),
            'datasets': {}
        }

        for dataset, result in self.results.items():
            if result:
                json_results['datasets'][dataset] = {
                    'method_name': result['method_name'],
                    'dataset': result['dataset'],
                    'total_files': result['total_files'],
                    'meaningful_files': result['meaningful_files'],
                    'meaningful_percentage': result['meaningful_percentage'],
                    'avg_content_length': result['avg_content_length'],
                    'median_content_length': result['median_content_length'],
                    'min_content_length': result['min_content_length'],
                    'max_content_length': result['max_content_length'],
                    'content_lengths': result['content_lengths'],
                    'round_stats': result['round_stats'],
                    'error_stats': result['error_stats']
                }

        out_name = f'enhanced_json_dataset_results_{self.output_prefix}.json'
        with open(out_name, 'w') as f:
            json.dump(json_results, f, indent=2)
        print(f"Saved dataset results to {out_name}")

        return out_name

    def _detect_datasets(self):
        """Detect dataset subfolders under the configured method path."""
        p = (self.base_path / self.method_path).resolve()
        if not p.exists():
            print(f"Warning: method path does not exist: {p}")
            return []

        datasets = []
        try:
            for child in sorted(p.iterdir()):
                if child.is_dir():
                    datasets.append(child.name)
        except Exception as e:
            print(f"Error detecting datasets in {p}: {e}")
        return datasets

    def run_analysis(self):
        """Run the complete analysis."""
        print("Starting Enhanced FormalizeCoT JSON Dataset Analysis...")
        print("=" * 60)
        self.analyze_all_datasets()
        report = self.generate_report()
        print(report)
        report_name = f'enhanced_json_dataset_report_{self.output_prefix}.txt'
        with open(report_name, 'w') as f:
            f.write(report)
        out_name = self.save_results()
        print("\nEnhanced JSON dataset analysis complete!")
        print("Files generated:")
        print(f"- {report_name}: Comprehensive summary report")
        print(f"- {out_name}: Detailed numerical results")


def main():
    base_path = "./"

    # --- Configurable variables ---
    # Set the method path (where model outputs are stored) and display name here.
    # Examples:
    # method_path = '../data/output/AMR-Frame-GPT5mini'
    # method_name = 'AMR-Frame'
    method_path = '../data/output/AMR-Frame-GPT5mini'
    method_name = 'AMR-Frame'

    analyzer = EnhancedJSONDatasetAnalyzer(base_path, method_path=method_path, method_name=method_name)
    analyzer.run_analysis()

    method_path = '../data/output/AMR-Role-GPT5mini'
    method_name = 'AMR-Role'

    analyzer = EnhancedJSONDatasetAnalyzer(base_path, method_path=method_path, method_name=method_name)
    analyzer.run_analysis()
    method_path = '../data/output/autof1-GPT5mini'
    method_name = 'autof1'

    analyzer = EnhancedJSONDatasetAnalyzer(base_path, method_path=method_path, method_name=method_name)
    analyzer.run_analysis()

    method_path = '../data/output/autof2-GPT5mini'
    method_name = 'autof2'

    analyzer = EnhancedJSONDatasetAnalyzer(base_path, method_path=method_path, method_name=method_name)
    analyzer.run_analysis()
if __name__ == "__main__":
    main()
