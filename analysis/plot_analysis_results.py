import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
import seaborn as sns
import os

# Set style
sns.set_style("whitegrid")
plt.rcParams['figure.figsize'] = (14, 8)

# When True, save PDF copies for all plots in addition to PNGs
SAVE_AS_PDF = True


def _savefig(fname, dpi=300):
    """Save current matplotlib figure to fname and, if enabled, a PDF with same base name.

    fname may include an extension (e.g., .png). The PDF will use the same base name.
    """
    # Ensure directory exists
    d = os.path.dirname(fname)
    if d and not os.path.exists(d):
        os.makedirs(d, exist_ok=True)

    plt.savefig(fname, dpi=dpi, bbox_inches='tight')
    if SAVE_AS_PDF:
        base, ext = os.path.splitext(fname)
        pdf_name = base + '.pdf'
        plt.savefig(pdf_name, dpi=dpi, bbox_inches='tight')

def load_json(file_path):
    """Load JSON file"""
    with open(file_path, 'r') as f:
        return json.load(f)


def _load_ext_results_for_method(method_hint=None, pattern='amr_frame_json_check_results_*.json'):
    """Load external-check JSON result files matching pattern.

    Returns a tuple (files_map, chosen_filename_or_None) where:
      - files_map is a dict mapping each matching filename -> its loaded JSON dict
      - chosen_filename_or_None is the filename that best matches method_hint (if any)

    Important: this function *does not merge* multiple files. Callers that want
    a per-method selection should pick the appropriate file from files_map. This
    avoids accidental mixing of different-method results.
    """
    from glob import glob
    files = sorted(glob(pattern))
    # If nothing found for the requested pattern, try common alternate patterns
    if not files:
        fallback_patterns = [
            'amr_json_external_axiom_check_results_*.json',
            'amr_frame_json_check_results_*.json',
            '*json_check_results*.json'
        ]
        for p in fallback_patterns:
            if p == pattern:
                continue
            files = sorted(glob(p))
            if files:
                # update pattern variable for informative messages
                pattern = p
                break
    if not files:
        return {}, None

    files_map = {}
    for f in files:
        try:
            files_map[f] = load_json(f)
        except Exception:
            # skip files that fail to load
            continue

    if method_hint:
        method_hint_l = method_hint.lower()
        # try exact match in filename stem
        for f in files_map.keys():
            if method_hint_l in Path(f).stem.lower():
                return files_map, f

        # token-based matching (split method_hint into parts and match tokens)
        try:
            import re
            raw_tokens = [t for t in re.split(r'[_\-\s]+', method_hint_l) if len(t) > 2]
            blacklist = set(['enhanced', 'json', 'dataset', 'results', 'gpt5mini', 'gpt5'])
            tokens = [t for t in raw_tokens if t not in blacklist]

            # consider adjacent pairs (bigrams) to prefer 'amr_role' over 'amr' or 'role'
            bigrams = []
            parts = [t for t in re.split(r'[_\-\s]+', method_hint_l) if t]
            for i in range(len(parts)-1):
                pair = f"{parts[i]}_{parts[i+1]}"
                if len(pair) > 2 and pair not in blacklist:
                    bigrams.append(pair)

            candidates = sorted(set(bigrams + tokens), key=lambda x: -len(x))
            for t in candidates:
                for f in files_map.keys():
                    stem = Path(f).stem.lower()
                    if t in stem:
                        return files_map, f
        except Exception:
            pass

    # no chosen file; return map and None so caller can decide how to use them
    return files_map, None

def plot_success_rates_by_method(data, file_prefix='gemini', model_name='Gemini'):
    """Plot success rates comparison across methods for a given model

    Args:
        data (dict): Loaded JSON data for the model
        file_prefix (str): Prefix used for output filenames (e.g., 'gemini', 'gpt5mini')
        model_name (str): Display name used in plot titles
    """
    methods = list(data.keys())
    success_rates = []

    for method in methods:
        total = data[method]['total_examples']
        successes = data[method]['error_stats']['successes']
        success_rate = (successes / total) * 100
        success_rates.append(success_rate)

    fig, ax = plt.subplots(figsize=(10, 6))
    colors = ['#2ecc71', '#3498db', '#e74c3c', '#f39c12']
    bars = ax.bar(methods, success_rates, color=colors, edgecolor='black', linewidth=1.5)
    
    # Add value labels on bars
    for bar in bars:
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height,
                f'{height:.1f}%', ha='center', va='bottom', fontsize=11, fontweight='bold')
    
    ax.set_ylabel('Success Rate (%)', fontsize=12, fontweight='bold')
    ax.set_title(f'Success Rate Comparison Across Methods ({model_name} Model)', fontsize=14, fontweight='bold')
    ax.set_ylim(0, 100)
    ax.grid(axis='y', alpha=0.3)
    
    plt.tight_layout()
    _savefig(f'./plots/01_{file_prefix}_success_rates_by_method.png')
    plt.close()


def plot_success_rates_by_method_before_after_extusage(data, ext_check_pattern='amr_json_external_axiom_check_results_*.json', file_prefix='gemini', model_name='Gemini'):
    """Plot success rates comparison across methods BEFORE and AFTER treating
    files that use 100% externals as NOT successful.

    This function loads external-check results (glob pattern) and for each
    method attempts to count how many previously-successful files used
    100% externals; these are subtracted from the success counts to compute
    an "after" success rate.
    """
    # Load available external-check files (do NOT merge them here)
    files_map, chosen_global = _load_ext_results_for_method(method_hint=None, pattern=ext_check_pattern)
    if not files_map:
        print(f"Warning: no external-check results found for pattern: {ext_check_pattern}")
        return
    if chosen_global:
        print(f"Loaded external-check data from: {chosen_global}")
    else:
        print(f"Found {len(files_map)} external-check files; selecting per-method files by filename when possible.")

    methods = list(data.keys())
    # print(methods)
    # print(ext_results)
    before_rates = []
    after_rates = []

    for method in methods:
        entry = data[method]
        total = entry.get('total_examples', entry.get('total_files', 0))
        successes = entry.get('error_stats', {}).get('successes', entry.get('successes', 0))

        # Determine which external-check file best corresponds to this method (by filename)
        chosen_file = None
        # try obvious matches first
        for fname in files_map.keys():
            stem = Path(fname).stem.lower()
            if method.lower() in stem or entry.get('method_name', '').lower() in stem:
                chosen_file = fname
                break

        # token/bigram fallback
        if chosen_file is None:
            try:
                import re
                method_hint_l = method.lower()
                raw_tokens = [t for t in re.split(r'[_\-\s]+', method_hint_l) if len(t) > 2]
                blacklist = set(['enhanced', 'json', 'dataset', 'results', 'gpt5mini', 'gpt5'])
                tokens = [t for t in raw_tokens if t not in blacklist]
                bigrams = []
                parts = [t for t in re.split(r'[_\-\s]+', method_hint_l) if t]
                for i in range(len(parts)-1):
                    pair = f"{parts[i]}_{parts[i+1]}"
                    if len(pair) > 2 and pair not in blacklist:
                        bigrams.append(pair)
                candidates = sorted(set(bigrams + tokens), key=lambda x: -len(x))
                for t in candidates:
                    for fname in files_map.keys():
                        if t in Path(fname).stem.lower():
                            chosen_file = fname
                            break
                    if chosen_file:
                        break
            except Exception:
                chosen_file = None

        if not chosen_file:
            # No per-method external-check file found; we skip external-based adjustment
            print(f"Warning: no external-check file found for method '{method}'. Skipping external-based adjustments for this method.")
            problematic = 0
        else:
            ext_results = files_map[chosen_file]
            # Count files for this method that are successful but use ~100% externals
            problematic = 0
            for path, info in ext_results.items():
                try:
                    details = info.get('original_theorems_analysis', {}).get('details', [])
                    if not details:
                        avg_pct = 0.0
                    else:
                        vals = [d.get('percent_of_externals_used', 0.0) for d in details]
                        avg_pct = float(np.mean(vals)) if vals else 0.0

                    successful = info.get('successful', None)
                    if successful is True and avg_pct >= 99.999:
                        problematic += 1
                except Exception:
                    continue

        adjusted_successes = max(0, successes - problematic)
        before_rate = (successes / total * 100) if total > 0 else 0.0
        after_rate = (adjusted_successes / total * 100) if total > 0 else 0.0

        before_rates.append(before_rate)
        after_rates.append(after_rate)

    # Plot grouped bars (before vs after)
    x = np.arange(len(methods))
    width = 0.35

    fig, ax = plt.subplots(figsize=(12, 6))
    b1 = ax.bar(x - width/2, before_rates, width, label='Before (original)', color='#2ecc71', edgecolor='black')
    b2 = ax.bar(x + width/2, after_rates, width, label='After (100% externals -> fail)', color='#e74c3c', edgecolor='black')

    # Add labels
    for bar in b1 + b2:
        h = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., h, f'{h:.1f}%', ha='center', va='bottom', fontsize=9)

    ax.set_xticks(x)
    ax.set_xticklabels(methods)
    ax.set_ylabel('Success Rate (%)', fontsize=12, fontweight='bold')
    ax.set_title(f'Success Rate Comparison: Before vs After (treat 100% external usage as failures) ({model_name})', fontsize=14, fontweight='bold')
    ax.set_ylim(0, 110)
    ax.legend()
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    _savefig(f'./plots/01_{file_prefix}_success_rates_by_method_before_after_extusage.png')
    plt.close()


def plot_immediate_vs_delayed_failures(data, file_prefix='gemini', model_name='Gemini'):
    """Plot immediate failures vs failed after rounds for a given model"""

    methods = list(data.keys())
    immediate_failures = []
    failed_after_rounds = []
    successes = []

    for method in methods:
        immediate_failures.append(data[method]['error_stats']['immediate_failures'])
        failed_after_rounds.append(data[method]['error_stats']['failed_after_rounds'])
        successes.append(data[method]['error_stats']['successes'])

    fig, ax = plt.subplots(figsize=(12, 6))

    x = np.arange(len(methods))
    width = 0.25

    bars1 = ax.bar(x - width, immediate_failures, width, label='Immediate Failures', color='#e74c3c', edgecolor='black')
    bars2 = ax.bar(x, failed_after_rounds, width, label='Failed After Rounds', color='#f39c12', edgecolor='black')
    bars3 = ax.bar(x + width, successes, width, label='Successes', color='#2ecc71', edgecolor='black')
    
    # Add value labels
    for bars in [bars1, bars2, bars3]:
        for bar in bars:
            height = bar.get_height()
            if height > 0:
                ax.text(bar.get_x() + bar.get_width()/2., height,
                        f'{int(height)}', ha='center', va='bottom', fontsize=9)
    
    ax.set_ylabel('Number of Examples', fontsize=12, fontweight='bold')
    ax.set_title(f'Example Classification: Immediate vs Failed After Rounds vs Successes ({model_name} Model)', 
                 fontsize=14, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels(methods)
    ax.legend(fontsize=11, loc='upper left')
    ax.grid(axis='y', alpha=0.3)
    
    plt.tight_layout()
    _savefig(f'./plots/02_{file_prefix}_failure_classification.png')
    plt.close()

# NOTE: The generic `plot_immediate_vs_delayed_failures` function can be used for any model
# by providing the appropriate `data`, `file_prefix`, and `model_name` when calling it.

def plot_success_by_round(data, file_prefix='gemini', model_name='Gemini'):
    """Plot success rates by round for each method for a given model"""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    axes = axes.flatten()

    methods = list(data.keys())
    colors = ['#3498db', '#2ecc71', '#e74c3c', '#f39c12', '#9b59b6']

    for idx, method in enumerate(methods):
        round_stats = data[method]['round_stats']
        success_rates = round_stats['success_rates_by_round']

        if success_rates:
            rounds = sorted([int(r) for r in success_rates.keys()])
            rates = [success_rates[str(r)] for r in rounds]

            ax = axes[idx]
            ax.plot(rounds, rates, marker='o', linewidth=2.5, markersize=8, color=colors[idx])
            ax.fill_between(rounds, rates, alpha=0.3, color=colors[idx])

            # Add value labels
            for r, rate in zip(rounds, rates):
                ax.text(r, rate, f'{rate:.1f}%', ha='center', va='bottom', fontsize=9)

            ax.set_xlabel('Round', fontsize=11, fontweight='bold')
            ax.set_ylabel('Success Rate (%)', fontsize=11, fontweight='bold')
            ax.set_title(f'{method} - Success Rate by Round', fontsize=12, fontweight='bold')
            ax.set_xticks(rounds)
            ax.grid(True, alpha=0.3)
            ax.set_ylim(0, max(rates) + 10 if rates else 10)

    plt.suptitle(f'Success Rate by Round ({model_name} Model)', fontsize=16, fontweight='bold', y=1.00)
    plt.tight_layout()
    _savefig(f'./plots/03_{file_prefix}_success_by_round.png')
    plt.close()


def plot_meaningful_content_percentage(data, file_prefix='gemini', model_name='Gemini'):
    """Plot percentage of files with meaningful content for a given model"""
    methods = list(data.keys())
    meaningful_percentages = []

    for method in methods:
        meaningful_percentages.append(data[method]['meaningful_percentage'])

    fig, ax = plt.subplots(figsize=(10, 6))
    colors = ['#2ecc71', '#3498db', '#e74c3c', '#f39c12']
    bars = ax.bar(methods, meaningful_percentages, color=colors, edgecolor='black', linewidth=1.5)

    # Add value labels
    for bar in bars:
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height,
                f'{height:.1f}%', ha='center', va='bottom', fontsize=11, fontweight='bold')

    ax.set_ylabel('Percentage (%)', fontsize=12, fontweight='bold')
    ax.set_title(f'Files with Meaningful Content by Method ({model_name} Model)', fontsize=14, fontweight='bold')
    ax.set_ylim(0, 100)
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    _savefig(f'./plots/05_{file_prefix}_meaningful_content.png')
    plt.close()



def plot_round_distribution(data, file_prefix='gemini', model_name='Gemini'):
    """Plot distribution of max rounds across methods for a given model"""
    methods = list(data.keys())

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    axes = axes.flatten()

    colors = ['#3498db', '#2ecc71', '#e74c3c', '#f39c12', '#9b59b6']

    for idx, method in enumerate(methods):
        max_rounds_dist = data[method]['round_stats']['max_rounds_distribution']

        rounds = sorted([int(r) for r in max_rounds_dist.keys()])
        counts = [max_rounds_dist[str(r)] for r in rounds]

        ax = axes[idx]
        bars = ax.bar(rounds, counts, color=colors[idx], edgecolor='black', linewidth=1.5)

        # Add value labels
        for bar in bars:
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2., height,
                    f'{int(height)}', ha='center', va='bottom', fontsize=9)

        ax.set_xlabel('Max Rounds', fontsize=11, fontweight='bold')
        ax.set_ylabel('Number of Problems', fontsize=11, fontweight='bold')
        ax.set_title(f'{method} - Round Distribution', fontsize=12, fontweight='bold')
        ax.grid(axis='y', alpha=0.3)

    plt.suptitle(f'Round Distribution ({model_name} Model)', fontsize=16, fontweight='bold', y=1.00)
    plt.tight_layout()
    _savefig(f'./plots/06_{file_prefix}_round_distribution.png')
    plt.close()



def plot_error_type_distribution(data, file_prefix='gemini', model_name='Gemini'):
    """Plot distribution of error types by method for a given model"""
    methods = list(data.keys())
    error_types = set()

    # Collect all error types
    for method in methods:
        error_types.update(data[method]['error_stats']['error_type_counts'].keys())

    error_types = sorted(list(error_types))

    fig, ax = plt.subplots(figsize=(14, 7))

    x = np.arange(len(methods))
    width = 0.15

    colors_error = plt.cm.Set3(np.linspace(0, 1, len(error_types)))

    for idx, error_type in enumerate(error_types):
        counts = []
        for method in methods:
            count = data[method]['error_stats']['error_type_counts'].get(error_type, 0)
            counts.append(count)

        offset = (idx - len(error_types)/2 + 0.5) * width
        ax.bar(x + offset, counts, width, label=error_type, color=colors_error[idx], edgecolor='black')

    ax.set_ylabel('Count', fontsize=12, fontweight='bold')
    ax.set_title(f'Error Type Distribution by Method ({model_name} Model)', fontsize=14, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels(methods)
    ax.legend(fontsize=10, loc='upper right', ncol=2)
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    _savefig(f'./plots/07_{file_prefix}_error_type_distribution.png')
    plt.close()


def plot_avg_content_length(data, file_prefix='gemini', model_name='Gemini'):
    """Plot average content length by method for a given model"""
    methods = list(data.keys())
    avg_lengths = []

    for method in methods:
        avg_lengths.append(data[method]['avg_content_length'])

    fig, ax = plt.subplots(figsize=(10, 6))
    colors = ['#2ecc71', '#3498db', '#e74c3c', '#f39c12']
    bars = ax.bar(methods, avg_lengths, color=colors, edgecolor='black', linewidth=1.5)

    # Add value labels
    for bar in bars:
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height,
                f'{int(height)}', ha='center', va='bottom', fontsize=11, fontweight='bold')

    ax.set_ylabel('Average Content Length (characters)', fontsize=12, fontweight='bold')
    ax.set_title(f'Average Content Length by Method ({model_name} Model)', fontsize=14, fontweight='bold')
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    _savefig(f'./plots/08_{file_prefix}_avg_content_length.png')
    plt.close()


def create_summary_table(data, file_prefix='gemini', model_name='Gemini'):
    """Create a summary comparison table for a given model"""
    methods = list(data.keys())

    fig, ax = plt.subplots(figsize=(14, 6))
    ax.axis('tight')
    ax.axis('off')

    table_data = []
    headers = ['Method', 'Total Files', 'Meaningful %', 'Immediate Fail', 'Failed After', 'Success', 'Success Rate']

    for method in methods:
        total = data[method]['total_examples']
        meaningful = data[method]['meaningful_percentage']
        immediate = data[method]['error_stats']['immediate_failures']
        failed_after = data[method]['error_stats']['failed_after_rounds']
        successes = data[method]['error_stats']['successes']
        success_rate = (successes / total) * 100 if total > 0 else 0

        table_data.append([
            method,
            str(total),
            f'{meaningful:.1f}%',
            str(immediate),
            str(failed_after),
            str(successes),
            f'{success_rate:.1f}%'
        ])

    table = ax.table(cellText=table_data, colLabels=headers, cellLoc='center', loc='center',
                     colWidths=[0.15, 0.12, 0.12, 0.15, 0.15, 0.12, 0.12])

    table.auto_set_font_size(False)
    table.set_fontsize(11)
    table.scale(1, 2.5)

    # Style header
    for i in range(len(headers)):
        table[(0, i)].set_facecolor('#34495e')
        table[(0, i)].set_text_props(weight='bold', color='white')

    # Alternate row colors
    for i in range(1, len(table_data) + 1):
        for j in range(len(headers)):
            if i % 2 == 0:
                table[(i, j)].set_facecolor('#ecf0f1')
            else:
                table[(i, j)].set_facecolor('#ffffff')

    plt.title(f'Summary Statistics by Method ({model_name} Model)', fontsize=14, fontweight='bold', pad=20)
    plt.tight_layout()
    _savefig(f'./plots/09_{file_prefix}_summary_table.png')
    plt.close()


def plot_dataset_comparison(dataset_data, file_prefix='gemini', model_name='Gemini', method_name=None):
    """Compare key metrics across datasets (success rate vs meaningful %)"""
    # dataset_data may include a top-level 'datasets' key
    if isinstance(dataset_data, dict) and 'datasets' in dataset_data:
        datasets = dataset_data['datasets']
    else:
        datasets = dataset_data

    names = []
    success_rates = []
    meaningful = []

    for ds_key, ds_val in datasets.items():
        # human-friendly label
        label = ds_key.strip('-').upper()
        total = ds_val.get('total_files', ds_val.get('total_examples', 0))
        # successes may be in error_stats
        successes = ds_val.get('error_stats', {}).get('successes', ds_val.get('successes', 0))
        success_rate = (successes / total * 100) if total > 0 else 0.0
        meaningful_pct = ds_val.get('meaningful_percentage', ds_val.get('meaningful_percent', 0.0))

        names.append(label)
        success_rates.append(success_rate)
        meaningful.append(meaningful_pct)

    x = np.arange(len(names))
    width = 0.35

    fig, ax = plt.subplots(figsize=(12, 6))
    b1 = ax.bar(x - width/2, success_rates, width, label='Success Rate (%)', color='#2ecc71', edgecolor='black')
    b2 = ax.bar(x + width/2, meaningful, width, label='Meaningful %', color='#3498db', edgecolor='black')

    # labels
    for bar in b1 + b2:
        h = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., h, f'{h:.1f}%', ha='center', va='bottom', fontsize=9)

    ax.set_xticks(x)
    ax.set_xticklabels(names)
    ax.set_ylabel('Percentage (%)', fontsize=12, fontweight='bold')
    ax.set_title(f'Dataset Comparison: Success Rate vs Meaningful % ({model_name})', fontsize=14, fontweight='bold')
    ax.set_ylim(0, 110)
    ax.legend()
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    # sanitize method_name for filename
    label = method_name if method_name else file_prefix
    label = str(label).replace(' ', '_')
    _savefig(f'./plots/04_{file_prefix}_success_by_dataset-{label}.png')
    plt.close()


def plot_dataset_comparison_by_method_before_after_extusage(dataset_data, ext_check_pattern='amr_json_external_axiom_check_results_*.json', file_prefix='gemini', model_name='Gemini', method_name=None):
    """Per-method dataset comparison before and after treating files that use
    100% externals as not successful.
    """
    # Load external-check results: prefer the file for this method if available
    files_map, chosen = _load_ext_results_for_method(method_hint=method_name, pattern=ext_check_pattern)
    if not files_map:
        print(f"Warning: no external-check results found for pattern: {ext_check_pattern}")
        return

    if chosen:
        print(f"Loaded external-check data from: {chosen}")
        ext_results = files_map[chosen]
    else:
        # Attempt to find a per-method file by matching method_name in filenames
        chosen_file = None
        if method_name:
            for fname in files_map.keys():
                if method_name.lower() in Path(fname).stem.lower():
                    chosen_file = fname
                    break
        if chosen_file:
            print(f"Selected external-check file for method {method_name}: {chosen_file}")
            ext_results = files_map[chosen_file]
        else:
            print(f"Warning: could not find a per-method external-check file for '{method_name}'. Skipping dataset-level before/after plot.")
            return

    # dataset_data may include a top-level 'datasets' key
    if isinstance(dataset_data, dict) and 'datasets' in dataset_data:
        datasets = dataset_data['datasets']
    else:
        datasets = dataset_data

    names = []
    before_rates = []
    after_rates = []

    for ds_key, ds_val in datasets.items():
        label = ds_key.strip('-').upper()
        total = ds_val.get('total_files', ds_val.get('total_examples', 0))
        successes = ds_val.get('error_stats', {}).get('successes', ds_val.get('successes', 0))

        # Count problematic files in this dataset (success==True and avg_ext_pct==100)
        problematic = 0
        for path, info in ext_results.items():
            try:
                # check dataset membership
                if ds_key in path or ds_key.strip('-') in path:
                    details = info.get('original_theorems_analysis', {}).get('details', [])
                    if not details:
                        avg_pct = 0.0
                    else:
                        vals = [d.get('percent_of_externals_used', 0.0) for d in details]
                        avg_pct = float(np.mean(vals)) if vals else 0.0

                    successful = info.get('successful', None)
                    if successful is True and avg_pct >= 99.999:
                        problematic += 1
            except Exception:
                continue

        adjusted_successes = max(0, successes - problematic)
        before_rate = (successes / total * 100) if total > 0 else 0.0
        after_rate = (adjusted_successes / total * 100) if total > 0 else 0.0

        names.append(label)
        before_rates.append(before_rate)
        after_rates.append(after_rate)

    if not names:
        print('No datasets found for dataset-level before/after external-usage plot.')
        return

    x = np.arange(len(names))
    width = 0.35

    fig, ax = plt.subplots(figsize=(12, 6))
    b1 = ax.bar(x - width/2, before_rates, width, label='Before (original)', color='#2ecc71', edgecolor='black')
    b2 = ax.bar(x + width/2, after_rates, width, label='After (100% externals -> fail)', color='#e74c3c', edgecolor='black')

    for bar in b1 + b2:
        h = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., h, f'{h:.1f}%', ha='center', va='bottom', fontsize=9)

    ax.set_xticks(x)
    ax.set_xticklabels(names)
    ax.set_ylabel('Success Rate (%)', fontsize=12, fontweight='bold')
    label = method_name if method_name else file_prefix
    label = str(label).replace(' ', '_')
    ax.set_title(f'Dataset: Success Rate Before vs After (treat 100% external usage as failures) - {label}', fontsize=14, fontweight='bold')
    ax.set_ylim(0, 110)
    ax.legend()
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    _savefig(f'./plots/04_{file_prefix}_success_by_dataset-{label}_before_after_extusage.png')
    plt.close()


def plot_external_usage_vs_success(dataset_data, external_check_file='amr_json_external_axiom_check_results_*.json', file_prefix='gemini', model_name='Gemini', method_name='AMR-Frame'):
    """Plot relationship between average external-axiom usage and success rate per dataset.

    external_check_file: path to JSON produced by `amr_frame_json_check.py`.
    dataset_data: dataset-level summary (contains 'datasets' mapping).
    """
    # Load external check results. Try to pick the file that matches this method
    try:
        if os.path.exists(external_check_file) and not ('*' in external_check_file or '?' in external_check_file):
            ext_results = load_json(external_check_file)
            chosen = external_check_file
            print(f"Loaded external-check data from: {chosen}")
        else:
            files_map, chosen = _load_ext_results_for_method(method_hint=method_name or None, pattern=external_check_file)
            if chosen:
                ext_results = files_map[chosen]
                print(f"Loaded external-check data from: {chosen}")
            else:
                print(f"Warning: no per-method external-check file found for '{method_name}'. Not merging files; cannot proceed.")
                return
    except Exception as e:
        print(f"Warning: could not load external check file(s): {e}")
        return

    # Prepare dataset mapping
    if isinstance(dataset_data, dict) and 'datasets' in dataset_data:
        datasets = dataset_data['datasets']
    else:
        datasets = dataset_data

    # Initialize per-dataset lists
    ds_file_vals = {k: [] for k in datasets.keys()}

    # For each file in ext_results, compute average percent_of_externals_used across its original theorems
    for path, info in ext_results.items():
        ota = info.get('original_theorems_analysis', {})
        details = ota.get('details', [])
        if not details:
            avg_pct = 0.0
        else:
            vals = [d.get('percent_of_externals_used', 0.0) for d in details]
            avg_pct = float(np.mean(vals)) if vals else 0.0

        # assign to dataset by matching dataset key in file path
        assigned = False
        for ds_key in datasets.keys():
            if f'/{ds_key}/' in path or ds_key in path:
                ds_file_vals[ds_key].append(avg_pct)
                assigned = True
                break
        if not assigned:
            # try to find by dataset suffix (strip leading -)
            for ds_key in datasets.keys():
                if ds_key.strip('-') in path:
                    ds_file_vals[ds_key].append(avg_pct)
                    assigned = True
                    break

    # Aggregate per-dataset statistics
    ds_names = []
    means = []
    medians = []
    stds = []
    counts = []
    success_rates = []

    for ds_key, ds_val in datasets.items():
        vals = ds_file_vals.get(ds_key, [])
        mean_ext = float(np.mean(vals)) if vals else 0.0
        med_ext = float(np.median(vals)) if vals else 0.0
        std_ext = float(np.std(vals, ddof=0)) if vals else 0.0
        cnt = len(vals)

        total = ds_val.get('total_files', ds_val.get('total_examples', 0))
        successes = ds_val.get('error_stats', {}).get('successes', ds_val.get('successes', 0))
        success_rate = (successes / total * 100) if total > 0 else 0.0

        ds_names.append(ds_key.strip('-').upper())
        means.append(mean_ext)
        medians.append(med_ext)
        stds.append(std_ext)
        counts.append(cnt)
        success_rates.append(success_rate)

    if not any(counts):
        print("No external-check data found for the given dataset summary.")
        return

    # Compute correlation between mean external usage and success rate
    corr = None
    if len(means) >= 2:
        try:
            corr = np.corrcoef(means, success_rates)[0, 1]
        except Exception:
            corr = None

    # Create a two-panel figure: scatter (mean vs success) + counts
    fig = plt.figure(figsize=(14, 6))
    gs = fig.add_gridspec(1, 2, width_ratios=[3, 1], wspace=0.3)
    ax = fig.add_subplot(gs[0, 0])
    ax2 = fig.add_subplot(gs[0, 1])

    # Scatter with error bars (std) and marker size by count
    sizes = [40 + c * 6 for c in counts]
    ax.errorbar(means, success_rates, xerr=stds, fmt='o', markersize=8, color='#9b59b6', ecolor='gray', elinewidth=2, capsize=4)
    ax.scatter(means, success_rates, s=sizes, color='#9b59b6', edgecolor='black')

    # Annotate with dataset labels and counts
    for x_val, y_val, label, cnt in zip(means, success_rates, ds_names, counts):
        ax.text(x_val, y_val, f' {label} (n={cnt})', fontsize=9, va='center')

    # Trend line
    if len(means) >= 2 and any(means):
        try:
            z = np.polyfit(means, success_rates, 1)
            p = np.poly1d(z)
            xs = np.linspace(min(means), max(means), 100)
            ax.plot(xs, p(xs), linestyle='--', color='gray')
        except Exception:
            pass

    ax.set_xlabel('Average % of Externals Used in Theorems (mean)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Success Rate (%)', fontsize=12, fontweight='bold')
    title = f'External Usage vs Success Rate ({model_name})'
    if corr is not None:
        title += f' — Pearson r = {corr:.2f}'
    ax.set_title(title, fontsize=14, fontweight='bold')
    ax.set_xlim(left=0)
    ax.set_ylim(0, 110)
    ax.grid(axis='y', alpha=0.3)

    # Right panel: counts (descending)
    order = sorted(range(len(counts)), key=lambda i: counts[i], reverse=True)
    count_vals = [counts[i] for i in order]
    labels_ordered = [ds_names[i] for i in order]
    ax2.barh(labels_ordered, count_vals, color='#3498db', edgecolor='black')
    ax2.set_xlabel('Files with external-check data', fontsize=10, fontweight='bold')
    ax2.set_title('Sample counts', fontsize=12, fontweight='bold')

    plt.tight_layout()
    # include method_name in filename label
    label = method_name if method_name else file_prefix
    label = str(label).replace(' ', '_')
    _savefig(f'./plots/10_{file_prefix}_external_usage_vs_success-{label}.png')
    plt.close()


def plot_external_usage_vs_success_multi(dataset_files, ext_check_pattern='amr_json_external_axiom_check_results_*.json', out_prefix='combined'):
    """Plot external usage vs success rate across multiple methods/dataset files.

    dataset_files: list of paths to enhanced_json_dataset_results_*.json files
    ext_check_pattern: glob pattern to find json check result files (merged)
    out_prefix: filename prefix for saved plot
    """
    # Load and merge all external check results
    ext_results = {}
    from glob import glob
    ext_files = sorted(glob(ext_check_pattern))
    for ef in ext_files:
        try:
            d = load_json(ef)
            ext_results.update(d)
        except Exception:
            continue

    # Collect points (avg_external_pct, success_rate, label, method)
    xs = []
    ys = []
    labels = []
    methods = []
    counts = []
    stds = []

    for df in dataset_files:
        try:
            data = load_json(df)
        except Exception:
            continue

        method_path = data.get('method_path', '')
        method_seg = Path(method_path).name if method_path else Path(df).stem
        method_label = data.get('method_name', method_seg)

        datasets = data.get('datasets', {})
        for ds_key, ds_val in datasets.items():
            # gather per-file avg ext pct for files belonging to this method and dataset
            per_file_vals = []
            for path, info in ext_results.items():
                # Determine whether this ext entry belongs to the current method by
                # checking if the path exists under the method_path root (this works
                # because per-method check outputs use relative paths when saved).
                try:
                    candidate = Path(method_path) / Path(path)
                    belongs = candidate.exists()
                except Exception:
                    belongs = False

                # Fallback: if candidate not found, try simple substring matching
                if not belongs:
                    if method_seg and method_seg in path:
                        belongs = True

                if not belongs:
                    continue

                # Ensure dataset key matches the path
                if ds_key not in path and ds_key.strip('-') not in path:
                    continue

                details = info.get('original_theorems_analysis', {}).get('details', [])
                if not details:
                    continue
                vals = [d.get('percent_of_externals_used', 0.0) for d in details]
                if vals:
                    per_file_vals.append(float(np.mean(vals)))

            if not per_file_vals:
                continue

            avg_ext = float(np.mean(per_file_vals))
            std_ext = float(np.std(per_file_vals)) if per_file_vals else 0.0
            cnt = len(per_file_vals)
            total = ds_val.get('total_files', ds_val.get('total_examples', 0))
            successes = ds_val.get('error_stats', {}).get('successes', ds_val.get('successes', 0))
            success_rate = (successes / total * 100) if total > 0 else 0.0

            xs.append(avg_ext)
            ys.append(success_rate)
            labels.append(f"{method_label}:{ds_key.strip('-')}")
            methods.append(method_label)
            counts.append(cnt)
            stds.append(std_ext)

    if not xs:
        print("No external-check data found for multi-method external usage plot.")
        return

    # Compute correlation
    corr = None
    if len(xs) >= 2:
        try:
            corr = np.corrcoef(xs, ys)[0, 1]
        except Exception:
            corr = None

    # Scatter with color by method
    unique_methods = sorted(set(methods))
    method_colors = {m: plt.cm.tab10(i % 10) for i, m in enumerate(unique_methods)}

    # Plot: scatter colored by method, size by sample count, x-error as std
    fig, ax = plt.subplots(figsize=(12, 7))
    for x_val, y_val, lbl, m, cnt, st in zip(xs, ys, labels, methods, counts, stds):
        size = 40 + cnt * 6
        # x-error = std of per-file means
        ax.errorbar(x_val, y_val, xerr=st, fmt='o', markersize=6, color=method_colors[m], ecolor='gray', elinewidth=1.5, capsize=3)
        ax.scatter(x_val, y_val, s=size, color=method_colors[m], edgecolor='black')
        ax.text(x_val, y_val, f' {lbl} (n={cnt})', fontsize=9, va='center')

    # trend line
    if len(xs) >= 2 and any(xs):
        z = np.polyfit(xs, ys, 1)
        p = np.poly1d(z)
        xs_line = np.linspace(min(xs), max(xs), 100)
        ax.plot(xs_line, p(xs_line), linestyle='--', color='gray')

    ax.set_xlabel('Average % of Externals Used in Theorems (per-file average)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Success Rate (%)', fontsize=12, fontweight='bold')
    title = f'External Usage vs Success Rate (multi-method)'
    if corr is not None:
        title += f' — Pearson r = {corr:.2f}'
    ax.set_title(title, fontsize=14, fontweight='bold')
    ax.set_xlim(left=0)
    ax.set_ylim(0, 110)
    ax.grid(axis='y', alpha=0.3)

    # legend
    handles = [plt.Line2D([0], [0], marker='o', color='w', markerfacecolor=method_colors[m], markersize=8, markeredgecolor='black') for m in unique_methods]
    ax.legend(handles, unique_methods, title='Method', fontsize=9)

    plt.tight_layout()
    _savefig(f'./plots/10_{out_prefix}_external_usage_vs_success_multi.png')
    plt.close()


def plot_relationships_across_methods(dataset_files, ext_check_pattern='amr_json_external_axiom_check_results_*.json', out_prefix='relationships'):
    """Aggregate metrics across methods and datasets, find strong correlations,
    and create focused scatter plots for the strongest relationships.

    The function builds a table with columns:
      - method, dataset, success_rate, meaningful_pct, avg_content_length,
        mean_ext_pct, median_ext_pct, ext_count
    Then it computes Pearson correlations between numeric columns and
    plots any relationship with |r| >= 0.45 (configurable threshold).
    """
    # Load and merge external-check results (all files matching pattern)
    from glob import glob
    ext_results = {}
    for ef in sorted(glob(ext_check_pattern)):
        try:
            d = load_json(ef)
            ext_results.update(d)
        except Exception:
            continue

    # Build per-dataset per-method table
    rows = []
    for df in dataset_files:
        try:
            data = load_json(df)
        except Exception:
            continue

        method_path = data.get('method_path', '')
        method_seg = Path(method_path).name if method_path else Path(df).stem
        method_label = data.get('method_name', method_seg)

        datasets = data.get('datasets', {})
        for ds_key, ds_val in datasets.items():
            # collect all ext entries that mention this dataset key (across all methods)
            vals = []
            for path, info in ext_results.items():
                if ds_key in path or ds_key.strip('-') in path:
                    details = info.get('original_theorems_analysis', {}).get('details', [])
                    if not details:
                        continue
                    per = [d.get('percent_of_externals_used', 0.0) for d in details]
                    if per:
                        vals.append(float(np.mean(per)))

            mean_ext = float(np.mean(vals)) if vals else np.nan
            med_ext = float(np.median(vals)) if vals else np.nan
            cnt = len(vals)

            total = ds_val.get('total_files', ds_val.get('total_examples', 0))
            successes = ds_val.get('error_stats', {}).get('successes', ds_val.get('successes', 0))
            success_rate = (successes / total * 100) if total > 0 else np.nan
            meaningful = ds_val.get('meaningful_percentage', ds_val.get('meaningful_percent', np.nan))
            avg_len = ds_val.get('avg_content_length', np.nan)

            rows.append({
                'method': method_label,
                'dataset': ds_key.strip('-'),
                'success_rate': success_rate,
                'meaningful_pct': meaningful,
                'avg_content_length': avg_len,
                'mean_ext_pct': mean_ext,
                'median_ext_pct': med_ext,
                'ext_count': cnt,
            })

    if not rows:
        print('No dataset rows available for relationship analysis.')
        return

    # Convert to arrays for correlation analysis
    import math
    numeric_keys = ['success_rate', 'meaningful_pct', 'avg_content_length', 'mean_ext_pct', 'median_ext_pct', 'ext_count']

    # Compute Pearson correlations pairwise
    pairs = []
    for i, a in enumerate(numeric_keys):
        for b in numeric_keys[i+1:]:
            xa = np.array([r[a] for r in rows if not (r[a] is None or (isinstance(r[a], float) and math.isnan(r[a]))) and not (r[b] is None or (isinstance(r[b], float) and math.isnan(r[b])) ) ])
            xb = np.array([r[b] for r in rows if not (r[a] is None or (isinstance(r[a], float) and math.isnan(r[a]))) and not (r[b] is None or (isinstance(r[b], float) and math.isnan(r[b])) ) ])
            if len(xa) >= 3:
                try:
                    rcoef = np.corrcoef(xa, xb)[0,1]
                    pairs.append((a, b, float(rcoef), len(xa)))
                except Exception:
                    continue

    # Sort by absolute correlation descending
    pairs.sort(key=lambda x: abs(x[2]), reverse=True)

    # Threshold for 'strong' relationships
    strong_threshold = 0.45
    strong_pairs = [p for p in pairs if abs(p[2]) >= strong_threshold]

    if not strong_pairs:
        print('No strong relationships found (|r| < {:.2f}).'.format(strong_threshold))
        # Still save a baseline scatter: meaningful_pct vs success_rate
        strong_pairs = [('meaningful_pct', 'success_rate', 0.0, len(rows))]

    # Create a multipanel figure with top 3 strongest relations
    top = strong_pairs[:3]
    n = len(top)
    fig, axes = plt.subplots(1, n, figsize=(6*n, 5))
    if n == 1:
        axes = [axes]

    for ax, (a, b, rcoef, cnt) in zip(axes, top):
        # gather plot data
        xs = [r[a] for r in rows if not (r[a] is None or (isinstance(r[a], float) and math.isnan(r[a]))) and not (r[b] is None or (isinstance(r[b], float) and math.isnan(r[b])) )]
        ys = [r[b] for r in rows if not (r[a] is None or (isinstance(r[a], float) and math.isnan(r[a]))) and not (r[b] is None or (isinstance(r[b], float) and math.isnan(r[b])) )]
        labs = [f"{r['method']}:{r['dataset']}" for r in rows if not (r[a] is None or (isinstance(r[a], float) and math.isnan(r[a]))) and not (r[b] is None or (isinstance(r[b], float) and math.isnan(r[b])) )]

        ax.scatter(xs, ys, s=80, color='#2ecc71', edgecolor='black')
        for x, y, l in zip(xs, ys, labs):
            ax.text(x, y, f' {l}', fontsize=8, va='center')

        # fit trend line
        try:
            z = np.polyfit(xs, ys, 1)
            p = np.poly1d(z)
            xs_line = np.linspace(min(xs), max(xs), 100)
            ax.plot(xs_line, p(xs_line), linestyle='--', color='gray')
        except Exception:
            pass

        ax.set_xlabel(a.replace('_', ' ').title(), fontsize=11, fontweight='bold')
        ax.set_ylabel(b.replace('_', ' ').title(), fontsize=11, fontweight='bold')
        ax.set_title(f'{a} vs {b} — r={rcoef:.2f} ({cnt} samples)')

    plt.tight_layout()
    _savefig(f'./plots/11_{out_prefix}_top_relationships.png')
    plt.close()


def main():
    """Generate all plots"""
    # Create plots directory
    plots_dir = Path('./plots')
    plots_dir.mkdir(exist_ok=True)
    # --- Configurable variables ---
    # Set the display name and file prefix for the model you want to plot.
    # Example: model_name='Gemini', file_prefix='gemini', data_file='./enhanced_analysis_results.json'
    model_name = 'GPT5-mini'        # Display name used in plot titles
    file_prefix = 'gpt5_mini'       # used in saved filenames (lowercase, no spaces)
    data_file = './enhanced_analysis_results.json'  # path to the JSON results for this model

    # Load data once and pass to plotting functions
    data = load_json(data_file)

    print(f"Generating plots for {model_name} Model...")
    print("=" * 60)

    plot_success_rates_by_method(data, file_prefix=file_prefix, model_name=model_name)
    print(f"✓ {model_name}: Success rates by method")

    # Before/After considering 100% external usage as failures
    # Attempt to run before/after external-usage comparison if function is available
    if 'plot_success_rates_by_method_before_after_extusage' in globals():
        try:
            plot_success_rates_by_method_before_after_extusage(data, ext_check_pattern='amr_json_external_axiom_check_results_*.json', file_prefix=file_prefix, model_name=model_name)
            print(f"✓ {model_name}: Success rates by method (before vs after external-usage)")
        except Exception as e:
            print(f"Warning: could not run before/after success rates plot: {e}")
    else:
        print("Warning: before/after success rates function not available in this module.")

    plot_immediate_vs_delayed_failures(data, file_prefix=file_prefix, model_name=model_name)
    print(f"✓ {model_name}: Failure classification")

    plot_success_by_round(data, file_prefix=file_prefix, model_name=model_name)
    print(f"✓ {model_name}: Success by round")

    plot_meaningful_content_percentage(data, file_prefix=file_prefix, model_name=model_name)
    print(f"✓ {model_name}: Meaningful content percentage")

    plot_round_distribution(data, file_prefix=file_prefix, model_name=model_name)
    print(f"✓ {model_name}: Round distribution")

    plot_error_type_distribution(data, file_prefix=file_prefix, model_name=model_name)
    print(f"✓ {model_name}: Error type distribution")

    plot_avg_content_length(data, file_prefix=file_prefix, model_name=model_name)
    print(f"✓ {model_name}: Average content length")

    create_summary_table(data, file_prefix=file_prefix, model_name=model_name)
    print(f"✓ {model_name}: Summary table")

    # --- Dataset-level analysis (optional files) ---
    dataset_file = './enhanced_json_dataset_results.json'
    dataset_files = ['./enhanced_json_dataset_results_amr_frame_gpt5mini.json', './enhanced_json_dataset_results_amr_role_gpt5mini.json', 'enhanced_json_dataset_results_autof1_gpt5mini.json', './enhanced_json_dataset_results_autof2_gpt5mini.json']
    # use pattern to match per-method external-check files generated by amr_frame_json_check
    external_check_file = 'amr_frame_json_check_results_*.json'

    try:
        for dataset_file in dataset_files:
            dataset_data = load_json(dataset_file)
            plot_dataset_comparison(dataset_data, file_prefix=file_prefix, model_name=model_name,method_name=f'{Path(dataset_file).stem}')
            print(f"✓ {model_name}: Dataset comparison (success vs meaningful)-{Path(dataset_file).stem}")
            # Dataset-level before/after considering 100% external usage
            # Attempt dataset-level before/after plot if function exists
            if 'plot_dataset_comparison_by_method_before_after_extusage' in globals():
                try:
                    plot_dataset_comparison_by_method_before_after_extusage(dataset_data, ext_check_pattern='amr_json_external_axiom_check_results_*.json', file_prefix=file_prefix, model_name=model_name, method_name=f'{Path(dataset_file).stem}')
                    print(f"✓ {model_name}: Dataset comparison before/after external-usage -{Path(dataset_file).stem}")
                except Exception as e:
                    print(f"Warning: could not run dataset before/after plot for {dataset_file}: {e}")
            else:
                print(f"Warning: dataset before/after plotting function not available for {dataset_file}.")
    except Exception as e:
        print(f"Warning: could not run dataset-level plots: {e}")
    # Try multi-method external usage plot using all enhanced_json_dataset_results_*.json files
    try:
        from glob import glob
        all_dataset_result_files = sorted(glob('enhanced_json_dataset_results_*.json'))
        if all_dataset_result_files:
            plot_external_usage_vs_success_multi(all_dataset_result_files, ext_check_pattern='amr_json_external_axiom_check_results_*.json', out_prefix='all_methods')
            print("✓ Multi-method: External usage vs success rate (combined)")
            # Run relationship discovery and plotting across all methods/datasets
            plot_relationships_across_methods(all_dataset_result_files, ext_check_pattern='amr_json_external_axiom_check_results_*.json', out_prefix='all_methods')
            print("✓ Multi-method: Relationship discovery and plots generated")
    except Exception as e:
        print(f"Warning: could not run multi-method external usage plot: {e}")
    
    
    print("\n" + "=" * 60)
    print("✅ All plots generated successfully!")
    print(f"Plots saved to: {plots_dir}")
    print("\nModel Plots: 01_<prefix>_* through 10_<prefix>_*")

if __name__ == "__main__":
    main()