# Formalization Test Module

A Python module for evaluating Lean code files for syntactic correctness using the `lean_interact` library.

## Features

### 1. Uses `lean_interact` Module
The module imports `LeanREPLConfig`, `LeanServer`, and `Command` from `lean_interact` to interact with Lean.

### 2. Loads Lean Files from Two-Level Folder Structure
The `find_lean_files()` function traverses directories up to a configurable depth (default: 2 levels) to find all `.lean` files.

### 3. Runs Lean Server for Evaluation
The `evaluate_lean_file()` function sends each file's content to the Lean REPL and captures:
- Errors
- Warnings/messages
- Sorry locations (incomplete proofs)

### 4. CSV Output with Diagnostic Information
The CSV includes these columns:

| Column | Description |
|--------|-------------|
| `code_folder` | Relative path of the containing folder |
| `file_name` | Name of the Lean file |
| `full_path` | Absolute path to the file |
| `error_count` | Number of errors found |
| `error_messages` | All error messages (pipe-separated) |
| `sorry_count` | Number of sorry statements |
| `sorries` | Sorry locations |
| `lean_version` | Lean version used |
| `evaluation_timestamp` | When the evaluation was run |

### 5. Lean Version Selection
You can specify the Lean version using `--lean-version`. Supported range: `v4.8.0-rc1` to `v4.26.0-rc2`.

## Usage Examples

```bash
# Basic usage
python formalization-test.py --folder ./lean_code

# With custom output and version
python formalization-test.py --folder ./lean_code --output results.csv --lean-version v4.23.0

# Verbose mode with all results (not just errors)
python formalization-test.py --folder ./lean_code --all-results --verbose

# List supported Lean versions
python formalization-test.py --list-versions

# Custom search depth
python formalization-test.py --folder ./lean_code --max-depth 3
```

## Exit Codes

| Code | Description |
|------|-------------|
| `0` | All files passed |
| `1` | Error during execution |
| `2` | Some files failed compilation |

## Requirements

- Python 3.10+
- `lean-interact` package (`pip install lean-interact`)
- Lean 4 installed (can be installed via `install-lean` command from lean-interact)

