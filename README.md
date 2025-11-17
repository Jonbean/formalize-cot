# Formalize-CoT

E.g., “formalization of natural language reasoning”

---

## 1. Project Overview

- **Goal:** This project investigate the capability of formalized reasoning of LLMs from both the translation and proving perspective
- **Main components:**
  1. **Translation modules** – AMR → Lean; CCG → Lean; text → Lean;
  2. **Prover modules** – LLM prompting / proof generation
  3. **Post-processing & analysis** – cleaning, evaluation, and stats

---

## 2. Repository Structure

```text
./
├── README.md
├── requirements.txt
├── provers
│   ├── langgraph_cot_amr_ms.py
│   └── langgraph_cot_auto.py
└── translators
    ├── amr2lean
    │   ├── amr_special_entities.py
    │   ├── amr_special_frames.py
    │   ├── amr_special_preps.py
    │   ├── amr2lean_batch_frame_centric.py
    │   ├── amr2lean_batch_role_centric.py
    │   ├── amr2lean.py
    │   ├── amr2lean2.py
    │   ├── lean_snippets.py
    │   ├── lean_snippets2.py
    │   ├── lean_snippets3.py
    │   ├── propbank_interface.py
    │   └── utils.py
    └── ccg2lean
        └── ccg2lean_pipeline.py
```

⸻

3. Setup

3.1. Environment
```bash
git clone <REPO_URL>
git clone git@github.com:Jonbean/AMRToolBox.git
```

**create env (pick one)**
`python -m venv .venv && source .venv/bin/activate`
**or**
```bash
conda create -n <env_name> python=3.10.18
conda activate <env_name>
```
```bash
cd AMRToolBox
pip install -e .
cd ../formalize-cot
pip install -r requirements.txt
```
3.2. Credentials / API Keys (if using LLMs)
-	Set the following environment variables (or use a .env file):
-	OPENAI_API_KEY / <OTHER_LLM_API_KEY>
-	Any extra notes about rate limits, models, etc.

⸻

4. Translation Modules: AMR → Lean; CCG → Lean;

4.1. Input format
-	Expected AMR data format encoded in JSON.
-	Example input file: `data/ready-to-be-translated-amr-data-format-sample.json`

4.2. Basic usage

### example
```
# role centric
python CoT-AMR2Lean-tran.py --shared-dir ./Cot-Rationales --out-base ./CoT-In-Lean-AMR-Role --f-or-r r

# frame centric
python CoT-AMR2Lean-tran.py --shared-dir ./Cot-Rationales --out-base ./CoT-In-Lean-AMR-Frame --f-or-r f
```

4.3. Key options
-	--shared-dir — path to AMR files (json files with the format as in 4.1)
-	--out-base — directory for generated .lean files. this will generate one lean file per chain
-	--f-or-r — short for frame-centric or role-centric flag

4.4. CCG translation

### example
```
python ccg2lean_pipeline_batch.py \
  --batch-dir ./Cot-Rationales \
  --batch-glob "*.json" \
  --batch-prefix "COT DATASET SAMPLES - " \
  --batch-out-base CoT-In-Lean-CCG \
  --model elmo --annotator spacy
```

4.5. key options
-   --batch-dir — path to rationale files (same json files with the format as in 4.1, only that we don't use the AMR in them, this module will parse the natural language with CCG parser)
-   --batch-glob — specifies the file type filter with file suffix
-   --batch-prefix - specifies the file type filter with file prefix
-   --batch-out-base - directory for generated .lean files. 
-   --model - the ccg parser embedding layer option
-   --annotator - the ccg pos and other linguistic features annotator module
⸻

5. Prover Modules: Prompting LLMs

This section covers LLM-based proving over the generated Lean files

5.1. Running the prover

### Example: run LLM prover on all Lean files in data/lean_out
```
python langgraph_cot_auto.py --inputs ../amr2lean-translator/autof-50-processed/gpt5-aqua/ --out ./autof-50-gemini-2.5-flash/aqua/ --rounds 5 --style autof
```

5.2. Configuration

Typical fields in configs/prover_default.yaml:
-	--inputs: the directory where lean files is stored
-	--out: the directory where llm chat log will be stored
-	--rounds: the maximum number of feedback loop to run before terminating the proving request per chain
-	--style: which translation pipeline the prover is fed. 3 options: autof, AMR-Role, and AMR-Frame
-	--min-id: (optional) can be specified by the index of the START file in the directory. This assumes the file names are sortable and the user knows the starting index of the file to execute this prompt engine
-   --max-id: (optional) can be specified by the index of the END file in the directory. This assumes the file names are sortable and the user knows the starting index of the file to execute this prompt engine
-   --exclude-processed: (optional) this option skips files that already have an output JSON file in the `--out` directory, avoiding repeated prompting effort

⸻

6. Post-Processing & Analysis


6.1. Collect and summarize runs
Todo:
add analysis component description here

⸻

7. Citation

If you use this codebase in a paper, please cite:
Todo: add citation bibtex after submission
@inproceedings{
}

