from typing import List, Tuple, Dict, Any, Optional
from pydantic import BaseModel, Field
from langgraph.graph import StateGraph, START, END
from langchain.chat_models import init_chat_model
from langchain.prompts import ChatPromptTemplate
from lean_interact import LeanREPLConfig, LocalProject, LeanServer, Command

from langchain_core.messages import (
    AnyMessage, BaseMessage,
    HumanMessage, AIMessage, SystemMessage
)

import os, json, time, argparse, re
from pathlib import Path
from langchain_google_genai import ChatGoogleGenerativeAI
from langgraph_cot_amr_ms import read_file as amr2lean_read_file
from langgraph_cot_amr_ms import AMR_Role_cheat_sheet, AMR_Frame_cheat_sheet, Auto_cheat_sheet, State

# Select the translation style from ["Auto"]
# STYLE = "Auto"


# set the max round
# LLM will not make response more than this round

os.environ["GOOGLE_API_KEY"] = "<google_api_key>"
os.environ["GOOGLE_CLOUD_PROJECT"]="vaulted-program-473016-j8"

llm = ChatGoogleGenerativeAI(
    model="gemini-2.5-flash",
    api_key=os.environ["GOOGLE_API_KEY"],
    temperature=0,
)

# ----------- helper funcs -----------
def strip_lean_comments(code: str) -> str:
    # remove block comments (non-nested) and line comments
    code = re.sub(r"/-.*?-/", "", code, flags=re.S)
    code = re.sub(r"^[ \t]*--.*?$", "", code, flags=re.M)
    return code

def contains_sorry(code: str) -> bool:
    return re.search(r"\bsorry\b", strip_lean_comments(code)) is not None

def inject_proof(thm_block: str, proof_text: str) -> str:
    """
    Replace a single 'sorry' in a theorem/lemma block with the given proof.
    Prefers replacing a standalone 'by sorry' line to preserve indentation.
    """
    # try: standalone "by sorry" on its own line
    m = re.search(r'(?m)^(?P<indent>\s*)by\s+sorry\s*$', thm_block)
    if m:
        indent = m.group('indent')
        proof_indented = "\n".join(
            (indent + "  " + ln if ln.strip() else ln)
            for ln in proof_text.strip("\n").splitlines()
        )
        return thm_block[:m.start()] + f"{indent}by\n{proof_indented}\n" + thm_block[m.end():]
    # fallback: replace the first whole-word 'sorry'
    return re.sub(r"\bsorry\b", proof_text.strip(), thm_block, count=1)
# ----------- end of helper funcs -----------


# state data class
# class State(BaseModel):
#     body:str = ""                       # the description of AMR-lean
#     PITs:List[str] = []                 # all PITs, including axiom, lemma and theorem
#     axioms_provided:List[int] = []      # the list of int describing index of provided axioms in PITs
#     unused:List[int] = []               # the list of int describing index of unused reasoning steps in PITs
#     theorems:List[int] = []             # the list of int describing index of provided theorems in PITs
#     axioms_added:List[str] = []         # axioms added by LLM
#     proof_tactics:List[str] = []        # proof tactics for each lemma and theorem
#     lean_messge:str = ""            # the message of lean system
#     round:int = 0                   # number of rounds
#     max_round:int = MAX_ROUND       # max number of querying LLM
#     file_path:str = ""              # path to the lean file
#     out_path: str = ""
#     preflight_ok: bool = False
#     style: str = "Auto"

# extra axiom and proof pair
class AxiomAndProof(BaseModel):
    axiom:str = Field(default = "", description = "extra axioms introduced to prove the current theorem")
    proof:str = Field(default = "", description = "proof tactics used to prove the theorem by all provided axioms and extra axioms added above")

# LLM response format
class LLMResponse(BaseModel):
    axiom_and_proof:List[AxiomAndProof] = Field(default = [], description = "A list of Objects including \"extra axioms introduced to prove the current theorem\", \"the current theorem with only `sorry` replaced with proof tactics\" for each theorem in the lean code")

def read_file(path:str, out_path:str, style:str, rounds: int) -> State:
    # read file and create initial state
    # check validility of file path
    match = re.search(r"[^\\/]+$", path)
    if match is not None:
        file_name = match.group(0)
    else:
        raise FileNotFoundError
    
    # create log file
    # with open(path.replace(file_name, "") + f"./log_" + style + f"_" + file_name[:-4] + f"txt", "w", encoding = "utf-8") as file:
    #     pass

    # read lean file from the given path
    with open(path, "r", encoding = "utf-8") as file:
        cot = "".join(file.readlines())
    
    # split the file by the start position of axiom or theorem
    PITs = []
    beg = 0
    for m in re.finditer(r"^(axiom|theorem)", cot, re.MULTILINE):
        PITs.append(cot[beg:m.start(0)])
        beg = m.start(0)
    PITs.append(cot[beg:])
    
    # get the type of each code chunk
    axioms = []
    unused = []
    theorems = []
    for i in range(len(PITs)):
        if "FAILED!" in PITs[i]:
            unused.append(i)
        elif PITs[i].startswith("axiom"):
            axioms.append(i)
        elif PITs[i].startswith("lemma"):
            unused.append(i)
        elif PITs[i].startswith("theorem"):
            if "sorry" in PITs[i]:
                theorems.append(i)
            else:
                continue

    return State(
        body = "",
        PITs = PITs,
        axioms_provided = axioms,
        unused = unused,
        theorems = theorems,
        file_path = path,
        out_path = out_path,
        style = style,
        max_round = rounds
    )

def link_lean_code(
    body: str,
    PITs: List[str],
    axioms_provided: List[int],
    unused: List[int],
    theorems: List[int],
    axiom_added: Optional[List[str]] = None,
    proof: Optional[List[str]] = None,
) -> str:
    # normalize optionals (avoid mutable default args)
    axiom_added = list(axiom_added) if axiom_added else []
    proof = list(proof) if proof else []

    lean_input = ""

    # --- 1) Hoist 'import ...' from added axioms to the top, dedup safely ---
    if axiom_added:
        imports: set[str] = set()
        for a in range(len(axiom_added)):
            seg_lines = []
            for line in axiom_added[a].splitlines():
                m = re.match(r"\s*(import[^\r\n]+)", line)
                if m and "--" not in line:
                    imports.add(m.group(1).strip())
                    # remove the import portion from this line
                    cleaned = re.sub(r"\s*import[^\r\n]+", "", line).rstrip()
                    if cleaned:
                        seg_lines.append(cleaned)
                else:
                    seg_lines.append(line)
            axiom_added[a] = "\n".join(seg_lines)

        for imp in sorted(imports):
            if imp not in body:
                lean_input += imp + "\n"

    # --- 2) Append body ---
    lean_input += "\n" + body + "\n"

    # --- 3) Build per-theorem lookups (no fragile index math) ---
    axiom_by_thm: Dict[int, str] = dict(zip(theorems, axiom_added))
    proof_by_thm: Dict[int, str] = dict(zip(theorems, proof))

    # --- 4) Emit chunks in PIT order, injecting per-theorem extras/proofs ---
    for i in range(len(PITs)):
        if i in axioms_provided:
            lean_input += PITs[i]
        elif i in theorems:
            extra_axiom = axiom_by_thm.get(i, "")
            proof_text = proof_by_thm.get(i, "")

            if extra_axiom:
                lean_input += extra_axiom + "\n\n"

            if proof_text:
                lean_input += inject_proof(PITs[i], proof_text) + "\n"
            else:
                lean_input += PITs[i] + "\n"
        elif i in unused:
            # skip failing lemma blocks
            continue
        else:
            lean_input += PITs[i] + "\n"

    return lean_input

def extract_code(text: str) -> str:
    # extract code from markdown style code block
    code = "\n".join(text.strip().splitlines())

    if code.startswith("```lean"):
        code = code[7:]

    if len(code) >= 3 and code[-3:] == "```":
        code = code[:-3]

    return code

def append_jsonl(rec: Dict[str, Any], path: str) -> None:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")

def write_log(state:State):
    # log the result of each round
    append_jsonl(
        {"event": "round-end",
         "round": str(state.round), 
         "lean_code": link_lean_code(state.body, state.PITs, state.axioms_provided, state.unused, state.theorems, state.axioms_added, state.proof_tactics), 
         "error": state.lean_messge},
         state.out_path
    )
    return state

def _invoke_structured_safe(runnable, prompt_input: dict, out_path: str) -> Optional["LLMResponse"]:
    """Call structured LLM; return LLMResponse or None on parse/validation issues."""
    try:
        resp = runnable.invoke(prompt_input)
    except Exception as e:
        append_jsonl(
            {"event": "llm-parse-exception", "error": repr(e)},
            out_path,
        )
        return None
    if resp is None:
        append_jsonl(
            {"event": "llm-parse-none", "note": "Structured output is None"},
            out_path,
        )
        return None
    # Some backends may return a dict instead of the model; coerce if needed
    if isinstance(resp, dict):
        try:
            return LLMResponse.model_validate(resp)
        except Exception as e:
            append_jsonl(
                {"event": "llm-parse-coerce-failed", "error": repr(e), "raw": resp},
                out_path,
            )
            return None
    return resp  # expected: an LLMResponse instance

def llm_response(state:State) -> State:
    # select the cheat sheet style
    # select the cheat sheet style
    if state.style == "AMR-Role":
        cheat_sheet = AMR_Role_cheat_sheet
    elif state.style == "AMR-Frame":
        cheat_sheet = AMR_Frame_cheat_sheet
    elif state.style == "autof":
        cheat_sheet = Auto_cheat_sheet
    else:
        cheat_sheet = ""
        raise ValueError
    # cheat_sheet = Auto_cheat_sheet

    # get LLM response
    # fit LLM with the answer template
    structured_llm = llm.with_structured_output(LLMResponse)
    prompt = ChatPromptTemplate.from_messages(
        [
            ("user", 
                "You are a Lean 4.23.0 proof assistant."
                "We have a chain of thought reasoning task written in lean language.\n"
                "In the following lean code, you will see reasoning step in natural language.\n"
                "You may see lean code as axiom or theorem after some natural language description.\n"
                "You need to write proof for **each theorem** followed by **sorry** in lean. You may introduce extra axioms which helps your to proof each theorem.\n"
                "You response should be in a list of objects for **each theorem** appearing in the given lean code.\n"
                "An object contains two properties:\n"
                " (1) extra axioms are extra knowledge you introduce to prove each theorem."
                " You should write empty string \"\" if you think there is no need to add extra axioms.\n"
                " (2) proof represents proof tactics to replace `sorry` in each theorem."
                " You should repeat the theorem body until `sorry` and replace `sorry` with your proof in your response.\n"
                "Inside your response, include only Lean code (no prose).\n\n"
                "---\n"
                "{lean_code}\n"
                "---\n"
                "{cheat_sheet}"
                "\n"
                "Requirements & tips:\n"
                "1) Assume a closed-world model: anything not asserted in axioms does not hold."
                " You may introduce new axioms capturing commonsense lexical entailments (e.g., `man → person`)"
                " or other commonsense to bridge gaps between given axioms and the target theorem."
                " It is often shorter to add such standalone axioms explicitly, feel free to do so.\n"
                "2) Use **Lean 4.23.0** syntax.\n"
                "3) A useful tactic pattern is to unfold the main axioms and `rcases` it to obtain all factual statements; relate those to the target theorem as needed.\n"
                "4) You may think out loud briefly, but your **answer must include exactly one**"
                " lists of objects containing \"extra axioms introduced\", \"theorem with `sorry` replaced with proof\" for each theorem.\n"
                "5) If you use any library-defined tactics, include the required `import` statements"
                " at the **beginning of extra-axiom block** in the corresponding answer object.\n"
                "6) If you think there is no need to introduce extra axioms to prove a theorem, please use an empty string \"\".\n"
                "7) Prefer standard tactics from core Lean; avoid nonstandard community tactics by default.\n"
                "8) In your response, you need to repeat theorems' until `sorry` and replace `sorry` with your proof.\n"
            )
        ]
    )

    # if there is already generated lean code and it caused errors
    # add generated code and let LLM generate new code
    if state.round != 0:
        prompt.extend(
            [
                ("user", 
                    "After inserting extra axioms and proofs you generated last time, the whole lean file is shown as follows.\n"
                    "---\n"
                    "{lean_code_with_last_response}\n"
                    "---\n"
                ),
                ("user", 
                    "Your last answer did not typecheck in Lean. Here are the compiler errors:\n"
                    "---\n"
                    "{error_message}\n"
                    "---\n"
                    "Please correct the mistakes. End your response with **one** lists of objects containing \"extra axioms introduced\", \"theorem with `sorry` replaced with proof\" for each theorem.\n"
                    "Ensure any required imports are at the top of the extra axioms block.\n"
                    "Both extra axioms and proof should be in lean.\n"
                )
            ]
        )

    # Build the prompt inputs once
    base_inputs = {
        "lean_code": link_lean_code(
            state.body, state.PITs, state.axioms_provided, state.unused, state.theorems
        ),
        "cheat_sheet": cheat_sheet,
    }
    if state.round != 0:
        base_inputs.update({
            "lean_code_with_last_response": link_lean_code(
                state.body, state.PITs, state.axioms_provided, state.unused, state.theorems,
                state.axioms_added, state.proof_tactics
            ),
            "error_message": state.lean_messge,
        })

    # --- invoke safely ---
    resp = _invoke_structured_safe(structured_llm, prompt.invoke(base_inputs), state.out_path)

    # If parsing failed or schema missing, count the interaction and continue
    if resp is None or not getattr(resp, "axiom_and_proof", None):
        state.round += 1
        state.lean_messge = "STRUCTURED_OUTPUT_PARSE_FAILED_OR_EMPTY"
        append_jsonl(
            {"event": "ai-response-parse-failed",
             "round": state.round,
             "note": "No axiom_and_proof parsed"},
            state.out_path,
        )
        # leave axioms_added / proof_tactics unchanged or clear them explicitly:
        # state.axioms_added, state.proof_tactics = [], []
        return state

    # --- normal path: extract axioms/proofs ---
    axioms: List[str] = []
    proofs: List[str] = []
    for o in resp.axiom_and_proof:
        axiom = extract_code(o.axiom)
        proof = extract_code(o.proof)
        # If the model echoed a theorem block, strip to tactics after "by\n"
        try:
            by = proof.index("by\n")
            proof = proof[by + 3:].strip() + "\n"
        except Exception:
            pass
        axioms.append(axiom)
        proofs.append(proof)

    # Normalize lengths to number of theorems
    n_thm = len(state.theorems)
    if len(axioms) < n_thm:
        axioms += [""] * (n_thm - len(axioms))
    if len(proofs) < n_thm:
        proofs += [""] * (n_thm - len(proofs))
    axioms = axioms[:n_thm]
    proofs = proofs[:n_thm]

    # Guard: forbid 'sorry' returning from the model
    if any(contains_sorry(p) for p in proofs if p):
        state.round += 1
        state.axioms_added = axioms
        state.proof_tactics = proofs
        state.lean_messge = "SORRY_PLACEHOLDER_DETECTED"
        append_jsonl({"event": "ai-response", "axioms": axioms, "proofs": proofs}, state.out_path)
        return state

    # Commit updates
    state.round += 1
    state.axioms_added = axioms
    state.proof_tactics = proofs
    append_jsonl({"event": "ai-response", "axioms": axioms, "proofs": proofs}, state.out_path)
    return state

config = LeanREPLConfig(verbose = True)
server = LeanServer(config = config)

def code_check(state:State) -> State:
    # check lean code before running
    lean_code = link_lean_code(state.body, state.PITs, state.axioms_provided, state.unused, state.theorems)


    result = server.run(Command(cmd = lean_code))

    message = "\n".join(["line " + str(m.start_pos.line) + ", col " + str(m.start_pos.column) + ": " + m.data for m in result.messages if m.severity in ("error")])

    if message != "":
        raise SyntaxError("The lean file {} did not pass the check of lean system. Please ignore this file and report it our google sheet.".format(state.file_path))

    return state

def route_preflight(state:State) -> str:
    if state.preflight_ok:
        print('preflight ok!')
        return "LLM response"
    else:
        print('preflight failed...')
        append_jsonl(
            {"event": "round-end",
             "round": str(state.round), 
             "lean_code": link_lean_code(state.body, state.PITs, state.axioms_provided, state.unused, state.theorems, state.axioms_added, state.proof_tactics), 
             "error": state.lean_messge},
             state.out_path
        )
        return "print result"

def preflight_compile(state: State) -> State:
    lean_code = link_lean_code(
        state.body, state.PITs, state.axioms_provided, state.unused, state.theorems
    )
    try:
        result = server.run(Command(cmd=lean_code))
        err_lines = []
        for m in result.messages:
            if getattr(m, "severity", "").lower() == "error":
                ln = getattr(getattr(m, "start_pos", None), "line", None)
                col = getattr(getattr(m, "start_pos", None), "column", None)
                data = getattr(m, "data", "")
                err_lines.append(f"line {ln}, col {col}: {data}")
        lean_msg = "\n".join(err_lines)
        append_jsonl(
            {"event": "preflight-check", "preflight_ok": (False if err_lines else True), "msg": lean_msg},
            state.out_path,
        )
        state.preflight_ok = not bool(err_lines)
        state.lean_messge = lean_msg
        return state
    except Exception as e:
        lean_msg = f"[preflight exception] {e}"
        append_jsonl(
            {"event": "preflight-check", "preflight_ok": False, "msg": lean_msg},
            state.out_path,
        )
        state.preflight_ok = False
        state.lean_messge = lean_msg
        return state

# --- helpers for pretty diagnostics ---
def _get_line(code: str, line_1based: int) -> str:
    if not isinstance(line_1based, int) or line_1based < 1:
        return ""
    lines = code.splitlines()
    if line_1based > len(lines):
        return ""
    return lines[line_1based - 1]

def _render_diag_block(code: str, line: int, col: int, msg: str, ctx: int = 1) -> str:
    """
    Render a small context block with a caret under 'col'.
    line/col are 1-based (Lean convention).
    """
    lines = code.splitlines()
    if not (isinstance(line, int) and 1 <= line <= len(lines)):
        # Fallback: no position, just return the message
        return f"{msg}"

    # Window of context
    start = max(1, line - ctx)
    end = min(len(lines), line + ctx)
    pad = len(str(end))  # line number width

    def _prefix(n: int) -> str:
        return f"{n:>{pad}} | "

    block_lines = []
    for ln in range(start, end + 1):
        mark = ">" if ln == line else " "
        block_lines.append(f"{mark}{_prefix(ln)}{lines[ln - 1]}")

    # Caret under column (best-effort)
    ref_line = lines[line - 1].expandtabs(2)
    col = max(1, int(col) if isinstance(col, int) else 1)
    caret_pos = len(_prefix(line)) + min(col - 1, max(0, len(ref_line)))
    caret_line = " " * caret_pos + "^"

    # Attach message at the end
    block_lines.append(caret_line)
    block_lines.append(f"{' ' * (len(_prefix(line)))}{msg}")

    return "\n".join(block_lines)


def lean_system_message(state: State) -> State:
    lean_code = link_lean_code(
        state.body, state.PITs, state.axioms_provided, state.unused, state.theorems,
        state.axioms_added, state.proof_tactics
    )

    # Early guard: if 'sorry' remains, skip compile and force another round
    if contains_sorry(lean_code):
        state.lean_messge = "Detected 'sorry' in candidate Lean code"
        return state

    result = server.run(Command(cmd=lean_code))

    def _is_no_goals_err(s: str) -> bool:
        return "no goals to be solved" in (s or "").lower()

    diag_blocks = []
    for m in getattr(result, "messages", []):
        if str(getattr(m, "severity", "")).lower() != "error":
            continue
        data = str(getattr(m, "data", "")) or ""
        if _is_no_goals_err(data):
            # Benign: goal already solved; extra tactics remain
            continue

        ln = getattr(getattr(m, "start_pos", None), "line", None)
        col = getattr(getattr(m, "start_pos", None), "column", None)

        # Build a readable block with source excerpt + caret
        block = _render_diag_block(
            code=lean_code,
            line=(int(ln) if isinstance(ln, int) else ln),
            col=(int(col) if isinstance(col, int) else col),
            msg=data,
            ctx=1,  # 1 line of context before/after; tweak as you like
        )
        # Prepend a compact header for quick scanning
        header = f"line {ln}, col {col}:"
        diag_blocks.append(f"{header}\n{block}")

    # Join all diagnostics. Empty → success.
    state.lean_messge = "\n\n".join(diag_blocks)
    return state

def print_state(state:State):
    # used to print the final generated reasoning steps and the body of lean file
    print("---round", state.round)
    # print("---lean code---")
    # print(link_lean_code(state.body, state.PITs, state.axioms_provided, state.unused, state.theorems, state.axioms_added, state.proof_tactics))
    print("---error message---")
    print(state.lean_messge)


def loop_check(state:State) -> str:
    # decide whether we continue the loop or exit
    if state.lean_messge == "":
        print("All theorems were successfully proved.")
        return "print result"
    
    if state.round >= state.max_round:
        print("Some theorem was not proved within {} rounds.".format(state.max_round))
        return "print result"
    else:
        return "LLM response"

# helper: pull a numeric index from filename (last number in the name)
def extract_index(name: str) -> int | None:
    m = re.search(r"(\d+)(?=\D*$)", name)  # last run of digits before extension/end
    return int(m.group(1)) if m else None

if __name__ == '__main__':
    MAX_ROUND = 3
    ap = argparse.ArgumentParser(description="Run LangGraph over many files with per-run JSON logging.")
    ap.add_argument("--inputs", type=str, default=".", help="Directory containing input .lean files")
    ap.add_argument("--pattern", type=str, default="*.lean", help="Glob for inputs (default: *.lean)")
    ap.add_argument("--out", type=str, default="out", help="Output directory for logs")
    ap.add_argument("--rounds", type=int, default=MAX_ROUND, help="Max LLM/Lean rounds per file")
    ap.add_argument("--style", type=str, default="autof", help="Translation style (default: autof, other options [AMR-Frame, AMR-Role, CCG])")
    ap.add_argument("--filename-re", type=str, default=None, help="Regex to match filenames")
    ap.add_argument("--min-id", type=int, default=None, help="Minimum numeric ID in filename to include")
    ap.add_argument("--max-id", type=int, default=None, help="Maximum numeric ID in filename to include")
    ap.add_argument("--exclude-processed", action="store_true", help="Skip files that already have an out JSON")

    args = ap.parse_args()
    # LLM will not make response more than this time

    inputs = Path(args.inputs)
    outdir = Path(args.out)

    graph_builder = StateGraph(State)
    graph_builder.add_node("preflight compile", preflight_compile)
    graph_builder.add_node("Code check", code_check)
    graph_builder.add_node("LLM response", llm_response)
    graph_builder.add_node("LEAN message", lean_system_message)
    graph_builder.add_node("write log file", write_log)
    graph_builder.add_node("print result", print_state)

    graph_builder.add_edge(START, "preflight compile")
    graph_builder.add_conditional_edges("preflight compile", route_preflight)
 
    # graph_builder.add_edge(START, "Code check")
    # graph_builder.add_edge("Code check", "LLM response")
    graph_builder.add_edge("LLM response", "LEAN message")
    graph_builder.add_edge("LEAN message", "write log file")
    graph_builder.add_conditional_edges("write log file", loop_check)
    graph_builder.add_edge("print result", END)

    graph = graph_builder.compile()

    # overall stats
    compiled_rounds = []
    
    # build processed set (based on out JSONs you write per file)
    processed_stems = set()
    if args.exclude_processed:
        for p in outdir.glob("*.json"):
            processed_stems.add(p.stem)  # run_id is f.stem, so this aligns

    filename_re = re.compile(args.filename_re) if args.filename_re else None

    # start with glob, then refine via regex / numeric range / processed skip
    candidates = sorted(inputs.glob(args.pattern))
    files = []
    for f in candidates:
        name = f.name
        idx = extract_index(name)

        if filename_re and not filename_re.search(name):
            continue
        if args.min_id is not None and (idx is None or idx < args.min_id):
            continue
        if args.max_id is not None and (idx is None or idx > args.max_id):
            continue
        if args.exclude_processed and f.stem in processed_stems:
            continue

        files.append(f)

    if not files:
        print(f"No files matched after filtering in {inputs.resolve()}")
        exit()

    read_file_func = read_file
    if args.style.startswith('AMR'):
        read_file_func = amr2lean_read_file

    for f in files:
        print(f"==> Running {f.name}")
        # run_one_file(graph, f, outdir, max_round=args.rounds)

        run_id = f"{f.stem}"
        # jsonl_path = outdir / f"{run_id}.jsonl"
        json_path  = outdir / f"{run_id}.json"

        initial_state = read_file_func(str(f.resolve()), str(json_path.resolve()), args.style, int(args.rounds))

        graph.invoke(initial_state)
