from __future__ import annotations
import re, textwrap, itertools
from collections import defaultdict
from typing import Dict, List, Tuple

from lean_snippets import *
from amr_patterns import *
from utils import *
from propbank_interface import PropbankCatalogue, Roleset
from amr_special_frames import AMRSpecialFrames
from amr_toolbox.AMRgraph import PenmanAMRTree, AMRNode, name_collapser
from amr_special_entities import AMRSpecialEntities
from amr_special_preps import PrepInventory

from collections import deque
import copy 
import math 



# --------------------------------------------------------------------------- #
#  Main Lean module container
# --------------------------------------------------------------------------- #
class LeanModule:
    def __init__(self, import_semantic_gadgets=False):
        self.inductives : Dict[str,str] = {}
        self.structs    : Dict[str,str] = {}
        self.instances  : List[str] = []
        self.exist_axioms : List[str] = []      # new: quantifier axioms
        self.axioms     : List[str] = []
        self.noncore_preds : Dict[str,str] = {}   # edge → template line
        self.noncore_axioms: List[str] = []
        self.import_semantic_gadgets = import_semantic_gadgets

    def render(self) -> str:
        if self.import_semantic_gadgets:
            parts = [
                "import AMRGadgets",
                *self.inductives.values(),
                "", *self.structs.values(),
                "", *self.instances,
                "", *self.exist_axioms,             # quantifier axioms before events
                "", *self.axioms,
                "", *self.noncore_preds.values(),
                "", *self.noncore_axioms]
        else:            
            parts = [
                MODIFIER_SNIPPET, MODIFIED_CONC_SNIPPET, CHOICE_SNIPPET,
                "", EVENT_FUN_DEFS,
                *self.inductives.values(),
                "", *self.structs.values(),
                "", *self.instances,
                "", *self.exist_axioms,             # quantifier axioms before events
                "", *self.axioms,
                "", *self.noncore_preds.values(),
                "", *self.noncore_axioms]
        return "\n\n".join(parts)

MOD_CACHE = set()   # keep at module level

# --------------------------------------------------------------------------- #
#  Translator
# --------------------------------------------------------------------------- #
class AMR2LeanTranslator:
    """Call translate(amr_str) -> Lean source string."""
    def __init__(self, propbank_root:str, import_semantic_gadgets:bool=False):
        self.pb = PropbankCatalogue(propbank_root)
        self.ent = AMRSpecialEntities("special_entities.json")
        self.M  = LeanModule(import_semantic_gadgets)
        self.import_semantic_gadgets = import_semantic_gadgets
        self.sf = AMRSpecialFrames("special_frames.json")
        self.preps = PrepInventory("special_preps.json")
        self.struct_arg_order: Dict[str, List[int]] = {}   # e.g. "new_02" → [1, 2]
        self._skip_instantiation: Set[str] = set()
        self._pred_sig : Dict[str, str] = {}
        self.node_deps : Dict[AMRNode, set] = {}
        self.node_order : List[AMRNode] = []

    @staticmethod
    def _is_predicate(node:AMRNode) -> bool:
        return bool(SENSE_RE.search(node.text.strip()))
    
    @staticmethod
    def _is_attribute(node: AMRNode) -> bool:
        """True for nodes whose var_name starts with 'attr-' (AMR attributes)."""
        return bool(ATTR_RE.match(node.var_name))
    # @staticmethod
    # def _filter_i(nodes:Dict[str,AMRNode]):
    #     # filter the node where the variable name and concept name are both 'i', confuses lean

    #     for nvar, node in nodes.items():
    #         if nvar == 'i' and node.text == 'i':
    #             node.var_name = 'ii'
    def categorize_node(self, node):
        # Rule 0: connectives
        if node.text in CONNECTOR:
            return "connector"

        # Rule 1: Special Frame
        if self.sf.get(node.text):
            return "special-frame"

        # Rule 2: Predicate
        if SENSE_RE.search(node.text):
            return "predicate"

        # Rule 3: Special Entity
        if self.ent.get(node.text):
            return "special-entity"

        # Rule 4: Attribute leaf
        if node.var_name.startswith("attr-"):
            number_type = _is_number(node.text)
            if number_type:
                return number_type
            return "attribute"

        # Rule 5: Terminal node
        if not node.children:
            if _is_mod(node.text):
                return "term-mod"
            elif _is_noun_lemma(node.text):
                return "term-noun"
            else:
                return "term-other"

        # Rule 6: Preposition (if in preposition dict or any :op children)
        if self.prep.get(node.text) or any(rel.startswith(":op") for rel, _ in node.children):
            return "inter-prep-mod"

        # Rule 7: Adjective/Noun intermediate nodes
        if _is_mod(node.text) and not _is_noun_lemma(node.text):
            return "inter-mod"
        return "inter-noun"
    # ---------- public entry ----------
    def translate(self, amr_str:str) -> str:
        tree = PenmanAMRTree(amr_str, remove_alignmark=True)
        # print(amr_str)
        print([(var_name, n.var_name, n.text) for var_name, n in tree.node_dict.items()])
        # self._filter_i(tree.node_dict)
        self._prop_cache = {}
        # reinit records banks 
        self.struct_arg_order = {}   # e.g. "new_02" → [1, 2]
        self._skip_instantiation = set()
        self._pred_sig = {}
        self.M = LeanModule(self.import_semantic_gadgets)

        # --- MUST happen first! ---
        self._annotate_meta(tree.node_dict)
        self.node_deps = self._annotate_node_category(tree)
        self.node_order = topo_sort(self.node_deps)

        self._annotate_attributives(tree.node_dict)

        # Now every node has a .meta dict, so these are safe:
        self._emit_types(tree.node_dict)
        self._quantifier_axioms(tree.node_dict)

        # ── Phase A: build every def … := … (fills self._pred_sig fully) ──
        self._emit_instances(tree.node_dict)

        # ── Phase B: now that pred_sig is complete, build axioms & prop_cache ─
        self._emit_event_axioms(tree.node_dict)

        # ── Phase C: now emit connectors from the final prop_cache ──────────
        self._emit_connectors(tree.node_dict)

        # ── rest of your noncore / attributive / modifier passes ───────────
        self._emit_noncore_axioms(tree.node_dict)
        self._emit_attributive_axioms(tree.node_dict)


        self._emit_modifiers(tree.node_dict)    # still keeps unary adverbs if any
        self._emit_modified(tree.node_dict)     # creates *foo_mc* constants
        # ------------------------------------------------------------------

        return self.M.render()

    # ------------------------------------------------------------------ #
    #  Phase 0 : annotate graph with meta flags
    # ------------------------------------------------------------------ #
    def _annotate_meta(self, nodes:Dict[str,AMRNode]):
        # 6. non-veridical = child reached via :content
        
        for n in nodes.values():
            for child, rel in n.children.items():
                if rel == ":content":
                    child.meta["nonveridical"] = True
                elif rel == ":content-of":          # ← new
                    n.meta["nonveridical"] = True
                
        # 7. definiteness
        for n in nodes.values():
            if self._is_attribute(n):
                continue
            if self._is_predicate(n):        # only concepts matter
                continue
            if has_child(n, ":definite", "+"):
                n.meta["definite"] = "+"
            elif has_child(n, ":definite", "-"):
                n.meta["definite"] = "-"
            else:
                n.meta["definite"] = None
            # 8. plural
            if has_child(n, ":plural", "+"):
                n.meta["plural"] = True
        # print('n.meta: ', [(n.text, n.var_name, n.meta) for n in nodes.values()])
        self._propagate_nonveridical(nodes)

    def _propagate_nonveridical(self, nodes):
        queue = [n for n in nodes.values() if n.meta.get("nonveridical")]
        while queue:
            cur = queue.pop()
            for ch, rel in cur.children.items():
                # print('ch: ', ch.var_name, '|', ch.text)
                if not ch.meta.get("nonveridical"):
                    ch.meta["nonveridical"] = True
                    queue.append(ch)
    

    def _annotate_attributives(self, nodes):
        for child in nodes.values():
            for parent, rel in child.parents.items():
                m = ATTR_OF_RE.match(rel)
                if m:
                    child.meta["attributive"] = int(m.group(1))   # which arg slot
                    child.meta["attr_head"]   = parent


    def _annotate_node_category(self, tree):
        queue = deque([tree.root])
        deps = {}  # for topological sorting

        while queue:
            node = queue.popleft()
            node.meta["category"] = categorize_node(node)

            for rel, child in node.children:
                queue.append(child)
                deps.setdefault(child, set()).add(node)
                deps.setdefault(node, set())  # ensure node exists in deps
        return deps
    # ------------------------------------------------------------------ #
    #  Phase 1 :  inductive & structure boiler-plate
    # ------------------------------------------------------------------ #

    def _emit_types(self, nodes:Dict[str,AMRNode]):

        for n in nodes.values():
            # ---------- connector lemmas ----------
            
            if n.meta['category'] == "connector":
                tname = CONNECTOR[n.text]
                if tname not in self.M.inductives:
                    self.M.inductives[tname] = INDUCTIVE_TMPL.format(name=tname)
                continue

            # for all predicate nodes, we generate structures to hold data
            if n.meta['category'] == 'predicate' or n.meta['category'] == 'special-frame':
                parts = n.text.rsplit('-', 1)
                lemma, sense = parts + [''] * (2 - len(parts))
                key = f"{lemma.replace('-','_')}_{sense}"
                if key in self.M.structs:      # already emitted
                    continue

                rs = self.pb.get_roleset(n.text)   # may be None
                # print('n.text: ', n.text)
                # print('rs: ', rs)
                # print('-'*80)
                if rs is not None:
                    # print('key: ', key)
                    self.M.structs[key] = self._mk_pb_struct(rs)
                else:
                    # ----- check AMR special-frame catalogue -----
                    spec_roles = self.sf.get(n.text)
                    if spec_roles is not None:
                        # Build structure with named fields from JSON
                        self.M.structs[key] = self._mk_spec_frame_struct(key, spec_roles)
                    else:
                        # fallback: generic arg0, arg1, … this case is AMR newly added frames not covered by propbank yet. 
                        # 1. collect roles ad-hoc from AMR
                        idx_set = set()
                        for node in nodes.values():
                            # 1.1 find the node in the AMR
                            if node.var_name != n.var_name:
                                continue
                            # 1.2 only consider the indexed roles
                            # outgoing :argk
                            for rel in node.children.values():
                                m = re.match(r":arg(\d+)", rel, re.I)
                                if m: idx_set.add(int(m.group(1)))
                            # incoming :argk-of
                            for rel in node.parents.values():
                                m = re.match(r":arg(\d+)-of", rel, re.I)
                                if m: idx_set.add(int(m.group(1)))
                        # if still empty, default to {0} arguments structure
                        if not idx_set:
                            idx_set.add(0)
                        self.M.structs[key] = self._mk_generic_struct(key, idx_set)
            else:
                # not a predicates or special frame, then, it could be noun nodes or special entity node or prep node
                norm_name = n.text.replace('-', '_')
                
                if n.meta['category'] == 'special-entity':
                    # --- declare fixed-field structure once
                    spec_ent = self.ent.get(n.text)


                    if spec_ent_name not in self.M.structs:
                        self.M.structs[n.text] = self._mk_spec_entity_struct(norm_name, spec_ent)
                
                elif n.meta['category'] == 'attribute':
                    if _is_number(n.text):
                        # only the most primative category of node can specify the type signature immediately.
                        self._pred_sig[n.var_name] = "Float"
                    continue
                else:
                    # the last bucket is the noun type 
                    if n.text not in self.M.inductives:
                        self.M.inductives[n.text] = INDUCTIVE_TMPL.format(name=norm_name)

    # ------------------------------------------------------------------ #
    #  generic struct for special entities such as rate-quantity
    # ------------------------------------------------------------------ #
    def _mk_spec_entity_struct(self, spec_ent_name: str, spec_ent: List[EntityField]) -> str:
        field_lines = "\n".join(f"  ({f.name} : {f.ty})" for f in spec_ent)
        return SPECIAL_ENTITY_TMPL.format(name=spec_ent_name, fields=field_lines)

    def _mk_pb_struct(self, rs:Roleset) -> str:
        # print('rs.roles: ', [(r.idx, r.fun) for r in rs.roles])
        roles = sorted(rs.roles, key=lambda r: int(r.idx))   # 0,1,2,…

        tparams = " ".join(f"(t{i+1} : Type)" for i,_ in enumerate(roles))

        fields  = "\n".join(
            f"  (arg{r.idx} : t{j+1}) -- {r.fun.lower()}"
            for j, r in enumerate(roles)      # j is the *position*, not r.idx
        )
        rslemma = copy.deepcopy(rs.lemma)
        normed_lemma = rslemma.replace('-', '_')
        self.struct_arg_order[f"{normed_lemma}_{rs.sense}"] = [int(r.idx) for r in roles]
        # print('self.struct_arg_order: ', self.struct_arg_order)
        return STRUCTURE_TMPL.format(
            lemma=normed_lemma, sense=rs.sense,
            type_params=tparams, fields=fields)
    
    # ------------------------------------------------------------------ #
    #  generic struct for AMR-only frames  (non PropBank entry)
    # ------------------------------------------------------------------ #
    def _mk_generic_struct(self, pred: str, indices: set[int]) -> str:
        # sorted list, e.g. [1,2]  (arg1, arg2) since generic frames also use index arguments.
        # pred already replaced `-` with underscore
        idxs = sorted(indices)
        tparams = " ".join(f"(t{i+1} : Type)" for i,_ in enumerate(idxs))
        fields  = "\n".join(
            f"  (arg{idx} : t{j+1})"
            for j, idx in enumerate(idxs))

        self.struct_arg_order[pred] = idxs
        return GENERIC_STRUCT_TMPL.format(
            name=pred, type_params=tparams, fields=fields)

    def _mk_spec_frame_struct(self, spec_frame_name: str, spec_roles: List[SpecialRole]) -> str:
        tparams = " ".join(f"(t{i+1} : Type)" for i in range(len(spec_roles)))
        fields  = "\n".join(
            f"  (arg{role.idx} : t{tidx+1}) -- {role.name}"
            for tidx, role in enumerate(spec_roles))
        self.struct_arg_order[spec_frame_name] = [int(r.idx) for r in spec_roles]
        return  GENERIC_STRUCT_TMPL.format(
            name=spec_frame_name, type_params=tparams, fields=fields)
    # ------------------------------------------------------------------ #
    #  Phase 2 : Quantifier / existence axioms (rules 7 & 8)
    # ------------------------------------------------------------------ #

    def _quantifier_axioms(self, nodes: Dict[str, AMRNode]):
        """
        For each NON-predicate, NON-attribute concept node:
            definite +    → nothing extra
            indefinite    →  ∃ x, x = <const>
            plural +      →  ∃ y, y ≠ <const>   (in addition if indefinite)
        """
        for n in nodes.values():
            # if (self._is_predicate(n) 
            #     or self._is_attribute(n) 
            #     or not _is_noun_lemma(n.text) 
            #     or (_is_mod(n.text) and _is_noun_lemma(n.text))
            #     or self.ent.get(n.text) is not None # special entity, not an event
            #     or n.text in {"and", "or", "multisentence", "name", "imperative"}
            #     or "mods" in n.meta): 
            #     continue
            if not (n.meta['category'] == "term-noun" 
                or n.meta['category'] == "term-other" 
                or n.meta['category'] == "inter-noun"):
                continue

            type_sig = n.text.replace('-', '_')
            is_definite = (n.meta.get("definite") == "+")
            is_plural   = n.meta.get("plural", False)

            if is_definite and not is_plural:
                # entirely specific ⇒ no quantifier axiom needed
                continue

            if not is_definite:
                self.M.exist_axioms.append(
                    f"axiom exists_{n.var_name} : ∃ x : {type_sig}, x = {n.var_name}")

            if is_plural:
                self.M.exist_axioms.append(
                    f"axiom plural_{n.var_name} : ∃ y : {type_sig}, y ≠ {n.var_name}")

    # ------------------------------------------------------------------ #
    #  Phase 3 :  concrete constants / structures
    # ------------------------------------------------------------------ #

    def _emit_instances(self, nodes: Dict[str, AMRNode]):
        concept_defs = []               # all non-predicate defs
        pred_nodes   = {}               # var_name → AMRNode for predicates, including connectors
        pred_deps    = {}               # var_name → set of predicate var deps


        # ── Phase 1: handle non-predicates (nouns, special entities, connectors) ──
        for n in nodes.values():
            # 1a) skip pure attributes
            node_cat = n.meta['category']
            if node_cat in ['attribute', 'term-mod', 'inter-prep-mod'] :
                continue

            elif node_cat in ['float', 'int']:
                self._pred_sig[n.var_name] = node_cat
                continue


            # 1b) connectors (and/or/etc) are handled elsewhere, we create a record in _pred_sig for signature reference and pred_nodes for predicate instantiation dependency resort
            if node_cat == 'connector':
                # e.g. self._pred_sig['o'] = 'Choice Prop'
                self._pred_sig[n.var_name] = 'Choice Prop'
                pred_nodes[n.var_name]     = n
                continue

            norm_name = n.text.replace("-", "_")
            # 1c) special‐entity records
            
            if node_cat == 'special-entity':
                spec_ent = self.ent.get(n.text)
                kvs = []
                for f in spec_ent:
                    # f means field
                    # c is the child node of the special entity node that corresponds to the f field
                    c = next((c for c,r in n.children.items() if r==f.role), None)
                    if c is None:
                        # no fields of this special entity was provided from AMR
                        kvs.append(f"{f.name} := _")
                    elif f.ty == "String":
                        ctext = c.text.strip('"')
                        kvs.append(f'{f.name} := "{ctext}"')
                    else:
                        if c.meta['category'] in ['attribute', 'flat', 'int']:
                            kvs.append(f"{f.name} := {c.text}")
                        else:
                            kvs.append(f"{f.name} := {c.var_name}")

                rec = "{ " + ", ".join(kvs) + " }"
                
                # record its type sig exactly as its structure name
                self._pred_sig[n.var_name] = norm_name
                concept_defs.append(
                    INSTANCE_TMPL.format(var=n.var_name,
                                         type=norm_name,
                                         value=rec))
                continue

            # 1d) bare nouns / concepts
            if node_cat in ['term-noun', 'inter-noun']:
                
                self._pred_sig[n.var_name] = norm_name
                concept_defs.append(
                    INSTANCE_TMPL.format(
                        var=n.var_name,
                        type=norm_name,
                        value=f"{norm_name}.mk") +
                    (" -- definite" if n.meta.get("definite")=="+"
                     else " -- indefinite / plural"))
                continue

            # 1e) predicate — collect for phase 2, since they have dependencies
            pred_nodes[n.var_name] = n

        # ── Phase 4: emit predicate defs in sorted order ──────────────────────
        pred_defs = []
        emitted_conns = set()
        connectors   = [n for v,n in pred_nodes.items() if n.text in CONNECTOR]
        
        for n in self.node_order:
            # ── 4a: if any connector feeds into this predicate, emit it first ──

            struct = n.text.replace("-", "_")

            # 4b) skip connectors here (they’re already emitted on demand)
            if n.meta['category'] == 'connector':
                # we put a placeholder since we need all types signature to be collected for the connector type
                pred_defs.append(f'PLACEHOLDER-connector-{n.var_name}')
                continue
          


            # 4c) otherwise an ordinary PropBank (or special‐frame) predicate
            # collect argument positions & vars
            arg_pairs, _ = self._collect_arg_info(n)
            
            val_map = {}
            for idx, node in arg_pairs:
                node_cat = node.meta['category']
                if node_cat == 'attribute':
                    val_map[int(idx)] = node.text
                elif node_cat in ['term-mod', 'inter-mod', 'inter-prep-mod']:
                    val_map[int(idx)] = f'"{node.text}"'
                else:
                    val_map[int(idx)] = node.var_name
            # val_map      = {int(idx): node for idx,node in arg_pairs}
            val_map_node = {int(idx): node for idx,node in arg_pairs}
            field_idxs   = self.struct_arg_order[struct]

            # build record literal
            record = ", ".join(
                f"arg{i} := {val_map.get(i, '()')}" for i in field_idxs)
            print('var:', var, 'val_map: ', val_map)
            # build signature by looking up each child’s recorded type
            raw_tps = []
            for i in field_idxs:
                child = val_map_node.get(i)
                if child:
                    if child.var_name in self._pred_sig:
                        raw_tps.append(self._pred_sig[child.var_name])
                    elif 'mod' in child.meta['category']:
                        raw_tps.append("String")

                else:
                    raw_tps.append("Unit")

            # wrap any multi‐token type in parentheses
            tp_list = [
                f"({tp})" if (" " in tp or tp.endswith("Unit")) else tp
                for tp in raw_tps
            ]

            # now compose the full signature
            sig = struct + ("" if not tp_list else " " + " ".join(tp_list))
            # cache it now for any later predicates
            # print('^'*30)
            # print(struct + '|' + var + ' sig available: ', sig)
           
            # print('^'*30)
            self._pred_sig[var] = sig

            pred_defs.append(
                INSTANCE_TMPL.format(var=var, type=sig, value=f"{{ {record} }}"))

        # emit the rest of the connectors
        # residue_connectors = [connector for connector in connectors if connector.var_name not in emitted_conns]
        # for conn in residue_connectors:
        for conn in connectors:
            cnode = pred_nodes[conn.var_name]
            opts = [
                self._prop_cache[ch.var_name]
                for ch in _ordered_children(cnode)
                if ch.var_name in self._prop_cache
            ]
            if not opts:
                # no structure but inductive types are the children of the connectors
                opts = []
                for ch in _ordered_children(cnode):
                    if ch.var_name in self._pred_sig:
                        # ch is a proposition or special frame struct init
                        pred_sig = self._pred_sig[ch.var_name]
                    else:
                        # ch is a noun type mk init
                        pred_sig = ch.text
                    e4c = f'E4C {pred_sig} {ch.var_name}'
                    opts.append(e4c)

            opts_str  = "[" + ", ".join(opts) + "]"
            excl_flag = "true" if conn.text=="or" else "false"
            pred_defs.append(
                f"def {conn.var_name} : Choice Prop :=\n"
                f"{{ options   := {opts_str},\n"
                f"  exclusive := {excl_flag} }}")
            emitted_conns.add(conn.var_name)

        # ── Phase 5: glue together ────────────────────────────────────────────
        self.M.instances.extend(concept_defs + pred_defs)


    def _emit_modified(self, nodes):
        for n in nodes.values():
            if "mods" not in n.meta:
                continue
            # concrete type of the head
            if self._is_predicate(n):
                base_type = self._pred_sig[n.var_name]          # e.g. learn_01 you skill Unit
            else:
                base_type = n.text.replace("-", "_")            # noun concept

            mc_var = f"{n.var_name}_mc"
            mods_list = "[" + ", ".join(n.meta["mods"]) + "]"
            

            self.M.instances.append(
                f"def {mc_var} : ModifiedConcept ({base_type}) :=\n"
                f"{{ head := {n.var_name}, mods := {mods_list} }}")

            self.M.exist_axioms.append(
                f"axiom exists_{mc_var} : ∃ m : ModifiedConcept ({base_type}), m = {mc_var}")

    def _collect_arg_info(self, pred_node:AMRNode):
        """
        Returns
            arg_pairs  : list[(idx_str, varname)]
            ty_params  : list[str]      -- in the same order
        with :content coerced to arg1, because in PropBank the 'content'
        argument is ARG1 and signals non-veridicality.
        """
        # def arg_value(node):
        #     if node.var_name.startswith('attr-'):
        #         return node.text
        #     else:
        #         return node.var_name

        arg_pairs, ty_params = [], []

        for child, rel in pred_node.children.items():
            m = re.match(r":arg(\d+)$", rel, re.I)   #  ← changed line
            if m:
                idx = m.group(1)                           # "0", "1", …
            elif rel == ":content":                       # our special rule
                idx = "1"                                 # maps to ARG1
            else:
                continue                                  # ignore modifiers etc.

            # arg_v = arg_value(child)
            arg_pairs.append((idx, child))
            ty_params.append(self._lean_type_of(child))


        # add this loop to pick up reversed roles
        for parent, rel in pred_node.parents.items():
            m = re.match(r":arg(\d+)-of", rel, re.I)
            if not m: continue
            idx = m.group(1)
            # arg_v = arg_value(parent)
            arg_pairs.append((idx, parent))
            ty_params.append(self._lean_type_of(parent))

        # keep Lean record fields deterministic
        arg_pairs.sort(key=lambda p: int(p[0]))
        return arg_pairs, ty_params

    def _lean_type_of(self, node: AMRNode) -> str:
        name = node.text.replace("-", "_")
        # 1) connector subgraphs stay as Choice Prop
        if node.text in CONNECTOR:
            return "(Choice Prop)"
        # 2) any predicate → saturated form
        if self._is_predicate(node):
            return f"({self._sat(name)})"
        # 3) any inductive (no params) → just name
        if name in self.M.inductives:
            return name
        # 4) any struct type (PropBank or special) → saturated with Units
        if name in self.struct_arg_order:
            # self._sat will pad missing slots with Unit
            return f"({self._sat(name)})"
        
        if _is_number(name):
            return "Float"
        # 5) everything else (e.g. bare nouns) → name
        return name
    
    def _sat(self, pred_name: str) -> str:
        idxs = self.struct_arg_order.get(pred_name)
        if idxs is None:
            return pred_name
        # pad every missing type‐param with "Unit"
        parts = []
        for _ in idxs:
            # look up a known concrete type (if you stored one), otherwise "Unit"
            # but since we now saturate **in** _lean_type_of, it's fine to always "Unit"
            parts.append("_")  
        # replace those "_" with actual Units?  or better, skip and do:
        return pred_name + " " + " ".join("Unit" for _ in idxs)
    # ----------  name helper  ----------
    def _name_literal(self, name_node: AMRNode) -> str | None:
        """
        For  (n / name :op1 "Denver" :op2 "International" …)
        return "Denver International …".  Returns None if pattern not matched.
        """
        if name_node.text != "name":
            return None
        parts = []
        for child, rel in name_node.children.items():
            if rel.startswith(":op"):
                # leaf nodes in your AMRs are attr-k / "String"
                parts.append(child.text.strip('"'))
        return " ".join(parts) if parts else None

    # ------------------------------------------------------------------ #
    #  Phase 4 : Event axioms  (∃-wrapping, modifiers, polarity)
    # ------------------------------------------------------------------ #
    def _emit_event_axioms(self, nodes: Dict[str, AMRNode]):

        def wrap_exist(arg_node: AMRNode, body: str) -> str:
            # no need to re-quantify definites
            if arg_node.meta.get("definite") == "+":
                return body
            # pick up the fully saturated type if this was a predicate
            typ = self._pred_sig.get(arg_node.var_name)
            if not typ:
                # fall back to naming the type after the concept
                typ = arg_node.text.replace("-", "_")
            return f"∃ ({arg_node.var_name} : {typ}), {body}"

        for n in nodes.values():
            if n.var_name.startswith('attr-'):
                # n is an attribute value node
                continue
            if (self._is_attribute(n) or not self._is_predicate(n)
                    or n.meta.get("attributive")
                    or self.ent.get(n.text)):          # value entities ≠ events
                continue

            # fetch the fully-saturated type of this event var
            event_sig = self._pred_sig.get(n.var_name)
            if not event_sig:
                # fallback to underscores if something went wrong
                lname = n.text.replace("-", "_")
                arity = len(self.struct_arg_order.get(lname, []))
                event_sig = f"{lname} " + " ".join("_" for _ in range(arity))

            # build the core proposition
            etype = ("NonVeridical"
                     if n.meta.get("nonveridical") else "Veridical")

            prop = f"{etype} ({event_sig}) {n.var_name}"

            # ---- apply polarity *after* binding arguments
            if n.meta.get("negated"):
                prop = f"¬ {prop}"
            
            # ---- existential wrap for each child argument
            for child, rel in n.children.items():
                if rel.lower().startswith(":arg") or rel == ":content":
                    if child.var_name.startswith('attr-') or (_is_mod(n.text) and not _is_noun_lemma(n.text)):
                        continue

                    prop = wrap_exist(child, prop)

            # ---- existentially bind the *event* var itself  ----
            # if you want every event axiom to be existential
            # >>> not sure if we want to quantify the event here.
            prop = f"∃ ({n.var_name} : {event_sig}), {prop}"
            self._prop_cache[n.var_name] = prop

            self.M.axioms.append(f"axiom {n.var_name}_evt : {prop}")

    def _emit_connectors(self, nodes):
        for n in nodes.values():
            if n.text not in CONNECTOR:
                continue
            opts = []
            for ch in _ordered_children(n):
                p = self._prop_cache.get(ch.var_name)
                if p:
                    opts.append(p)
            
            if not opts:
                continue
            opts_str  = "[" + ", ".join(opts) + "]"
            excl_flag = "true" if n.text=="or" else "false"
            self.M.instances.append(
                f"def {n.var_name} : Choice Prop :=\n"
                f"{{ options   := {opts_str},\n"
                f"  exclusive := {excl_flag} }}")

    # ------------------------------------------------------------------ #
    #  Phase 5 : non-core semantic edges (literal, preps, generic)
    # ------------------------------------------------------------------ #
    def _emit_noncore_axioms(self, nodes: Dict[str, AMRNode]):

        for parent in nodes.values():
            if self._is_attribute(parent):
                continue

            for child, rel in parent.children.items():

                # ================= 3. generic non-core edges ===============
                if rel in NON_CORE_EDGES:
                    mod_name = NON_CORE_EDGES[rel]      # e.g. "Medium", "ConsistOf", …
                    
                    # ================= 1. preposition lemmas ==================
                    prep = self.preps.get(child.text)

                    # special‐case: if this child is actually a numeric prep subgraph
                    #   (e.g. :duration (a/about :op1 t)) then we want to throw away
                    #   the preparatory node “a” and wrap the inner node “t” in the
                    #   prep’s stem (Approx) before attaching.
                    if prep and rel != ":name":
                    
                        # find op1 or arg1 under that prep‐node
                        inner = next((c for c,r in child.children.items()
                                      if r in {":op1", ":arg1"}), None)
                        if inner:
                            if inner.var_name in self._pred_sig:
                                pred_sig = self._pred_sig[inner.var_name]
                            else:
                                pred_sig = inner.text
                            wrapped = f"{prep.stem} {pred_sig} {inner.var_name}"
                        else:
                            wrapped = child.var_name
                        parent.meta.setdefault("mods", []).append(
                            f'Modifier.binaryRel "{mod_name}" {parent.var_name} ({wrapped})')
                        continue


                    # special-case :name  → Modifier.nameAdj "Lit"
                    if rel == ":name":
                        lit = self._name_literal(child) or child.var_name
                        parent.meta.setdefault("mods", []).append(
                            f'Modifier.nameAdj "{lit}"')
                        continue

                    if rel == ":mode":
                        lit = child.text
                        parent.meta.setdefault("mods", []).append(
                            f'Modifier.modeAdj "{lit}"')
                        continue

                    if self._is_attribute(child):
                        # child is an attribute leaf. we can do literal 
                        lit = child.text.strip('"')
                        parent.meta.setdefault("mods", []).append(
                            f'Modifier.literalAdj "{mod_name}" "{lit}"')
                        continue 

                    if self.ent.get(child.text) is not None:
                        parent.meta.setdefault("mods", []).append(
                                    f'(Modifier.entityAdj {child.var_name})')
                        continue

                    # default binary relation: e.g. Modifier.medium m p3
                    if _is_mod(child.text) and not _is_noun_lemma(child.text):
                        child_rep = f'"{child.text}"'
                    else:
                        child_rep = child.var_name
                    parent.meta.setdefault("mods", []).append(
                        f'Modifier.binaryRel "{mod_name}" {parent.var_name} {child_rep}')
                    continue
    
    # ------------------------------------------------------------------ #
    #  Phase 6 :  constraint axioms
    # ------------------------------------------------------------------ #
    def _emit_attributive_axioms(self, nodes):
        for n in nodes.values():
            k = n.meta.get("attributive")
            if k is None: continue
            head = n.meta["attr_head"]        # AMRNode of the noun being modified
            struct = n.text.replace("-", "_")
            const  = n.var_name
            field  = f"arg{k}"
            # equate occ.argk with head constant
            head.meta.setdefault("mods", []).append(
                f"(Modifier.eventAdj {const})")
            body   = f"{struct} _ _ _ {const} ∧ {const}.{field} = {head.var_name}"
            # optional ∃ for indefinite head
            if head.meta.get("definite") != "+":
                body = f"∃ ({head.var_name} : {head.text}), {body}"
            # self.M.noncore_axioms.append(f"axiom attr_{head.var_name}_{const} : {body}")

    # ------------------------------------------------------------------ #
    #  Phase 7 :  modifier predicate phase
    # ------------------------------------------------------------------ #
    def _emit_modifiers(self, nodes):
        for n in nodes.values():
            if (n.text in CONNECTOR
                    or self._is_attribute(n) 
                    or self._is_predicate(n)
                    or _is_noun_lemma(n.text) or self.preps.get(n.text) 
                    # or n.text in LITERAL_EDGES.values()
                    or self.ent.get(n.text)
                    or "mods" in n.meta):
                continue
            # declare predicate once
            pname = f"{n.text.capitalize()}"
            if pname not in MOD_CACHE:
                self.M.noncore_preds[pname] = \
                    f"def {pname} {{E : Type}} (e : E) : Prop := True"
                MOD_CACHE.add(pname)
            # attach to parent event/concept
            for parent, rel in n.parents.items():
                if rel in {":degree", ":manner-of", ":mod"}:
                    self.M.noncore_axioms.append(
                        f"axiom mod_{parent.var_name}_{n.var_name} : "
                        f"{pname} {parent.var_name}")

# ---------------------------------------------------------------------------
# Script entry‑point
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    
    # demo_amr = r"""
    # (c / close-10
    #    :ARG1 (i / i)
    #    :ARG2 (p / point
    #             :mod (b / break-01
    #                     :ARG1 i))
    #    :degree (v / very))
    # """
    t = AMR2LeanTranslator(propbank_root="/Users/jonzcai/Documents/ComputerScience/NLP/data/datasets/propbank-frames/frames/")
    # print(t.translate(demo_amr))


    # demo_amr3 = r"""
    # (d / drive-01
    #      :arg0 (p / person)
    #      :arg1 (c / car)
    #      :source (s / city :name (n / name :op1 "Denver"))
    #      :destination (l / city :name (n2 / name :op1 "Boulder")))
    # """

    # print(t.translate(demo_amr2))

    # demo_amr3 = r"""
    # (k / know-01~3
    #    :ARG0 (i / i~0)
    #    :ARG1 (o / or~7
    #             :op1 (t / thing~6
    #                     :ARG1-of (d / do-02~6
    #                                 :ARG0 i))
    #             :op2 (t2 / thing~8
    #                      :manner-of (h / help-01~10
    #                                    :ARG0 i
    #                                    :ARG1 (h2 / happy-01~13
    #                                              :ARG1 i
    #                                              :mod (a / again~14))
    #                                    :ARG2 i)))
    #    :degree (r / really~1)
    #    :polarity -~2)
    # """

    demo_amr3 = r"""
    (l / love-01~1
       :ARG0 (i / i~0)
       :ARG1 (g / girl~4
                :ARG1-of (s / same-01~3))
       :duration (a / about~6
                    :op1 (t / temporal-quantity~7,8
                            :quant 6~7,8
                            :unit (y / year~7,8))))
    """

    # demo_amr3 = r"""
    # (l / learn-01~1
    #    :ARG0 (y / you~1)
    #    :ARG1 (s / skill~4
    #             :ARG1-of (n / new-02~5)
    #             :ARG1-of (e / exemplify-01~3
    #                         :ARG0 (o / or~13
    #                                  :op1 (p / play-11~7
    #                                          :ARG2 (i / instrument~9))
    #                                  :op2 (d / draw-01~10)
    #                                  :op3 (t / try-01~11
    #                                          :ARG1 (s2 / sport~14
    #                                                    :ARG1-of (n2 / new-02~17
    #                                                                 :definite -)))
    #                                  :op4 (d2 / design-01~16
    #                                           :ARG1 (w / web~15))
    #                                  :op5 (e2 / et-cetera~10
    #                                           :definite -))
    #                         :content-of (p2 / possible-01~3))
    #             :definite -)
    #    :mode (i2 / imperative~1))
    # """

    # demo_amr3 = r"""
    # (a / and~10
    #    :op1 (f / find-01~0
    #            :ARG0 (y / you~3)
    #            :ARG1 (a2 / activity-06~2
    #                      :ARG1-of (l / like-01~4
    #                                  :ARG0 y)
    #                      :definite -)
    #            :mode (i / imperative~0))
    #    :op2 (s / set-02~5
    #            :ARG0 y
    #            :ARG1 (g / goal~7
    #                     :quant some)
    #            :mode (i2 / imperative~5))
    #    :op3 (s3 / stick-01~8,9
    #             :ARG0 y
    #             :ARG2 g
    #             :mode (i3 / imperative~8,9
    #                       :plural +)))
    # """

#     demo_amr3 = r'''
# (p / possible-01~0
#    :content (m / make-01~1
#                :ARG0 (y / you~1)
#                :ARG1 (p2 / playlist~4
#                          :ARG1-of (n / new-01~3)
#                          :consist-of (m2 / music~11
#                                          :ARG1-of (h / happy-01~10)
#                                          :example (a / and~12
#                                                      :op1 (m3 / music~17
#                                                               :ARG1-of (a2 / author-01~16
#                                                                            :ARG0 (o / organization~15
#                                                                                     :name (n3 / name~15
#                                                                                               :op1 "Fleetwood"~15
#                                                                                               :op2 "Mac"~15)))
#                                                               :name (n2 / name~17
#                                                                         :op1 "Don't"~17
#                                                                         :op2 "Stop"~17))
#                                                      :op2 (e / et-cetera~13)))
#                          :definite -)
#                :ARG2-of (s / start-01~8
#                            :ARG0 y
#                            :plural +)
#                :medium (p3 / product~6
#                            :name (n4 / name~6
#                                      :op1 "iTunes"~6))))
#     '''

    # demo_amr3 = r'''
    # (c / close-10~2,3
    #    :ARG1 (i / i~1)
    #    :ARG2 (p / point~5
    #             :mod (b / break-01~4
    #                     :ARG1 i))
    #    :degree (v / very~1))
    # '''
    demo_amr3 = r'''
    (s3a / and~1
         :op1 (s3k / keep-01~1
                   :ARG0 (s3i / i~15)
                   :ARG1 (s3i2 / it~2)
                   :duration (s3f / forever~5))
         :op2 (s3t / tell-01~7
                   :ARG0 s3i
                   :content s3i2
                   :ARG1-of (s3c / cause-01~14
                                 :ARG0 (s3p2 / possible-01~17
                                             :content (s3c2 / cope-01~18
                                                            :ARG0 s3i
                                                            :time (s3a2 / anymore~19))
                                             :mod (s3j / just~16)
                                             :polarity -~17)
                                 :plural +)
                   :ARG2 (s3p / person~9
                              :ARG0-of (s3h / have-rel-role-91~9
                                            :ARG1 s3i
                                            :ARG2 (s3f2 / friend~9)))
                   :time (s3b / before~13
                              :op1 (s3n / now~13)
                              :quant (s3f3 / few~11
                                           :op1 (s3t2 / temporal-quantity~12
                                                      :quant 1~12
                                                      :unit (s3m / month~12))
                                           :definite -))
                   :time (s3t3 / then~6)))
    '''
    leancode = t.translate(demo_amr3)
    new_leancode = reorder_choice_blocks(leancode)

    # print(new_leancode)