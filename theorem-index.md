# Paper → Rocq proof index

This file lists the numbered results (definitions, lemmas, propositions,
theorems, corollaries) of the paper **"Definitional Inversion, Without
Normalisation"** and links each to the corresponding Rocq proof in
this repository, where one exists.

## Scope of the Rocq mechanisation

The paper is mechanised in Agda, Lean, and Rocq. 
The **Rocq** development covers the core system MLTT_U — the
universe with type-in-type (`U : U`) and dependent products (`Π`) — plus natural
numbers (`0` and `S`). It does **not** mechanise Σ/unit, `Y`, the identity type
`Id`, `Prop`, or full `ℕ` pattern-matching; those rows of the table are Agda
and/or Lean only.

Two structural notes on the Rocq proof that affect the mapping below:

1. **Everything is done on compact elements.** The paper develops an abstract
   domain-theory layer (Scott domains, ideals, CUSL, the equivalence
   `Dom◁ ≃ CUSL`, finitary projectors). As the paper says, this layer is *not
   strictly necessary* — there is an elementary form working directly with
   compact elements. The Rocq development takes exactly that elementary route:
   the domain of compact elements is a single inductive type
   [`elt`](src/finelt/findom.v#L36), so the abstract domain-theoretic results
   (Defs 2.2–2.7, 2.8–2.17, 2.23–2.30, Thms 2.12/2.24, Props 2.10/2.14–2.18/2.25–2.30)
   have **no separate Rocq counterpart** — they are subsumed by concrete
   operations (`le`, `lub`, `compatible`, `valid`) on `elt`.

2. **Fuel instead of stages.** Where the paper stratifies by a stage `n`
   (`C_n`), the Rocq proof uses a rank function `rk` and a *fuel* index, with
   fuel-independence ([`fuel_stable`](src/finelt/raw_validity.v#L2085)) playing
   the role of the paper's stage-independence (Cor 2.36).

Legend: ✅ mechanised in Rocq · ⬜ not mechanised in Rocq (abstract
domain-theory layer, or Agda/Lean-only extension).

---

## §2.1 Computing a fixed-point domain (domain-theory primer)

| # | Result | Rocq |
|---|--------|------|
| Def 2.1 | Compatibility (`↑`) | ✅ `compatible` — [findom.v:129](src/finelt/findom.v#L129), [findom.v:166](src/finelt/findom.v#L166); decision lemma [`compatibilityP`](src/finelt/findom.v#L1719) |
| Def 2.2 | Directed / bounded subsets | ⬜ abstract |
| Def 2.3 | Bounded complete partial order | ⬜ abstract |
| Def 2.4 | Directed complete partial order | ⬜ abstract |
| Def 2.5 | Compact elements | ✅ *implicit*: the whole type [`elt`](src/finelt/findom.v#L36) is the poset of compact elements |
| Def 2.6 | Basis of an element | ⬜ abstract |
| Def 2.7 | Scott domains | ⬜ abstract |
| Def 2.8 | Conditional upper semi-lattice (CUSL) | ⬜ abstract (well-formedness of a function graph is [`valid`/`valid_fun`](src/finelt/findom.v#L838)) |
| Def 2.9 | Ideals | ⬜ abstract (an ideal is realised as an [`EvalRel`](src/finelt/raw_semantics.v#L58) predicate) |
| Prop 2.10 | `ideals(P)` is a Scott domain iff `P` is a CUSL | ⬜ abstract |
| Def 2.11 | Embedding | ⬜ abstract |
| Thm 2.12 | `Dom◁ ≃ CUSL` equivalence of categories | ⬜ abstract |
| Def 2.13 | Step function | ⬜ abstract (a compact function is the finite graph `list (elt*elt)` under [`abs`](src/finelt/findom.v#L36)) |
| Prop 2.14 | Step functions form a CUSL | ⬜ abstract (validity condition [`valid_fun`](src/finelt/findom.v#L838)) |
| Prop 2.15 | `compacts([D,E]) ≅ compacts D ⇒ compacts E` | ⬜ abstract |
| Prop 2.16 | `ideals(D⇒E) ≅ [ideals D, ideals E]` | ⬜ abstract |
| Prop 2.17 | `−⇒−` is a functor | ⬜ abstract |
| Prop 2.18 | `C_n ⊆ C_{n+1}` is an embedding | ⬜ abstract (Rocq uses one `elt` with rank [`rk`](src/finelt/findom.v#L96), not a stratification) |

## §2.2 Semantic typing

The semantic typing judgement `u : a` of Fig. 2 is the inductive
[`wt`](src/finelt/types.v#L73).

| # | Result | Rocq |
|---|--------|------|
| Fig. 2 | Semantic typing rules `u : a` | ✅ [`wt`](src/finelt/types.v#L73) |
| — | `dom(f,a)` auxiliary | ✅ [`Selection`](src/finelt/selection.v#L34) |
| Prop 2.19 | Characterisation of function typing | ✅ [`Selection`](src/finelt/selection.v#L34) + [`wt_Selection`](src/finelt/selection.v#L73), [`wt_Selection_cod`](src/finelt/selection.v#L96), [`selectionBelow`](src/finelt/selection.v#L177), [`Selection_le_app`](src/finelt/selection.v#L210) |
| Prop 2.20 | Closure under compatible join | ✅ [`wt_lub`](src/finelt/types.v#L396) |
| Prop 2.21 | Typing preserved by `≤` | ✅ [`wt_le`](src/finelt/types.v#L387) |
| Prop 2.22 | Stability of semantic typing (across stages) | ⬜ no stages in Rocq — a single [`wt`](src/finelt/types.v#L73) on [`elt`](src/finelt/findom.v#L36) makes this vacuous |

## §2.3–2.4 Finitary projectors

The finitary-projector reformulation is the abstract domain-theory view of
semantic typing; the Rocq development works with `wt` directly and does not
build it.

## §2.5 The domain model

| # | Result | Rocq |
|---|--------|------|
| Fig. 3 | Syntax and typing of MLTT_U | ✅ [`Tm`](src/syntax/syntax.v), [`typing`](src/syntax/typing.v#L54) / [`conv`](src/syntax/typing.v#L98); head reduction [`HeadRed1`](src/syntax/reduction.v#L24) |
| Fig. 4 | Semantics of a term `⟦M⟧` | ✅ [`EvalRel`](src/finelt/raw_semantics.v#L58) (well-definedness: [`EvalRel_valid`](src/finelt/raw_semantics.v#L160), [`EvalRel_ideal`](src/finelt/raw_semantics.v#L841)) |
| Def 2.31 | Environments | ✅ [`Env`](src/finelt/raw_semantics.v#L44), [`bot_env`](src/finelt/eval_substitution.v#L316) |
| Lemma 2.32 | Stability under substitution of the semantics | ✅ [`EvalRel_subst`](src/finelt/eval_substitution.v#L140) |
| Def 2.33 | Environment fits a context | ✅ [`fits`](src/finelt/typing_semantics.v#L74) |
| Prop 2.34 | Soundness of the semantics | ✅ fundamental theorem [`adequacySub`](src/finelt/adequacy.v#L2461) / [`adequacyEqSub`](src/finelt/adequacy.v#L2463) (well-typed syntax ⇒ semantically typed) |

## §2.6 The logical relation

The four judgements `Γ ⊨ … type ∣_a` and `Γ ⊨ … : A ∣_{a:A}` are the mutually
recursive [`Val`](src/finelt/raw_validity.v#L275) / `EqVal` /
[`ValTy`](src/finelt/raw_validity.v#L180) / `EqValTy` (Notations at
[raw_validity.v:358](src/finelt/raw_validity.v#L358)).

| # | Result | Rocq |
|---|--------|------|
| — | Logical relation (the four `⊨` judgements) | ✅ [`Val`](src/finelt/raw_validity.v#L275), [`ValTy`](src/finelt/raw_validity.v#L180), `EqVal`, `EqValTy` |
| — | PER laws (`ValEqSymm`, `ValEqTrans`, …) | ✅ [`EqVal_sym`](src/finelt/raw_validity.v#L2511), [`EqVal_trans`](src/finelt/raw_validity.v#L2517), [`EqValTy_sym`](src/finelt/raw_validity.v#L2523), [`EqValTy_trans`](src/finelt/raw_validity.v#L2529); reflexivity [`Val_EqVal`](src/finelt/raw_validity.v#L523) |
| — | Monotonicity (`ValIncrType`, `ValDecrType`, …, `ValSup`) | ✅ [`upVal`/`downVal`/`restrictVal`](src/finelt/raw_validity.v#L1579), [`Val_transport`](src/finelt/raw_validity.v#L1624) |
| **Thm 2.35** | **Disjointness of type constructors** | ✅ [`tuniv_not_tpi`](src/finelt/adequacy.v#L2763) (paper's `Π ≢ U`); also [`tnat_not_tpi`](src/finelt/adequacy.v#L2744), [`tpi_not_tnat`](src/finelt/adequacy.v#L2755) |
| Cor 2.36 | Stability (independence of stage) | ✅ [`fuel_stable`](src/finelt/raw_validity.v#L2085) (fuel-independence above rank) |
| Lemma 2.37 | Head expansion | ✅ [`ValTy_HeadRed_expand`](src/finelt/raw_validity.v#L642), [`Val_beta_expand`](src/finelt/raw_validity.v#L854), [`EqVal_headred_expand`](src/finelt/raw_validity.v#L859) |
| **Lemma 2.38** | **The Fundamental Lemma** | ✅ [`adequacySub`](src/finelt/adequacy.v#L2461) / [`adequacyEqSub`](src/finelt/adequacy.v#L2463) (assembled from the per-rule `st_*`/`sc_*` lemmas) |
| **Cor 2.39** | **Injectivity of Π** | ✅ [`piInjectivity`](src/finelt/adequacy.v#L2653) (via [`piConv`](src/finelt/adequacy.v#L2590)) |
| **Thm 2.40** | **Subject reduction** | ✅ [`subject_red`](src/finelt/adequacy.v#L2730) (single step [`subject_red1`](src/finelt/adequacy.v#L2691)) |
| **Thm 2.41** | **Progress** | ✅ [`progress`](src/finelt/adequacy.v#L2843) (open version [`progress_gen`](src/finelt/adequacy.v#L2810), [`canonical_pi`](src/finelt/adequacy.v#L2796)) |

### Per-rule fundamental-theorem lemmas (§2.6, used to build Lemma 2.38)

Typing rules — [`st_var`](src/finelt/adequacy.v#L639),
[`st_conv`](src/finelt/adequacy.v#L654), [`st_app`](src/finelt/adequacy.v#L691),
[`st_tpi`](src/finelt/adequacy.v#L1395), [`st_abs`](src/finelt/adequacy.v#L1669),
[`st_univ`](src/finelt/adequacy.v#L1687).
Conversion rules — [`sc_conv`](src/finelt/adequacy.v#L1714),
[`sc_refl`](src/finelt/adequacy.v#L1737), [`sc_sym`](src/finelt/adequacy.v#L1764),
[`sc_trans`](src/finelt/adequacy.v#L1782), [`sc_app1`](src/finelt/adequacy.v#L1801),
[`sc_app2`](src/finelt/adequacy.v#L1896), [`sc_beta`](src/finelt/adequacy.v#L1991),
[`sc_eta`](src/finelt/adequacy.v#L2029), [`sc_tpi`](src/finelt/adequacy.v#L2271),
[`sc_abs`](src/finelt/adequacy.v#L2345).

## §3–§4 Extensions

Per the paper's mechanisation table, the Rocq development mechanises only the
**natural numbers** extension, and only for the `0`/`S` constructors (not full
pattern-matching); Σ/unit, `Y`, `Id`, and `Prop` are Agda/Lean only.

| Feature | Rocq |
|---------|------|
| Naturals `ℕ`, `0`, `S` (typing) | ✅ [`wt_tnat`/`wt_zero`/`wt_succ`](src/finelt/types.v#L73); adequacy [`st_nat`](src/finelt/adequacy.v#L914), [`st_zero`](src/finelt/adequacy.v#L938), [`st_succ`](src/finelt/adequacy.v#L965), [`sc_succ`](src/finelt/adequacy.v#L2173) |
| `nrec` computation rules (`0` / `S`) | ✅ [`sc_nrec_Z`](src/finelt/adequacy.v#L2148), [`sc_nrec_S`](src/finelt/adequacy.v#L2160), [`InvConv_nrec_Z`](src/finelt/typing_semantics.v#L1236), [`InvConv_nrec_S`](src/finelt/typing_semantics.v#L1245) |
| Full `ℕ` pattern-matching adequacy | ⬜ Agda/Lean only |
| Dependent sums `Σ`, unit `1` (+ η) | ⬜ Lean only |
| Fixed-point combinator `Y` | ⬜ Agda/Lean only |
| Identity type `Id` (with `J`) | ⬜ Agda/Lean only (Lean: `transport` only) |
| Universe of propositions `Prop` | ⬜ not mechanised |

---


