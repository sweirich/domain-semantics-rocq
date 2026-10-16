# Paper → Rocq proof index

This file lists the numbered results (definitions, lemmas, propositions,
theorems, corollaries) of the paper **"Definitional Inversion, Without
Normalisation"** and links each to the corresponding Rocq proof in
this repository, where one exists.

## Scope of the Rocq mechanisation

The paper is mechanised in Agda, Lean, and Rocq.
The **Rocq** development covers the core system MLTT_U — the
universe with type-in-type (`U : U`) and dependent products (`Π`) — together
with all of the extensions of §3–§4: natural numbers with dependent
pattern-matching (`ncase`), the fixed-point combinator `Y`, the identity type
`Id` with based `J`, dependent sums `Σ`, the unit type `1` with η, and the
universe of propositions `Prop`. The whole development is admit-free; the only
axioms are functional extensionality, propositional extensionality, proof
irrelevance and `eq_rect_eq` (`Print Assumptions progress` at the end of
[adequacy.v](src/finelt/adequacy.v)).

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
   fuel-independence ([`fuel_stable`](src/finelt/raw_validity.v#L4548)) playing
   the role of the paper's stage-independence (Cor 2.36).

Legend: ✅ mechanised in Rocq · ⬜ not mechanised in Rocq (abstract
domain-theory layer).

---

## §2.1 Computing a fixed-point domain (domain-theory primer)

| # | Result | Rocq |
|---|--------|------|
| Def 2.1 | Compatibility (`↑`) | ✅ [`compatible`](src/finelt/findom.v#L169), [`_compatible_fun`](src/finelt/findom.v#L160); decision lemma [`compatibilityP`](src/finelt/findom.v#L2017) |
| Def 2.2 | Directed / bounded subsets | ⬜ abstract |
| Def 2.3 | Bounded complete partial order | ⬜ abstract |
| Def 2.4 | Directed complete partial order | ⬜ abstract |
| Def 2.5 | Compact elements | ✅ *implicit*: the whole type [`elt`](src/finelt/findom.v#L36) is the poset of compact elements |
| Def 2.6 | Basis of an element | ⬜ abstract |
| Def 2.7 | Scott domains | ⬜ abstract |
| Def 2.8 | Conditional upper semi-lattice (CUSL) | ⬜ abstract (well-formedness of a function graph is [`valid`](src/finelt/findom.v#L992) / [`_valid_fun`](src/finelt/findom.v#L983)) |
| Def 2.9 | Ideals | ⬜ abstract (an ideal is realised as an [`EvalRel`](src/finelt/raw_semantics.v#L181) predicate) |
| Prop 2.10 | `ideals(P)` is a Scott domain iff `P` is a CUSL | ⬜ abstract |
| Def 2.11 | Embedding | ⬜ abstract |
| Thm 2.12 | `Dom◁ ≃ CUSL` equivalence of categories | ⬜ abstract |
| Def 2.13 | Step function | ⬜ abstract (a compact function is the finite graph `list (elt*elt)` under [`abs`](src/finelt/findom.v#L43)) |
| Prop 2.14 | Step functions form a CUSL | ⬜ abstract (validity condition [`_valid_fun`](src/finelt/findom.v#L983)) |
| Prop 2.15 | `compacts([D,E]) ≅ compacts D ⇒ compacts E` | ⬜ abstract |
| Prop 2.16 | `ideals(D⇒E) ≅ [ideals D, ideals E]` | ⬜ abstract |
| Prop 2.17 | `−⇒−` is a functor | ⬜ abstract |
| Prop 2.18 | `C_n ⊆ C_{n+1}` is an embedding | ⬜ abstract (Rocq uses one `elt` with rank [`rk`](src/finelt/findom.v#L106), not a stratification) |

## §2.2 Semantic typing

The semantic typing judgement `u : a` of Fig. 2 is the inductive
[`wt`](src/finelt/types.v#L73).

| # | Result | Rocq |
|---|--------|------|
| Fig. 2 | Semantic typing rules `u : a` | ✅ [`wt`](src/finelt/types.v#L73); minimal presentation [`mwt`](src/finelt/minimal_types.v#L159), equivalence [`mwt_iff_wt`](src/finelt/minimal_types.v#L430) |
| — | `dom(f,a)` auxiliary | ✅ [`Selection`](src/finelt/selection.v#L34) |
| Prop 2.19 | Characterisation of function typing | ✅ [`Selection`](src/finelt/selection.v#L34) + [`wt_Selection`](src/finelt/selection.v#L73), [`wt_Selection_cod`](src/finelt/selection.v#L96), [`selectionBelow`](src/finelt/selection.v#L177), [`Selection_le_app`](src/finelt/selection.v#L210) |
| Prop 2.20 | Closure under compatible join | ✅ [`wt_lub`](src/finelt/types.v#L821) |
| Prop 2.21 | Typing preserved by `≤` | ✅ [`wt_le`](src/finelt/types.v#L812) |
| Prop 2.22 | Stability of semantic typing (across stages) | ⬜ no stages in Rocq — a single [`wt`](src/finelt/types.v#L73) on [`elt`](src/finelt/findom.v#L36) makes this vacuous |

## §2.3–2.4 Finitary projectors

The finitary-projector reformulation is the abstract domain-theory view of
semantic typing; the Rocq development works with `wt` directly and does not
build it.

## §2.5 The domain model

| # | Result | Rocq |
|---|--------|------|
| Fig. 3 | Syntax and typing of MLTT_U | ✅ [`Tm`](src/syntax/syntax.v#L8), [`typing`](src/syntax/typing.v#L90) / [`conv`](src/syntax/typing.v#L210); head reduction [`HeadRed1`](src/syntax/reduction.v#L24); minimal (presupposition-free) presentation [`mtyping`](src/syntax/minimal_typing.v#L241), equivalence [`mtyping_iff`](src/syntax/minimal_typing.v#L670) / [`mconv_iff`](src/syntax/minimal_typing.v#L673) |
| Fig. 4 | Semantics of a term `⟦M⟧` | ✅ [`EvalRel`](src/finelt/raw_semantics.v#L181) (well-definedness: [`EvalRel_valid`](src/finelt/raw_semantics.v#L373), [`EvalRel_ideal`](src/finelt/raw_semantics.v#L1644)) |
| Def 2.31 | Environments | ✅ [`Env`](src/finelt/raw_semantics.v#L44), [`bot_env`](src/finelt/eval_substitution.v#L504) |
| Lemma 2.32 | Stability under substitution of the semantics | ✅ [`EvalRel_subst`](src/finelt/eval_substitution.v#L231) |
| Def 2.33 | Environment fits a context | ✅ [`fits`](src/finelt/typing_semantics.v#L74) |
| Prop 2.34 | Soundness of the semantics | ✅ fundamental theorem [`adequacySub`](src/finelt/adequacy.v#L8915) / [`adequacyEqSub`](src/finelt/adequacy.v#L8917) (well-typed syntax ⇒ semantically typed) |

## §2.6 The logical relation

The four judgements `Γ ⊨ … type ∣_a` and `Γ ⊨ … : A ∣_{a:A}` are the mutually
recursive [`Val`](src/finelt/raw_validity.v#L541) / `EqVal` /
[`ValTy`](src/finelt/raw_validity.v#L424) / `EqValTy` (Notations at
[raw_validity.v:684](src/finelt/raw_validity.v#L684)).

| # | Result | Rocq |
|---|--------|------|
| — | Logical relation (the four `⊨` judgements) | ✅ [`Val`](src/finelt/raw_validity.v#L541), [`ValTy`](src/finelt/raw_validity.v#L424), `EqVal`, `EqValTy` |
| — | PER laws (`ValEqSymm`, `ValEqTrans`, …) | ✅ [`EqVal_sym`](src/finelt/raw_validity.v#L5814), [`EqVal_trans`](src/finelt/raw_validity.v#L5820), [`EqValTy_sym`](src/finelt/raw_validity.v#L5826), [`EqValTy_trans`](src/finelt/raw_validity.v#L5832); reflexivity [`Val_EqVal`](src/finelt/raw_validity.v#L998) |
| — | Monotonicity (`ValIncrType`, `ValDecrType`, …, `ValSup`) | ✅ [`upVal`](src/finelt/raw_validity.v#L3691), [`downVal`](src/finelt/raw_validity.v#L3701), [`restrictVal`](src/finelt/raw_validity.v#L3711), [`Val_transport`](src/finelt/raw_validity.v#L3736) |
| **Thm 2.35** | **Disjointness of type constructors** | ✅ [`tuniv_not_tpi`](src/finelt/adequacy.v#L9185) (paper's `Π ≢ U`); also [`tnat_not_tpi`](src/finelt/adequacy.v#L9166), [`tpi_not_tnat`](src/finelt/adequacy.v#L9177), [`tuniv_not_tnat`](src/finelt/adequacy.v#L9739), and the pairwise disjointness of the extension formers ([`tuniv_not_tsig`](src/finelt/adequacy.v#L9267), [`tuniv_not_tid`](src/finelt/adequacy.v#L9415), [`tsig_not_tpi`](src/finelt/adequacy.v#L9806), [`tprop_not_tpi`](src/finelt/adequacy.v#L9841), [`tunit_not_tpi`](src/finelt/adequacy.v#L9883), …) |
| Cor 2.36 | Stability (independence of stage) | ✅ [`fuel_stable`](src/finelt/raw_validity.v#L4548) (fuel-independence above rank) |
| Lemma 2.37 | Head expansion | ✅ [`ValTy_HeadRed_expand`](src/finelt/raw_validity.v#L1388), [`Val_beta_expand`](src/finelt/raw_validity.v#L1833), [`EqVal_headred_expand`](src/finelt/raw_validity.v#L1838) |
| **Lemma 2.38** | **The Fundamental Lemma** | ✅ [`adequacySub`](src/finelt/adequacy.v#L8915) / [`adequacyEqSub`](src/finelt/adequacy.v#L8917) (assembled from the per-rule `st_*`/`sc_*` lemmas) |
| **Cor 2.39** | **Injectivity of Π** | ✅ [`piInjectivity`](src/finelt/adequacy.v#L9142) (via [`piConv`](src/finelt/adequacy.v#L9079)) |
| **Thm 2.40** | **Subject reduction** | ✅ [`subject_red`](src/finelt/adequacy.v#L9726) (single step [`subject_red1`](src/finelt/adequacy.v#L9618)) |
| **Thm 2.41** | **Progress** | ✅ [`progress`](src/finelt/adequacy.v#L10208) (open version [`progress_gen`](src/finelt/adequacy.v#L10116); canonical forms [`canonical_pi`](src/finelt/adequacy.v#L9962), [`canonical_nat`](src/finelt/adequacy.v#L9996), [`canonical_id`](src/finelt/adequacy.v#L10032), [`canonical_sigma`](src/finelt/adequacy.v#L10091)) |

### Per-rule fundamental-theorem lemmas (§2.6, used to build Lemma 2.38)

Typing rules — [`st_var`](src/finelt/adequacy.v#L959),
[`st_conv`](src/finelt/adequacy.v#L974), [`st_app`](src/finelt/adequacy.v#L1016),
[`st_tpi`](src/finelt/adequacy.v#L5718), [`st_abs`](src/finelt/adequacy.v#L6958),
[`st_univ`](src/finelt/adequacy.v#L6978).
Conversion rules — [`sc_conv`](src/finelt/adequacy.v#L7005),
[`sc_refl`](src/finelt/adequacy.v#L7031), [`sc_sym`](src/finelt/adequacy.v#L7058),
[`sc_trans`](src/finelt/adequacy.v#L7078), [`sc_app1`](src/finelt/adequacy.v#L7100),
[`sc_app2`](src/finelt/adequacy.v#L7195), [`sc_beta`](src/finelt/adequacy.v#L7290),
[`sc_eta`](src/finelt/adequacy.v#L7341), [`sc_tpi`](src/finelt/adequacy.v#L7576),
[`sc_abs`](src/finelt/adequacy.v#L8502).

## §3–§4 Extensions

All of the paper's extensions are mechanised in Rocq. Each adds term formers to
[`Tm`](src/syntax/syntax.v#L8), typing/conversion rules to
[`typing`](src/syntax/typing.v#L90) / [`conv`](src/syntax/typing.v#L210), finite
codes to [`elt`](src/finelt/findom.v#L36) and rules to
[`wt`](src/finelt/types.v#L73), a clause to
[`EvalRel`](src/finelt/raw_semantics.v#L181), and a case to the logical relation;
the per-rule soundness (`InvTyp_*`/`InvConv_*`) and adequacy (`st_*`/`sc_*`)
lemmas are then assembled into [`typing_EvalRel`](src/finelt/typing_semantics.v#L2898)
and [`adequacySub`](src/finelt/adequacy.v#L8915).

| Feature | Rocq |
|---------|------|
| Naturals `ℕ`, `0`, `S` | ✅ [`wt_tnat`](src/finelt/types.v#L81), [`wt_zero`](src/finelt/types.v#L84), [`wt_succ`](src/finelt/types.v#L87); adequacy [`st_nat`](src/finelt/adequacy.v#L1242), [`st_zero`](src/finelt/adequacy.v#L1266), [`st_succ`](src/finelt/adequacy.v#L1296), [`sc_succ`](src/finelt/adequacy.v#L7464) |
| Dependent `ℕ` pattern-matching (`ncase`) | ✅ rules [`t_case`](src/syntax/typing.v#L119), [`c_ncase_Z`](src/syntax/typing.v#L253), [`c_ncase_S`](src/syntax/typing.v#L259); soundness [`InvTyp_Case`](src/finelt/typing_semantics.v#L1588); adequacy [`st_case`](src/finelt/adequacy.v#L2280), [`sc_ncase_Z`](src/finelt/adequacy.v#L2304), [`sc_ncase_S`](src/finelt/adequacy.v#L2344), [`sc_ncase`](src/finelt/adequacy.v#L2827) |
| Fixed-point combinator `Y` | ✅ rules [`t_fix`](src/syntax/typing.v#L128), [`c_fix`](src/syntax/typing.v#L298), [`c_fix_cong`](src/syntax/typing.v#L302); Kleene approximants [`Approx`](src/finelt/raw_semantics.v#L64); soundness [`InvTyp_Y`](src/finelt/typing_semantics.v#L1710); adequacy [`st_fix`](src/finelt/adequacy.v#L3094), [`sc_fix`](src/finelt/adequacy.v#L3115), [`sc_fix_cong`](src/finelt/adequacy.v#L3318) |
| Identity type `Id` (with based `J`) | ✅ rules [`t_tid`](src/syntax/typing.v#L133), [`t_rfl`](src/syntax/typing.v#L138), [`t_jcase`](src/syntax/typing.v#L144), [`c_jcase_beta`](src/syntax/typing.v#L330); codes [`wt_tid`](src/finelt/types.v#L116), [`wt_rfl`](src/finelt/types.v#L126); soundness [`InvTyp_Id`](src/finelt/typing_semantics.v#L1737), [`InvTyp_Ref`](src/finelt/typing_semantics.v#L1854), [`InvTyp_J`](src/finelt/typing_semantics.v#L2027); adequacy [`st_tid`](src/finelt/adequacy.v#L3461), [`st_rfl`](src/finelt/adequacy.v#L3608), [`st_jcase`](src/finelt/adequacy.v#L4375), [`sc_jcase_beta`](src/finelt/adequacy.v#L4973), [`sc_jcase`](src/finelt/adequacy.v#L5025); **Id-injectivity** [`idInjectivity`](src/finelt/adequacy.v#L9342) (via [`idConv`](src/finelt/adequacy.v#L9294)) |
| Dependent sums `Σ` (+ surjective pairing) | ✅ rules [`t_tsig`](src/syntax/typing.v#L163), [`t_mkpair`](src/syntax/typing.v#L167), [`t_pfst`](src/syntax/typing.v#L173), [`t_psnd`](src/syntax/typing.v#L178), [`c_beta_fst`](src/syntax/typing.v#L374), [`c_beta_snd`](src/syntax/typing.v#L380), [`c_pair_eta`](src/syntax/typing.v#L386); codes [`wt_tsig`](src/finelt/types.v#L139), [`wt_mkpair`](src/finelt/types.v#L150); soundness [`InvTyp_Sigma`](src/finelt/typing_semantics.v#L2147), [`InvTyp_MkPair`](src/finelt/typing_semantics.v#L2283), [`InvConv_pair_eta`](src/finelt/typing_semantics.v#L2671); adequacy [`st_tsig`](src/finelt/adequacy.v#L6626), [`st_mkpair`](src/finelt/adequacy.v#L6073), [`st_pfst`](src/finelt/adequacy.v#L6263), [`st_psnd`](src/finelt/adequacy.v#L6608), [`sc_pair_eta`](src/finelt/adequacy.v#L8329); **Σ-injectivity** [`sigmaInjectivity`](src/finelt/adequacy.v#L9253) (via [`sigmaConv`](src/finelt/adequacy.v#L9206)) |
| Unit `1` (+ η) | ✅ rules [`t_unit`](src/syntax/typing.v#L203), [`t_star`](src/syntax/typing.v#L207), [`c_unit_eta`](src/syntax/typing.v#L444); code [`wt_tunit`](src/finelt/types.v#L184) with only `bot` as member ([`wt_unit_bot`](src/finelt/types.v#L966)); soundness [`InvConv_unit_eta`](src/finelt/typing_semantics.v#L2854); adequacy [`st_unit`](src/finelt/adequacy.v#L8853), [`st_star`](src/finelt/adequacy.v#L8877), [`sc_unit_eta`](src/finelt/adequacy.v#L8891) |
| Universe of propositions `Prop` (proof irrelevance) | ✅ rules [`t_prop`](src/syntax/typing.v#L185), [`t_prop_u`](src/syntax/typing.v#L192), [`t_tpi_prop`](src/syntax/typing.v#L196), [`c_prop`](src/syntax/typing.v#L420); codes [`wt_tprop`](src/finelt/types.v#L165), [`wt_tpi_prop`](src/finelt/types.v#L172), [`wt_prop_bot`](src/finelt/types.v#L969), [`wt_prop_univ`](src/finelt/types.v#L957); soundness [`InvConv_prop_irrel`](src/finelt/typing_semantics.v#L2818), [`InvConv_prop_u`](src/finelt/typing_semantics.v#L2779); adequacy [`st_prop`](src/finelt/adequacy.v#L8642), [`st_prop_u`](src/finelt/adequacy.v#L8666), [`st_tpi_prop`](src/finelt/adequacy.v#L8751), [`sc_prop`](src/finelt/adequacy.v#L8786) |

---
