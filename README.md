# fixismu-coq
[![build](https://github.com/dominiquedevriese/fixismu-coq/actions/workflows/build.yml/badge.svg)](https://github.com/dominiquedevriese/fixismu-coq/actions/workflows/build.yml)

Coq proofs establishing semantic equi-expressiveness results for recursive types between [STLC] with
1. a fixpoint combinator
2. iso-recurisve types
3. equi-recursive types

See the paper [on arxiv][arxiv]

[arxiv]: https://arxiv.org/abs/2010.10859
[STLC]: https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

## Building the proof

1. Clone the repository
2. run `make` from the repo root

### Compatible Coq versions
- 8.14
- 8.15
- 8.16

This is checked using the [docker-coq] github action.

[docker-coq]: https://github.com/coq-community/docker-coq-action

### Assumptions

We depend on only two Axioms
* [`Coq.Logic.FunctionalExtensionality.functional_extensionality_dep`][functional_extensionality_dep]
* [`Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`][eq_rect_eq]

[functional_extensionality_dep]: https://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html#functional_extensionality_dep
[eq_rect_eq]: https://coq.inria.fr/library/Coq.Logic.Eqdep.html#Eq_rect_eq.eq_rect_eq

## Paper-to-artifact correspondence guide

Note that we indicate which compiler we are working with (or proving claims about) with abbreviations:
* *FI* indicates the compiler from *F*ix to *I*so
* *FE* indicates the compiler from *F*ix to *E*qui
* *IE* indicates the compiler from *I*so to *E*qui

| Definition / Theorem | Paper | File | Name of Formalization | Notation |
|---|---|---|---|---|
| Syntax of STLCs | Page 7, Figure ? | Stlc{Fix, Iso, Equi}/SpecSyntax.v | `Inductive Tm` |  |
| Syntax of Program contexts | Page 7, Figure ? | Stlc{Fix, Iso, Equi}/SpecSyntax.v | `Inductive PCtx` |  |
| Size of STLC terms | Page 7, Figure ? | Stlc{Fix, Iso, Equi}/Size.v | `Fixpoint size` |  |
| 2.2 STLC Static Semantics | Page 7-8, Figure ? | Stlc{Fix, Iso, Equi}/SpecTyping.v | `Inductive Typing` | `⟪  Γ `?`⊢ t : T  ⟫` where ? is either the empty string, i, or e for STLC `Fix`, `Iso`, or `Equi` respectively |
| 2.2 Program context static Semantics | Page 8-9, Figure ? | Stlc{Fix, Iso, Equi}/SpecTyping.v | `Inductive PCtxTyping` | `⟪ `?`⊢ C : Γ₀ , τ₀ → Γ , τ ⟫`, with ? as above
| 2.3 Dynamic Semantics primitive reductions | Page 10, Figure ? | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Inductive eval₀` | `t₁ -->₀ t₂` |
| 2.3 Dynamic Semantics non-primitive reductions | Page 10, Figure ? | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Inductive eval` | `t₁ --> t₂` |
| 2.4 Termination | Page 10, Definition 1 | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Definition Terminating` | `t ⇓` |
| 2.4 (Bounded termination) | Page 10, Figure ? | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Definition TerminatingN` | `t ⇓_ n` |
| 2.4 (Size-bounded termination) | Page 10, Figure ? | Stlc{Fix, Iso, Equi}/Size.v  | `Definition TermHor` |  |
| Relation between Termination and Size-Bound Termination | Page 11, Theorem 1 | Stlc{Fix, Iso, Equi}/Size.v | `Lemma evalHor_evaln` and `Lemma TermHor_TerminatingN` | |
| Observation relation | Page 11, Figure 2 | LogRel{FI, FE, IE}/LR.v | `Definition Obs` |  |
| Pseudo types | Page 12, Figure ? | LogRel{FI, FE, IE}/PseudoType.v | `Inductive PTy` | |
| Pseudo type conversions | Page 12, Figure ? | LogRel{FI, FE, IE}/PseudoType.v | `Fixpoint repEmul`, `Fixpoint fxToIs`, `Fixpoint isToEq`, `Definition OfType`, `Definition OfTypeStlcIso`, `Definition OfTypeStlcEqui` | |
| Value relation | Page 13, Figure 3 | LogRel{FI, FE, IE}/LR.v | `Definition valrel` |  |
| Term relation | Page 13, Figure 3 | LogRel{FI, FE, IE}/LR.v | `Definition termrel` | |
| Context relation | Page 13, Figure 3 | LogRel{FI, FE, IE}/LR.v | `Definition contrel` | |
| Substitution relation | Page 13, Figure 3 | LogRel{FI, FE, IE}/LR.v | `Definition envrel` | |
| Logical relation up to _n_ steps for FI | Page 14, Definition 2 | LogRel{FI, FE, IE}/LR.v | `Definition OpenLRN` | `⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ ⟫` (`d` is the direction of the relation—▽ in the paper) |
| Logical relations for FI, FE, and IE | Page 14, Definitions 3-5 | LogRel{FI, FE, IE}/LR.v | `Definition OpenLR` | `⟪ Γ ⊩ ts ⟦ d ⟧ tu : τ ⟫` |
| Logical relations for FI, FE, and IE program contexts | Page 15, Definitions 6-8 | LogRel{FI, FE, IE}/LR.v | `Definition OpenLRCtx` | `⟪ ⊩ Cs ⟦ d ⟧ Cu : Γ₀ , τ₀ → Γ , τ ⟫` |
| Adequacy for ≈ for FI | Page 15, Lemma 1 | LogRelFI/LemmasLR.v | `Lemma adequacy_lt` and `Lemma adequacy_gt` | |
| Contextual Equivalence | Page 16, Definition 9 | Stlc{Fix, Iso, Equi}/SpecEquivalent.v | `Definition PCtxEquivalent` | `⟪  Γ ⊢ t₁ ≃ t₂ : τ  ⟫` |
| Fully-abstract compilation | Page 16, Definition 10 | FullAbstraction{FI, FE, IE}.v | `Definition FullAbstraction` | |
| The type of backtranslated terms | Page 18, Figure 5 | UVal{FI, FE, IE}.v | `Fixpoint UVal`{`FI`, `FE`, `IE`} | |
| The upgrade function | Page 20, Figure 6 | BackTrans{FI, FE, IE}/UpgradeDowngrade.v | `Fixpoint upgrade` | |
| The downgrade function | Page 21, Figure 7 | BackTrans{FI, FE, IE}/UpgradeDowngrade.v | `Fixpoint downgrade` | |
| Compacted functions used to manipulate backtranslated values | Page 23, Figure 8 | BackTrans{FI, FE, IE}/UValHelpers.v | `Section Intro` and `Section Destruct` | |
| Missing bits of the logical relation | Page 23, Figure 9 | LogRel{FI, FE, IE}/LR.v | `Definition valrel` |  |
| Missing auxiliary functions of the logical relation | Page 24, Figure 10 | LogRel{FI, FE, IE}/PseudoType.v | `Fixpoint repEmul`, `Fixpoint fxToIs`, `Fixpoint isToEq`
| Compatibility lemma for λ | Page 25, Lemma 2 | Compiler{FI, FE, IE}/Compiler.v | `Lemma compat_lambda` | |
| Compilers are semantics preserving | Page 25, Lemmas 3-5 | Compiler{FI, FE, IE}/Compiler.v | `Lemma comp`{`fi`, `fe`, `ie`}`_correct`
| Definition of our compilers | Page 26, Figure 11 | Compiler{FI, FE, IE}/Compiler.v | `Fixpoint comp`{`fi`, `fe`, `ie`} | |
| Compilers are semantics preserving for contexts | Page 26, Lemmas 6-8 | Compiler{FI, FE, IE}/Compiler.v | `Lemma comp`{`fi`, `fe`, `ie`}`_ctx_correct` | |
| Compilers reflect equivalence | Page 27, Theorems 2-4 | Compiler{FI, FE, IE}/Compiler.v | `Lemma equivalenceReflection` | |
| Emulation of targets terms into source ones | Page 28, Figure 12 | Backtrans{FI, FE, IE}/Emulate.v | `Fixpoint emulate` | | 
| Emulation of targets contexts into source ones | Page 29, Figure 13 | Backtrans{FI, FE, IE}/Emulate.v | `Fixpoint emulate_pctx` | |
| Equivalent types are backtranslated to the same type | Page 29, Theorem 5 | UValIE/UVal.v | `Lemma UVal_eq` | |
| Compatibility for λ emulation | Page 30, Lemma 9 | Backtrans{FI, FE, IE}/Emulate.v | `Lemma compat_emul_abs` | |
| Compatibility lemma for emulation of type equality | Page 30, Lemma 10 | ? | ? | |
| Equivalent types have the same term relation | Page 30, Corollary 1 | ? | ? | |
| Emulate is semantics preserving | Page 30, Lemma 11 | Backtrans{FI, FE, IE}/Emulate.v | `Lemma emulate_works` | |
| Emulate is semantics preserving for contexts | Page 31, Lemma 12 | Backtrans{FI, FE, IE}/Emulate.v | `Lemma emulate_pctx_works` | |
| Inject and extract functions | Page 31, Figure 14 | Backtrans{FI, FE, IE}/InjectExtract.v | `Definition inject`, `Definition extract` | |
| Inject and extract are semantics preserving | Page 32, Lemma 13 | Backtrans{FI, FE, IE}/InjectExtract.v | `Lemma inject_works with extract_works` | |
| Approximate backtranslation for Iso contexts into Fix | Page 34, Definition 11 | FullAbstractionFI.v | `Definition backtranslateCtx` | |
| Correctness of backtranslation for Iso contexts into Fix | Page 35, Lemma 14 | FullAbstractionFI.v | `Lemma backtranslateCtx_works` | |
| Compilation preserves equivalence | Page 35-36, Theorems 6-8 | FullAbstraction{FI, FE, IE}.v | `Lemma equivalencePreservation` | |
| Compilation is fully abstract | Page 36, Theorems 9-11 | FullAbstraction{FI, FE, IE}.v | `Lemma FullAbstraction` | |
