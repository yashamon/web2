# stablelean — a Lean 4 formalization of *Incompleteness theorems via stable computability*

The manuscript: [turingcategory.pdf](https://yashamon.github.io/web2/papers/turingcategory.pdf).
Section, theorem and definition numbers below refer to its latest version of 21 November 2026, in which the second incompleteness theorem is Theorem 1.1, except in the dated items of "Remarks on the manuscript"; labels (`lemma_closure`, …) are given where a number may drift.  The numbers which changed with respect to the version of 10 November 2026 are listed in "The restructured manuscript" below.  With respect to the version of 15 November 2026 there is one new number, Corollary A.3.

Release 0.4.9 (21 November 2026).  Hosted at <https://yashamon.github.io/web2/papers/turingcategory/>:
this [README](README.md), the archive [stablelean-0.4.9.zip](stablelean-0.4.9.zip), and the files of
the archive, unpacked, under `stablelean/`.  To check everything, see "Building and checking".

**Status.** Sections 2–6 are formalized: the category of encoded sets and its computability axioms
(Section 2.1), first order theories and translations (2.2), stability, decision maps and the
stabilizer lemma (3), the stable halting problem (4), the first incompleteness theorem (5) with the
second incompleteness theorem in its abstract form (5.1), and the whole `Σ⁰ₙ₊₁` generalization (6)
including `Dec^n`, `C^n`, `Spec^n`, the level-`n` stable halting theorem, Theorems 6.8 and 6.9, and Theorem 1.1 at level `n`.
Theorem 1.1, the second incompleteness theorem for a `Σ⁰₂`-definable theory, is
`second_incompleteness_sigma`; it is deduced from its form for a theory presented by a machine,
Theorem 5.11.
Theorem A.2 (Penrose), that `{b ∈ 𝓑₂ | 𝓗 ∪ {ε} ⊢ b*}` is not `1`-consistent, is formalized in
the same abstract form as the second incompleteness theorem, see "Second incompleteness".
Corollary A.3 uses truth in a universe of set theory, and is not formalized.

**Appendix B is now a note.**  In the manuscript of 12 November 2026 the former Appendix B is
replaced by Remark 5.25, which states its two propositions and refers here for the proofs.  The
written proofs are in [doc/undefinable.pdf](stablelean/doc/undefinable.pdf) (source
`doc/undefinable.tex`).  The note keeps the numbering of the appendix.  So "Appendix B",
"Definition B.1", …, "Proposition B.10" in this file and in the sources refer to the note.

Proposition B.7 (a
`2`-translation `𝓐 → 𝓐` inducing a non-arithmetical theory from `PA`) is proved relative to the
interface `UndefData` described below.  Proposition B.10 (if `ZFC` is arithmetically sound, a
`2`-translation `i : 𝓩 → 𝓩` with `ZFC ⊢ⁱ ZFC` inducing a non-arithmetical theory of arithmetic from `ZFC`:
an undefinable instance of the hypotheses of Theorem 5.11) is proved relative to the interface
`UndefZData`, also described below.  Every headline
statement is checked by `Audit.lean` to depend only on `propext`, `Classical.choice`, `Quot.sound`;
there are no `sorry`s and no `axiom` declarations.  The development is relative to two interfaces:

* `TuringModel` (Proposition 2.4, parts (1)–(4) and (6), the computability axioms) — **discharged**:
  the package `model/` builds a concrete instance `StableModel.mathlibModel` from Mathlib's
  `Nat.Partrec.Code`, with the same three Lean axioms.  So the computability claims derived from it
  are theorems about the standard model of partial recursive functions.  Part (5) of
  Proposition 2.4 is the interface `Language`, on which `Arith` is built; its fields are assumed.
* `Arith` (the classical facts about first order arithmetic used by the paper: the `Σ⁰ₙ/Π⁰ₙ`
  hierarchy and its instance maps, decidability of `Δ₀` truth, `Q` deciding `Δ₀` sentences, and the
  representability of computable relations by arithmetic sentences, Lemma 4.2) — **assumed**, exactly
  as the paper assumes them (citing Tarski–Mostowski–Robinson and Hájek–Pudlák).  The full list is in
  "Trusted base" below.

The steps of the paper that are *not* theorems about these interfaces are its assertions of
provability in `ZFC`, first of all equation (5.12), the formalization *inside* `ZFC` of
Proposition 5.5 (3).  Equation (5.12) and the equivalence of Lemma 5.16 enter the second
incompleteness theorems as explicit hypotheses (see "Second incompleteness").

**Exceptions**, in the terms of the footnote of the manuscript's Introduction.  The standard facts
taken as axioms are the fields of the structures `Language`, `Arith`, `UndefData` and `UndefZData`,
listed in "Trusted base", and the computability of the sets `𝓑ₙ` (point 1 of "The restructured
manuscript").  The standard interpretation `i_{𝓐,𝓩}` of Example 2.8 is an arbitrary translation
`iAZ`: that it is a translation is not proved here.  The assertions of provability in `ZFC` taken as
hypotheses are listed in "Second incompleteness".  Accordingly the sentences `Con₁` and `Sndₙ`
(Lemma 5.9, Definition 5.10, and their forms at level `n`) are not constructed: the second
incompleteness theorems are proved for an arbitrary sentence in their place, subject to these
hypotheses.  The remarks and examples which are not formalized: Remark 2.5 (`𝒮` is a Turing
category); Remark 2.7 (interpretations and guards); Example 3.2, Remark 3.3 and Example 3.19 (the
halting and Diophantine examples); the comparison with experimental logics after Corollary 3.7; the
notes on re-indexing and dovetailing in Remark 3.18; Remarks 5.14, 5.22 and 5.24; the first
paragraph of Remark 5.25; and Corollary A.3.  Remarks 5.15 and 6.10 state an
expectation and facts from the literature.  Of Proposition 2.4, the computability of `Halt` in
part (2), used only in Example 3.2, and part (4)(c) are not formalized.  The last claim of
Theorem 1.5, that `𝒢` and a machine computing it are given explicitly, is not formalized:
`first_incompleteness_arith` is an existence statement, and `G₀` is defined through
`Classical.choose`.  The other assertions of provability in `ZFC` (the paragraph "Fixed choices",
Lemma 4.2, and their forms in Section 6.3) are not hypotheses of a theorem here, and have no
counterpart.  Beyond these, every statement depends only on the three axioms of Lean named above.

## The restructured manuscript (11 November 2026)

In the manuscript of 11 November 2026 the theorems are stated for stably c.e. theories of
arithmetic, with no translation, and other languages enter through *readings* (Section 5.2).
Earlier versions stated the theorems relative to a translation.  Everything new is formalized, in
five modules.

| Paper | Lean |
|---|---|
| Definition 2.9 (`1`-, `2`-consistency) and Definition 6.5 (`Σₙ`-soundness) of a theory of arithmetic | `Arith.OneConsistent`, `Arith.TwoConsistent`, `Arith.SigmaSound` (`Stable/Plain.lean`) |
| Definition B.6 (the same relative to a translation) | `Translation.OneConsistent`, …; `Translation.oneConsistent_iff_induced` etc. hold by `Iff.rfl` |
| `𝓑₂`, `𝓑ₙ₊₁` | `Arith.BoolComb 2`, `Arith.BoolComb (m + 2)` (`∨` omitted, as everywhere) |
| Theorem 1.5, Proposition 5.5 | `first_incompleteness_arith`; `G₀`, `Arith.not_deriv_G₀`, `Arith.not_deriv_neg_G₀`, `Arith.trueN_G₀` |
| Lemma 6.6 (1), (2) | `Arith.oneConsistent_iff_sigmaSound`, `Arith.twoConsistent_iff_sigmaSound`, `Arith.SigmaSound.mono` |
| Theorem 5.11, Corollary 5.13 | `second_incompleteness_H`, `second_incompleteness_H_corollary` |
| The simplest case of Theorem 5.11 | `second_incompleteness_simple` |
| Theorem 1.1 | `second_incompleteness_sigma`, for every machine presenting `F`; `exists_machine_of_isSigma2Set` gives such a machine, by Corollary 3.7 (`Stable/Plain.lean`) |
| Lemma 5.16 | a machine presenting `F` is given by `exists_machine_of_isSigma2Set`; the machine `T_σ` is not constructed from a formula `σ`, and the equivalence `Con₁ (σ)* ↔ Con₁ (T_σ)*` in `ZFC` is a hypothesis of Theorem 1.1, see "Second incompleteness" |
| Corollary 5.17 | `second_incompleteness_sigma_simple` |
| Definition 5.18 | `Asserted` (= `F₀^R`), `IsReadingOn`, `IsTwoReading` (`Stable/Readings.lean`) |
| Lemma 5.19 | `RSh`, `compSet_RSh`, `SR_RSh_iff`, `exists_shadow`, `Shadow`, `Shadow_Ts`; `shadow_two` |
| Corollary 5.20 | `reading_first`; `corollary_readingfirst` |
| Corollary 5.21 | `reading_second`, `reading_second_corollary`; `corollary_readingsecond` |
| Example 5.23 | `isReadingOn_translation`, `asserted_graph_eq_induced`, `first_incompleteness_via_readings`, `second_incompleteness_via_readings` (`Stable/ReadingsTranslations.lean`) |
| Theorem 6.8 | `n_first_incompleteness_arith`; `NG₀`, `Arith.not_deriv_NG₀`, … (`Stable/NPlain.lean`) |
| Theorem 6.9 and its simplest case | `n_second_incompleteness_H`, `n_second_incompleteness_H_corollary`, `n_second_incompleteness_simple` |
| Theorem 1.1 and Corollary 5.17 at level `n` (Section 6.3) | `n_second_incompleteness_sigma`, `n_second_incompleteness_sigma_simple`, for every machine presenting `F`; `exists_nmachine_of_isSigmaNSet` gives such a machine, by Corollary 6.3 (`Stable/NPlain.lean`) |
| Section 6.3, readings at level `n` | `NSR_and_absorb`, `IsNReadingOn`, `IsNReading`, `exists_nShadow`, `NShadow`, `NShadow_NTs`, `n_corollary_readingfirst`, `n_corollary_readingsecond` (`Stable/NReadings.lean`); `n_reading_first`, `n_reading_second` (`Stable/NPlain.lean`) |
| Theorem A.2 | `penrose_family`, deduced from Corollary 5.21 as in the manuscript; for a family with one member, with the sentence `ε → Con₁ (δ + ε)` in axiom (3): `penrose_two_way_delta`; with `Con₁ (Sh_R (T₀))*` in place of `Con₁ (δ + ε)`: `penrose_two_way`; `Tplus` = the machine `Sh_R (T₀)` of the proof, `Tplus_Ts`, `Tplus_Ts_closed`, `isReadingOn_graph`; the deduction from Theorem 5.11: `penrose_conditional` (`Stable/Penrose.lean`) |
| Corollary A.3 | not formalized: it uses truth in the universe `𝒰` of Appendix A |
| Remark A.3 of the versions up to 12 November (now removed), last paragraph | Corollary 5.13 for `H = 𝓗`: `second_incompleteness_H_corollary`; for a reading: `penrose_reading` |

Four points.

1. **`𝓑ₙ` is computable: a hypothesis.**  The paper uses that `𝓑₂` (resp. `𝓑ₙ₊₁`) is a computable
   subset of `𝓐`.  The interface `Arith` has no syntax from which to prove this.  So Lemma 5.19 and
   Corollaries 5.20, 5.21 are proved for any computable `P ⊇ 𝓑ₙ`, with `R ∩ (P × 𝓛)` a `Σ⁰ₙ` set.
   The paper's statements are the case `P = 𝓑ₙ`, under the explicit hypothesis
   `CompSet M (A.BoolComb n)` (`shadow_two`, `corollary_readingfirst`, `corollary_readingsecond`
   and their level-`n` forms).
2. **Equation (5.12) is still a hypothesis** (`hcon`, `hsnd`), stated for an arbitrary sentence
   `con ∈ 𝓩`, exactly as in `Stable/Second.lean`.  The standard interpretation `i_{𝓐,𝓩}` enters as an
   arbitrary `Translation A.toLanguage Z`.
3. **The simplest case has a direct proof.**  If `F ⊢ Con₁ (T)`, then by (5.12) `ZFC` proves the
   translation of `c := ¬(Con₁ (T) ∧ ¬𝒢 (T))`, so `F ⊢ c` and hence `F ⊢ 𝒢 (T)`.  The hypothesis
   "`F ⊢ a` whenever `ZFC ⊢ a*`" is used for this one sentence.  The manuscript deduces the case
   from Theorem 5.11 through the theory `H`; both proofs are valid.
4. **The earlier modules keep the form for translations.**  `Stable/Incompleteness.lean`,
   `Stable/Second.lean` and `Stable/NIncompleteness.lean` state the theorems relative to a
   translation `i`.  In the present manuscript that form is Example 5.23, read with the notation of
   Appendix B.  The new statements are their case `𝓛 = 𝓐`, `i = id` (`Translation.id`).
   Not formalized: Remark 5.24.

Numbers which changed (manuscript of 10 November 2026 → 11 November 2026): Definitions 2.9,
2.10, 2.12 and Lemmas 2.11, 2.13 → B.1, B.2, B.4, B.3, B.5; Definition 2.14 → 2.9, with its form
relative to a translation now Definition B.6; Proposition B.1 → B.7; (B.2) → (B.8); Remark B.3 →
B.9; Proposition B.4 → B.10.  New: Definition 5.14, Lemma 5.15, Corollaries 5.16, 5.17,
Example 5.18, Remark 5.19.

Numbers which changed on 12 November 2026 (manuscript of 11 November → the latest of 12 November):
Definition 1.1, Remark 1.2, Definition 1.3 → 1.2, 1.3, 1.4; Theorem 1.4 → 5.11; Corollary 1.5 →
5.13; Theorem 1.6 → 1.5; equation (5.11) → (5.12); Remarks 5.12, 5.13 → 5.14, 5.15; Definition
5.14 → 5.18; Lemma 5.15 → 5.19; Corollaries 5.16, 5.17 → 5.20, 5.21; Example 5.18 → 5.23; Remark
5.19 → 5.24.  New: Theorem 1.1, Lemma 5.16, Corollary 5.17 (not the earlier Corollary 5.17),
Remark 5.22, and Remark 5.25, which is the Remark 5.20 of item 16 below.  Appendix B became a note,
see above.  Remark A.3 was removed.

## Building and checking

Lean 4.35.0 (pinned by `lean-toolchain`), no dependencies: core Lean only, no Mathlib, no Batteries.
Five commands, the first of which installs Lean's version manager `elan`:

```
curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
curl -LO https://yashamon.github.io/web2/papers/turingcategory/stablelean-0.4.9.zip
unzip stablelean-0.4.9.zip && cd stablelean
lake build                 # the whole library, kernel-checked (about a minute)
lake env lean Audit.lean   # the axioms of the 65 headline statements
```

On Windows, `tar -xf stablelean-0.4.9.zip` unpacks the archive.  The build prints no warning.  The
audit prints 65 lines, one for each headline statement, all of the form

```
'Stable.stable_halting' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So no headline statement depends on `sorryAx` (an incomplete proof), on an `axiom` declared by this
project (there is none), or on `Lean.ofReduceBool` (trust in the compiler).  The workflow
`.github/workflows/ci.yml`, for a git hosting of the same files, runs the build and counts the 65
lines.

`model/` is a separate Lake project depending on Mathlib (`v4.35.0`) and on this library (path `..`).
Its build prints the axioms of `StableModel.mathlibModel`:

```
cd model && lake exe cache get && lake build
```

## Module map (print ↔ Lean)

| File | Content |
|---|---|
| `Stable/Comp.lean` | `TuringModel`: machines `Code`, step semantics `run`, `eval`, `code = e_𝒯`, the pairing `⟨·,·⟩`, and the computability axioms (basic functions; closure under composition, pairing, cases on a total decidable predicate, primitive recursion, unbounded search; `Halt'` decidable; universal `U`; s-m-n). `IsComp`, `IsCompSet`, `IsCompT` and their algebra. |
| `Stable/Prim.lean` | ℕ-level helpers: predecessor, iteration, bounded `∀`, primitive recursion as total functions. |
| `Stable/Enc.lean` | Section 2.1. `Enc` (encoding `e_A`, injective, computable image; Definition 2.1), `Comp`/`CompT`/`CompSet` (Definition 2.3), `Computes`. Encodings of `ℕ`, `{±} = Bool` (`- ↦ 0`, `+ ↦ 1`), `𝒯`, `Unit`, products (Prop. 2.4 (1), `e (a,b) = ⟨e a, e b⟩`), `Option`, lists (Prop. 2.4 (4): `compT_length`, `comp_nth`), induced encodings `Enc.restrict`. Closure lemmas incl. cases (2.4 (6)), bounded quantifiers, bounded search `bmin`, unbounded search `mu` (2.4 (6)), `compSet_halt'`, `comp_univ` (2.4 (2)), `smn` (2.4 (3)), `e_A⁻¹` computable (Lemma 3.11 `comp_decode`), `ε_A` and its inverse (`epsilon`, `epsilonInv`), `CompSet.exists_decode`, `CompSet.exists_eq_some`, `Comp.ofRestrict`. |
| `Stable/Stab.lean` | Section 3.1–3.2. `IsStable`/`Stab` (Def. 1.2, 3.1), `IsDecided`/`Decided` (Def. 3.4), `StablyEquiv` (Def. 3.20), `decOfSeq` = `D_M`, `seqOfDec` = `M_D` with `ι (b,t) = ⟨ε_B b, t⟩` (Remark 3.5; `isDecided_decOfSeq_iff`, `isStable_seqOfDec_iff`, computability, totality), `cT` = `c_t`, `DR` = `D_R`, **Lemma 3.6** (`isDecided_DR_iff`, `compT_DR`). |
| `Stable/Machines.lean` | Section 3.2, 4. `seqOf` = `T'` for `𝒯_B` (Def. 3.9; defined for every `T` as `e⁻¹ ∘ T`), `InTB` = `T ∈ 𝒯_B`, `decOf`/`InDB` for `𝒟_B` (Def. 3.8), `Ts` = `T^s` (Notation 3.21), `TStable`, `TDecided` (Def. 3.10), `StablyComputes` (Def. 1.4/3.1), `StablyComputesDec`, `Theta` = `Θ_{D,T}`. `exists_K` (Lemma 3.13), `exists_Omega` (Lemma 4.1), the uniform machines `exists_decMachine`, `exists_stabMachine` (stabilizer lemma + s-m-n), `RB` = `R_B`, `compSet_RB`, `tStable_iff_SR_RB`, **`exists_Dec`** = `Dec_B` with Lemmas 3.15, 3.16, and **Remark 3.18** `exists_total_uniform` (the last statement of Corollary 3.7, uniformly in `T`). |
| `Stable/Logic.lean` | Section 2.2. `Language` (sentences, encoding, `Deriv` = `⊢`, `neg`, `and`, `Prf` (Prop. 2.4 (5)), structural and propositional rules, compactness, `𝓛` infinite), `closure`, `Closed`, `Consistent`; `Translation` (Def. 2.6; `∨` omitted: here it is a defined connective), `induced` = `F_{i,𝓛'}` (Def. B.2), `DerivI` = `⊢ⁱ` (Def. B.4), **Lemma B.5** `derivI_iff`, Lemma B.3 `induced_closed`. |
| `Stable/Arith.lean` | `Arith` (interface for `𝓐`, see below), `TrPi n` = `Tr_{Πₙ}`, `Q_sigma1`, `Translation.OneConsistent`/`TwoConsistent`/`SigmaSound` (Def. B.6, relative to a translation; the forms of Def. 2.9 and 6.5 for theories of arithmetic are in `Stable/Plain.lean`), `Speculative` (Def. 3.24, relative to a translation), `IsNTranslation` (Def. B.1), `repr` (Lemma 4.2 form) derived from `reprN`. |
| `Stable/Closure.lean` | `RC` = `R_C`, `compSet_RC`, `SR_RC_iff`, **Lemma 3.22** `exists_C`. |
| `Stable/SpecRel.lean`, `Stable/Spec.lean` | `RS` = `R_S` in the form for a translation `i` (for `c = 1` it also asks `w = e_𝓐 (π)` and `x = i (π)`; the print has no condition on `w`, and `S_{R_S}` is the same), `compSet_RS`, `SR_RS_iff`; `conjPi`, `specExtN`/`specExt` = `F ∪ i(Tr_{Πₙ})`, **Lemma 3.26** (`exists_trPiN_derivI_neg_of_not_consistent`, all levels), `consistent_specExt`, **Theorem 3.25** `exists_Spec` (parts 1–4). |
| `Stable/Halting.lean` | Section 4. `Omega` = `Ω`, `W`, `compSet_W`, `tDecided_Omega_iff`, `Arith.sigmaT` = `σ` (Lemma 4.2 via `repr`), `Arith.sT` = `s` (Def. 4.3), `StablySound`, `StablyDecides`, `StablySoundComplete` (Def. 4.4), **Lemma 4.5** `not_theta_or_not_decided`, **Theorem 4.6** `stable_halting`. |
| `Stable/Incompleteness.lean` | Section 5. `DecL`, `CL`, `SpecI`, `compT_i_sT`, `H` = `Λ`, `comp_H` (5.1), `Tur` (5.2), `G` = `𝒢` (5.4), `Mt` = `M̃`, `stab_Mt_iff`, `Mt_speculative`, `consistent_Mt`, `isStable_Mt_G_iff` ((5.6)–(5.7)), **Proposition 5.5** (`trueN_G`, `not_derivI_G`, `not_derivI_neg_G`), **Theorem 1.5** `first_incompleteness`. |
| `Stable/Second.lean` | Section 5.1. `Translation.comp`, **Theorem 5.11** `second_incompleteness`, **Corollary 5.13** `second_incompleteness_corollary`, `penrose` (Theorem A.2 in the form of the versions before 11 November 2026) — all with the `ZFC`-provability hypotheses explicit (see below). |
| `Stable/Sigma2.lean` | **Corollary 3.7**: `StablyCE`, `DecidedByTotal`, `IsSigma2Set`, `stablyCE_iff_isSigma2Set`, `stablyCE_iff_decidedByTotal`, `exists_total_of_stablyCE`. |
| `Stable/SoundCons.lean` | **Lemma 6.6**: `oneConsistent_iff_sigmaSound`, `twoConsistent_iff_sigmaSound` (1), `SigmaSound.mono` (2), `consistent_specExtN_of_sigmaSound` (3). |
| `Stable/NStab.lean` | Section 6.1 with `m = n - 1`. `NB B m = B × ℕ^m` (nested, `NB B (m+1) = NB (B × ℕ) m`), `nbBase`, `nbMapBase`; `NDec m` = `(m+1)`-decided, `nslice`, `NStable m` = `(m+1)`-stable (Def. 6.1); `NRel`, `compl`, `complPow`, `NSR m` = `S_R` with `m+2` alternating quantifiers; `NRelComp`; `NDec_iff_NSR`, `NSR_nbMapBase`, `NSR_ite`, `NSR_congr`, `NDec_assoc`/`NDec_nbMapBase`; **Lemma 6.2** `n_stabilizer`; `DM` = `D_M`, `MD` = `M_D` with `NDec_DM_iff`, `NStable_MD_iff` (the recursions of the proof of Corollary 6.3). |
| `Stable/NList.lean` | Closure of `Σ⁰_{m+2}` conditions (uniformly in a parameter) under precomposition, cases, conjunction with a decidable predicate, an existential over an encoded set, disjunction, bounded `∃` and bounded `∀` over the entries of a list (Section 6.2; **Lemma 6.4**, absorption, is `NSR_forall_nth_absorb`): `NSR_comp_base`, `NSR_and_dec`, `NSR_exists_absorb`, `NSR_or_absorb`, `NSR_exists_nth_absorb`, `NSR_forall_nth_absorb`, … |
| `Stable/NTruth.lean` | `trSigma k`: `Σ⁰_{k+2}`-truth (and hence `Π⁰_{k+1}`-truth) as an `NSR k` condition with computable matrix (`NSR_trSigma`, `exists_trPi`) — the condition `π ∈ Tr_{Πₙ}` of Section 6.2, built from `instS`/`instP` and used for `Spec^n`; the arithmetic `Σ⁰ₙ` truth definition of Section 6.3 enters `Soundₙ` and is not constructed. |
| `Stable/NMachines.lean` | `nseqOf` = `T'` for `𝒯^{m+1}_B`, `NTs` = `T^{s_{m+1}}`, `RBase`, `NTs_iff_NSR` (the `Σ⁰_{m+2}` form of `(m+1)`-stability), `exists_nDecMachine`, `exists_nStabMachine`, **`Dec^{m+1}`** `exists_nDec`, `deriv_iff_exists_prf`, **`C^{m+1}`** `exists_nC`. |
| `Stable/NSpec.lean` | `NSpeculative`, `compSet_isPi_eq`, **`Spec^{m+1}`** `exists_nSpec` (Theorem 3.25 at level `m+1`, part 4 via Lemma 6.6 (3)). |
| `Stable/NHalting.lean` | `NOmega` = `Ω^{m+1}`, `NTheta`, `RW`, `RWdiag`, `Arith.nsigmaT` = `σ_{m+1}`, `Arith.nsT` = `s_{m+1}`, `NStablySound`, `NStablyComplete`, **Theorem 6.7** `n_stable_halting`. |
| `Stable/NIncompleteness.lean` | `NDecL`, `NCL`, `NSpecI`, `NH`, `NTur` = `Tur_{m+1}`, `NG` = `𝒢_{m+1}`, `NTs_NG_iff`, **Theorem 6.8** (`trueN_NG`, `not_derivI_NG`, `not_derivI_neg_NG`, `n_first_incompleteness`), **Theorem 6.9** (`n_second_incompleteness`, `n_second_incompleteness_corollary`). |
| `Stable/NSigma.lean` | **Corollary 6.3**: `NStablyCE`, `NDecidedByTotal`, `IsSigmaNSet`, `nStablyCE_iff_isSigmaNSet`, `nStablyCE_iff_nDecidedByTotal`. |
| `Stable/PropCalc.lean` | Derived connectives `∨`, `→`, `↔`, `F ∪ {a}`, finite `⋀`/`⋁`, logical validity and equivalence, and the derived propositional rules (deduction theorem, modus ponens, case analysis, `∨`-elimination, congruences) used in Appendix B. |
| `Stable/Undefinable.lean` | **Appendix B.** `Arith.InB` = `𝓑`, `TrB` = `Tr_𝓑`; the interface `UndefData` (see below); the identity translation and `exists_true_not_deriv` (`PA + w` is incomplete for true `w`, from Theorem 1.5); the construction `d_n`, `U_n`, `x_n`, `ι_n`, `w_n`, `ε_n` (`stage`, `epsN`, …) with its invariant `Good`; the properties `eps_deriv_iff_tr` ((B.2)), `eps_deriv_neg_eps`, `lt_code_neg_eps`; `thetaK`, `theta`, `thetaK_pos`, `thetaK_neg`, `thetaK_cases`, `theta_and`, `theta_neg`, `theta_equiv_inB`, `theta_valid`, the encoding `theta_neg_eps_valid` / `not_deriv_PA_theta_neg_eps`; `jmap`, `jTrans` = `j` with `jTrans_isN2`, `jTrans_id`, `jTrans_twoConsistent`, `induced_neg_eps_iff`; **Proposition B.7** as `undefinable_family` (the family `j_X`, `¬ε_n ∈ PA_{j_X,𝓐} ↔ n ∈ X`) and `exists_undefinable` (`PA_{j,𝓐}`, `Q_{j,𝓐}` not `Σ⁰ₙ` for any `n`, by counting: `cantor`, `arithEnum`). |
| `Stable/Perturb.lean` | The language-independent core of Appendix B, used for Proposition B.10. `SentSyntax` (unique readability, `size`, `wrap`), `BoolOver`, `Language.botOf`/`topOf`, `Language.firstN`, the complete conjunctions `Language.vals` over a finite list with `vals_decide`, `vals_excl`, `deriv_disj_vals`; `Translation.map_imp`, `map_conjList`, `deriv_single`; the structure `Perturb` (stages `s` with `E s`, `act s`, `lvl s`); `thetaK`, `theta` with `thetaK_pos`, `thetaK_neg`, `thetaK_cases`, `theta_and`, `theta_neg`, `theta_valid`, and `theta_pos`, `theta_off`, `theta_fix`, `theta_intro` (the syntactic form of (B.5): `M ⊨ θ (b)` iff `M^X ⊨ b`); `imap`, `imap_inj`, `imap_equiv_theta`, `imap_eq_of_boolOver`, and the translation `Perturb.trans`. |
| `Stable/UndefinableZFC.lean` | **Proposition B.10.** The interface `UndefZData` and its extension `UndefZSound` by arithmetic soundness (see below); `exists_true_not_deriv` (`ZFC + w*` is incomplete for true `w`, from Theorem 1.5 for `i_{𝓐,𝓩}`); `Gam` = `Γ_n`, `allV`, `Vl` = `V_n`, `aBad` = `a_ν`; the construction `dPsi` = `d_ν`, `dN`, `tauN` = `τ_ν`, `trN` = `ι_ν`, `xN`, `wN`, `cN`, `epsN` with its invariant `Good`; the stages `(n, ψ_ν)` with `EN` = `ε_n* ∧ ζ ∧ ψ_ν`, `actN` = `b ↦ (b^{ι_ν})*` and their properties (i)–(iv) (`E_deriv_act_of_deriv_ZFC`, `E_deriv_iff_act_star`, `E_deriv_iff_act_of_mem_Gam`, `E_deriv_neg_act_eps_lt`, `E_deriv_neg_act_d`), `E_excl`, `pert : Perturb 𝓩`, `P0_fix`; `iT` = `i_X` with `iT_of_deriv_ZFC` (`ZFC ⊢ⁱ ZFC`), `iT_star_equiv`, `jT_isN2`, `jT_twoConsistent`, the encoding `induced_of_mem` / `not_induced_of_not_mem`; `exists_not_arithmetical` (counting); **Proposition B.10** as `undefinableZFC_family` and `exists_undefinable_ZFC`. |
| `Stable/Plain.lean` | Theories of arithmetic. `Translation.id`; `Arith.OneConsistent`, `Arith.TwoConsistent`, `Arith.SigmaSound` (Def. 2.9, 6.5) and their agreement with the notions relative to a translation; `Arith.BoolComb n` = `𝓑ₙ`; `G₀` = `𝒢`; **Proposition 5.5**, **Theorem 1.5** `first_incompleteness_arith`; **Lemma 6.6** for theories of arithmetic; **Theorem 5.11** `second_incompleteness_H`, **Corollary 5.13** `second_incompleteness_H_corollary`, the simplest case `second_incompleteness_simple`; **Theorem 1.1** `second_incompleteness_sigma`, with `exists_machine_of_isSigma2Set`, and **Corollary 5.17** `second_incompleteness_sigma_simple`. |
| `Stable/Readings.lean` | Section 5.2. `Asserted` = `F₀^R`, `IsReadingOn`, `IsTwoReading` (Def. 5.18); `RSh` = `R_Sh`, `compSet_RSh`, `SR_RSh_iff`, **Lemma 5.19** `exists_shadow`, `Shadow` = `Sh_R`; **Corollary 5.20** `reading_first`, **Corollary 5.21** `reading_second`, `reading_second_corollary`; `penrose_reading` (Remark A.3 of the versions up to 12 November, last paragraph, for a reading); the statements for `P = 𝓑₂`: `shadow_two`, `corollary_readingfirst`, `corollary_readingsecond`. |
| `Stable/ReadingsTranslations.lean` | **Example 5.23.** `IsSigma2Set.of_compSet`, `isReadingOn_translation`, `asserted_graph_eq_induced`, `ShadowT`, `first_incompleteness_via_readings`, `second_incompleteness_via_readings`. |
| `Stable/NPlain.lean` | Section 6.3 for theories of arithmetic. `NG₀` = `𝒢ₙ`; **Theorem 6.8** `n_first_incompleteness_arith`; `not_mem_of_deriv_godel`, `not_deriv_of_deriv_godel` (the deductions of Theorems 5.11 and 6.9 and of their simplest cases, for an arbitrary sentence); **Theorem 6.9** `n_second_incompleteness_H`, `n_second_incompleteness_H_corollary`, `n_second_incompleteness_simple`; Theorem 1.1 and Corollary 5.17 at level `n`: `n_second_incompleteness_sigma`, `n_second_incompleteness_sigma_simple`, with the machine `exists_nmachine_of_isSigmaNSet`; Corollaries 5.20, 5.21 at level `n` for a given machine: `n_reading_first`, `n_reading_second`, `n_reading_second_corollary`. |
| `Stable/NReadings.lean` | Section 6.3, readings at level `n`. `NSR_and_absorb` (conjunction of two `Σ⁰_{m+2}` conditions), `IsNReadingOn`, `IsNReading`, `exists_nShadow`, `NShadow` = `Shⁿ_R`, `n_corollary_readingfirst`, `n_corollary_readingsecond`. |
| `Stable/Penrose.lean` | Appendix A. `penrose_conditional` (the deduction of Theorem A.2 from Theorem 5.11), `isReadingOn_graph` (the graph of a map computable on `P` is a reading), `Tplus` = the machine `Sh_R (T₀)` of the proof of Theorem A.2, `Tplus_Ts`, `Tplus_Ts_closed`, **Theorem A.2**: `penrose_family`; for a family with one member: `penrose_two_way_delta`; with `Con₁ (Sh_R (T₀))*` in axiom (3): `penrose_two_way`. |
| `model/StableModel/Basic.lean` | `StableModel.mathlibModel : Stable.TuringModel` from `Nat.Partrec.Code` (`run := evaln`, `eval` the `Option`-valued `Code.eval`, `code := encode`, `pair := Nat.pair`); every field proved from Mathlib (`Nat.Partrec.prec`, `rfind`, `Partrec.cond`, `primrec_evaln`, `eval_part`, `smn`, …). |
| `Audit.lean` | `#print axioms` for the headline statements. |

Statistics: 33 files, ≈ 11 000 lines, ≈ 830 theorems (plus 280 lines for the Mathlib model).

## How the paper's objects are modelled

* A partial map `f : A → B` is `f : A → Option B`; `none` is "undefined".  `{±}` is `Bool`, `+ = true`.
* `M : ℕ → 𝓛 × {±}` is `ℕ → Option (L.Sent × Bool)`; a decision map `D : B × ℕ → {±}` is
  `B → ℕ → Option Bool`.
* The map `T'` of `𝒯_B` (`𝒟_B`) is defined for **every** `T` as `e⁻¹ ∘ T` (`e⁻¹ ∘ T ∘ e`), and
  `T ∈ 𝒯_B` (`InTB`) is the statement that `T` computes it.  Consequently the lemmas stated in the
  paper for `T ∈ 𝒯_B` (Lemmas 3.16 and 3.22, Theorem 3.25 (3), Proposition 5.5, Theorems 6.8 and 6.9, …) are proved here for every `T`, with
  `T^s = Stab (seqOf T)`; for `T ∈ 𝒯_B` this is the printed statement.  `T` "stably computes `M`"
  (`StablyComputes`) is `T ∈ 𝒯_B ∧ (T')^s = M^s`, as printed.
* Tuples of witnesses `n̄ ∈ ℕ^r` are contracted to a single number via the fixed surjections `β_r` of
  Section 2.2, bijective for `r ≥ 1` (as the paper itself does for `Tr_{Π₁}`): for `σ = ∃x̄ φ`, `instS σ v = φ(β_r v)`, and for
  `π = ∀x̄ φ`, `instP π v = φ(β_r v)`.  So `1`-consistency reads: for every `Σ⁰₁` sentence `σ` with
  `F ⊢ⁱ σ` there is `v` with `F ⊬ⁱ ¬ instS σ v` (Definitions 2.9 and B.6 with `n̄ = β_r v`).  The decomposition
  `σ = ∃x̄ φ` is the one chosen by `instS` (the maximal leading block, in the standard model).
* Level `n` of Section 6 is indexed by `m = n - 1` (the number of extra variables): `NDec m` is
  "`(m+1)`-decided", `NStable m` is "`(m+1)`-stable", `NSR m` is a `Σ⁰_{m+2}` condition.  `ℕ^{m+1}` is
  `NB ℕ m`, where the paper's tuple `(u₁, …, u_{m+1})` is `((u_{m+1}, u₁), u₂, …, u_m)`: the last
  variable is the base and `u₁` is next to it; the slice
  `M (u₁, ·)` of Definition 6.1 is `nslice m M u₁` (insert `u₁` next to the base).  Definition 6.1's
  identification of an `n`-decision map on `B` with an `(n-1)`-decision map on `B × ℕ` is the
  definitional equality `NB B (m+1) = NB (B × ℕ) m`, so no coercions appear.
* Lemma 4.2 is used only through: `σ (T) ∈ Σ⁰₂` (resp. `Σ⁰_{m+2}`), computable in `T`, with
  `ℕ ⊨ σ (T)` iff `T` is `Ω T`-decided.  The explicit shape `∃ u ∀ v̄ γ (u, v̄)` with `γ ∈ 𝓕₀` is
  not needed: Proposition 5.5 (2) only uses the `Π⁰₁` instances `instS (σ T) u` and `Q`'s decision
  of their `Δ₀` instances.
* A `Σ⁰ₙ₊₁` subset of an encoded set is modelled by the form with a computable relation given in
  Section 2.2 (`IsSigma2Set`, `IsSigmaNSet`).  Its equivalence with definability by a `Σ⁰ₙ₊₁` formula
  is a standard fact and is not formalized: `Arith` has no formulas with free variables.
* Here `∨` is a defined connective (`Stable/PropCalc.lean`); the manuscript counts it among the
  logical symbols (Section 2.2).  So translations are only required to preserve `¬`, `∧` and
  derivability.  Where a translation is a hypothesis this loses nothing.  Where it is constructed,
  in the two existence statements of Remark 5.25 (`exists_undefinable`, `exists_undefinable_ZFC`),
  the statement is verified for maps preserving `¬` and `∧`.  The written proof in
  `doc/undefinable.pdf` extends the maps over all connectives.

## Trusted base

All theorems are universally quantified over `M : TuringModel`, `L : Language M`, `A : Arith M`, and a
translation `i`.  What is *assumed* is therefore exactly the content of these structures.

**`TuringModel`** (Proposition 2.4, parts (1)–(4) and (6)): discharged by `model/`, i.e. satisfied by Mathlib's partial
recursive functions.  Fields: `run_mono`, `eval_iff` (step semantics), `code_inj`, `comp_code_mem`,
pairing bijection + strict monotonicity, `comp_const/succ/fst/snd/add/le/eq`, `comp_comp`,
`comp_pair`, `comp_cases` (total decidable predicate), `comp_primrec`, `comp_mu`, `comp_halt'`,
`comp_univ`, `comp_smn`.

**`Language`** (Section 2.2, Proposition 2.4 (5)): a type of sentences with a computable encoding,
`Prf` decidable with `(∃ p, Prf p l γ) ↔ image l ⊢ γ`, `𝓛` infinite, `¬` computable, and the
properties of `⊢` the paper uses: reflexivity, monotonicity, cut, compactness, `¬`-introduction
(from inconsistency of `F ∪ {α}`), explosion, double negation (both ways), `∧`-introduction/elimination.

**`Arith`** (extends `Language`; the classical facts about `𝓐`, cited in the paper from [TMR53],
[HP93]): truth `TrueN` with `trueN_neg`, `trueN_and`, soundness of `⊢` for `ℕ`; classes `IsSigma n`,
`IsPi n` with `Σ⁰₀ = Π⁰₀`, `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Σ⁰ₙ₊₁ ∩ Π⁰ₙ₊₁` (`pi_sigma_succ`, `sigma_pi_succ`, `sigma_succ`,
`pi_succ`), `Δ₀` closed under `¬`, all computable; instance maps `instS`, `instP` (computable) with
`instS_pi`, `instP_sigma`, `trueN_sigma`, `trueN_pi`, `exists_intro`, `forall_elim`; `negPi`
(`¬∀x̄ φ ⊢ ∃x̄ ¬φ`, `Σ⁰ₙ₊₁`, instances `¬ instP`, computable); `andPi` (a `Π⁰ₙ` sentence logically
equivalent to `π₁ ∧ π₂`); `delta0_dec` (truth of `Δ₀` sentences decidable); a true `Δ₀` sentence
exists; `Q` with `Q_delta0`, `Q_delta0_neg`; and `reprN` (representability: for a computable
`R ⊂ 𝒯 × ℕ^{m+2}` a total computable `σ_R : 𝒯 → 𝓐` with `σ_R T ∈ Σ⁰_{m+2}` and `ℕ ⊨ σ_R T ↔ NSR m R T ()`;
Lemma 4.2 and its level-`n` version).

**`UndefData`** (Appendix B; the classical facts and the syntax its proof uses beyond `Arith`, cited in
the paper from [HP93] and Soare): *syntax* — `destruct` (unique readability: every sentence is prime,
or `¬a`, or `a ∧ b`, in exactly one way), a `size` decreasing to subformulas, `Δ₀` closed under
subformulas (`delta0_neg`, `delta0_and`), a `Σ⁰₂` or `Π⁰₂` sentence that is a negation or a conjunction
is `Δ₀`, `wrap s` (= `∀y (y = y ∧ s)`: prime, injective, logically equivalent to `s`, in `Σ⁰₂ ∪ Π⁰₂`
only if `s` is `Δ₀`), each axiom of `Q` logically equivalent to a sentence of `𝓑`; *`PA`* — sound, `Q ⊆ PA`,
c.e., with a sentence `PA_r` (a finite fragment) provable from `PA` and proving `Q`; *definable theories* —
a type `Def3` of `Σ⁰₃`-definable theories with `tau τ β` = `τ(⌜β⌝)`, `con τ` = `Con_τ` true when the
defined theory is consistent, `satDef` = `Sat_𝓑` with the Tarski biconditionals over `PA_r` for `β ∈ 𝓑`
and true only on `𝓑`, `addFin τ l` = `τ ∨ "v ∈ l"` with its three obvious properties; *fact (2)* `act`,
the arithmetized completeness theorem: for `x_τ = PA_r ∧ Con_τ` an interpretation `β ↦ β^ι` commuting
with `¬`, `∧`, with `S ⊢ β` implying `{x_τ} ∪ S^ι ⊢ β^ι`, and `{x_τ} ⊢ τ(⌜β⌝) → β^ι`; *fact (3)*
`pi3_indep`: for every false `s` there is a true `Π⁰₃` sentence `d` with `Tr_𝓑 ⊬ d ∨ s`.  The
incompleteness of `PA + w` is *not* assumed: it is derived from `first_incompleteness`.

**`UndefZData`** (Proposition B.10; for a language `𝓩`, the language of set theory in the paper):
*syntax of `𝓩`* — `syn : SentSyntax 𝓩` (unique readability, `size`, and `wrap s` = `∀y (y = y ∧ s)`: prime,
injective, logically equivalent to `s`), and `wrapAll`, the computable syntactic operation replacing each
prime constituent `p` of a sentence by `wrap p`; *the standard interpretation* — `star` = `i_{𝓐,𝓩}`, a
computable translation, the guard `zeta` = `ζ` with the list `zetaPC` of its prime constituents, and a
set `P0` of prime sentences such that `a*` is a Boolean combination of sentences of `P0` for `a ∈ 𝓑`
(`star_bool`), each element of `P0` being some `a*` with `a ∈ 𝓑`, or in `zetaPC`, or a sentence `p` with
`η* = ζ → p` or `η* = ζ ∧ p` for some `η ∈ 𝓑` (`P0_cases`; this is the print's description of the elements
of `P₀`, which rests on its convention that `η^ω` begins with a quantifier); *`ZFC`* — a c.e. set of
sentences of `𝓩` proving `ζ` and `q*` for the axioms `q` of `Q`; *arithmetic* — a true sentence `PA_r`, a type
`Def3` of `Σ⁰₃`-definable theories in the language `𝓩` with `tau`, `con` as in `UndefData`, `baseDef` defining
`ZFC ∪ Tr_𝓑*` (`base_ax`: `{PA_r} ⊢ τ(⌜φ⌝)` for the axioms `φ`; `base_sat`: `{PA_r} ⊢ β → τ(⌜β*⌝)` for `β ∈ 𝓑`,
from fact (1) and `Σ₁`-completeness; `base_true`: what it defines in `ℕ`), `addFin` as before; *fact (2) for
`𝓩`* `act`, with the same three properties as in `UndefData` for interpretations of `𝓩` in `𝓐`; *fact (3)*
`pi3_indep`: a theory `ZFC ∪ Tr_𝓑* ∪ l`, `l` a finite list, which proves `d*` only for true `Π⁰₃` sentences
`d` does not prove `d*` for every true `Π⁰₃` sentence `d` (its set of such `d` is `Σ⁰₃`).  The hypothesis of
Proposition B.10, `∀ a, ZFC ⊢ a* → ℕ ⊨ a`, is an explicit hypothesis of `undefinableZFC_family` and
`exists_undefinable_ZFC` (internally the field `sound` of `UndefZSound`).  The incompleteness of `ZFC + w*`
is derived from `first_incompleteness` for the translation `i_{𝓐,𝓩}`.

## Second incompleteness: what is and is not formalized

In its present form Theorem 5.11 is `second_incompleteness_H` (`Stable/Plain.lean`): for `iAZ : 𝓐 → 𝓩`,
`F = T^s` `1`-consistent, `H ⊂ 𝓩` deductively closed and containing `ZFC`, with `F ⊢ b` for every
`b ∈ 𝓑₂` with `iAZ b ∈ H`, and **any** sentence `con ∈ 𝓩` such that `ZFC ∪ {con} ⊢ iAZ (𝒢 (T))`, we have
`con ∉ H`.  Applied to `con = Con₁ (T)*`, the hypothesis is equation (5.12).  Corollary 5.13, the
simplest case, Corollary 5.21 and Theorem 6.9 are proved in the same way.  Theorem A.2
(`penrose_family`) is deduced from Corollary 5.21, as in the manuscript.  In it the sentence of
axiom (3) is an arbitrary sentence `pen` of `𝓩`, and `ε` is an arbitrary sentence in place
of `ε_{T₀}`.  The claims of `ZFC`-provability in its proof are one hypothesis:
`ZFC ∪ {ε, pen} ⊢ con`, with the same arbitrary `con`.  In the manuscript these are two steps: the
sentence of axiom (3) implies its instance for `T₀`, and `ε` together with this instance implies
`Con₁ (T)*`.  The earlier form, for a family with one member, is
`penrose_two_way_delta`.  In it the sentence
of axiom (3) is `ε → conδ`, for arbitrary sentences `ε` and
`conδ` in place of `ε_{T₀}` and `Con₁ (δ + ε_{T₀})`.  The two claims of `ZFC`-provability in its
proof are hypotheses: `ZFC ∪ {ε} ⊢ enum` and, as in Corollary 5.13, `ZFC ∪ {enum, conδ} ⊢ con`, with
`enum` in place of `Enum (Sh_R (T₀), δ + ε_{T₀})` and the same arbitrary `con`.  What follows
describes the earlier form, for a translation; the remarks on (5.12) apply to both.

Theorem 1.1 (`second_incompleteness_sigma`) is stated for a `Σ⁰₂` set `F` of sentences
(`IsSigma2Set F`), not for a formula `σ`: the interface `Arith` has no syntax of formulas.  It
says that some machine presents `F`, by Corollary 3.7, and that the conclusion holds for every
machine `T` with `T^s = F`.  There are two hypotheses of provability in `ZFC`, for arbitrary
sentences `con` and `conσ`: `ZFC ∪ {con} ⊢ 𝒢 (T)*` and `ZFC ∪ {conσ} ⊢ con`.  For the machine
`T = T_σ` of Lemma 5.16, with `con = Con₁ (T_σ)*` and `conσ = Con₁ (σ)*`, the first is (5.12) and
the second follows from Lemma 5.16.  Corollary 5.17 (`second_incompleteness_sigma_simple`) is
treated in the same way.  So are Theorem 1.1 and Corollary 5.17 at level `n`
(`n_second_incompleteness_sigma`, `n_second_incompleteness_sigma_simple`), for a `Σ⁰ₙ₊₁` set `F`
(`IsSigmaNSet m F`, `n = m + 1`) and every machine `T` with `T^{s_n} = F`, with `Sndₙ` in place of
`Con₁`.  Not formalized: Remark 5.22.

For a translation, Theorem 5.11 is proved in the form (`second_incompleteness`): for `𝓩`, `iAZ : 𝓐 → 𝓩`, `i : 𝓩 → 𝓛` with
`j = i ∘ iAZ` a `2`-translation, `F = T^s`, `F ⊢ⁱ ZFC`, `F` `1`-consistent relative to `j`, and **any**
sentence `con ∈ 𝓩` such that `ZFC ∪ {con} ⊢ iAZ (𝒢 (T))`, we have `F ⊬ⁱ con`.  Applied to
`con = Con₁ (T, i)`, the hypothesis is equation (5.12), "`ZFC ⊢ Con₁ (T, i) → i_{𝓐,𝓩} (𝒢 (T))`", the
formalization of Proposition 5.5 (3) inside `ZFC`.  Verifying (5.12) would require formalizing
`ZFC`-provability and replaying the development inside it; this is outside the scope of the project,
and the sentence `Con₁ (T, i)` itself (Lemma 5.9 and Definition 5.10 in their form before
11 November 2026) is not constructed.  Corollary 5.13,
Theorem 6.9 and the earlier form of Theorem A.2 (`penrose`) are proved in the same form, with
"`ZFC ⊢ Enum (T, δ) → (Con₁ (δ, i) ↔ Con₁ (T, i))`" as a further hypothesis.  Everything else in the
proofs of these results is a theorem here.

## Remarks on the manuscript

No mathematical gap was found.  Small points the formalization made visible.  Items 1, 2, 4 and 5 are
now reflected in the manuscript (Remark 3.17, the clause "we may take n ≥ 1" in the proof of Lemma 3.26,
Lemma 6.4, and the parenthetical in Section 6.2); the all-`T` reading used in the proof of
Theorem 5.11 came out of subsequent proofreading and is consistent with what is formalized here
(`hcon` takes an arbitrary sentence, and Proposition 5.5 is proved for every `T`).

1. Lemmas 3.16, 3.22, Theorem 3.25 (3) and Proposition 5.5 hold for every `T ∈ 𝒯`, not only `T ∈ 𝒯_𝓛`, once
   `T'` is read as the partial map `e⁻¹ ∘ T` (silent where `T` outputs a non-code).
2. Lemma 3.26 / Theorem 3.25 (4): the proof as printed takes an `α` with `F ∪ i(Tr_{Π₁}) ⊢ α ∧ ¬α`;
   formally one needs some sentence of `𝓛` to exist (here `i (0 = 0)`), and the conjunction
   `π₁ ∧ … ∧ πₙ` needs a base case for `n = 0` (a true `Δ₀` sentence) — the degenerate case where no
   `π_j` occurs, i.e. `F` itself is inconsistent.  The paper's statement "unless for some
   `π ∈ Tr_{Π₁}`, `F ⊢ⁱ ¬π`" is then still correct.
3. The totality claims (`T'_spec`, `(C T)'` total; Corollary 3.7 (2) ⇒ (1)) need `B` (resp. `𝓛`)
   infinite, as the paper says; the formalization carries `Enc.Infinite` as the hypothesis, and
   derives `B × ℕ` infinite for the level-`n` constructions.
4. Section 6.2, "absorbed by quantifying over lists of witnesses": this is where the bulk of the extra
   work lies (`Stable/NList.lean`, ≈ 400 lines).  The absorption of a bounded `∀ j < length l` in front
   of an `NSR m` condition proceeds level by level: at level `m+1` it produces a bounded `∃` over the
   list at level `m`, which is a separate (easier) absorption lemma.  Nothing goes wrong, but the
   phrase hides a real induction.
5. The `Σ⁰_{m+2}` form of "`b` is `T`-`(m+1)`-stable" is `NSR m (compl^m R_base)`, i.e. the matrix
   "`1`-stability of the slice" is negated `m` times, in agreement with the parenthetical "1-stability
   of a slice *or its negation*".
6. Lemma 4.2's explicit form `∃ u ∀ v̄ γ (u, v̄)` is only used through the `Π⁰₁` instances; the
   Lean statement of the representability axiom (`reprN`) is correspondingly weaker.
7. Theorem 1.5 (1), as Proposition 5.5 (1), is used in the proof of Theorem 5.11; in Lean,
   `Arith.not_deriv_G₀` in `second_incompleteness_H`.  For a translation it is `not_derivI_G` for
   the composite translation `j = i ∘ iAZ` in `second_incompleteness`, with
   `Translation.derivI_iff` applied twice.
8. Changes of the 21 Oct 2026 version, checked against the sources. (a) Theorem 1.6 now fixes a
   machine `K` computing `i` on `Σ⁰₂` sentences and says `𝒢` is obtained explicitly from `K`; here
   `first_incompleteness` is the existence statement `∃ G, CompT M G ∧ …`, with `G` obtained by choice
   from the hypothesis `hi : i.IsNTranslation 2`, so the printed statement implies the formal one and
   the constructivity clause is not formalized. (b) The level-`n` machine `Tur^n` now has its last
   argument in `ℕ^n`; this is what `NH : NB M.Code m → ℕ → Option Bool` always had. (c) `Ω^n` is
   stated total computable with `ZFC`-provable properties; `NOmega_compT`, `NOmega_inDB`,
   `decOf_NOmega` are the first three, `ZFC` is out of scope. (d) Definition 2.14 (then numbered 2.15) now says "free
   variables among `x̄`"; `OneConsistent` quantifies over all `Σ⁰₁` sentences, which is that reading.
   (e) The convention on languages (`ZFC` proves the syntax machine total), the fixed choices after
   Lemma 4.1 (Cantor pairing, `β_r`, `D_R`), and the rewritten proof of Lemma 5.9 and of Theorem 1.4
   concern `ZFC`-provability only and change nothing that is formalized.
9. A later version of the same day renames the map of Lemma 3.13 to `κ`, since `K` now denotes
   the machine of Theorem 1.6; the Lean name `exists_K` is unchanged. The record of fixed choices after
   Lemma 4.1 and the rewritten proof of Lemma 5.9 again concern `ZFC`-provability only.
10. The 9 Nov 2026 version. (a) Theorem 6.7 is now stated in the
   form of Theorem 4.6: no `n`-decision map `D` which is `n`-stably computed by some `T ∈ 𝒟ⁿ_𝒯` is
   `n`-stably sound and complete, in particular no computable such `D`. This is exactly the form of
   `n_stable_halting` (`¬ NTheta m D T` for every `T`), so the Lean statement now matches the print
   without the "in particular" step. (b) The uncited Lemma 2.14 (transitivity of "interprets",
   `lemma_inducedinterpretation`) is deleted; Definition 2.15 becomes Definition 2.14, and the
   docstrings of `OneConsistent` and `TwoConsistent` follow. (c) The other changes
   are to flow and wording only (pointers, paragraph breaks, reminders, the appendix's `N`-body
   passage); none touches a formalized statement.

11. Appendix B (9 Nov 2026), Proposition B.1, is formalized in `Stable/Undefinable.lean` relative to
   `UndefData`. Differences from the print, none affecting the statement: (a) non-arithmeticity is
   proved by counting (`exists_undefinable`): the map `X ↦ PA_{j_X,𝓐}` is injective since
   `¬ε_n ∈ PA_{j_X,𝓐} ↔ n ∈ X` (`undefinable_family`), and the arithmetical sets of sentences are
   enumerated by `ℕ` (`arithEnum`, via the machine codes in `IsSigmaNSet`), so Cantor's theorem gives an
   `X` with `PA_{j_X,𝓐}` and `Q_{j_X,𝓐}` not `Σ⁰ₙ` for any `n`; the print's "not computable from true
   arithmetic" is a relativized statement outside the interface. (b) `d_n` and `b_{t(n)}` are chosen
   by `Classical.epsilon`, not as least elements; the choice does not matter. (c) The empty conjunction
   and disjunction are `¬(a₀ ∧ ¬a₀)` and `a₀ ∧ ¬a₀` for the fixed true `Δ₀` sentence `a₀`; `ρ_n` (Lean `sN`) is the
   disjunction of the negations of the sentences `b_k^ℕ`, `¬ε_m`, logically equivalent to the print's
   `¬⋀ b_k^ℕ ∨ ⋁ ε_m`. (d) The paper's `b_0, b_1, …` is the encoding `e`: `k(b) = e b`, and the
   sentences with code `≤ n` replace `b_0, …, b_n`. (e) `θ_K` is the print's disjunction verbatim; the
   proofs go through the case analysis `thetaK_cases` along `X_K` instead of models. (f) The print's
   argument "`∀y (y = y ∧ θ(p))` is not in `Σ⁰₂ ∪ Π⁰₂`" is `wrap_theta_not`, from `wrap_sigma2`,
   `wrap_pi2` and `Δ₀` closed under subformulas; injectivity from "the first conjunct of the first
   disjunct" is `eq_of_thetaK_eq`. (g) `PA + w_n` incomplete is Theorem 1.6 (3) and (1) for the identity
   translation and a machine enumerating `PA + w_n` (`exists_true_not_deriv`). (h) The `1`- and
   `2`-consistency of `PA`, `Q` relative to `j` use that each axiom of `Q` is logically equivalent to a
   sentence of `𝓑` (`Q_equivB`), as `j` need not fix a non-prenex axiom syntactically.

12. The 10 Nov 2026 version. (a) The text changes in flow and wording only: the auxiliary sentence `s_n`
   of the proof of Proposition B.1 is now `ρ_n`, the bound variable of `wrap` is `y`, Definition 2.10
   names the induced theory; no formalized statement changes. (b) Proposition B.4 is formalized in
   `Stable/UndefinableZFC.lean` relative to `UndefZData`, on top of the language-independent
   `Stable/Perturb.lean`. Differences from the print, none affecting the statement: (i) the print's
   `E_n` and `b^{(n)}` are split along the valuations: a stage is a pair `(n, ψ_ν)` with `ν ∈ V_n`,
   `E (n, ν) = ε_n* ∧ ζ ∧ ψ_ν` and `act (n, ν) b = (b^{ι_ν})*`, which commutes with `¬` and `∧` exactly;
   over `ZFC + ε_n*` some `E (n, ν)`, `ν ∈ V_n`, holds (`inconsistent_of_eps`), which is the print's
   "`ZFC ⊢ ε_n* → E_n`". (ii) A valuation `ν` of `Γ_n` is represented by its complete conjunction `ψ_ν`
   (`Language.vals`). (iii) `x_n` is the conjunction of the sentences `PA_r ∧ Con_{τ_ν}`, `ν ∈ V_n`.
   (iv) Equation (B.5) is used in the syntactic forms `theta_pos`, `theta_off`, `theta_intro`.
   (v) `ZFC + w_n*` incomplete is Theorem 1.6 (3) and (1) for the translation `i_{𝓐,𝓩}` and a machine
   enumerating `ZFC + w_n*` (`UndefZSound.exists_true_not_deriv`). (vi) `d_ν`, `c_n`, `a_ν` are chosen by
   `Classical.epsilon`. (vii) "Theorem 1.4 applies" is the conjunction of the hypotheses of
   `second_incompleteness` on `i`: `j = i ∘ i_{𝓐,𝓩}` is a `2`-translation, `ZFC ⊢ⁱ ZFC`, and `ZFC` is
   `1`-consistent relative to `j`; that `ZFC` is stably c.e. is not restated.

13. The restructured manuscript (11 Nov 2026). (a) The theorems are stated for
   theories of arithmetic; `Stable/Plain.lean` and `Stable/NPlain.lean` derive them from the earlier
   modules by the identity translation. Theorems 1.4 and 6.9 take the form with an ambient theory `H`.
   (b) Section 5.2 (readings) and its level-`n` analogue are formalized in `Stable/Readings.lean`,
   `Stable/ReadingsTranslations.lean` and `Stable/NReadings.lean`, for a computable `P ⊇ 𝓑ₙ`; see "The
   restructured manuscript" above for the hypothesis that `𝓑ₙ` is computable. (c) In the manuscript the
   pairing "quantifier by quantifier" of the last paragraph of Section 6.3 is `NSR_and_absorb`: a conjunction at
   one level becomes a disjunction under the negation of the recursion, which is absorbed by
   `NSR_or_absorb`. (d) In that version Theorem A.2 had three
   alternatives, the third being that the sentence `Enum (Sh_R (T₀), δ)` is not asserted.
   This is `penrose_reading`; its alternative (1) is the case in which no machine `T₀` exists. (e) Items 8–12 above use the numbering of their dates. (f) The
   encoding `¬ε_n ∈ F_{j,𝓐} ↔ n ∈ X` in the proof of Proposition B.7 holds for every `F ⊆ PA`
   (`induced_neg_eps_iff`): that `F` contains `Q` is not used there.

14. The new Appendix A (11 Nov 2026, later the same day). (a) The idealized mathematician asserts
   sentences of set theory. Axiom (3), the Penrose property, is: `ε_T → Con₁ (δ + ε_T)` is in `𝓗`,
   for every `T`. Here `δ + ε` is the formula saying that `x` is the code of some `b ∈ 𝓑₂` and that
   `δ` holds of the code of `ε → b*`. In the first version of that day the sentence was
   `ε_T → Con₁ (T⁺)*`, for the machine `T⁺ = Sh_R (T)` of the reading `R = {(a, ε_T → a*)}`. Given
   axiom (1) the two are equivalent. Theorem A.2 has two alternatives: `𝓗` is not stably c.e., or
   `𝓗` is not sound. Its first part is `penrose_two_way_delta` (`Stable/Penrose.lean`), a
   consequence of Corollary 1.5 for the machine `Sh_R (T₀)`, the formula `δ + ε_{T₀}` and the
   deductive closure of `𝓗 ∪ {ε_{T₀}}`. With the earlier sentence it is `penrose_two_way`, a
   consequence of Theorem 1.4. The passage from the first part to the two alternatives uses truth
   in the intended interpretation of `𝓩`. It is not formalized. For the version of 12 Nov see
   item 15.
   (b) Not formalized: the example of Remark 5.12 (in Corollary 1.5 the existential hypothesis does
   not suffice), and its use in Remark A.3. They assert provability in `ZFC`. (c) The last paragraph of
   Remark A.3 is Corollary 1.5 for `H = 𝓗`. (d) `Tplus` is defined under the hypotheses that `𝓑₂` is
   computable, as in point 1 of "The restructured manuscript", and that `a ↦ (ε → a*)` is computable
   on `𝓑₂`.

15. The 12 Nov 2026 version. No statement changes here. (a) Appendix A now fixes an `ω`-model `𝒰`
   of set theory. "True", "sound" and "defines" refer to `𝒰`, and the appendix holds for every
   `𝒰`. So both parts of Theorem A.2 are theorems of `ZFC`. The last part is still not formalized:
   this project has no structures for `𝓩`.  For the present version see item 22. (b) The proof of
   Theorem A.2 now cites Corollary 5.17,
   for `T₀` and `R' = {(z, ε_{T₀} → z)}`. `penrose_two_way_delta` is now proved in the same way, from
   `reading_second_corollary`. The theory `H` of the corollary is `{z | (ε_{T₀} → z) ∈ 𝓗}`. That it is
   deductively closed and contains `ZFC` is checked in the proof. (c) The map of (5.1) is called
   `Λ` in the manuscript, where `H` is the theory of Theorem 1.4. Here it is still `H`
   (`Stable/Incompleteness.lean`). (d) Section 1.2 now says that at level `n` the `Σ⁰ₙ₊₁` sentences
   replace the `Σ⁰₂` sentences in the definition of `𝓑₂`. Theorem 6.9 and
   `n_second_incompleteness_H` had `𝓑ₙ₊₁` before.

16. The 12 Nov 2026 version, later the same day. Appendix B is removed from the manuscript. Its
   two propositions are stated in the new Remark 5.20, with the definition of "arithmetically
   sound". Their proofs are in the note `doc/undefinable.pdf` of this repository, which is the
   former appendix with its numbering. The first paragraph of Remark 5.20 (a reading whose asserted
   set is not arithmetical, without deductive closure) is not formalized. No statement changes
   here.

17. The latest version of 12 Nov 2026: Section 1.2 is reshuffled. (a) The second incompleteness
   theorem is now Theorem 1.1, in `Σ⁰₂` language, with the theory `H` as the main actor: `H` is a
   deductively closed theory of set theory containing `ZFC` which admits a `2`-`F`-reading, that
   is `F` is `Σ⁰₂`-definable and proves the sentences of `H₂ = {b ∈ 𝓑₂ | b* ∈ H}`; if `F` is
   `1`-consistent then `Con₁ (σ)* ∉ H` for every `Σ⁰₂` formula `σ` defining `F`. This is
   `second_incompleteness_sigma`. (b) The former Theorem 1.4, for a theory presented by a machine,
   is Theorem 5.11, with the same statement and the same Lean theorem `second_incompleteness_H`.
   Theorem 1.1 is deduced from it by the new Lemma 5.16: a `Σ⁰₂` formula `σ` gives a machine
   `T_σ`, and `ZFC` proves `Con₁ (σ)* ↔ Con₁ (T_σ)*`. (c) The definitions of stable enumeration
   come after Theorem 1.1, and the first incompleteness theorem is Theorem 1.5. (d) New
   Corollary 5.17 (the simplest case for a `Σ⁰₂` definition, `second_incompleteness_sigma_simple`)
   and Remark 5.22 (`H` admits a `2`-reading iff it arises from a stably c.e. system under a
   reading; not formalized). (e) Remark A.3 is removed from the manuscript. (f) The numbers of
   this file and of the sources follow the new numbering, see "The restructured manuscript"; the
   items above keep the numbering of their dates.

18. Appendix A for a family of theories (12 Nov 2026, the last version of that day). (a) A formula
   `Δ (y, z)` of set theory defines a family of theories, one for each value of the parameter `y`.
   Axiom (2) is now: `𝓗` is a member of the family. Axiom (3), the Penrose property, is now: for
   every `T`, `𝓗` contains the sentence `∀ y, ε_T (y) → Con₁ ((Δ + ε_T)_y)`, where `ε_T (y)` says
   that `T` stably enumerates the member with parameter `y`, and `ε_T` is `∃ y, ε_T (y)`. Before,
   the family had one member, defined by `δ`. (b) Theorem A.2 keeps its statement. Its first part
   is `penrose_family`: the sentence of axiom (3) for `T₀` is an arbitrary sentence `pen ∈ 𝓗`, and
   the step "`ZFC` proves that `ε` and this sentence imply `Con₁ (T)*`" is the hypothesis `hpen`.
   In the manuscript this step uses the proof of Corollary 5.13 with a parameter.
   `penrose_two_way_delta` is the case of one member. (c) The last part is still not formalized.
   For the present version see item 22.
19. The 13 Nov 2026 version, after a proofread.  No numbers change. (a) Section 6.3 now states
   Theorem 1.1 at level `n`.  It is formalized as `n_second_incompleteness_sigma`, with Corollary
   5.17 at level `n` as `n_second_incompleteness_sigma_simple` (`Stable/NPlain.lean`); the machine
   of Lemma 5.16 at level `n` is `exists_nmachine_of_isSigmaNSet`, by Corollary 6.3.  As at level
   `1`, the two claims of provability in `ZFC` are hypotheses. (b) Remark 5.14 has a second
   paragraph: the same example with a formula of `𝓐`, which shows that the restriction to `Σ⁰₂`
   formulas in Theorem 1.1 matters.  Like the first paragraph, it is not formalized. (c) Remark 6.10
   (1) now restricts its claim to `n`-consistency in its usual form, with one free variable, as in
   Salehi–Seraji.  It is about the literature and is not formalized. (d) Proposition 2.4 (5) now
   encodes terms and formulas, and states the hypothesis on languages.  The interface `Language`
   keeps sentences only; no formalized statement changes.  The other changes are in wording.
20. The 15 Nov 2026 version, after a second proofread.  No numbers change, and no formalized
   statement changes. (a) The abstract now says that the paper is formalized in Lean "with
   exceptions of standard type".  The footnote of the Introduction adds that the sentences
   expressing `1`-consistency are not constructed, that the second incompleteness theorems are
   proved for an arbitrary sentence in their place, and that some remarks are not formalized;
   "Exceptions" above lists them. (b) In Section 6 the hypothesis "`B` infinite" is no longer a
   standing convention.  It is stated in Corollary 6.3, where it is used; here it is the hypothesis
   `Enc.Infinite` of `nStablyCE_iff_isSigmaNSet`, see item 3. (c) Section 2.1 states two elementary
   facts which the manuscript uses without mention: a composition of computable maps is computable
   (`Comp.comp`), and a subset is computable iff its total `±`-valued map is
   (`compSet_iff_compT_decide`). (d) The proof of Lemma 5.16 gives the reason for
   `ZFC ⊢ Con₁ (σ)* ↔ Con₁ (σ')*`, where `σ'` is `σ` without repeated variables in its prefix: the two
   sentences are logically equivalent.  The machine `T_σ` is `exists_machine_of_isSigma2Set`, for a
   `Σ⁰₂` set; the equivalence in `ZFC` stays a hypothesis. (e) Section 1.1 defines an "arithmetic
   theorem" of a set `H` of sentences of `𝓩`: a sentence `a` of `𝓐` with `H ⊢ a*`.  The notation
   `β ⊢ α` for a single sentence `β`, which was not used, is removed. (f) Remark 6.10 (1) cites
   Kreisel's theorem, through Salehi–Seraji, for the fact that `n`-consistency does not imply
   `Σₙ`-soundness when `n ≥ 3`.  In Appendix A, the paragraph which motivates the Penrose property
   now asks that the members of the family be sound, deductively closed and contain `ZFC`, as the
   paragraph on the truth of the sentences of axiom (3) does.  These parts are not formalized.  The
   other changes are in wording and in the references.  In this file, the numbers of Definitions
   3.4, 3.20, 4.3 and 4.4, and a few other references, are corrected to the present numbering.
21. Release 0.4.8 (15 Nov 2026), after a third proofread, which compared the printed statements
   with the Lean statements. (a) A change in Lean.  Up to release 0.4.7 the four theorems for
   Theorem 1.1 and Corollary 5.17 (`second_incompleteness_sigma`,
   `second_incompleteness_sigma_simple`, and their forms at level `n`) said: there is a machine
   `T` presenting `F` such that the conclusion holds for all `con`, `conσ`.  Lemma 5.16 gives its
   equivalence only for the machine `T_σ` built from `σ`, so it could not be applied to this
   unnamed machine, and the printed theorem did not follow from the Lean statement, (5.12) and
   Lemma 5.16.  The four theorems now say: some machine presents `F`, and the conclusion holds for
   every machine `T` presenting `F`.  The proofs are the same.  The audit is unchanged. (b) In
   this file: "Status" no longer says that all computability claims of the paper are theorems
   about the standard model, since Proposition 2.4 (5) is the interface `Language`; "Exceptions"
   lists Remark 2.7, the notes of Remark 3.18, the comparison with experimental logics, two parts
   of Proposition 2.4, the last claim of Theorem 1.5, and the remaining assertions of provability
   in `ZFC`; the rows on `RS` and `trSigma`, the order of the variables at level `n`, the
   modelling of `Σ⁰ₙ₊₁` sets, and item 7 are corrected. (c) Docstrings are corrected in
   `Stable/Machines.lean`, `Stable/Enc.lean`, `Stable/Arith.lean`, `Stable/NStab.lean` and
   `Stable/Penrose.lean`.  No other statement changes. (d) The manuscript after this proofread,
   still of 15 Nov 2026.  No numbers change, and no formalized statement changes.
   Proposition 2.4 (6) has a third item, closure under unbounded search.  The inverse of `ε_A`
   uses it, and so does `M_D` (`comp_mu`, `comp_epsilonInv`, `comp_seqOfDec`).  The footnote of
   the Introduction says that the first part of Theorem A.2 is verified in the same form as the
   second incompleteness theorems, and that its last part is not formalized.  Appendix A writes
   `Δ (y)` and `(Δ + ε_T) (y)` for a formula with the parameter `y`, and keeps `𝓗_p` for the
   members of the family.  The sentence of axiom (3) is `∀ y, ε_T (y) → Con₁ ((Δ + ε_T) (y))`.
   For the later changes of Appendix A see item 22.
22. Release 0.4.9 (21 Nov 2026): the manuscript of 21 November 2026, after a revision of
   Appendix A and a fourth proofread.  One new number: Corollary A.3. (a) Appendix A fixes a
   Grothendieck universe `𝒰` containing `ω`, in place of an `ω`-model.  "True" and "sound" refer
   to `𝒰`.  The family is a set `𝓕 ∈ 𝒰` of theories in the language `𝓩`, with a definition `Δ`
   in `𝒰`: a formula with one free variable.  Formulas with a parameter are gone.  In a sentence,
   "`∀ F ∈ 𝓕 …`" stands for `∀ F, Δ (F) → …`.  For a set `F` of sentences of `𝓩`,
   `F + ε := {b ∈ 𝓑₂ | (ε → b*) ∈ F}`. (b) Axiom (3), the Penrose property, is one sentence:
   `∀ T, ∀ F ∈ 𝓕, ε_T (F) → Con₁ (F + ε_T)`, with the machine a variable, as in Definition
   5.10 (4).  `ZFC` proves that it implies its instance for each `T`.  Before, axiom (3) asked
   for the instances. (c) Theorem A.2 now says only: under axioms (1) and (3), if `T₀` stably
   enumerates `𝓗`, then `{b ∈ 𝓑₂ | 𝓗 ∪ {ε_{T₀}} ⊢ b*}` is not `1`-consistent.  This is
   `penrose_family`, unchanged: `pen` stands for the sentence of axiom (3), or for its instance
   for `T₀`, and `hpen` for the claims of `ZFC`-provability.  The former last part is the new
   Corollary A.3: if `𝓗` is *Penrose*, that is satisfies axioms (1)–(3) relative to some family,
   then `𝓗` is not stably c.e. or not sound.  It uses truth in `𝒰` and is not formalized.  The
   manuscript notes that both results use less of `𝒰`, with no assumption beyond `ZFC`.
   (d) Section 2.2 lists the logical symbols, `∨` among them, and fixes the deductive system of
   Shoenfield.  Example 2.8 states how quantifiers are relativized by the guard `ζ`.  Here `∨` is
   a defined connective, see "How the paper's objects are modelled", and `i_{𝓐,𝓩}` is an
   arbitrary translation, see "Exceptions". (e) The footnote of the Introduction now says that
   the sentences expressing `1`-consistency and `Σₙ`-soundness are not constructed, that Theorem
   A.2 is verified in the same form as the second incompleteness theorems, and that Corollary
   A.3 is not formalized.  The Introduction says that Appendix A assumes a Grothendieck universe.
   The other changes are in wording. (f) New in Lean: `exists_total_uniform`
   (`Stable/Machines.lean`), the first half of Remark 3.18.  For infinite `B` it gives a total
   computable `St : 𝒯 → 𝒯` with `St T ∈ 𝒯_B`, `(St T)'` total and `(St T)^s = T^s`, for every
   `T`.  It is the instance `R = R_B` of `exists_stabMachine`.  Before, only the non-uniform
   `exists_total_of_stablyCE` was stated.  The audit now has 65 lines.  No other statement
   changes. (g) Docstrings and comments are corrected in `Stable/Penrose.lean` (the universe, the
   family, the sentence of axiom (3), Corollary A.3), `Stable/Halting.lean` (equations (4.7) and
   (4.8)), `Stable/Incompleteness.lean` (`first_incompleteness` is the form for a translation),
   `Stable/NPlain.lean` (the map `Shⁿ_R` is `exists_nShadow`), `Stable/NReadings.lean` and
   `Stable/Logic.lean`. (h) In this file: "Status", "Exceptions", the rows of Theorem A.2,
   "Second incompleteness", and the remark on `∨` in "How the paper's objects are modelled".

## Conventions used in the sources

See `CONVENTIONS.md` (toolchain, core-Lean idioms, pitfalls recorded during the development).
