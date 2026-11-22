import Stable.ReadingsTranslations
import Stable.PropCalc

/-!
# Appendix A: the Penrose property (Theorem A.2)

In Appendix A the idealized mathematician stably asserts a set `𝓗` of sentences of set theory, which
is deductively closed and contains `ZFC` (axiom (1)).  The appendix fixes a Grothendieck universe
`𝒰` containing `ω`, and a set `𝓕 ∈ 𝒰` of theories in the language `𝓩`, the family.  The family
has a definition `Δ` in `𝒰`: a formula of `𝓩` with one free variable, which holds in `𝒰` exactly
of the members of the family.  `𝓗` is a member of the family (axiom (2)).  For a machine `T`,
`ε_T (F)` is the formula "`T` stably enumerates `F`", and `ε_T ∈ 𝓩` is the sentence
`∃ F ∈ 𝓕, ε_T (F)`, which stands for `∃ F, Δ (F) ∧ ε_T (F)`.  For a sentence `ε ∈ 𝓩` and a set
`F` of sentences of `𝓩`, `F + ε := {b ∈ 𝓑₂ | (ε → b*) ∈ F}`.  The Penrose property (axiom (3))
says that `𝓗` contains one sentence, `∀ T, ∀ F ∈ 𝓕, ε_T (F) → Con₁ (F + ε_T)`.  In it the
machine `T` is a variable (Definition 5.10 (4)).  Its instance for a machine `T` is the sentence
`∀ F ∈ 𝓕, ε_T (F) → Con₁ (F + ε_T)`, and `ZFC` proves that the sentence implies each instance.
Up to release 0.4.8 of this project (manuscript of 15 November 2026) a formula `Δ (y, z)` with a
parameter `y` defined the family, and axiom (3) asked for the instances, one sentence for each
`T`.  In the versions of the manuscript before the last one of 12 November 2026 the family had
one member, defined by a formula `δ (z)`, and the sentence of axiom (3) was
`ε_T → Con₁ (δ + ε_T)`.

The proof of Theorem A.2 applies Corollary 5.21 to `T₀` and the relation `R' := {(z, ε → z)}`, for
`ε := ε_{T₀}`.  The reading of the corollary is `R = {(a, ε → a*)}`, and its machine is
`Sh_R (T₀)`.  Here it is `Tplus … T₀`, written `T₀⁺`, with
`(T₀⁺)^s = {b ∈ 𝓑₂ | (ε → b*) ∈ T₀^s}`.  The theory `H` of the corollary is `{z | (ε → z) ∈ 𝓗}`,
the deductive closure of `𝓗 ∪ {ε}`.

* `penrose_conditional`: the deduction from Theorem 5.11, for any machine `Tp` with
  `Tp^s = {b ∈ 𝓑₂ | 𝓗 ∪ {ε} ⊢ b*}`.
* `isReadingOn_graph`: the graph of a map computable on `P` is a reading with `IsReadingOn P`.
* `Tplus`, `Tplus_Ts`, `Tplus_Ts_closed`: the machine `T₀⁺` and the description of `(T₀⁺)^s`.
* `penrose_family`: Theorem A.2, as in the manuscript: if `T₀` stably enumerates `𝓗`,
  then `{b ∈ 𝓑₂ | 𝓗 ∪ {ε_{T₀}} ⊢ b*}` is not `1`-consistent.  It applies Corollary 5.21
  (`reading_second`), as the manuscript does.
* `penrose_two_way_delta`: the same for a family with one member, in the form of the earlier
  versions, with the sentence `ε → Con₁ (δ + ε)` in axiom (3).  It applies Corollary 5.21
  (`reading_second_corollary`).
* `penrose_two_way`: the same conclusion, from the sentence `ε → Con₁ (T₀⁺)*` in place of the
  sentence of axiom (3).  This was axiom (3) in an earlier version of the manuscript.  Given axiom
  (1) the two sentences are equivalent, as `ZFC` proves `ε → (Con₁ (δ + ε) ↔ Con₁ (T₀⁺)*)`.

As everywhere, (5.12) is a hypothesis (`hcon`), for an arbitrary sentence `con` in place of
`Con₁ (T₀⁺)*`, and `ε` is an arbitrary sentence of `𝓩`.  In `penrose_family` the sentence of axiom
(3) is an arbitrary sentence `pen` of `𝓩`, and the claims of `ZFC`-provability in the proof are
the hypothesis `hpen`: `ZFC ∪ {ε, pen} ⊢ con`.  In the manuscript these are two steps: the
sentence of axiom (3) implies its instance for `T₀`, and `ε` together with this instance implies
`Con₁ (T₀⁺)*`.  With `pen` the instance, `hpen` is the second step.  In `penrose_two_way_delta`
the two claims
of `ZFC`-provability in the proof are hypotheses as well, for arbitrary sentences `enum` and `conδ`
in place of `Enum (T₀⁺, δ + ε)` and `Con₁ (δ + ε)`: `henum` (`ZFC` proves that `ε` implies `enum`)
and `hδ` (as in Corollary 5.13).  Corollary A.3 says that a sound `𝓗` which is Penrose, that is
satisfies axioms (1)–(3) relative to some family, is not stably c.e.  Up to release 0.4.8 it was
the last part of Theorem A.2.  It uses truth in `𝒰`, and axiom (2): `𝓗 ∈ 𝓕`, so `Δ` holds of `𝓗`
in `𝒰`.  It is not formalized: this project has no structures for `𝓩`.
-/

namespace Stable

open Classical

variable {M : TuringModel} {A : Arith M} {Z : Language M}

/-- Theorem A.2, the deduction from Theorem 5.11.  `Hm` contains `ZFC`.  `eps ∈ 𝓩` stands for the
sentence `ε_{T₀}`.  `Tp` is a machine with `Tp^s = {b ∈ 𝓑₂ | Hm ∪ {eps} ⊢ b*}`.
`con` satisfies (5.12) for `Tp`, and `Hm ∪ {eps} ⊢ con`, with `con = Con₁ (Tp)*`.  Then `Tp^s` is
not `1`-consistent. -/
theorem penrose_conditional (iAZ : Translation A.toLanguage Z) (ZFC Hm : Z.Sent → Prop)
    (hZFC : ∀ β, ZFC β → Hm β) (eps : Z.Sent) (Tp : M.Code)
    (hTp : ∀ b, Ts (M := M) A.Sent Tp b ↔
      (A.BoolComb 2 b ∧ Z.Deriv (Z.ext Hm eps) (iAZ.i b)))
    (con : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A Tp)))
    (h3 : Z.Deriv (Z.ext Hm eps) con) :
    ¬ A.OneConsistent (Ts (M := M) A.Sent Tp) := by
  intro h1
  -- Theorem 5.11 for `Tp` and the deductive closure of `Hm ∪ {eps}`
  refine second_incompleteness_H iAZ ZFC (Z.closure (Z.ext Hm eps)) (Z.closed_closure _)
    (fun β hβ => Z.deriv_of_mem (Or.inl (hZFC β hβ))) Tp h1 (fun b hb hH => ?_) con hcon h3
  exact A.deriv_of_mem ((hTp b).2 ⟨hb, hH⟩)

/-- The graph of a map `f : 𝓐 → 𝓛` whose restriction to a computable `P` is computable is a reading
whose part on `P` is computable, hence `Σ⁰₂`. -/
theorem isReadingOn_graph {L : Language M} (f : A.Sent → L.Sent) {P : A.Sent → Prop}
    (hP : CompSet M P)
    (hf : @CompT M {α // P α} L.Sent (Enc.restrict P hP) L.enc (fun σ => f σ.1)) :
    IsReadingOn (M := M) P (fun (a : A.Sent) (α : L.Sent) => f a = α) := by
  have hg : CompT M (fun b : A.Sent => if P b then some (f b) else none) := by
    refine CompT.ofComp (Comp.ofRestrict hP (f := f) hf) ?_
    exact hP.congr fun b => by by_cases h : P b <;> simp [h]
  have hEq : CompSet M (fun p : A.Sent × L.Sent =>
      (if P p.1 then some (f p.1) else none) = some p.2) :=
    compSet_eq (hg.comp compT_fst) (compT_some.comp compT_snd)
  refine IsSigma2Set.of_compSet (hEq.congr fun p => ?_)
  by_cases h : P p.1 <;> simp [h]

section Paper

variable (iAZ : Translation A.toLanguage Z) (hB2 : CompSet M (A.BoolComb 2)) (eps : Z.Sent)
  (hf : @CompT M {b // A.BoolComb 2 b} Z.Sent (Enc.restrict (A.BoolComb 2) hB2) Z.enc
    (fun σ => Z.imp eps (iAZ.i σ.1)))

/-- The machine `T⁺ = Sh_R (T)` of the proof of Theorem A.2, for the reading `R = {(a, ε → a*)}`.
The hypothesis `hf` says that `a ↦ (ε → a*)` is computable on `𝓑₂`. -/
noncomputable def Tplus : M.Code → M.Code :=
  Shadow hB2 (isReadingOn_graph (fun a => Z.imp eps (iAZ.i a)) hB2 hf)

/-- `(T⁺)^s = {b ∈ 𝓑₂ | (ε → b*) ∈ T^s}`. -/
theorem Tplus_Ts (T : M.Code) (b : A.Sent) :
    Ts (M := M) A.Sent (Tplus iAZ hB2 eps hf T) b ↔
      A.BoolComb 2 b ∧ Ts (M := M) Z.Sent T (Z.imp eps (iAZ.i b)) := by
  unfold Tplus
  rw [Shadow_Ts]
  constructor
  · rintro ⟨hb, α, hα, rfl⟩
    exact ⟨hb, hα⟩
  · rintro ⟨hb, h⟩
    exact ⟨hb, _, h, rfl⟩

/-- Theorem A.2 (`theorem_penrose`), with `Con₁ (T₀⁺)*` in axiom (3).  `T₀` stably
enumerates `𝓗 = T₀^s`, which is deductively closed and contains `ZFC` (axiom (1)).  `con` satisfies
(5.12) for `T₀⁺`, and `ε → con` is in `𝓗`, with `con = Con₁ (T₀⁺)*`.  Then
`(T₀⁺)^s = {b ∈ 𝓑₂ | 𝓗 ∪ {ε} ⊢ b*}` is not `1`-consistent.  For axiom (3) as in the manuscript see
`penrose_family`. -/
theorem penrose_two_way (ZFC : Z.Sent → Prop) (T₀ : M.Code)
    (hcl : Z.Closed (Ts (M := M) Z.Sent T₀)) (hZFC : ∀ β, ZFC β → Ts (M := M) Z.Sent T₀ β)
    (con : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A (Tplus iAZ hB2 eps hf T₀))))
    (h3 : Ts (M := M) Z.Sent T₀ (Z.imp eps con)) :
    ¬ A.OneConsistent (Ts (M := M) A.Sent (Tplus iAZ hB2 eps hf T₀)) := by
  refine penrose_conditional iAZ ZFC (Ts (M := M) Z.Sent T₀) hZFC eps _ (fun b => ?_) con hcon
    (Z.deriv_ext_of_imp (Z.deriv_of_mem h3))
  rw [Tplus_Ts]
  constructor
  · rintro ⟨hb, h⟩
    exact ⟨hb, Z.deriv_ext_of_imp (Z.deriv_of_mem h)⟩
  · rintro ⟨hb, h⟩
    exact ⟨hb, hcl _ (Z.deriv_imp_intro h)⟩

/-- The set `{b ∈ 𝓑₂ | 𝓗 ∪ {ε} ⊢ b*}` of the statement of Theorem A.2 is `(T₀⁺)^s`. -/
theorem Tplus_Ts_closed (T₀ : M.Code) (hcl : Z.Closed (Ts (M := M) Z.Sent T₀)) (b : A.Sent) :
    Ts (M := M) A.Sent (Tplus iAZ hB2 eps hf T₀) b ↔
      A.BoolComb 2 b ∧ Z.Deriv (Z.ext (Ts (M := M) Z.Sent T₀) eps) (iAZ.i b) := by
  rw [Tplus_Ts]
  constructor
  · rintro ⟨hb, h⟩
    exact ⟨hb, Z.deriv_ext_of_imp (Z.deriv_of_mem h)⟩
  · rintro ⟨hb, h⟩
    exact ⟨hb, hcl _ (Z.deriv_imp_intro h)⟩

/-- Theorem A.2 (`theorem_penrose`) for a family with one member, in the form of the
versions of the manuscript before the last one of 12 November 2026.  `T₀` stably enumerates
`𝓗 = T₀^s`, which is deductively closed and contains `ZFC` (axiom (1)).  `enum`, `conδ ∈ 𝓩` stand
for the sentences `Enum (T₀⁺, δ + ε)` and `Con₁ (δ + ε)`, where `δ + ε` says: `x` is the code of
some `b ∈ 𝓑₂`, and `δ` holds of the code of `ε → b*`.  `henum`: `ZFC ∪ {ε} ⊢ enum`.  `hδ`:
`ZFC ∪ {enum, conδ} ⊢ con`, as in Corollary 5.13, with `con = Con₁ (T₀⁺)*`.  `h3`: `ε → conδ` is in
`𝓗`; this is axiom (3) for `T₀`.  Then `(T₀⁺)^s = {b ∈ 𝓑₂ | 𝓗 ∪ {ε} ⊢ b*}` is not `1`-consistent.
The proof applies Corollary 5.21 to `T₀` and `R' = {(z, ε → z)}`.  The
theory `H` of the corollary is `{z | (ε → z) ∈ 𝓗}`, the deductive closure of `𝓗 ∪ {ε}`. -/
theorem penrose_two_way_delta (ZFC : Z.Sent → Prop) (T₀ : M.Code)
    (hcl : Z.Closed (Ts (M := M) Z.Sent T₀)) (hZFC : ∀ β, ZFC β → Ts (M := M) Z.Sent T₀ β)
    (con enum conδ : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A (Tplus iAZ hB2 eps hf T₀))))
    (henum : Z.Deriv (Z.ext ZFC eps) enum)
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = conδ) con)
    (h3 : Ts (M := M) Z.Sent T₀ (Z.imp eps conδ)) :
    ¬ A.OneConsistent (Ts (M := M) A.Sent (Tplus iAZ hB2 eps hf T₀)) := by
  intro h1
  -- the theory `H` of Corollary 5.21, for `R' = {(z, ε → z)}` and `F₀ = 𝓗`
  have hH : ∀ z, Asserted (fun (z α : Z.Sent) => Z.imp eps z = α) (Ts (M := M) Z.Sent T₀) z ↔
      Ts (M := M) Z.Sent T₀ (Z.imp eps z) := by
    intro z
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact hα
    · exact fun h => ⟨_, h, rfl⟩
  refine reading_second_corollary (R' := fun (z α : Z.Sent) => Z.imp eps z = α)
    (F₀ := Ts (M := M) Z.Sent T₀) (P := A.BoolComb 2) (T := Tplus iAZ hB2 eps hf T₀) iAZ ZFC
    (fun _ hb => hb) (fun b => Shadow_Ts hB2 _ T₀ b) (fun z hz => ?_) (fun β hβ => ?_) h1
    con enum conδ hcon hδ ⟨?_, ?_⟩
  · -- `H` is deductively closed: it is the deductive closure of `𝓗 ∪ {ε}`
    refine (hH z).2 (hcl _ (Z.deriv_imp_intro (Z.deriv_cut (fun β hβ => ?_) hz)))
    exact Z.deriv_ext_of_imp (Z.deriv_of_mem ((hH β).1 hβ))
  · -- `H` contains `ZFC`, by axiom (1)
    exact (hH β).2 (hcl _ (Z.deriv_imp_intro (Z.deriv_of_mem (Or.inl (hZFC β hβ)))))
  · -- `enum ∈ H`, as `ZFC ⊂ 𝓗`
    refine (hH enum).2 (hcl _ (Z.deriv_imp_intro (Z.deriv_mono (fun β hβ => ?_) henum)))
    rcases hβ with hβ | rfl
    · exact Or.inl (hZFC β hβ)
    · exact Or.inr rfl
  · -- `conδ ∈ H`, by axiom (3)
    exact (hH conδ).2 h3

/-- Theorem A.2 (`theorem_penrose`), as in the manuscript: the Penrose property for a
family of theories.  `T₀` stably enumerates `𝓗 = T₀^s`, which is deductively closed and contains
`ZFC` (axiom (1)).  `eps ∈ 𝓩` stands for the sentence `ε_{T₀}`: `T₀` stably enumerates some member
of the family.  `pen ∈ 𝓩` stands for the sentence of axiom (3), or for its instance for `T₀`, and
`h3` says that it is in `𝓗`.  `hpen`: `ZFC ∪ {ε, pen} ⊢ con`, with `con = Con₁ (T₀⁺)*`.  The
manuscript proves this in two steps.  `ZFC` proves that the sentence of axiom (3) implies its
instance for `T₀`.  And `ZFC` proves that `ε` and this instance imply `con`, from the proof of
Corollary 5.13, applied with a parameter.  Then `(T₀⁺)^s = {b ∈ 𝓑₂ | 𝓗 ∪ {ε} ⊢ b*}` is not
`1`-consistent.  The proof applies Corollary 5.21 to `T₀` and `R' = {(z, ε → z)}`. -/
theorem penrose_family (ZFC : Z.Sent → Prop) (T₀ : M.Code)
    (hcl : Z.Closed (Ts (M := M) Z.Sent T₀)) (hZFC : ∀ β, ZFC β → Ts (M := M) Z.Sent T₀ β)
    (con pen : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A (Tplus iAZ hB2 eps hf T₀))))
    (hpen : Z.Deriv (fun β => ZFC β ∨ β = eps ∨ β = pen) con)
    (h3 : Ts (M := M) Z.Sent T₀ pen) :
    ¬ A.OneConsistent (Ts (M := M) A.Sent (Tplus iAZ hB2 eps hf T₀)) := by
  intro h1
  -- the theory `H` of Corollary 5.21, for `R' = {(z, ε → z)}` and `F₀ = 𝓗`
  have hH : ∀ z, Asserted (fun (z α : Z.Sent) => Z.imp eps z = α) (Ts (M := M) Z.Sent T₀) z ↔
      Ts (M := M) Z.Sent T₀ (Z.imp eps z) := by
    intro z
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact hα
    · exact fun h => ⟨_, h, rfl⟩
  refine reading_second (R' := fun (z α : Z.Sent) => Z.imp eps z = α)
    (F₀ := Ts (M := M) Z.Sent T₀) (P := A.BoolComb 2) (T := Tplus iAZ hB2 eps hf T₀) iAZ ZFC
    (fun _ hb => hb) (fun b => Shadow_Ts hB2 _ T₀ b) (fun z hz => ?_) (fun β hβ => ?_) h1
    con hcon ?_
  · -- `H` is deductively closed: it is the deductive closure of `𝓗 ∪ {ε}`
    refine (hH z).2 (hcl _ (Z.deriv_imp_intro (Z.deriv_cut (fun β hβ => ?_) hz)))
    exact Z.deriv_ext_of_imp (Z.deriv_of_mem ((hH β).1 hβ))
  · -- `H` contains `ZFC`, by axiom (1)
    exact (hH β).2 (hcl _ (Z.deriv_imp_intro (Z.deriv_of_mem (Or.inl (hZFC β hβ)))))
  · -- `con ∈ H`: `𝓗 ∪ {ε} ⊢ con`, as `ZFC ⊂ 𝓗` and `pen ∈ 𝓗` by axiom (3)
    refine (hH con).2 (hcl _ (Z.deriv_imp_intro (Z.deriv_cut (fun β hβ => ?_) hpen)))
    rcases hβ with hβ | rfl | rfl
    · exact Z.deriv_of_mem (Or.inl (hZFC β hβ))
    · exact Z.deriv_of_mem (Or.inr rfl)
    · exact Z.deriv_of_mem (Or.inl h3)

end Paper

end Stable
