import Stable.Plain
import Stable.Sigma2

/-!
# Other languages: readings (Section 5.2 of the restructured paper)

Let `𝓛` be an encoded set of utterances (a type `B` with `Enc M B`; no logical structure).

* A *reading* of `𝓛` (Definition 5.18) is a relation `R ⊂ 𝓐 × 𝓛`; `Asserted R F₀` is the set
  `F₀^R` of sentences asserted by `F₀ ⊂ 𝓛` under `R`.
* `IsReadingOn P R`: `R ∩ (P × 𝓛)` is a `Σ⁰₂` subset of `𝓐 × 𝓛`.  A `2`-reading is the case
  `P = 𝓑₂` (`IsTwoReading`).
* Lemma 5.19 (`exists_shadow`, `Shadow`): for a computable `P ⊂ 𝓐` and `R` with `IsReadingOn P R`
  there is a total computable `Sh : 𝒯 → 𝒯` with `Sh (T₀) ∈ 𝒯_𝓐`, `(Sh T₀)'` total, and
  `(Sh T₀)^s = (T₀^s)^R ∩ P`.  It is an instance of the stabilizer lemma, through
  `exists_stabMachine`, for the relation `RSh` below.
* Corollary 5.20 (`reading_first`) and Corollary 5.21 (`reading_second`,
  `reading_second_corollary`).

The paper takes `P = 𝓑₂` and uses that `𝓑₂` is a computable subset of `𝓐`.  The interface `Arith`
has no syntax from which to prove this, so the statements below are for a computable `P ⊇ 𝓑₂`;
with `P = 𝓑₂` they are the paper's statements, under the hypothesis `CompSet M (A.BoolComb 2)`
(`shadow_two`, `corollary_readingfirst`, `corollary_readingsecond`).
-/

namespace Stable

open Classical

/-- Definition 5.18: the set `F₀^R` of sentences asserted by `F₀` under the reading `R`. -/
def Asserted {X Y : Type} (R : X → Y → Prop) (F₀ : Y → Prop) : X → Prop :=
  fun a => ∃ α, F₀ α ∧ R a α

variable {M : TuringModel} {A : Arith M} {B : Type} [Enc M B]

/-- `R ∩ (P × 𝓛)` is a `Σ⁰₂` subset of `𝓐 × 𝓛`. -/
def IsReadingOn (P : A.Sent → Prop) (R : A.Sent → B → Prop) : Prop :=
  IsSigma2Set (M := M) (fun p : A.Sent × B => P p.1 ∧ R p.1 p.2)

/-- Definition 5.18: `R` is a `2`-reading of `𝓛`. -/
def IsTwoReading (A : Arith M) (R : A.Sent → B → Prop) : Prop :=
  IsReadingOn (M := M) (A.BoolComb 2) R

/-- The computable relation `R₀` fixed after Definition 5.18: `(b, α) ∈ R` iff
`∃ u ∀ v, (b, α, u, v) ∈ R₀`, for `b ∈ P`. -/
theorem IsReadingOn.exists_rel {P : A.Sent → Prop} {R : A.Sent → B → Prop}
    (h : IsReadingOn (M := M) P R) :
    ∃ R₀ : A.Sent → B → ℕ → ℕ → Prop,
      CompSet M (fun q : A.Sent × B × ℕ × ℕ => R₀ q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      ∀ b α, (P b ∧ R b α) ↔ ∃ u, ∀ v, R₀ b α u v := by
  obtain ⟨R', hR', h'⟩ := h
  refine ⟨fun b α u v => R' (e M (b, α)) u v, ?_, fun b α => ?_⟩
  · exact hR'.comp (CompT.pair (compT_e.comp (CompT.pair compT_fst (compT_fst.comp compT_snd)))
      (CompT.pair (compT_fst.comp (compT_snd.comp compT_snd))
        (compT_snd.comp (compT_snd.comp compT_snd))))
  · rw [← h' (e M (b, α))]
    constructor
    · intro hh; exact ⟨(b, α), rfl, hh⟩
    · rintro ⟨p, hp, hh⟩
      have hpe : p = (b, α) := Enc.inj hp
      rw [hpe] at hh
      exact hh

/-- The relation `R_Sh ⊂ 𝒯 × 𝓐 × ℕ × ℕ` of the proof of Lemma 5.19: `(T₀, b, u, v) ∈ R_Sh` iff
`b ∈ P`, `u = ⟨e (α), ⟨u₁, u₂⟩⟩` for some `α ∈ 𝓛`, and, writing `v = ⟨v₁, v₂⟩`,
`(T₀, α, u₁, v₁) ∈ R_𝓛` and `(b, α, u₂, v₂) ∈ R₀`. -/
def RSh (P : A.Sent → Prop) (R₀ : A.Sent → B → ℕ → ℕ → Prop) (T₀ : M.Code) (b : A.Sent)
    (u v : ℕ) : Prop :=
  P b ∧ ∃ α : B, e M α = (M.unpair u).1 ∧
    RB (M := M) B T₀ α (M.unpair (M.unpair u).2).1 (M.unpair v).1 ∧
    R₀ b α (M.unpair (M.unpair u).2).2 (M.unpair v).2

/-- `R_Sh` is computable. -/
theorem compSet_RSh {P : A.Sent → Prop} (hP : CompSet M P) {R₀ : A.Sent → B → ℕ → ℕ → Prop}
    (hR₀ : CompSet M (fun q : A.Sent × B × ℕ × ℕ => R₀ q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    CompSet M (fun q : M.Code × A.Sent × ℕ × ℕ => RSh P R₀ q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hb : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => q.2.1) := compT_fst.comp compT_snd
  have hu : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => q.2.2.1) :=
    compT_fst.comp (compT_snd.comp compT_snd)
  have hv : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => q.2.2.2) :=
    compT_snd.comp (compT_snd.comp compT_snd)
  have hcode : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => (M.unpair q.2.2.1).1) :=
    compT_unpair_fst.comp hu
  have hw : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => (M.unpair q.2.2.1).2) :=
    compT_unpair_snd.comp hu
  have hu1 : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => (M.unpair (M.unpair q.2.2.1).2).1) :=
    compT_unpair_fst.comp hw
  have hu2 : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => (M.unpair (M.unpair q.2.2.1).2).2) :=
    compT_unpair_snd.comp hw
  have hv1 : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => (M.unpair q.2.2.2).1) :=
    compT_unpair_fst.comp hv
  have hv2 : CompT M (fun q : M.Code × A.Sent × ℕ × ℕ => (M.unpair q.2.2.2).2) :=
    compT_unpair_snd.comp hv
  -- the condition on `(((T₀, b), ((u₁, u₂), (v₁, v₂))), α)`
  have hΦ : CompSet M (fun p : ((M.Code × A.Sent) × ((ℕ × ℕ) × (ℕ × ℕ))) × B =>
      RB (M := M) B p.1.1.1 p.2 p.1.2.1.1 p.1.2.2.1 ∧ R₀ p.1.1.2 p.2 p.1.2.1.2 p.1.2.2.2) := by
    refine CompSet.and ?_ ?_
    · exact (compSet_RB (B := B)).comp (CompT.pair (compT_fst.comp (compT_fst.comp compT_fst))
        (CompT.pair compT_snd (CompT.pair (compT_fst.comp (compT_fst.comp (compT_snd.comp compT_fst)))
          (compT_fst.comp (compT_snd.comp (compT_snd.comp compT_fst))))))
    · exact hR₀.comp (CompT.pair (compT_snd.comp (compT_fst.comp compT_fst))
        (CompT.pair compT_snd (CompT.pair (compT_snd.comp (compT_fst.comp (compT_snd.comp compT_fst)))
          (compT_snd.comp (compT_snd.comp (compT_snd.comp compT_fst))))))
  have hEx : CompSet M (fun q : M.Code × A.Sent × ℕ × ℕ =>
      ∃ α : B, e M α = (M.unpair q.2.2.1).1 ∧
        RB (M := M) B q.1 α (M.unpair (M.unpair q.2.2.1).2).1 (M.unpair q.2.2.2).1 ∧
        R₀ q.2.1 α (M.unpair (M.unpair q.2.2.1).2).2 (M.unpair q.2.2.2).2) :=
    (CompSet.exists_decode (Φ := fun (a : (M.Code × A.Sent) × ((ℕ × ℕ) × (ℕ × ℕ))) (α : B) =>
      RB (M := M) B a.1.1 α a.2.1.1 a.2.2.1 ∧ R₀ a.1.2 α a.2.1.2 a.2.2.2) hΦ).comp
      (CompT.pair (CompT.pair (CompT.pair compT_fst hb)
        (CompT.pair (CompT.pair hu1 hu2) (CompT.pair hv1 hv2))) hcode)
  exact ((hP.comp hb).and hEx).congr fun q => Iff.rfl

/-- `S_{R_Sh} (T₀) = {b ∈ P | (b, α) ∈ R for some α ∈ T₀^s}`, in terms of `R₀`. -/
theorem SR_RSh_iff (P : A.Sent → Prop) (R₀ : A.Sent → B → ℕ → ℕ → Prop) (T₀ : M.Code)
    (b : A.Sent) :
    SR (RSh (M := M) P R₀) T₀ b ↔
      P b ∧ ∃ α : B, TStable (M := M) T₀ α ∧ ∃ u, ∀ v, R₀ b α u v := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hPb, α, hα, -, -⟩ := hu 0
    refine ⟨hPb, α, ?_, (M.unpair (M.unpair u).2).2, fun v₂ => ?_⟩
    · rw [tStable_iff_SR_RB]
      refine ⟨(M.unpair (M.unpair u).2).1, fun v₁ => ?_⟩
      obtain ⟨-, α', hα', h1, -⟩ := hu (M.pair v₁ 0)
      rw [M.unpair_pair] at h1
      have hαα : α' = α := Enc.inj (hα'.trans hα.symm)
      rw [hαα] at h1
      exact h1
    · obtain ⟨-, α', hα', -, h2⟩ := hu (M.pair 0 v₂)
      rw [M.unpair_pair] at h2
      have hαα : α' = α := Enc.inj (hα'.trans hα.symm)
      rw [hαα] at h2
      exact h2
  · rintro ⟨hPb, α, hα, u₂, hu₂⟩
    rw [tStable_iff_SR_RB] at hα
    obtain ⟨u₁, hu₁⟩ := hα
    refine ⟨M.pair (e M α) (M.pair u₁ u₂), fun v => ⟨hPb, α, ?_, ?_, ?_⟩⟩
    · rw [M.unpair_pair]
    · rw [M.unpair_pair, M.unpair_pair]
      exact hu₁ _
    · rw [M.unpair_pair, M.unpair_pair]
      exact hu₂ _

/-- Lemma 5.19 (`lemma_shadow`): for a computable `P ⊂ 𝓐` and a reading `R` whose part on `P` is
`Σ⁰₂`, there is a total computable `Sh : 𝒯 → 𝒯` s.t. for every `T₀`: `Sh (T₀) ∈ 𝒯_𝓐`, `(Sh T₀)'` is
total, and `(Sh T₀)^s = (T₀^s)^R ∩ P`.  (`T₀^s` is read as in Remark 3.17, so no hypothesis
`T₀ ∈ 𝒯_𝓛` is needed.) -/
theorem exists_shadow {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsReadingOn (M := M) P R) :
    ∃ Sh : M.Code → M.Code, CompT M Sh ∧ ∀ T₀,
      InTB (M := M) A.Sent (Sh T₀) ∧ (∀ n, seqOf (M := M) A.Sent (Sh T₀) n ≠ none) ∧
      ∀ b, Ts (M := M) A.Sent (Sh T₀) b ↔ P b ∧ Asserted R (Ts (M := M) B T₀) b := by
  obtain ⟨R₀, hR₀, hR₀'⟩ := hR.exists_rel
  obtain ⟨Sh, hSh, hSh'⟩ :=
    exists_stabMachine (M := M) (B := A.Sent) A.infinite (compSet_RSh hP hR₀)
  refine ⟨Sh, hSh, fun T₀ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hSh' T₀
  refine ⟨h1, h2, fun b => ?_⟩
  rw [Ts_def, h3, SR_RSh_iff]
  constructor
  · rintro ⟨hPb, α, hα, hu⟩
    exact ⟨hPb, α, hα, ((hR₀' b α).2 hu).2⟩
  · rintro ⟨hPb, α, hα, hRbα⟩
    exact ⟨hPb, α, hα, (hR₀' b α).1 ⟨hPb, hRbα⟩⟩

/-- The map `Sh_R` of Lemma 5.19. -/
noncomputable def Shadow {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsReadingOn (M := M) P R) : M.Code → M.Code := choose (exists_shadow hP hR)

theorem Shadow_compT {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsReadingOn (M := M) P R) : CompT M (Shadow hP hR) :=
  (choose_spec (exists_shadow hP hR)).1

theorem Shadow_inTB {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsReadingOn (M := M) P R) (T₀ : M.Code) : InTB (M := M) A.Sent (Shadow hP hR T₀) :=
  ((choose_spec (exists_shadow hP hR)).2 T₀).1

/-- `(Sh_R T₀)^s = (T₀^s)^R ∩ P`. -/
theorem Shadow_Ts {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsReadingOn (M := M) P R) (T₀ : M.Code) (b : A.Sent) :
    Ts (M := M) A.Sent (Shadow hP hR T₀) b ↔ P b ∧ Asserted R (Ts (M := M) B T₀) b :=
  ((choose_spec (exists_shadow hP hR)).2 T₀).2.2 b

/-! ### Corollary 5.20 -/

section First

variable {Y : Type} {P : A.Sent → Prop} (hPB : ∀ b, A.BoolComb 2 b → P b) {R : A.Sent → Y → Prop}
  {F₀ : Y → Prop} {T : M.Code}
  (hT : ∀ b, Ts (M := M) A.Sent T b ↔ P b ∧ Asserted R F₀ b)
  (hcl : A.toLanguage.Closed (Asserted R F₀))

include hPB hT hcl

/-- For `b ∈ 𝓑₂`: `T^s ⊢ b` iff `b ∈ F₀^R`, when `T^s = F₀^R ∩ P` and `F₀^R` is deductively closed. -/
theorem deriv_shadow_iff {b : A.Sent} (hb : A.BoolComb 2 b) :
    A.Deriv (Ts (M := M) A.Sent T) b ↔ Asserted R F₀ b :=
  ⟨fun h => hcl b (A.deriv_mono (fun β hβ => ((hT β).1 hβ).2) h),
    fun h => A.deriv_of_mem ((hT b).2 ⟨hPB b hb, h⟩)⟩

/-- `T^s` is `1`-consistent if `F₀^R` is. -/
theorem oneConsistent_shadow (h : A.OneConsistent (Asserted R F₀)) :
    A.OneConsistent (Ts (M := M) A.Sent T) := by
  obtain ⟨hQ, h1⟩ := h
  refine ⟨fun q hq => (deriv_shadow_iff hPB hT hcl (Arith.BoolComb.axQ hq)).2 (hcl q (hQ q hq)),
    fun σ hσ hd => ?_⟩
  have hσ2 : A.BoolComb 2 σ := Arith.BoolComb.sigma (A.sigma_succ 1 σ hσ)
  obtain ⟨v, hv⟩ := h1 σ hσ (A.deriv_of_mem ((deriv_shadow_iff hPB hT hcl hσ2).1 hd))
  have h0 : A.IsSigma 0 (A.instS σ v) := (A.sigma_zero_iff_pi_zero _).2 (A.instS_pi 0 σ v hσ)
  have hneg : A.BoolComb 2 (A.neg (A.instS σ v)) :=
    Arith.BoolComb.neg (Arith.BoolComb.sigma (A.sigma_of_delta0 h0 2))
  exact ⟨v, fun hd' => hv (A.deriv_of_mem ((deriv_shadow_iff hPB hT hcl hneg).1 hd'))⟩

/-- `T^s` is `2`-consistent if `F₀^R` is. -/
theorem twoConsistent_shadow (h : A.TwoConsistent (Asserted R F₀)) :
    A.TwoConsistent (Ts (M := M) A.Sent T) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨oneConsistent_shadow hPB hT hcl h1, fun σ hσ hd => ?_⟩
  have hσ2 : A.BoolComb 2 σ := Arith.BoolComb.sigma hσ
  obtain ⟨v, hv⟩ := h2 σ hσ (A.deriv_of_mem ((deriv_shadow_iff hPB hT hcl hσ2).1 hd))
  have hneg : A.BoolComb 2 (A.neg (A.instS σ v)) :=
    Arith.BoolComb.neg (Arith.BoolComb.sigma (A.pi_sigma_succ 1 _ (A.instS_pi 1 σ v hσ)))
  exact ⟨v, fun hd' => hv (A.deriv_of_mem ((deriv_shadow_iff hPB hT hcl hneg).1 hd'))⟩

/-- Corollary 5.20 (`corollary_readingfirst`), for a machine `T` with `T^s = F₀^R ∩ P`, `P ⊇ 𝓑₂`,
and `F₀^R` deductively closed: (1) `𝒢 (T) ∉ F₀^R` if `F₀^R` is `1`-consistent;
(2) `¬𝒢 (T) ∉ F₀^R` if `F₀^R` is `2`-consistent; (3) `ℕ ⊨ 𝒢 (T)` if `F₀^R` is `1`-consistent. -/
theorem reading_first :
    (A.OneConsistent (Asserted R F₀) → ¬ Asserted R F₀ (G₀ A T)) ∧
    (A.TwoConsistent (Asserted R F₀) → ¬ Asserted R F₀ (A.neg (G₀ A T))) ∧
    (A.OneConsistent (Asserted R F₀) → A.TrueN (G₀ A T)) := by
  refine ⟨fun h hg => ?_, fun h hg => ?_, fun h => ?_⟩
  · exact A.not_deriv_G₀ T (oneConsistent_shadow hPB hT hcl h)
      ((deriv_shadow_iff hPB hT hcl (A.G₀_boolComb T)).2 hg)
  · exact A.not_deriv_neg_G₀ T (twoConsistent_shadow hPB hT hcl h)
      ((deriv_shadow_iff hPB hT hcl (Arith.BoolComb.neg (A.G₀_boolComb T))).2 hg)
  · exact A.trueN_G₀ T (oneConsistent_shadow hPB hT hcl h)

end First

/-! ### Corollary 5.21 -/

section Second

variable {Z : Language M} {Y : Type} (iAZ : Translation A.toLanguage Z) (ZFC : Z.Sent → Prop)
  {P : A.Sent → Prop} {R' : Z.Sent → Y → Prop} {F₀ : Y → Prop} {T : M.Code}

/-- Corollary 5.21 (`corollary_readingsecond`), first assertion, abstract form.  `R' ⊂ 𝓩 × 𝓛` is a
reading in set theory, `H = F₀^{R'}` is deductively closed and contains `ZFC`, and `T` is a machine
with `T^s = {b ∈ P | b* ∈ H}`, `P ⊇ 𝓑₂`, and `T^s` `1`-consistent.  With (5.12) as the hypothesis
`hcon`: `con ∉ H`. -/
theorem reading_second
    (hPB : ∀ b, A.BoolComb 2 b → P b)
    (hT : ∀ b, Ts (M := M) A.Sent T b ↔ P b ∧ Asserted (fun a α => R' (iAZ.i a) α) F₀ b)
    (hH : Z.Closed (Asserted R' F₀)) (hZFC : ∀ β, ZFC β → Asserted R' F₀ β)
    (h1 : A.OneConsistent (Ts (M := M) A.Sent T)) (con : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A T))) : ¬ Asserted R' F₀ con :=
  second_incompleteness_H iAZ ZFC (Asserted R' F₀) hH hZFC T h1
    (fun b hb hHb => A.deriv_of_mem ((hT b).2 ⟨hPB b hb, hHb⟩)) con hcon

/-- Corollary 5.21, second assertion: `H` does not contain both `Enum (T, δ)` and `Con₁ (δ)`. -/
theorem reading_second_corollary
    (hPB : ∀ b, A.BoolComb 2 b → P b)
    (hT : ∀ b, Ts (M := M) A.Sent T b ↔ P b ∧ Asserted (fun a α => R' (iAZ.i a) α) F₀ b)
    (hH : Z.Closed (Asserted R' F₀)) (hZFC : ∀ β, ZFC β → Asserted R' F₀ β)
    (h1 : A.OneConsistent (Ts (M := M) A.Sent T)) (con enum conδ : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A T)))
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = conδ) con) :
    ¬ (Asserted R' F₀ enum ∧ Asserted R' F₀ conδ) :=
  second_incompleteness_H_corollary iAZ ZFC (Asserted R' F₀) hH hZFC T h1
    (fun b hb hHb => A.deriv_of_mem ((hT b).2 ⟨hPB b hb, hHb⟩)) con enum conδ hcon hδ

/-- The last paragraph of Remark A.3, for a reading, in abstract form.  (It was Theorem A.2 in the
manuscript before the Penrose property took its present form, for which see `Stable.Penrose`.)
`𝓗 = F₀` is the set of stable utterances, `𝓗_𝓩 = F₀^{R'}`, and `T = Sh_R (T₀)` presents
`𝓗₂ = {b ∈ 𝓑₂ | b* ∈ 𝓗_𝓩}`.  Given that `𝓗_𝓩` is deductively closed, contains `ZFC`, and contains
`Con₁ (δ)`: either `𝓗₂` is not `1`-consistent, or the sentence `Enum (Sh_R (T₀), δ)` is not in
`𝓗_𝓩`. -/
theorem penrose_reading
    (hPB : ∀ b, A.BoolComb 2 b → P b)
    (hT : ∀ b, Ts (M := M) A.Sent T b ↔ P b ∧ Asserted (fun a α => R' (iAZ.i a) α) F₀ b)
    (hH : Z.Closed (Asserted R' F₀)) (hZFC : ∀ β, ZFC β → Asserted R' F₀ β)
    (con enum conδ : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A T)))
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = conδ) con)
    (hpenrose : Asserted R' F₀ conδ) :
    ¬ A.OneConsistent (Ts (M := M) A.Sent T) ∨ ¬ Asserted R' F₀ enum := by
  by_cases h1 : A.OneConsistent (Ts (M := M) A.Sent T)
  · right
    intro henum
    exact reading_second_corollary iAZ ZFC hPB hT hH hZFC h1 con enum conδ hcon hδ ⟨henum, hpenrose⟩
  · exact Or.inl h1

end Second

/-! ### The statements of the paper, for `P = 𝓑₂` -/

section Paper

variable (hB2 : CompSet M (A.BoolComb 2))

/-- Lemma 5.19 for a `2`-reading: `(Sh_R T₀)^s = (T₀^s)^R ∩ 𝓑₂`. -/
theorem shadow_two {R : A.Sent → B → Prop} (hR : IsTwoReading A R) (T₀ : M.Code) (b : A.Sent) :
    Ts (M := M) A.Sent (Shadow hB2 hR T₀) b ↔
      A.BoolComb 2 b ∧ Asserted R (Ts (M := M) B T₀) b := Shadow_Ts hB2 hR T₀ b

/-- Corollary 5.20 (`corollary_readingfirst`). -/
theorem corollary_readingfirst {R : A.Sent → B → Prop} (hR : IsTwoReading A R) (T₀ : M.Code)
    (hcl : A.toLanguage.Closed (Asserted R (Ts (M := M) B T₀))) :
    (A.OneConsistent (Asserted R (Ts (M := M) B T₀)) →
      ¬ Asserted R (Ts (M := M) B T₀) (G₀ A (Shadow hB2 hR T₀))) ∧
    (A.TwoConsistent (Asserted R (Ts (M := M) B T₀)) →
      ¬ Asserted R (Ts (M := M) B T₀) (A.neg (G₀ A (Shadow hB2 hR T₀)))) ∧
    (A.OneConsistent (Asserted R (Ts (M := M) B T₀)) → A.TrueN (G₀ A (Shadow hB2 hR T₀))) :=
  reading_first (fun _ hb => hb) (Shadow_Ts hB2 hR T₀) hcl

/-- Corollary 5.21 (`corollary_readingsecond`), with (5.12) as the hypothesis `hcon`. -/
theorem corollary_readingsecond {Z : Language M} (iAZ : Translation A.toLanguage Z)
    (ZFC : Z.Sent → Prop) {R' : Z.Sent → B → Prop}
    (hR : IsTwoReading A (fun a α => R' (iAZ.i a) α)) (T₀ : M.Code)
    (hH : Z.Closed (Asserted R' (Ts (M := M) B T₀)))
    (hZFC : ∀ β, ZFC β → Asserted R' (Ts (M := M) B T₀) β)
    (h1 : A.OneConsistent (Ts (M := M) A.Sent (Shadow hB2 hR T₀))) (con : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A (Shadow hB2 hR T₀)))) :
    ¬ Asserted R' (Ts (M := M) B T₀) con :=
  reading_second iAZ ZFC (fun _ hb => hb) (Shadow_Ts hB2 hR T₀) hH hZFC h1 con hcon

end Paper

end Stable
