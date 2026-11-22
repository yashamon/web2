import Stable.NPlain
import Stable.NSpec
import Stable.NSigma

/-!
# Readings at level `n` (the last paragraph of Section 6.3 of the restructured paper)

Paper level `n = m + 1`.

* `NSR_and_absorb`: a conjunction of two conditions of the form of Lemma 6.2 is of this form
  ("the variables of the two prefixes are paired quantifier by quantifier").
* `IsNReadingOn m P R`: `R ∩ (P × 𝓛)` is a `Σ⁰_{m+2}` subset of `𝓐 × 𝓛`; an `(n+1)`-reading is the
  case `P = 𝓑ₙ₊₁`.
* `exists_nShadow`, `NShadow`: the map `Shⁿ_R`, with `(Shⁿ_R T₀)^{sₙ} = (T₀^{sₙ})^R ∩ P`.
* `n_corollary_readingfirst`, `n_corollary_readingsecond`: Corollaries 5.20 and 5.21 at level `n`,
  for `P = 𝓑ₙ₊₁` under the hypothesis that `𝓑ₙ₊₁` is a computable subset of `𝓐`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

section And

variable {A B : Type} [Enc M A] [Enc M B]

/-- A conjunction of two `Σ⁰_{m+2}` conditions, by pairing the quantified variables. -/
theorem NSR_and_absorb (m : ℕ) (R₁ R₂ : NRel A B m) (h₁ : NRelComp (M := M) m R₁)
    (h₂ : NRelComp (M := M) m R₂) :
    ∃ R' : NRel A B m, NRelComp (M := M) m R' ∧
      ∀ a b, NSR m R' a b ↔ NSR m R₁ a b ∧ NSR m R₂ a b := by
  cases m with
  | zero =>
    refine ⟨fun a b u v => R₁ a b (M.unpair u).1 (M.unpair v).1 ∧
      R₂ a b (M.unpair u).2 (M.unpair v).2, ?_, fun a b => ?_⟩
    · have hu : CompT M (fun q : A × B × ℕ × ℕ => q.2.2.1) :=
        compT_fst.comp (compT_snd.comp compT_snd)
      have hv : CompT M (fun q : A × B × ℕ × ℕ => q.2.2.2) :=
        compT_snd.comp (compT_snd.comp compT_snd)
      have hb : CompT M (fun q : A × B × ℕ × ℕ => q.2.1) := compT_fst.comp compT_snd
      exact (h₁.comp (CompT.pair compT_fst (CompT.pair hb
          (CompT.pair (compT_unpair_fst.comp hu) (compT_unpair_fst.comp hv))))).and
        (h₂.comp (CompT.pair compT_fst (CompT.pair hb
          (CompT.pair (compT_unpair_snd.comp hu) (compT_unpair_snd.comp hv)))))
    · constructor
      · rintro ⟨u, hu⟩
        refine ⟨⟨(M.unpair u).1, fun v => ?_⟩, ⟨(M.unpair u).2, fun v => ?_⟩⟩
        · have h := (hu (M.pair v 0)).1
          rw [M.unpair_pair] at h
          exact h
        · have h := (hu (M.pair 0 v)).2
          rw [M.unpair_pair] at h
          exact h
      · rintro ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩
        refine ⟨M.pair u₁ u₂, fun v => ?_⟩
        show R₁ a b (M.unpair (M.pair u₁ u₂)).1 (M.unpair v).1 ∧
          R₂ a b (M.unpair (M.pair u₁ u₂)).2 (M.unpair v).2
        rw [M.unpair_pair]
        exact ⟨hu₁ _, hu₂ _⟩
  | succ m =>
    -- `NSR (m+1) R a b = ∃ u, ¬ NSR m (compl R) a (b, u)`; a conjunction of two such conditions
    -- is `∃ u, ¬ (N₁ (b, u.1) ∨ N₂ (b, u.2))`, and the disjunction is absorbed at level `m`
    obtain ⟨S₁, hS₁, e₁⟩ := NSR_comp_base (M := M) (B := B × ℕ) (C := B × ℕ) m (compl R₁) h₁.compl
      (f := fun p => (p.1, (M.unpair p.2).1)) (CompT.pair compT_fst (compT_unpair_fst.comp compT_snd))
    obtain ⟨S₂, hS₂, e₂⟩ := NSR_comp_base (M := M) (B := B × ℕ) (C := B × ℕ) m (compl R₂) h₂.compl
      (f := fun p => (p.1, (M.unpair p.2).2)) (CompT.pair compT_fst (compT_unpair_snd.comp compT_snd))
    obtain ⟨S, hS, eS⟩ := NSR_or_absorb (M := M) (B := B × ℕ) m S₁ S₂ hS₁ hS₂
    refine ⟨compl S, hS.compl, fun a b => ?_⟩
    have key : ∀ u, NSR m (compl (compl S)) a (b, u) ↔
        NSR m (compl R₁) a (b, (M.unpair u).1) ∨ NSR m (compl R₂) a (b, (M.unpair u).2) :=
      fun u => (NSR_congr m (fun _ _ _ _ => Classical.not_not) a (b, u)).trans
        ((eS a (b, u)).trans (or_congr (e₁ a (b, u)) (e₂ a (b, u))))
    show (∃ u, ¬ NSR m (compl (compl S)) a (b, u)) ↔
      (∃ u, ¬ NSR m (compl R₁) a (b, u)) ∧ (∃ u, ¬ NSR m (compl R₂) a (b, u))
    constructor
    · rintro ⟨u, hu⟩
      rw [key] at hu
      exact ⟨⟨(M.unpair u).1, fun h => hu (Or.inl h)⟩, ⟨(M.unpair u).2, fun h => hu (Or.inr h)⟩⟩
    · rintro ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩
      refine ⟨M.pair u₁ u₂, fun h => ?_⟩
      rw [key, M.unpair_pair] at h
      rcases h with h | h
      · exact hu₁ h
      · exact hu₂ h

end And

variable {A : Arith M} {B : Type} [Enc M B]

/-- `R ∩ (P × 𝓛)` is a `Σ⁰_{m+2}` subset of `𝓐 × 𝓛`. -/
def IsNReadingOn (m : ℕ) (P : A.Sent → Prop) (R : A.Sent → B → Prop) : Prop :=
  IsSigmaNSet (M := M) m (fun p : A.Sent × B => P p.1 ∧ R p.1 p.2)

/-- `R` is an `(n+1)`-reading of `𝓛`, `n = m + 1` (Section 6.3). -/
def IsNReading (A : Arith M) (m : ℕ) (R : A.Sent → B → Prop) : Prop :=
  IsNReadingOn (M := M) m (A.BoolComb (m + 2)) R

/-- The map `Shⁿ_R` of Section 6.3, `n = m + 1`: for a computable `P ⊂ 𝓐` and a reading `R` whose
part on `P` is `Σ⁰ₙ₊₁`, a total computable `Sh : 𝒯 → 𝒯` with `Sh (T₀) ∈ 𝒯ⁿ_𝓐`, `(Sh T₀)'` total, and
`(Sh T₀)^{sₙ} = (T₀^{sₙ})^R ∩ P`. -/
theorem exists_nShadow (m : ℕ) {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsNReadingOn (M := M) m P R) :
    ∃ Sh : M.Code → M.Code, CompT M Sh ∧ ∀ T₀,
      InTB (M := M) A.Sent (Sh T₀) ∧ (∀ y, nseqOf (M := M) m A.Sent (Sh T₀) y ≠ none) ∧
      ∀ b, NTs (M := M) m A.Sent (Sh T₀) b ↔ P b ∧ Asserted R (NTs (M := M) m B T₀) b := by
  obtain ⟨R₀, hR₀, hR₀'⟩ := hR
  -- `R₁`: `α ∈ T₀^{sₙ}`, as a condition on `(T₀, (b, α))`
  have hR₁ : NRelComp (M := M) m (complPow m (RBase (M := M) m B)) :=
    (nRelComp_RBase (M := M) (B := B) m).complPow m
  obtain ⟨R₁', hR₁', e₁⟩ := NSR_comp_base (M := M) (A := M.Code) (B := A.Sent × B) m _ hR₁
    (f := fun p => p.2) compT_snd
  -- `R₀'`: `(b, α) ∈ R`, for `b ∈ P`, with the parameter `T₀` carried along
  have hR₀'' : NRelComp (M := M) m (fun (_ : M.Code) (x : NB (A.Sent × B) m) u v => R₀ () x u v) :=
    hR₀.comp (CompT.pair (compT_const ()) compT_snd)
  obtain ⟨R₂, hR₂, e₂⟩ := NSR_and_absorb (M := M) m R₁' _ hR₁' hR₀''
  obtain ⟨R₃, hR₃, e₃⟩ := NSR_exists_absorb (M := M) m R₂ hR₂
  obtain ⟨R₄, hR₄, e₄⟩ := NSR_and_dec (M := M) m R₃ hR₃ hP
  obtain ⟨Sh, hSh, hSh'⟩ := exists_nStabMachine (M := M) m A.infinite hR₄
  refine ⟨Sh, hSh, fun T₀ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hSh' T₀
  refine ⟨h1, h2, fun b => ?_⟩
  rw [h3, e₄, e₃]
  refine and_congr_right fun hPb => exists_congr fun α => ?_
  rw [e₂, e₁, NSR_param_const, ← NTs_iff_NSR, ← hR₀' (b, α)]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hPb, h.2⟩⟩

/-- The map `Shⁿ_R`. -/
noncomputable def NShadow (m : ℕ) {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsNReadingOn (M := M) m P R) : M.Code → M.Code := choose (exists_nShadow m hP hR)

theorem NShadow_compT (m : ℕ) {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsNReadingOn (M := M) m P R) : CompT M (NShadow m hP hR) :=
  (choose_spec (exists_nShadow m hP hR)).1

/-- `(Shⁿ_R T₀)^{sₙ} = (T₀^{sₙ})^R ∩ P`. -/
theorem NShadow_NTs (m : ℕ) {P : A.Sent → Prop} (hP : CompSet M P) {R : A.Sent → B → Prop}
    (hR : IsNReadingOn (M := M) m P R) (T₀ : M.Code) (b : A.Sent) :
    NTs (M := M) m A.Sent (NShadow m hP hR T₀) b ↔
      P b ∧ Asserted R (NTs (M := M) m B T₀) b :=
  ((choose_spec (exists_nShadow m hP hR)).2 T₀).2.2 b

/-! ### Corollaries 5.20 and 5.21 at level `n`, for `P = 𝓑ₙ₊₁` -/

section Paper

variable (m : ℕ) (hBn : CompSet M (A.BoolComb (m + 2)))

/-- Corollary 5.20 at level `n = m + 1`. -/
theorem n_corollary_readingfirst {R : A.Sent → B → Prop} (hR : IsNReading A m R) (T₀ : M.Code)
    (hcl : A.toLanguage.Closed (Asserted R (NTs (M := M) m B T₀))) :
    (A.SigmaSound (m + 1) (Asserted R (NTs (M := M) m B T₀)) →
      ¬ Asserted R (NTs (M := M) m B T₀) (NG₀ A m (NShadow m hBn hR T₀)) ∧
        A.TrueN (NG₀ A m (NShadow m hBn hR T₀))) ∧
    (A.SigmaSound (m + 2) (Asserted R (NTs (M := M) m B T₀)) →
      ¬ Asserted R (NTs (M := M) m B T₀) (A.neg (NG₀ A m (NShadow m hBn hR T₀)))) :=
  n_reading_first m (fun _ hb => hb) (NShadow_NTs m hBn hR T₀) hcl

/-- Corollary 5.21 at level `n = m + 1`, with the `ZFC`-formalization of Theorem 6.8 (1) as the
hypothesis `hsnd`. -/
theorem n_corollary_readingsecond {Z : Language M} (iAZ : Translation A.toLanguage Z)
    (ZFC : Z.Sent → Prop) {R' : Z.Sent → B → Prop}
    (hR : IsNReading A m (fun a α => R' (iAZ.i a) α)) (T₀ : M.Code)
    (hH : Z.Closed (Asserted R' (NTs (M := M) m B T₀)))
    (hZFC : ∀ β, ZFC β → Asserted R' (NTs (M := M) m B T₀) β)
    (h1 : A.SigmaSound (m + 1) (NTs (M := M) m A.Sent (NShadow m hBn hR T₀))) (snd : Z.Sent)
    (hsnd : Z.Deriv (fun β => ZFC β ∨ β = snd) (iAZ.i (NG₀ A m (NShadow m hBn hR T₀)))) :
    ¬ Asserted R' (NTs (M := M) m B T₀) snd :=
  n_reading_second iAZ ZFC m (fun _ hb => hb) (NShadow_NTs m hBn hR T₀) hH hZFC h1 snd hsnd

end Paper

end Stable
