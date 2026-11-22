import Stable.NMachines
import Stable.NTruth
import Stable.SoundCons

/-!
# `Spec^{m+1}`: the speculative closure at level `n = m+1` (Section 6.2)

For an `(m+2)`-translation `i : 𝓐 → 𝓛` there is a total computable `Spec^{m+1}_i : 𝒯 → 𝒯` with
`Spec T ∈ 𝒯^{m+1}_𝓛`, `(Spec T)'` total and `(m+1)`-speculative (it proves, under `i`, every true
`Π⁰_{m+1}` sentence), and `(Spec T)^{s_{m+1}} = T^{s_{m+1}} ∪ i (Tr_{Π_{m+1}})`; if `T^{s_{m+1}}` is
`Σ_{m+1}`-sound then `(Spec T)^{s_{m+1}}` is consistent (Lemma 6.6 (3)).
-/

namespace Stable

open Classical

variable {M : TuringModel} {A : Arith M} {L : Language M} (i : Translation A.toLanguage L)

/-- `M : ℕ^{m+1} → 𝓛 × {±}` is `(m+1)`-speculative with respect to `i`: `M^{s_{m+1}} ⊢ⁱ π` for every
`π ∈ Tr_{Π_{m+1}}`. -/
def NSpeculative (m : ℕ) (Mp : NB ℕ m → Option (L.Sent × Bool)) : Prop :=
  ∀ π, A.TrPi (m + 1) π → i.DerivI (fun b => NStable m Mp b) π

/-- An `(m+2)`-translation is computable on a computable subclass of the `Σ⁰_{m+2}` sentences. -/
theorem Translation.compT_on_sub {P : A.Sent → Prop} (hP : CompSet M P) {n : ℕ}
    (hPsub : ∀ α, P α → A.IsSigma n α) (h : i.IsNTranslation n) :
    @CompT M {α // P α} L.Sent (Enc.restrict P hP) L.enc (fun σ => i.i σ.1) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun σ => hT ⟨σ.1, hPsub σ.1 σ.2⟩⟩

/-- `(x, π) ↦ (π ∈ Π⁰_{m+1} ∧ x = i π)` is a computable relation for an `(m+2)`-translation `i`. -/
theorem compSet_isPi_eq (m : ℕ) (hi : i.IsNTranslation (m + 2)) :
    CompSet M (fun p : L.Sent × A.Sent => A.IsPi (m + 1) p.2 ∧ p.1 = i.i p.2) := by
  have hg : CompT M (fun π : A.Sent => if A.IsPi (m + 1) π then some (i.i π) else none) := by
    refine CompT.ofComp (Comp.ofRestrict (A.pi_comp (m + 1)) (f := i.i)
      (i.compT_on_sub (A.pi_comp (m + 1)) (A.pi_sigma_succ (m + 1)) hi)) ?_
    exact (A.pi_comp (m + 1)).congr fun π => by by_cases h : A.IsPi (m + 1) π <;> simp [h]
  have hEq : CompSet M (fun p : L.Sent × A.Sent =>
      some p.1 = if A.IsPi (m + 1) p.2 then some (i.i p.2) else none) :=
    compSet_eq (compT_some.comp compT_fst) (hg.comp compT_snd)
  refine hEq.congr fun p => ?_
  by_cases h : A.IsPi (m + 1) p.2
  · rw [ite_eq_left h]
    exact ⟨fun h1 => ⟨h, Option.some.inj h1⟩, fun h1 => congrArg some h1.2⟩
  · rw [ite_eq_right h]
    exact ⟨fun h1 => absurd h1 (Option.some_ne_none _), fun h1 => absurd h1.1 h⟩

/-- `Spec^{m+1}_i` (Theorem 3.25 at level `m+1`). -/
theorem exists_nSpec (m : ℕ) (hi : i.IsNTranslation (m + 2)) :
    ∃ Spec : M.Code → M.Code, CompT M Spec ∧ ∀ T,
      InTB (M := M) L.Sent (Spec T) ∧ (∀ y, nseqOf (M := M) m L.Sent (Spec T) y ≠ none) ∧
      NSpeculative i m (nseqOf (M := M) m L.Sent (Spec T)) ∧
      (∀ x, NTs (M := M) m L.Sent (Spec T) x ↔ specExtN i (m + 1) (NTs (M := M) m L.Sent T) x) ∧
      (i.SigmaSound (m + 1) (NTs (M := M) m L.Sent T) → L.Consistent (NTs (M := M) m L.Sent (Spec T))) := by
  -- `R₁`: `x ∈ T^{s_{m+1}}`
  have hR₁ : NRelComp (M := M) m (complPow m (RBase (M := M) m L.Sent)) :=
    (nRelComp_RBase (M := M) (B := L.Sent) m).complPow m
  -- `R₂`: `∃ π, (π ∈ Π⁰_{m+1} ∧ x = i π) ∧ ℕ ⊨ π`
  obtain ⟨RT, hRT, hRT'⟩ := exists_trPi (M := M) A m
  have hRT₂ : NRelComp (M := M) m (fun (_ : M.Code) (x : NB A.Sent m) u v => RT () x u v) :=
    hRT.comp (CompT.pair (compT_const ()) compT_snd)
  obtain ⟨R₂a, hR₂a, h₂a⟩ := NSR_comp_base (M := M) (B := L.Sent × A.Sent) m _ hRT₂
    (f := fun p => p.2) compT_snd
  obtain ⟨R₂b, hR₂b, h₂b⟩ := NSR_and_dec (M := M) m R₂a hR₂a (compSet_isPi_eq i m hi)
  obtain ⟨R₂, hR₂, h₂⟩ := NSR_exists_absorb (M := M) m R₂b hR₂b
  obtain ⟨R₃, hR₃, h₃⟩ := NSR_or_absorb (M := M) m _ R₂ hR₁ hR₂
  obtain ⟨Spec, hSpec, hSpec'⟩ := exists_nStabMachine (M := M) m L.infinite hR₃
  refine ⟨Spec, hSpec, fun T => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hSpec' T
  have hset : ∀ x, NTs (M := M) m L.Sent (Spec T) x ↔ specExtN i (m + 1) (NTs (M := M) m L.Sent T) x := by
    intro x
    rw [h3, h₃, ← NTs_iff_NSR, h₂]
    refine or_congr Iff.rfl (exists_congr fun π => ?_)
    rw [h₂b, h₂a, NSR_param_const]
    show (A.IsPi (m + 1) π ∧ x = i.i π) ∧ NSR m RT () π ↔ (A.IsPi (m + 1) π ∧ A.TrueN π) ∧ x = i.i π
    constructor
    · rintro ⟨⟨hπ, hx⟩, ht⟩; exact ⟨⟨hπ, (hRT' π hπ).1 ht⟩, hx⟩
    · rintro ⟨⟨hπ, ht⟩, hx⟩; exact ⟨⟨hπ, hx⟩, (hRT' π hπ).2 ht⟩
  refine ⟨h1, h2, ?_, hset, ?_⟩
  · intro π hπ
    rw [i.derivI_iff]
    exact L.deriv_of_mem ((hset (i.i π)).2 (Or.inr ⟨π, hπ, rfl⟩))
  · intro hsound
    obtain ⟨α, hα⟩ := consistent_specExtN_of_sigmaSound i hsound
    refine ⟨α, fun hd => hα ?_⟩
    exact L.deriv_mono (fun β hβ => (hset β).1 hβ) hd

end Stable
