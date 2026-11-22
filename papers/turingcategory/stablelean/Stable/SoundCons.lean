import Stable.Spec

/-!
# `Σₙ`-soundness versus `n`-consistency (Lemma 6.6, `lemma_soundvsconsistent`)

Let `i : 𝓐 → 𝓛` be a translation and `F` an `𝓛`-theory.
1. If `F ⊢ⁱ Q` then `F` is `1`-consistent relative to `i` iff it is `Σ₁`-sound, and
   `2`-consistent iff `Σ₂`-sound.
2. `Σₙ₊₁`-soundness implies `Σₙ`-soundness.
3. If `F` is `Σₙ`-sound relative to `i` then `F ∪ i (Tr_{Πₙ})` is consistent.
-/

namespace Stable

open Classical

variable {M : TuringModel} {A : Arith M} {L : Language M} (i : Translation A.toLanguage L)

/-- Lemma 6.6 (2). -/
theorem SigmaSound.mono {n : ℕ} {F : L.Sent → Prop} (h : i.SigmaSound (n + 1) F) :
    i.SigmaSound n F := fun σ hσ hd => h σ (A.sigma_succ n σ hσ) hd

/-- An inconsistent theory `F_{i,𝓐}` is not `Σₙ`-sound (there is a false `Δ₀` sentence). -/
theorem SigmaSound.consistent {n : ℕ} {F : L.Sent → Prop} (h : i.SigmaSound n F) :
    ∃ α : A.Sent, ¬ i.DerivI F α := by
  obtain ⟨δ, hδ0, hδt⟩ := A.exists_true_delta0
  refine ⟨A.neg δ, fun hd => ?_⟩
  have := h _ (A.sigma_of_delta0 (A.neg_delta0 δ hδ0) n) hd
  rw [A.trueN_neg] at this; exact this hδt

/-- Lemma 6.6 (1), first half: given `F ⊢ⁱ Q`, `1`-consistency is `Σ₁`-soundness. -/
theorem oneConsistent_iff_sigmaSound {F : L.Sent → Prop} (hQ : i.DerivISet F A.Q) :
    i.OneConsistent F ↔ i.SigmaSound 1 F := by
  constructor
  · intro h σ hσ hd
    refine Classical.byContradiction fun hf => ?_
    obtain ⟨v, hv⟩ := h.2 σ hσ hd
    -- every instance is a false `Δ₀` sentence, refuted by `Q`
    have hfv : ¬ A.TrueN (A.instS σ v) := fun ht => hf ((A.trueN_sigma 0 σ hσ).2 ⟨v, ht⟩)
    have h0 : A.IsSigma 0 (A.instS σ v) := (A.sigma_zero_iff_pi_zero _).2 (A.instS_pi 0 σ v hσ)
    exact hv (i.derivI_cut (fun q hq => hQ q hq) (A.Q_delta0_neg _ h0 hfv))
  · intro h
    refine ⟨hQ, fun σ hσ hd => ?_⟩
    obtain ⟨v, hv⟩ := (A.trueN_sigma 0 σ hσ).1 (h σ hσ hd)
    refine ⟨v, fun hneg => ?_⟩
    have h0 : A.IsSigma 0 (A.instS σ v) := (A.sigma_zero_iff_pi_zero _).2 (A.instS_pi 0 σ v hσ)
    have hpos : i.DerivI F (A.instS σ v) := i.derivI_cut (fun q hq => hQ q hq) (A.Q_delta0 _ h0 hv)
    -- `F_{i,𝓐}` is inconsistent, contradicting `Σ₁`-soundness
    obtain ⟨α, hα⟩ := SigmaSound.consistent i h
    exact hα (A.deriv_explosion hpos hneg)

/-- Lemma 6.6 (1), second half: given `F ⊢ⁱ Q`, `2`-consistency is `Σ₂`-soundness. -/
theorem twoConsistent_iff_sigmaSound {F : L.Sent → Prop} (hQ : i.DerivISet F A.Q) :
    i.TwoConsistent F ↔ i.SigmaSound 2 F := by
  constructor
  · intro h σ hσ hd
    refine Classical.byContradiction fun hf => ?_
    obtain ⟨u, hu⟩ := h.2 σ hσ hd
    have hπ : A.IsPi 1 (A.instS σ u) := A.instS_pi 1 σ u hσ
    have hfu : ¬ A.TrueN (A.instS σ u) := fun ht => hf ((A.trueN_sigma 1 σ hσ).2 ⟨u, ht⟩)
    -- a false `Π⁰₁` sentence has a false `Δ₀` instance, refuted by `Q`, so `Q ⊢ ¬π`
    have hv : ∃ v, ¬ A.TrueN (A.instP (A.instS σ u) v) := by
      refine Classical.byContradiction fun hc => hfu ((A.trueN_pi 0 _ hπ).2 fun v => ?_)
      exact Classical.byContradiction fun hv => hc ⟨v, hv⟩
    obtain ⟨v, hv⟩ := hv
    have hQneg : A.Deriv A.Q (A.neg (A.instS σ u)) :=
      A.deriv_neg_pi_of_neg_inst hπ (A.Q_delta0_neg _ (A.instP_sigma 0 _ v hπ) hv)
    exact hu (i.derivI_cut (fun q hq => hQ q hq) hQneg)
  · intro h
    refine ⟨(oneConsistent_iff_sigmaSound i hQ).2 (SigmaSound.mono i h), fun σ hσ hd => ?_⟩
    obtain ⟨u, hu⟩ := (A.trueN_sigma 1 σ hσ).1 (h σ hσ hd)
    have hπ : A.IsPi 1 (A.instS σ u) := A.instS_pi 1 σ u hσ
    refine ⟨u, fun hneg => ?_⟩
    -- `F ⊢ⁱ ∃x̄ ¬φ`, a `Σ₁` sentence, so it is true, contradicting the truth of `π = ∀x̄ φ`
    have hs : i.DerivI F (A.negPi (A.instS σ u)) :=
      i.derivI_cut (fun β hβ => by rw [hβ]; exact hneg) (A.negPi_deriv 0 _ hπ)
    have ht := h _ (A.sigma_succ 1 _ (A.negPi_sigma 0 _ hπ)) hs
    exact A.not_trueN_of_trueN_negPi hπ ht hu

/-- Lemma 6.6 (3): a `Σₙ`-sound theory stays consistent after adding the true `Π⁰ₙ` sentences. -/
theorem consistent_specExtN_of_sigmaSound {n : ℕ} {F : L.Sent → Prop} (h : i.SigmaSound n F) :
    L.Consistent (specExtN i n F) := by
  refine Classical.byContradiction fun hc => ?_
  obtain ⟨π, ⟨hπ, hπt⟩, hneg⟩ := exists_trPiN_derivI_neg_of_not_consistent i hc
  cases n with
  | zero =>
    -- `¬π` is a false `Δ₀` sentence proved by `F` under `i`
    have h0 : A.IsSigma 0 (A.neg π) := A.neg_delta0 π ((A.sigma_zero_iff_pi_zero π).2 hπ)
    have := h _ h0 hneg
    rw [A.trueN_neg] at this; exact this hπt
  | succ n =>
    -- `F ⊢ⁱ ∃x̄ ¬φ ∈ Σₙ₊₁`, which is then true, so `π` is false
    have hs : i.DerivI F (A.negPi π) :=
      i.derivI_cut (fun β hβ => by rw [hβ]; exact hneg) (A.negPi_deriv n π hπ)
    exact A.not_trueN_of_trueN_negPi hπ (h _ (A.negPi_sigma n π hπ) hs) hπt

end Stable
