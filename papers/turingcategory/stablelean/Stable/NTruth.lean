import Stable.NStab
import Stable.Arith

/-!
# Truth of `Σ⁰ₙ` and `Π⁰ₙ` sentences as arithmetical conditions

The paper uses that `Tr_{Πₙ}`, "as a condition on the code of a sentence, is `Π⁰ₙ` with a computable
matrix, the truth of a `Δ₀` instance being decidable" (Section 6.2), and the standard `Σ⁰ₙ` truth
definition (Section 6.3).  From the instance maps `instS`, `instP` of the interface `Arith` and the
decidability of `Δ₀` truth we build, by recursion on `k`:

* `trSigma k : NRel Unit 𝓐 k` with `NSR k (trSigma k) () σ ↔ ℕ ⊨ σ` for `σ ∈ Σ⁰_{k+2}`
  (`NSR_trSigma`): for `k = 0` the matrix is `(σ, u, v) ↦ ℕ ⊨ instP (instS σ u) v` (a `Δ₀`
  sentence), and `trSigma (k+1)` is the complement of `trSigma k` along the base map
  `(σ, u) ↦ negPi (instS σ u)`, so that `NSR (k+1) (trSigma (k+1)) () σ` is
  `∃ u, ¬ ℕ ⊨ negPi (instS σ u)`, i.e. `∃ u, ℕ ⊨ instS σ u`;
* the same relation `trSigma k` works for `π ∈ Π⁰_{k+1}` (`exists_trPi`), as `Π⁰_{k+1} ⊂ Σ⁰_{k+2}`.
-/

namespace Stable

open Classical

variable {M : TuringModel} (A : Arith M)

/-! ### Helpers -/

/-- For `π ∈ Π⁰_{n+1}`, `ℕ ⊨ negPi π` iff `ℕ ⊭ π`. -/
private theorem trueN_negPi_iff {n : ℕ} {π : A.Sent} (hπ : A.IsPi (n + 1) π) :
    A.TrueN (A.negPi π) ↔ ¬ A.TrueN π := by
  refine ⟨A.not_trueN_of_trueN_negPi hπ, fun h => ?_⟩
  obtain ⟨v, hv⟩ := Classical.not_forall.1 fun hall => h ((A.trueN_pi n π hπ).2 hall)
  refine (A.trueN_sigma n _ (A.negPi_sigma n π hπ)).2 ⟨v, ?_⟩
  rw [A.negPi_inst n π v hπ, A.trueN_neg]
  exact hv

/-- A double complement does not change `NSR`. -/
private theorem NSR_compl_compl (m : ℕ) {B : Type} (R : NRel Unit B m) (a : Unit) (b : B) :
    NSR m (compl (compl R)) a b ↔ NSR m R a b :=
  NSR_congr m (fun _ _ _ _ => Classical.not_not) a b

/-- Precomposing a computable relation with a computable base map keeps it computable. -/
private theorem nRelComp_mapBase {B C : Type} [Enc M B] [Enc M C] (m : ℕ) {R : NRel Unit C m}
    (hR : NRelComp (M := M) m R) {f : B → C} (hf : CompT M f) :
    NRelComp (M := M) m (B := B) (fun a x u v => R a (nbMapBase m f x) u v) := by
  have hg : CompT M (fun q : Unit × NB B m × ℕ × ℕ =>
      ((q.1, nbMapBase m f q.2.1, q.2.2) : Unit × NB C m × ℕ × ℕ)) :=
    CompT.pair compT_fst (CompT.pair ((compT_nbMapBase m hf).comp (compT_fst.comp compT_snd))
      (compT_snd.comp compT_snd))
  exact CompSet.comp hR hg

/-! ### The matrix of `Σ⁰_{k+2}`-truth -/

/-- The computable matrix of `Σ⁰_{k+2}`-truth (`NSR_trSigma`): for `k = 0`,
`(σ, u, v) ↦ ℕ ⊨ instP (instS σ u) v` (a `Δ₀` condition); for `k + 1`, the complement of
`trSigma k` precomposed with the base map `(σ, u) ↦ negPi (instS σ u)`. -/
def trSigma : (k : ℕ) → NRel Unit A.Sent k
  | 0 => fun _ σ u v => A.IsSigma 0 (A.instP (A.instS σ u) v) ∧ A.TrueN (A.instP (A.instS σ u) v)
  | k + 1 => compl fun a x u v =>
      trSigma k a (nbMapBase k (fun p : A.Sent × ℕ => A.negPi (A.instS p.1 p.2)) x) u v

/-- Level `0`: the matrix is decidable, by the decidability of `Δ₀` truth. -/
private theorem nRelComp_trSigma_zero : NRelComp (M := M) 0 (trSigma A 0) := by
  have hg : CompT M (fun q : Unit × A.Sent × ℕ × ℕ => A.instP (A.instS q.2.1 q.2.2.1) q.2.2.2) :=
    A.instP_comp.comp (CompT.pair (A.instS_comp.comp (CompT.pair (compT_fst.comp compT_snd)
      (compT_fst.comp (compT_snd.comp compT_snd)))) (compT_snd.comp (compT_snd.comp compT_snd)))
  exact CompSet.comp A.delta0_dec hg

/-- Level `0`: `∃ u ∀ v, ℕ ⊨ instP (instS σ u) v` is `ℕ ⊨ σ` for `σ ∈ Σ⁰₂`. -/
private theorem NSR_trSigma_zero {σ : A.Sent} (hσ : A.IsSigma 2 σ) :
    NSR 0 (trSigma A 0) () σ ↔ A.TrueN σ := by
  rw [NSR_zero, A.trueN_sigma 1 σ hσ]
  refine exists_congr fun u => ?_
  have hπ : A.IsPi 1 (A.instS σ u) := A.instS_pi 1 σ u hσ
  rw [A.trueN_pi 0 _ hπ]
  refine forall_congr' fun v => ?_
  show A.IsSigma 0 (A.instP (A.instS σ u) v) ∧ A.TrueN (A.instP (A.instS σ u) v) ↔ _
  exact ⟨fun h => h.2, fun h => ⟨A.instP_sigma 0 _ v hπ, h⟩⟩

/-- Level `k + 1` from level `k`: `NSR (k+1) (trSigma (k+1)) () σ` is
`∃ u, ¬ NSR k (trSigma k) () (negPi (instS σ u))`, i.e. `∃ u, ℕ ⊨ instS σ u`. -/
private theorem NSR_trSigma_succ (k : ℕ)
    (ih : ∀ {σ : A.Sent}, A.IsSigma (k + 2) σ → (NSR k (trSigma A k) () σ ↔ A.TrueN σ))
    {σ : A.Sent} (hσ : A.IsSigma (k + 1 + 2) σ) :
    NSR (k + 1) (trSigma A (k + 1)) () σ ↔ A.TrueN σ := by
  rw [NSR_succ, A.trueN_sigma (k + 2) σ hσ]
  refine exists_congr fun u => ?_
  have hπ : A.IsPi (k + 2) (A.instS σ u) := A.instS_pi (k + 2) σ u hσ
  have key : NSR k (compl (trSigma A (k + 1))) () (σ, u) ↔ ¬ A.TrueN (A.instS σ u) :=
    (NSR_compl_compl k (B := A.Sent × ℕ) (fun a x u v => trSigma A k a
        (nbMapBase k (fun p : A.Sent × ℕ => A.negPi (A.instS p.1 p.2)) x) u v) () (σ, u)).trans
      ((NSR_nbMapBase k (trSigma A k) (fun p : A.Sent × ℕ => A.negPi (A.instS p.1 p.2))
        () (σ, u)).trans
        ((ih (A.negPi_sigma (k + 1) _ hπ)).trans (trueN_negPi_iff A (n := k + 1) hπ)))
  rw [key, Classical.not_not]

/-- `trSigma k` is computable. -/
theorem nRelComp_trSigma : ∀ k, NRelComp (M := M) k (trSigma A k)
  | 0 => nRelComp_trSigma_zero A
  | k + 1 => NRelComp.compl (nRelComp_mapBase k (B := A.Sent × ℕ) (nRelComp_trSigma k)
      (A.negPi_comp.comp A.instS_comp))

/-- `NSR k (trSigma k) () σ` is `ℕ ⊨ σ`, for `σ ∈ Σ⁰_{k+2}`. -/
theorem NSR_trSigma : ∀ (k : ℕ) {σ : A.Sent}, A.IsSigma (k + 2) σ →
    (NSR k (trSigma A k) () σ ↔ A.TrueN σ)
  | 0, _, hσ => NSR_trSigma_zero A hσ
  | k + 1, _, hσ => NSR_trSigma_succ A k (fun h => NSR_trSigma k h) hσ

/-- `Σ⁰_{k+2}`-truth is a `Σ⁰_{k+2}` condition with computable matrix. -/
theorem exists_trSigma (k : ℕ) : ∃ R : NRel Unit A.Sent k, NRelComp (M := M) k R ∧
    ∀ σ, A.IsSigma (k + 2) σ → (NSR k R () σ ↔ A.TrueN σ) :=
  ⟨trSigma A k, nRelComp_trSigma A k, fun _ hσ => NSR_trSigma A k hσ⟩

/-- `Π⁰_{k+1}`-truth is a `Σ⁰_{k+2}` condition with computable matrix. -/
theorem exists_trPi (k : ℕ) : ∃ R : NRel Unit A.Sent k, NRelComp (M := M) k R ∧
    ∀ π, A.IsPi (k + 1) π → (NSR k R () π ↔ A.TrueN π) :=
  ⟨trSigma A k, nRelComp_trSigma A k, fun π hπ => NSR_trSigma A k (A.pi_sigma_succ (k + 1) π hπ)⟩

end Stable
