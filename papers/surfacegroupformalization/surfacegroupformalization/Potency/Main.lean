/-
# Lemma 6.9, formal statement and proof

The paper statement (Lemma 6.9, `lem_potency` of *Invariant arithmetic of
closed geodesics*): let `G = π₁(Σ)` for a closed orientable surface of genus
`≥ 2`, `a ≠ 1`, and `p` prime.  Then `G` has a finite quotient in which the
image of `a` has order exactly `p`.

Formal decomposition:

* `PotentAt G a` — the conclusion, for an element of an arbitrary group.
* `potentAt_freeGroup` — potency of finitely generated free groups.  Proved
  from scratch via the truncated Magnus embedding (`Potency/NC.lean`,
  `Potency/Magnus.lean`, `Potency/Order.lean`).
* `potentAt_of_residuallyFree` — the final glue: any group with the stated
  residual-freeness property inherits potency.  **The single classical input
  is the hypothesis `hres`** — for surface groups this is Baumslag's theorem
  [G. Baumslag, *On generalised free products*, Math. Z. 78 (1962) 423–438]
  that surface groups are residually free.  (For the torus, `ℤ²` is
  residually free by projecting to a coordinate, so the statement holds for
  all closed orientable aspherical surfaces.)

Also included: `exists_addOrderOf_eq_prime`, the one-line valuation lemma
used by the paper's case (i) (homologically visible classes), kept for the
audit even though the Magnus route subsumes it.
-/
import Potency.Order

namespace Potency

/-- `a` is *potent*: for every prime `p` there is a finite group `Q` and a
homomorphism `π : G →* Q` with `orderOf (π a) = p` — a finite quotient (the
image of `π`) where `a` has order exactly `p`. -/
def PotentAt (G : Type*) [Group G] (a : G) : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (π : G →* Q), orderOf (π a) = p

/-- Finitely generated free groups are potent at every nontrivial element. -/
theorem potentAt_freeGroup {k : ℕ} {x : FreeGroup (Fin k)} (hx : x ≠ 1) :
    PotentAt (FreeGroup (Fin k)) x :=
  fun _ hp => freeGroup_exists_orderOf_eq x hx hp

/-- **Lemma 6.9, formal version.**  If every nontrivial element of `G`
survives in some finitely generated free quotient (residual freeness — for
surface groups this is Baumslag [Bau62], the single classical input), then
`G` is potent at every nontrivial element: for every prime `p` there is a
finite quotient where the image of `a` has order exactly `p`. -/
theorem potentAt_of_residuallyFree {G : Type*} [Group G]
    (hres : ∀ b : G, b ≠ 1 → ∃ (k : ℕ) (φ : G →* FreeGroup (Fin k)), φ b ≠ 1)
    {a : G} (ha : a ≠ 1) : PotentAt G a := by
  obtain ⟨k, φ, hφ⟩ := hres a ha
  intro p hp
  obtain ⟨Q, hG, hF, π, hπ⟩ := potentAt_freeGroup hφ p hp
  exact ⟨Q, hG, hF, π.comp φ, hπ⟩

/-- Case (i) of the paper's proof of Lemma 6.9 (homologically visible
classes), kept standalone for the audit: a vector of integers with a nonzero
coordinate admits, for every prime `p`, an additive map to some
`ZMod (p^(s+1))` under which it has additive order exactly `p`.  (Take `s`
to be the `p`-valuation of the chosen nonzero coordinate.) -/
theorem exists_addOrderOf_eq_prime {ι : Type*} (f : ι → ℤ) (i₀ : ι) (hf : f i₀ ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    ∃ (s : ℕ) (φ : (ι → ℤ) →+ ZMod (p ^ (s + 1))), addOrderOf (φ f) = p := by
  classical
  have hE : ∃ s : ℕ, ¬ ((p : ℤ) ^ (s + 1) ∣ f i₀) := by
    obtain ⟨s, hs⟩ := exists_pow_not_dvd hp.two_le hf
    cases s with
    | zero =>
      refine absurd (one_dvd (f i₀)) ?_
      simpa using hs
    | succ s => exact ⟨s, hs⟩
  set s : ℕ := Nat.find hE with hs
  have hspec : ¬ ((p : ℤ) ^ (s + 1) ∣ f i₀) := Nat.find_spec hE
  have hall : (p : ℤ) ^ s ∣ f i₀ := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0, pow_zero]
      exact one_dvd _
    · by_contra hnd
      have hprop : ¬ ((p : ℤ) ^ ((s - 1) + 1) ∣ f i₀) := by
        rwa [show s - 1 + 1 = s by omega]
      exact absurd hprop (Nat.find_min hE (by omega))
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨s, (Int.castAddHom (ZMod (p ^ (s + 1)))).comp
    (Pi.evalAddMonoidHom (fun _ : ι => ℤ) i₀), ?_⟩
  obtain ⟨y, hy⟩ := hall
  apply addOrderOf_eq_prime
  · show p • ((f i₀ : ℤ) : ZMod (p ^ (s + 1))) = 0
    rw [nsmul_eq_mul,
      show ((p : ℕ) : ZMod (p ^ (s + 1))) * ((f i₀ : ℤ) : ZMod (p ^ (s + 1)))
        = (((p : ℤ) * f i₀ : ℤ) : ZMod (p ^ (s + 1))) by push_cast; ring,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨y, by rw [hy]; push_cast; ring⟩
  · show ((f i₀ : ℤ) : ZMod (p ^ (s + 1))) ≠ 0
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    apply hspec
    obtain ⟨y', hy'⟩ := hdvd
    exact ⟨y', by rw [hy']; push_cast; ring⟩

end Potency
