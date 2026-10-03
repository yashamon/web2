/-
# From signed counts to counts

The signed prime count `s_d = ∑_{o ∈ P_d} i(o)` has `±1`-valued terms.  This
file records the elementary passage from a value of such a sum to a statement
about the number of terms, used throughout the paper:

* `s_d = 0` forces `#P_d` even (so a prime string in the class is accompanied
  by another one: `two_le_card_of_signsum_zero`);
* `s_d = 1` forces `#P_d` odd;
* in general `#P_d ≥ |s_d|`.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

namespace GeodesicArithmetic

variable {α : Type*} (P : Finset α) (i : α → ℤ)

/-- For `±1`-valued `i`, `∑_{o ∈ P} i(o) ≡ #P (mod 2)`. -/
theorem signsum_sub_card_even (hi : ∀ o ∈ P, i o = 1 ∨ i o = -1) :
    Even (∑ o ∈ P, i o - (P.card : ℤ)) := by
  have hcard : (P.card : ℤ) = ∑ _o ∈ P, (1 : ℤ) := by simp
  rw [hcard, ← Finset.sum_sub_distrib]
  refine Finset.sum_induction _ Even (fun a b ha hb => ha.add hb) Even.zero ?_
  intro o ho
  rcases hi o ho with h | h
  · rw [h]; exact ⟨0, by norm_num⟩
  · rw [h]; exact ⟨-1, by norm_num⟩

/-- A `±1`-sum equal to `0` has an even number of terms. -/
theorem even_card_of_signsum_zero (hi : ∀ o ∈ P, i o = 1 ∨ i o = -1)
    (hsum : ∑ o ∈ P, i o = 0) : Even P.card := by
  have h := signsum_sub_card_even P i hi
  rw [hsum, zero_sub, even_neg, Int.even_coe_nat] at h
  exact h

/-- A `±1`-sum equal to `1` has an odd number of terms. -/
theorem odd_card_of_signsum_one (hi : ∀ o ∈ P, i o = 1 ∨ i o = -1)
    (hsum : ∑ o ∈ P, i o = 1) : Odd P.card := by
  have h := signsum_sub_card_even P i hi
  rw [hsum, Int.even_sub] at h
  have hc : ¬ Even (P.card : ℤ) := fun hc => Int.not_even_one (h.mpr hc)
  rw [Int.even_coe_nat] at hc
  exact Nat.not_even_iff_odd.mp hc

/-- A nonempty set of `±1`-terms summing to `0` has at least two elements:
a prime geodesic string in a class with `s = 0` is accompanied by another. -/
theorem two_le_card_of_signsum_zero (hi : ∀ o ∈ P, i o = 1 ∨ i o = -1)
    (hsum : ∑ o ∈ P, i o = 0) (hP : P.Nonempty) : 2 ≤ P.card := by
  obtain ⟨k, hk⟩ := even_card_of_signsum_zero P i hi hsum
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact absurd (Finset.card_eq_zero.mp (by omega)) hP.ne_empty
  · omega

/-- `#P ≥ |∑_{o ∈ P} i(o)|` for `±1`-valued `i`. -/
theorem abs_signsum_le_card (hi : ∀ o ∈ P, i o = 1 ∨ i o = -1) :
    |∑ o ∈ P, i o| ≤ (P.card : ℤ) := by
  calc |∑ o ∈ P, i o| ≤ ∑ o ∈ P, |i o| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _o ∈ P, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro o ho
        rcases hi o ho with h | h <;> rw [h] <;> norm_num
    _ = P.card := by simp

end GeodesicArithmetic
