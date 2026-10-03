/-
# Generalized integer binomial coefficients

`intBinom a s` is the polynomial binomial coefficient `C(a, s)` for an
*integer* upper argument `a`, so that in any truncated power series ring
`(1 + X) ^ a = ∑ s, intBinom a s • X ^ s` for every `a : ℤ`.  Negative upper
arguments use `C(-m, s) = (-1)^s C(m + s - 1, s)`.

Only the Pascal recurrence and the values at `s = 0, 1` are needed
downstream.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace Potency

/-- Generalized binomial coefficient with integer upper argument. -/
def intBinom : ℤ → ℕ → ℤ
  | Int.ofNat n, s => (n.choose s : ℤ)
  | Int.negSucc n, s => (-1) ^ s * ((n + s).choose s : ℤ)

@[simp] theorem intBinom_zero_right (a : ℤ) : intBinom a 0 = 1 := by
  cases a <;> simp [intBinom]

@[simp] theorem intBinom_one_right (a : ℤ) : intBinom a 1 = a := by
  cases a with
  | ofNat n => simp [intBinom, Nat.choose_one_right]
  | negSucc n =>
    simp only [intBinom, Nat.choose_one_right, pow_one, Int.negSucc_eq]
    push_cast
    ring

theorem intBinom_zero_left (s : ℕ) : intBinom 0 (s + 1) = 0 := by
  show intBinom (Int.ofNat 0) (s + 1) = 0
  simp [intBinom, Nat.choose_eq_zero_of_lt (Nat.succ_pos s)]

/-- Pascal's rule for the generalized binomial coefficient. -/
theorem intBinom_pascal (a : ℤ) (s : ℕ) :
    intBinom (a + 1) (s + 1) = intBinom a (s + 1) + intBinom a s := by
  cases a with
  | ofNat n =>
    rw [show (Int.ofNat n : ℤ) + 1 = Int.ofNat (n + 1) from rfl]
    simp only [intBinom]
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  | negSucc n =>
    cases n with
    | zero =>
      rw [show (Int.negSucc 0 : ℤ) + 1 = Int.ofNat 0 by decide]
      simp only [intBinom, Nat.zero_add, Nat.choose_self,
        Nat.choose_eq_zero_of_lt (Nat.succ_pos s)]
      rw [pow_succ]
      push_cast
      ring
    | succ m =>
      rw [show (Int.negSucc (m + 1) : ℤ) + 1 = Int.negSucc m by
        rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring]
      simp only [intBinom]
      rw [show m + (s + 1) = m + s + 1 by omega,
        show (m + 1) + (s + 1) = (m + s + 1) + 1 by omega,
        show (m + 1) + s = m + s + 1 by omega,
        Nat.choose_succ_succ (m + s + 1) s]
      push_cast
      rw [pow_succ]
      ring

end Potency
