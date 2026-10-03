/-
# The odd-class arithmetic law (Theorem `thm_mobius`)

This file formalizes the arithmetic content of Theorem `thm_mobius` of
*Invariant arithmetic of closed geodesics*.

Setup.  For an indivisible class `β` and a metric `g` that is `eβ`-taut and
`eβ`-regular, write `F d := F(g, dβ) ∈ ℚ` and `s d := ∑_{o ∈ P_d} i(o) ∈ ℤ`
for the signed count of prime geodesic strings of class `dβ` (here embedded
in `ℚ`).  The geometry of the paper (Lemma `lem_mobius`, the covering
bijection, together with the parity sign law `lem_paritysigns`) yields, for
every **odd** `e ≥ 1`, the identity `eq_oddmobius`:

    e · F(g, eβ)  =  ∑_{d ∣ e} d · s_d.

That identity is the sole geometric input; it enters here as the hypothesis
`hodd`.  Everything below is pure arithmetic.

We prove:

* `mobius_inversion` — the Möbius-inverted form `eq_mobiusinversion`,
  `e · s_e = ∑_{(a,b) : ab = e} μ(a) · b · F(g, bβ)` (the divisor-antidiagonal
  spelling of `s_e = (1/e) ∑_{d∣e} μ(e/d) · d · F(g, dβ)`), via Mathlib's
  Möbius inversion on the divisor-closed set of odd numbers.
* `s_eq_zero_of_F_eq_zero` — consequence (1): if `F(g, dβ) = 0` for every
  `d ∣ e`, then `s_e = 0`.
* `s_eq_indicator_of_F_eq_inv` — consequence (2): if `F(g, dβ) = 1/d` for
  every `d ∣ e`, then `s_e = 0` for `e > 1`, while `s_1 = 1`.
The passage from `s_e = 0` (resp. `s_e = 1`) to the parity of `#P_e` — the
"contains another" corollary — is in `ArithLaw/Counting.lean`.

Both consequences are proved directly from `hodd` by strong induction over
divisors, independently of the inversion formula, matching the paper's
"in particular".
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Finset
open scoped ArithmeticFunction.Moebius

namespace GeodesicArithmetic

/-- A divisor of an odd number is odd — so the set of odd numbers is closed
under taking divisors, which is what Möbius inversion on it requires. -/
theorem odd_of_dvd_odd {m n : ℕ} (h : m ∣ n) (hn : Odd n) : Odd m := by
  rw [Nat.odd_iff] at hn ⊢
  rcases h with ⟨t, rfl⟩
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · rw [Nat.mul_mod, hm, zero_mul, Nat.zero_mod] at hn
    omega
  · exact hm

variable {s F : ℕ → ℚ}

/-- **Möbius inversion** (`eq_mobiusinversion`).  From the odd-class identity
`eq_oddmobius` at every odd argument, `e · s_e = ∑_{(a,b) : a·b = e} μ(a)·b·F b`
for odd `e`.  Summing `μ(a)·b·F b` over the divisor antidiagonal of `e` is the
Mathlib spelling of `∑_{d ∣ e} μ(e/d)·d·F d`; dividing by `e` gives the paper's
`s_e = (1/e) ∑_{d ∣ e} μ(e/d)·d·F(g, dβ)`. -/
theorem mobius_inversion
    (hodd : ∀ n : ℕ, 0 < n → Odd n → ∑ d ∈ n.divisors, (d : ℚ) * s d = (n : ℚ) * F n)
    (e : ℕ) (he : 0 < e) (hoe : Odd e) :
    ∑ x ∈ e.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℚ) * ((x.2 : ℚ) * F x.2) = (e : ℚ) * s e := by
  have hclosed : ∀ m n : ℕ, m ∣ n → n ∈ {k : ℕ | Odd k} → m ∈ {k : ℕ | Odd k} :=
    fun _ _ hmn hn => odd_of_dvd_odd hmn hn
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on (R := ℚ)
    (f := fun d => (d : ℚ) * s d) (g := fun n => (n : ℚ) * F n)
    {k : ℕ | Odd k} hclosed).mp hodd e he hoe

/-- **Consequence (1)** of `thm_mobius`: if `F(g, dβ) = 0` for every divisor
`d` of `e`, then the signed prime count `s_e` vanishes. -/
theorem s_eq_zero_of_F_eq_zero
    (hodd : ∀ n : ℕ, 0 < n → Odd n → ∑ d ∈ n.divisors, (d : ℚ) * s d = (n : ℚ) * F n)
    {e : ℕ} (he : 0 < e) (hoe : Odd e) (hF : ∀ d, d ∣ e → F d = 0) :
    ∀ n, n ∣ e → s n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn he
    have hno : Odd n := odd_of_dvd_odd hn hoe
    have hsum := hodd n hn0 hno
    rw [hF n hn, mul_zero] at hsum
    have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn0.ne'
    rw [← Finset.add_sum_erase _ (fun d : ℕ => (d : ℚ) * s d) hmem] at hsum
    have herase : ∑ d ∈ n.divisors.erase n, (d : ℚ) * s d = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      obtain ⟨hdne, hdmem⟩ := Finset.mem_erase.mp hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
      have hlt : d < n := lt_of_le_of_ne (Nat.divisor_le hdmem) hdne
      rw [ih d hlt (hdvd.trans hn), mul_zero]
    rw [herase, add_zero] at hsum
    have hne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    exact (mul_eq_zero.mp hsum).resolve_left hne

/-- **Consequence (2)** of `thm_mobius`: if `F(g, dβ) = 1/d` for every divisor
`d` of `e` (the negative-curvature pattern), then `s_n = 1` for `n = 1` and
`s_n = 0` otherwise; in particular `s_e = 0` for `e > 1`. -/
theorem s_eq_indicator_of_F_eq_inv
    (hodd : ∀ n : ℕ, 0 < n → Odd n → ∑ d ∈ n.divisors, (d : ℚ) * s d = (n : ℚ) * F n)
    {e : ℕ} (he : 0 < e) (hoe : Odd e) (hF : ∀ d, d ∣ e → F d = 1 / (d : ℚ)) :
    ∀ n, n ∣ e → s n = (if n = 1 then 1 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn he
    have hno : Odd n := odd_of_dvd_odd hn hoe
    have hne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    have hsum := hodd n hn0 hno
    rw [hF n hn, mul_one_div, div_self hne] at hsum
    have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn0.ne'
    rw [← Finset.add_sum_erase _ (fun d : ℕ => (d : ℚ) * s d) hmem] at hsum
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn0.ne') with h1 | h1
    · -- n = 1
      subst h1
      simp only [Nat.divisors_one, Finset.erase_singleton, Finset.sum_empty, add_zero,
        Nat.cast_one, one_mul] at hsum
      simp [hsum]
    · -- 1 < n
      have herase : ∑ d ∈ n.divisors.erase n, (d : ℚ) * s d = 1 := by
        have hrw : ∑ d ∈ n.divisors.erase n, (d : ℚ) * s d
            = ∑ d ∈ n.divisors.erase n, (if d = 1 then (1 : ℚ) else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨hdne, hdmem⟩ := Finset.mem_erase.mp hd
          have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
          have hlt : d < n := lt_of_le_of_ne (Nat.divisor_le hdmem) hdne
          rw [ih d hlt (hdvd.trans hn)]
          rcases eq_or_ne d 1 with h | h <;> simp [h]
        rw [hrw, Finset.sum_ite_eq']
        have h1mem : (1 : ℕ) ∈ n.divisors.erase n := by
          rw [Finset.mem_erase]
          exact ⟨by omega, Nat.one_mem_divisors.mpr hn0.ne'⟩
        rw [if_pos h1mem]
      rw [herase] at hsum
      have hsn : (n : ℚ) * s n = 0 := by linarith
      rw [if_neg (by omega : ¬ n = 1)]
      exact (mul_eq_zero.mp hsn).resolve_left hne

end GeodesicArithmetic
