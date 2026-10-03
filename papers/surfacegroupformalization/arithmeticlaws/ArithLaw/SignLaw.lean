/-
# The ±1 sign cancellation (`lem_iteratesigns` → the master identity)

This file closes the gap between the raw geometric inputs of §11 and the
`master` identity used in `ArithLaw/DivisorSystem.lean`.  The two geometric
inputs are:

* `hdF` — Lemma `lem_mobius` (`eq_dF`, the covering bijection), at the
  divisor levels `d ∣ e` where the paper establishes it:
      `d · F(g, dβ₀) = ∑_{c ∣ d} c · I c (d/c)`,
  where `I c k := ∑_{o ∈ P_c} i(o^k)` is the aggregated signed iterate sum;
* `hiter` — the aggregated surface sign law `lem_iteratesigns`:
      `I c k = u_c + (-1)^k · b_c`   (for `k ≥ 1` with `c·k ∣ e`, i.e. exactly
  at the iterates `o^{k}` whose class `ckβ₀` is a divisor class of `eβ₀`, which
  `eβ₀`-regularity makes nondegenerate),
  with `u_c` the pos-hyperbolic-minus-elliptic count and `b_c` the
  inverse-hyperbolic count, and `s_c = u_c − b_c` (`hsub`).

`master_of_signlaw` derives the master identity

    d · F(g, dβ₀) = (∑_{c ∣ d} c · s_c) + 2 · B_{d/2}

by the ±1 cancellation: `(-1)^{d/c} + 1` is `2` when `d/c` is even and `0`
otherwise, and `d/c` is even exactly when `2c ∣ d`, i.e. `c ∣ d/2`.  The
even-quotient reindexing `evenquot` carries out that counting.
-/
import ArithLaw.DivisorSystem

open Finset

namespace GeodesicArithmetic

variable (b : ℕ → ℚ)

/-- The even-quotient reindexing.  `∑_{c ∣ d} c·((-1)^{d/c}+1)·b_c = 2·B_{d/2}`:
the factor is `2` exactly when `d/c` is even (`2c ∣ d`, i.e. `c ∣ d/2`) and `0`
otherwise. -/
theorem evenquot (d : ℕ) :
    ∑ c ∈ d.divisors, (c : ℚ) * ((-1 : ℚ) ^ (d / c) + 1) * b c = 2 * Bhalf b d := by
  by_cases hdd : 2 ∣ d
  · obtain ⟨d', rfl⟩ := hdd
    rcases Nat.eq_zero_or_pos d' with rfl | hd'0
    · simp [Bhalf, Nat.divisors_zero]
    have hd'ne : d' ≠ 0 := hd'0.ne'
    -- collapse the ±1 factor to an indicator of `2 ∣ (2d')/c`
    have step1 : ∑ c ∈ (2 * d').divisors, (c : ℚ) * ((-1 : ℚ) ^ ((2 * d') / c) + 1) * b c
        = ∑ c ∈ (2 * d').divisors.filter (fun c => 2 ∣ (2 * d') / c), (c : ℚ) * 2 * b c := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c _
      set m := (2 * d') / c with hm
      by_cases he : 2 ∣ m
      · obtain ⟨k, hk⟩ := he
        rw [Even.neg_one_pow ⟨k, by omega⟩, if_pos ⟨k, hk⟩]; ring
      · rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega)), if_neg he]; ring
    -- the quotient-even divisors of 2d' are exactly the divisors of d'
    have hset : (2 * d').divisors.filter (fun c => 2 ∣ (2 * d') / c) = d'.divisors := by
      ext c
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hcd, _⟩, k, hk⟩
        have hcc : c * ((2 * d') / c) = 2 * d' := Nat.mul_div_cancel' hcd
        rw [hk] at hcc
        have h2ck : 2 * (c * k) = 2 * d' := by rw [← hcc]; ring
        exact ⟨⟨k, (Nat.eq_of_mul_eq_mul_left (by norm_num) h2ck).symm⟩, hd'ne⟩
      · rintro ⟨hcd', _⟩
        have hc0 : 0 < c := Nat.pos_of_ne_zero (by
          rintro rfl; exact hd'ne (Nat.eq_zero_of_zero_dvd hcd'))
        obtain ⟨t, ht⟩ := hcd'
        refine ⟨⟨Dvd.dvd.mul_left ⟨t, ht⟩ 2, Nat.mul_ne_zero (by norm_num) hd'ne⟩, ?_⟩
        have hdiv : (2 * d') / c = 2 * t := by
          rw [ht, show 2 * (c * t) = c * (2 * t) by ring, Nat.mul_div_cancel_left (2 * t) hc0]
        rw [hdiv]; exact ⟨t, rfl⟩
    rw [step1, hset, Bhalf, if_pos ⟨d', rfl⟩]
    have hdiv : 2 * d' / 2 = d' := by omega
    rw [hdiv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    push_cast; ring
  · rw [Bhalf_odd b hdd, mul_zero]
    apply Finset.sum_eq_zero
    intro c hc
    have hcdvd : c ∣ d := (Nat.mem_divisors.mp hc).1
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    -- d odd ⟹ d/c odd ⟹ (-1)^{d/c} = -1 ⟹ factor 0
    have hqodd : Odd (d / c) := by
      rcases (Nat.even_or_odd (d / c)) with he | ho
      · exfalso
        obtain ⟨k, hk⟩ := he
        have : c * (d / c) = d := Nat.mul_div_cancel' hcdvd
        rw [hk] at this
        exact hdd ⟨c * k, by rw [← this]; ring⟩
      · exact ho
    rw [Odd.neg_one_pow hqodd]; ring

variable (s F I u : ℕ → ℚ)

/-- **The master identity, from the sign law.**  Given `eq_dF` (`hdF`), the
aggregated surface sign law `lem_iteratesigns` (`hiter`), and `s = u − b`
(`hsub`), the ±1 cancellation yields

    d · F(g, dβ₀) = (∑_{c ∣ d} c · s_c) + 2 · B_{d/2}.

This is the hypothesis `hmaster` consumed by the results in
`ArithLaw/DivisorSystem.lean`. -/
theorem master_of_signlaw {Ik : ℕ → ℕ → ℚ} {e : ℕ} (he : 0 < e)
    (hsub : ∀ c, s c = u c - b c)
    (hiter : ∀ c k : ℕ, 1 ≤ k → c * k ∣ e → Ik c k = u c + (-1 : ℚ) ^ k * b c)
    (hdF : ∀ d : ℕ, d ∣ e → (d : ℚ) * F d = ∑ c ∈ d.divisors, (c : ℚ) * Ik c (d / c)) :
    ∀ d : ℕ, d ∣ e →
      (d : ℚ) * F d = (∑ c ∈ d.divisors, (c : ℚ) * s c) + 2 * Bhalf b d := by
  intro d hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd he
  rw [hdF d hd]
  have hstep : ∑ c ∈ d.divisors, (c : ℚ) * Ik c (d / c)
      = ∑ c ∈ d.divisors, ((c : ℚ) * s c + (c : ℚ) * ((-1 : ℚ) ^ (d / c) + 1) * b c) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcdvd : c ∣ d := (Nat.mem_divisors.mp hc).1
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    have hk : 1 ≤ d / c := (Nat.one_le_div_iff hc0).mpr (Nat.le_of_dvd hd0 hcdvd)
    have hck : c * (d / c) ∣ e := by rw [Nat.mul_div_cancel' hcdvd]; exact hd
    rw [hiter c (d / c) hk hck, hsub c]; ring
  rw [hstep, Finset.sum_add_distrib, evenquot b d]

end GeodesicArithmetic
