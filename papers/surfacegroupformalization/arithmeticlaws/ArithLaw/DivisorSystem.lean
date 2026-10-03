/-
# The divisor-system law on surfaces (Proposition `prop_primitivelaw`, §11)

This file formalizes the arithmetic of §11 of *Invariant arithmetic of closed
geodesics*: the divisor-system identity `eq_divisorsystem` and its solution
(`solve_divisorsystem`), the primitive law `prop_primitivelaw` (both
directions), and the unconditional laws `cor_unconditionallaw` (torus) and
`cor_unconditionalsurface` (higher genus), the latter both as the printed
divisor system and solved (`s_1 = 1`, `s_d = −b_{d/2}` for `d > 1`).

Setup (notation of the §11 preamble).  For an indivisible class `β₀` and a
metric that is `eβ₀`-taut and `eβ₀`-regular, `P_c` is the set of prime closed
geodesic strings of class `cβ₀`, and, with `i` the local Fuller index,

* `s c := ∑_{o ∈ P_c} i(o)`                       signed prime count;
* `b c := #{o ∈ P_c : o inverse-hyperbolic}`        inverse-hyperbolic count;
* `u c := #pos-hyperbolic − #elliptic in P_c`,      so `s c = u c − b c`.

The geometry enters through a single identity, the **master identity**, which
is Lemma `lem_mobius` (`eq_dF`, the covering bijection) after the surface sign
law `lem_iteratesigns` has been applied to each iterate `o^{d/c}`:

    d · F(g, dβ₀)  =  (∑_{c ∣ d} c · s_c)  +  2 · B_{d/2},     (master)

where `B_{d/2} = ∑_{f ∣ d/2} f · b_f` for `d` even and `0` for `d` odd.  This
is the hypothesis `hmaster` below, assumed exactly where the paper establishes
it: at the divisor levels `d ∣ e`.  Everything else here is pure arithmetic
over the divisor lattice.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Finset

namespace GeodesicArithmetic

variable (b : ℕ → ℚ)

/-- `b_{c/2}`, with the convention that it is `0` for `c` odd. -/
def bhalf (c : ℕ) : ℚ := if 2 ∣ c then b (c / 2) else 0

/-- `B_{d/2} = ∑_{f ∣ d/2} f · b_f`, with the convention `B_x = 0` for `x` not
an integer (i.e. `d` odd). -/
def Bhalf (d : ℕ) : ℚ := if 2 ∣ d then ∑ f ∈ (d / 2).divisors, (f : ℚ) * b f else 0

theorem bhalf_odd {c : ℕ} (h : ¬ 2 ∣ c) : bhalf b c = 0 := if_neg h
theorem Bhalf_odd {d : ℕ} (h : ¬ 2 ∣ d) : Bhalf b d = 0 := if_neg h

/-- **`eq_evendivisors`**: `∑_{c ∣ d} c · b_{c/2} = 2·B_{d/2}`.  Only even `c`
contribute, and `c = 2f` runs over the divisors of `d/2`. -/
theorem eq_evendivisors (d : ℕ) :
    ∑ c ∈ d.divisors, (c : ℚ) * bhalf b c = 2 * Bhalf b d := by
  by_cases hdd : 2 ∣ d
  · obtain ⟨d', rfl⟩ := hdd
    rcases Nat.eq_zero_or_pos d' with hd'0 | hd'0
    · subst hd'0; simp [Bhalf]
    have hd'ne : d' ≠ 0 := hd'0.ne'
    have step1 : ∑ c ∈ (2 * d').divisors, (c : ℚ) * bhalf b c
        = ∑ c ∈ (2 * d').divisors.filter (fun c => 2 ∣ c), (c : ℚ) * b (c / 2) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : 2 ∣ c <;> simp [bhalf, hc]
    have hset : (2 * d').divisors.filter (fun c => 2 ∣ c)
        = (d').divisors.image (fun f => 2 * f) := by
      ext c
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
      constructor
      · rintro ⟨⟨hcdvd, _⟩, f, rfl⟩
        exact ⟨f, ⟨(Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hcdvd, hd'ne⟩, rfl⟩
      · rintro ⟨f, ⟨hfdvd, _⟩, rfl⟩
        exact ⟨⟨(Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mpr hfdvd,
          Nat.mul_ne_zero (by norm_num) hd'ne⟩, ⟨f, rfl⟩⟩
    have hinj : ∀ x ∈ (d').divisors, ∀ y ∈ (d').divisors, 2 * x = 2 * y → x = y :=
      fun x _ y _ h => by omega
    rw [step1, hset, Finset.sum_image hinj, Bhalf, if_pos ⟨d', rfl⟩]
    have hdiv : 2 * d' / 2 = d' := by omega
    rw [hdiv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    have hf2 : 2 * f / 2 = f := by omega
    rw [hf2]; push_cast; ring
  · rw [Bhalf_odd b hdd, mul_zero]
    apply Finset.sum_eq_zero
    intro c hc
    have hcdvd : c ∣ d := (Nat.mem_divisors.mp hc).1
    have : ¬ 2 ∣ c := fun h2c => hdd (h2c.trans hcdvd)
    rw [bhalf_odd b this, mul_zero]

variable (s : ℕ → ℚ)

/-- **The divisor system `eq_divisorsystem`, solved.**  If
`∑_{c ∣ d} c·s_c = −2·B_{d/2}` for every divisor `d` of `e`, then
`s_d = −b_{d/2}` for every divisor `d` of `e`.  This is the induction over
divisors in the proof of `prop_primitivelaw`. -/
theorem solve_divisorsystem
    {e : ℕ} (he : 0 < e)
    (hsys : ∀ d : ℕ, d ∣ e → ∑ c ∈ d.divisors, (c : ℚ) * s c = - (2 * Bhalf b d)) :
    ∀ n, n ∣ e → s n = - bhalf b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn he
    have hne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn0.ne'
    -- the divisor-system equation at n, split off its top term
    have hsys : (n : ℚ) * s n + ∑ c ∈ n.divisors.erase n, (c : ℚ) * s c = - (2 * Bhalf b n) := by
      rw [Finset.add_sum_erase _ (fun c : ℕ => (c : ℚ) * s c) hmem]
      exact hsys n hn
    -- the full even-divisor sum, split off its top term
    have hfull : (n : ℚ) * bhalf b n + ∑ c ∈ n.divisors.erase n, (c : ℚ) * bhalf b c
        = 2 * Bhalf b n := by
      rw [Finset.add_sum_erase _ (fun c : ℕ => (c : ℚ) * bhalf b c) hmem]
      exact eq_evendivisors b n
    -- the two erased tails cancel, termwise, by the induction hypothesis
    have hzero : ∑ c ∈ n.divisors.erase n, ((c : ℚ) * s c + (c : ℚ) * bhalf b c) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      obtain ⟨hcne, hcmem⟩ := Finset.mem_erase.mp hc
      have hcdvd : c ∣ n := (Nat.mem_divisors.mp hcmem).1
      have hlt : c < n := lt_of_le_of_ne (Nat.divisor_le hcmem) hcne
      rw [ih c hlt (hcdvd.trans hn)]; ring
    rw [Finset.sum_add_distrib] at hzero
    have hkey : (n : ℚ) * (s n + bhalf b n) = 0 := by rw [mul_add]; linarith
    have hsum0 : s n + bhalf b n = 0 := (mul_eq_zero.mp hkey).resolve_left hne
    linarith

variable (F : ℕ → ℚ)

/-- **`prop_primitivelaw`, forward direction.**  If `F(g, dβ₀) = 0` for every
divisor `d` of `e`, then `s_d = −b_{d/2}` for every divisor `d` of `e`; at
`d = e` this is `eq_primitivelaw`. -/
theorem primitivelaw_forward
    {e : ℕ} (he : 0 < e)
    (hmaster : ∀ d : ℕ, d ∣ e →
      (d : ℚ) * F d = (∑ c ∈ d.divisors, (c : ℚ) * s c) + 2 * Bhalf b d) (hF : ∀ d, d ∣ e → F d = 0) :
    ∀ n, n ∣ e → s n = - bhalf b n :=
  solve_divisorsystem b s he (fun d hd => by
    have hm := hmaster d hd
    rw [hF d hd, mul_zero] at hm
    linarith)

/-- **`prop_primitivelaw`, converse direction.**  If `s_d = −b_{d/2}` for every
divisor `d` of `e`, then `F(g, dβ₀) = 0` for every divisor `d` of `e`. -/
theorem primitivelaw_converse
    {e : ℕ} (he : 0 < e)
    (hmaster : ∀ d : ℕ, d ∣ e →
      (d : ℚ) * F d = (∑ c ∈ d.divisors, (c : ℚ) * s c) + 2 * Bhalf b d) (hs : ∀ d, d ∣ e → s d = - bhalf b d) :
    ∀ d, d ∣ e → F d = 0 := by
  intro d hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd he
  have hne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hzero : ∑ c ∈ d.divisors, ((c : ℚ) * s c + (c : ℚ) * bhalf b c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have hcdvd : c ∣ d := (Nat.mem_divisors.mp hc).1
    rw [hs c (hcdvd.trans hd)]; ring
  rw [Finset.sum_add_distrib, eq_evendivisors b d] at hzero
  have hmul : (d : ℚ) * F d = 0 := by rw [hmaster d hd]; linarith
  exact (mul_eq_zero.mp hmul).resolve_left hne

/-- **`cor_unconditionallaw`** (torus).  When `F` vanishes on the divisors of
`e` — automatic on `T²` by `thm_torusvanishing` — the signed prime count obeys
`s_e = −b_{e/2}`. -/
theorem unconditional_torus
    {e : ℕ} (he : 0 < e)
    (hmaster : ∀ d : ℕ, d ∣ e →
      (d : ℚ) * F d = (∑ c ∈ d.divisors, (c : ℚ) * s c) + 2 * Bhalf b d) (hF : ∀ d, d ∣ e → F d = 0) :
    s e = - bhalf b e :=
  primitivelaw_forward b s F he hmaster hF e dvd_rfl

/-- **`cor_unconditionalsurface`** (genus ≥ 2).  When `F(g, dβ₀) = 1/d` on the
divisors of `e` — automatic by `thm_surfacevanishing` — the signed counts obey
the divisor system `∑_{c ∣ d} c·s_c = 1 − 2·B_{d/2}` for every `d ∣ e`. -/
theorem unconditional_surface
    {e : ℕ} (he : 0 < e)
    (hmaster : ∀ d : ℕ, d ∣ e →
      (d : ℚ) * F d = (∑ c ∈ d.divisors, (c : ℚ) * s c) + 2 * Bhalf b d) (hF : ∀ d, d ∣ e → F d = 1 / (d : ℚ)) :
    ∀ d, d ∣ e → (∑ c ∈ d.divisors, (c : ℚ) * s c) = 1 - 2 * Bhalf b d := by
  intro d hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd he
  have hne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hm := hmaster d hd
  rw [hF d hd, mul_one_div, div_self hne] at hm
  linarith

/-- **`cor_unconditionalsurface`, solved.**  The surface divisor system
`∑_{c ∣ d} c·s_c = 1 − 2·B_{d/2}` (`d ∣ e`) has the unique solution
`s_1 = 1`, `s_d = −b_{d/2}` for `d > 1`: shifting `s_1` by `1` turns it into
the torus system `eq_divisorsystem`, which `solve_divisorsystem` solves. -/
theorem unconditional_surface_solution
    {e : ℕ} (he : 0 < e)
    (hmaster : ∀ d : ℕ, d ∣ e →
      (d : ℚ) * F d = (∑ c ∈ d.divisors, (c : ℚ) * s c) + 2 * Bhalf b d) (hF : ∀ d, d ∣ e → F d = 1 / (d : ℚ)) :
    ∀ d, d ∣ e → s d = (if d = 1 then 1 else 0) - bhalf b d := by
  have hsurf := unconditional_surface b s F he hmaster hF
  -- the shifted counts satisfy the torus system
  have hsys : ∀ d : ℕ, d ∣ e →
      ∑ c ∈ d.divisors, (c : ℚ) * (s c - (if c = 1 then 1 else 0)) = - (2 * Bhalf b d) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd he
    have h1 : ∑ c ∈ d.divisors, (c : ℚ) * (if c = 1 then (1 : ℚ) else 0) = 1 := by
      rw [Finset.sum_eq_single 1 (fun c _ hc => by simp [hc])
        (fun h => absurd (Nat.one_mem_divisors.mpr hd0.ne') h)]
      simp
    have hsplit : ∑ c ∈ d.divisors, (c : ℚ) * (s c - (if c = 1 then 1 else 0))
        = ∑ c ∈ d.divisors, (c : ℚ) * s c
          - ∑ c ∈ d.divisors, (c : ℚ) * (if c = 1 then (1 : ℚ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hsplit, hsurf d hd, h1]; ring
  intro d hd
  have h : s d - (if d = 1 then 1 else 0) = - bhalf b d :=
    solve_divisorsystem b (fun c => s c - (if c = 1 then 1 else 0)) he hsys d hd
  linarith

end GeodesicArithmetic
