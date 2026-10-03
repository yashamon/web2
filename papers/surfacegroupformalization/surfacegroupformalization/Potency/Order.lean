/-
# The exact-order engine

From the Magnus data of `x ≠ 1` — a unit `u = magnus x` of `NC k ℤ` with
constant term `1` and a nonzero coefficient on some nonempty word — we
manufacture, for every prime `p`, a finite group in which the image of `u`
has order *exactly* `p`:

1. Let `c` be the least positive degree carrying a nonzero coefficient of
   `u` (exists by hypothesis).  Truncate at `c`: the image is `1 + P` with
   `P` supported on words of length exactly `c`, so `P * P = 0` and
   `(1 + P)^m = 1 + m • P` — powers are *affine* in the truncation.
2. Let `s` be the least `p`-valuation of the (integer) coefficients of `P`.
   Reduce coefficients mod `p^(s+1)`: then `p • P̄ = 0` while `P̄ ≠ 0`, so
   `(1 + P̄)` has order exactly `p` in the units of the finite ring
   `TNC k c (ZMod (p^(s+1)))`.

This discharges, for free groups, what the paper's Lemma 6.9 obtained from
residual torsion-free nilpotence of free groups [Magnus], the structure of
the lower central series [Witt], and residual finiteness of f.g. nilpotent
groups [Segal] — none of which are needed here.
-/
import Potency.Magnus
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace Potency

variable {k : ℕ}

/-- If `y ≠ 0`, then some power of `p ≥ 2` fails to divide `y`. -/
theorem exists_pow_not_dvd {p : ℕ} (hp : 2 ≤ p) {y : ℤ} (hy : y ≠ 0) :
    ∃ s : ℕ, ¬ ((p : ℤ) ^ s ∣ y) := by
  refine ⟨y.natAbs, fun hdvd => ?_⟩
  have h1 : ((p : ℤ)) ^ y.natAbs = ((p ^ y.natAbs : ℕ) : ℤ) := by push_cast; ring
  rw [h1] at hdvd
  have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
  rw [Int.natAbs_natCast] at h2
  have h3 : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
  have h4 : y.natAbs < p ^ y.natAbs := Nat.lt_pow_self hp
  have h5 := Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2
  omega

/-- Affine powers: if `Q * Q = 0` then `(1 + Q) ^ n = 1 + n • Q`. -/
theorem one_add_pow_of_mul_self_eq_zero {A : Type*} [Ring A] (Q : A) (hQ : Q * Q = 0) :
    ∀ n : ℕ, (1 + Q) ^ n = 1 + n • Q
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, one_add_pow_of_mul_self_eq_zero Q hQ n, mul_add, mul_one, add_mul, one_mul,
      smul_mul_assoc, hQ, smul_zero, add_zero, add_assoc, ← succ_nsmul]

/-- **The exact-order engine.**  A unit of `NC k ℤ` with constant term `1`
and a nonzero coefficient on a nonempty word maps, for every prime `p`, onto
an element of order exactly `p` in a finite group. -/
theorem exists_finite_orderOf_eq (u : (NC k ℤ)ˣ)
    (hct : NC.coeff ((u : (NC k ℤ)ˣ) : NC k ℤ) [] = 1)
    (hne : ∃ M : Word k, M ≠ [] ∧ NC.coeff ((u : (NC k ℤ)ˣ) : NC k ℤ) M ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (φ : (NC k ℤ)ˣ →* Q),
      orderOf (φ u) = p := by
  classical
  obtain ⟨M₀, hM₀ne, hM₀⟩ := hne
  -- the least positive degree carrying a nonzero coefficient
  have hD : ∃ n : ℕ, ∃ M : Word k, M.length = n + 1 ∧ NC.coeff (u : NC k ℤ) M ≠ 0 := by
    refine ⟨M₀.length - 1, M₀, ?_, hM₀⟩
    have h0 : M₀.length ≠ 0 := by
      intro h
      exact hM₀ne (List.eq_nil_of_length_eq_zero h)
    omega
  set c : ℕ := Nat.find hD + 1 with hc
  obtain ⟨M₁, hM₁len, hM₁⟩ := Nat.find_spec hD
  have hM₁c : M₁.length = c := by rw [hM₁len, hc]
  have hmin : ∀ m, 1 ≤ m → m < c → ∀ M : Word k, M.length = m →
      NC.coeff (u : NC k ℤ) M = 0 := by
    intro m hm1 hmc M hMlen
    by_contra hne0
    have hfound : Nat.find hD ≤ m - 1 := Nat.find_le ⟨M, by omega, hne0⟩
    omega
  -- truncate at c; P := (image of u) - 1 is supported in degree exactly c
  set P : TNC k c ℤ := NC.trunc c (u : NC k ℤ) - 1 with hP
  have hPapp : ∀ w : BWord k c, P w = NC.coeff (u : NC k ℤ) w.1 - (if w.1 = [] then 1 else 0) := by
    intro w
    rw [hP, TNC.sub_apply, NC.trunc_apply, TNC.one_apply]
  have hPsupp : ∀ w : BWord k c, P w ≠ 0 → w.1.length = c := by
    intro w hw
    by_contra hlen
    have hlt : w.1.length < c := lt_of_le_of_ne w.2 hlen
    apply hw
    rw [hPapp]
    rcases Nat.eq_zero_or_pos w.1.length with h0 | hpos
    · have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero h0
      rw [hnil, hct, if_pos rfl, sub_self]
    · have hnnil : w.1 ≠ [] := by
        intro h
        rw [h] at hpos
        simp at hpos
      rw [hmin w.1.length hpos hlt w.1 rfl, if_neg hnnil, sub_zero]
  have hPM₁ : P ⟨M₁, le_of_eq hM₁c⟩ ≠ 0 := by
    rw [hPapp ⟨M₁, le_of_eq hM₁c⟩]
    have hM₁ne : M₁ ≠ [] := by
      intro h
      rw [h] at hM₁len
      simp at hM₁len
    rw [if_neg hM₁ne, sub_zero]
    exact hM₁
  -- P * P = 0 : two degree-c factors overflow the degree-c truncation
  have hPP : P * P = 0 := by
    funext w
    show (P * P) w = (0 : TNC k c ℤ) w
    rw [TNC.mul_apply, TNC.zero_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    by_cases h1 : P (TNC.tk w i) = 0
    · rw [h1, zero_mul]
    · have hlen1 := hPsupp _ h1
      rw [TNC.tk_val, List.length_take] at hlen1
      have hdrop : (TNC.dr w i).1 = [] := by
        rw [TNC.dr_val, List.drop_eq_nil_iff]
        have := w.2
        omega
      have h2 : P (TNC.dr w i) = 0 := by
        by_contra hne0
        have hlen2 := hPsupp _ hne0
        rw [hdrop] at hlen2
        simp only [List.length_nil] at hlen2
        omega
      rw [h2, mul_zero]
  -- the p-valuation of P
  have hE : ∃ s : ℕ, ∃ w : BWord k c, ¬ ((p : ℤ) ^ (s + 1) ∣ P w) := by
    obtain ⟨s, hs⟩ := exists_pow_not_dvd hp.two_le hPM₁
    cases s with
    | zero =>
      refine absurd (one_dvd (P ⟨M₁, le_of_eq hM₁c⟩)) ?_
      simpa using hs
    | succ s => exact ⟨s, ⟨M₁, le_of_eq hM₁c⟩, hs⟩
  set s : ℕ := Nat.find hE with hs
  obtain ⟨w₁, hw₁⟩ := Nat.find_spec hE
  have hall : ∀ w : BWord k c, (p : ℤ) ^ s ∣ P w := by
    intro w
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0, pow_zero]
      exact one_dvd _
    · by_contra hnd
      have hprop : ∃ w : BWord k c, ¬ ((p : ℤ) ^ ((s - 1) + 1) ∣ P w) := by
        refine ⟨w, ?_⟩
        rwa [show s - 1 + 1 = s by omega]
      exact absurd hprop (Nat.find_min hE (by omega))
  -- reduce coefficients mod p^(s+1)
  haveI hfact : Fact p.Prime := ⟨hp⟩
  haveI hnz : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set ρ : TNC k c ℤ →+* TNC k c (ZMod (p ^ (s + 1))) :=
    TNC.mapCoeff (Int.castRingHom (ZMod (p ^ (s + 1)))) with hρ
  haveI hTNCfin : Finite (TNC k c (ZMod (p ^ (s + 1)))) := inferInstance
  refine ⟨(TNC k c (ZMod (p ^ (s + 1))))ˣ, inferInstance,
    Finite.of_injective Units.val (fun _ _ h => Units.ext h),
    Units.map (ρ.comp (NC.trunc c)).toMonoidHom, ?_⟩
  set φ : (NC k ℤ)ˣ →* (TNC k c (ZMod (p ^ (s + 1))))ˣ :=
    Units.map (ρ.comp (NC.trunc c)).toMonoidHom with hφ
  have hφval : ((φ u : (TNC k c (ZMod (p ^ (s + 1))))ˣ) : TNC k c (ZMod (p ^ (s + 1))))
      = 1 + ρ P := by
    show ρ (NC.trunc c (u : NC k ℤ)) = 1 + ρ P
    rw [hP, map_sub, map_one,
      add_comm 1 (ρ (NC.trunc c (u : NC k ℤ)) - 1), sub_add_cancel]
  have hPbar : ρ P * ρ P = 0 := by rw [← map_mul, hPP, map_zero]
  -- p • (ρ P) = 0 : every coefficient of P is divisible by p^s
  have hpP : p • (ρ P) = 0 := by
    funext w
    show p • (ρ P) w = (0 : TNC k c (ZMod (p ^ (s + 1)))) w
    rw [TNC.zero_apply, hρ, TNC.mapCoeff_apply]
    obtain ⟨y, hy⟩ := hall w
    rw [nsmul_eq_mul]
    rw [show ((Int.castRingHom (ZMod (p ^ (s + 1)))) (P w))
        = ((P w : ℤ) : ZMod (p ^ (s + 1))) from rfl]
    rw [show ((p : ℕ) : ZMod (p ^ (s + 1))) * ((P w : ℤ) : ZMod (p ^ (s + 1)))
        = (((p : ℤ) * P w : ℤ) : ZMod (p ^ (s + 1))) by push_cast; ring]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨y, by rw [hy]; push_cast; ring⟩
  have hppow : (φ u) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hφval, Units.val_one,
      one_add_pow_of_mul_self_eq_zero (ρ P) hPbar p, hpP, add_zero]
  have hne1 : φ u ≠ 1 := by
    intro h
    apply hw₁
    have hval := congrArg Units.val h
    rw [hφval, Units.val_one] at hval
    have hρP : ρ P = 0 := by
      have h2 := congrArg (fun z => z - (1 : TNC k c (ZMod (p ^ (s + 1))))) hval
      simpa using h2
    have h3 := congrFun hρP w₁
    rw [hρ] at h3
    rw [TNC.mapCoeff_apply] at h3
    rw [show (0 : TNC k c (ZMod (p ^ (s + 1)))) w₁ = 0 from rfl] at h3
    rw [show ((Int.castRingHom (ZMod (p ^ (s + 1)))) (P w₁))
        = ((P w₁ : ℤ) : ZMod (p ^ (s + 1))) from rfl] at h3
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
    obtain ⟨y, hy⟩ := h3
    exact ⟨y, by rw [hy]; push_cast; ring⟩
  exact orderOf_eq_prime hppow hne1

/-- **Free groups are potent** (the R3 payload): every `x ≠ 1` in a finitely
generated free group has, for every prime `p`, a finite quotient in which
its image has order exactly `p`.  Self-contained: truncated Magnus embedding
plus the syllable-coefficient computation. -/
theorem freeGroup_exists_orderOf_eq (x : FreeGroup (Fin k)) (hx : x ≠ 1)
    {p : ℕ} (hp : p.Prime) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (π : FreeGroup (Fin k) →* Q),
      orderOf (π x) = p := by
  obtain ⟨Q, hG, hF, φ, hφ⟩ :=
    exists_finite_orderOf_eq (magnus x) (constantCoeff_magnus x) (exists_coeff_ne_zero hx) hp
  exact ⟨Q, hG, hF, φ.comp magnus, hφ⟩

end Potency
