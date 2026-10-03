/-
# Noncommutative power series on a free monoid, and their bounded truncations

This file is part of the formalization of Lemma 6.9 ("potency of surface
groups") of *Invariant arithmetic of closed geodesics*.  It builds, from
scratch:

* `Potency.NC k R` — the ring of noncommutative formal power series in `k`
  variables over `R`, realized as arbitrary coefficient functions
  `List (Fin k) → R` with convolution product.  (Mathlib's `MonoidAlgebra`
  is finitely supported, hence has no inverses for `1 + X`; we need the
  full function space.)
* `Potency.NC.constantCoeff` — the constant-term ring homomorphism.
* `Potency.NC.unitOfCT` — every series with constant term `1` is a unit,
  with inverse built by recursion on word length.
* `Potency.TNC k c R` — the truncation to words of length `≤ c`, again a
  ring; `Potency.NC.trunc` is the truncation ring homomorphism.  When `R`
  is finite, `TNC k c R` is a *finite* ring, so its unit group is a finite
  group: this is the sole source of finite quotients in the potency proof.
* `Potency.TNC.mapCoeff` — coefficientwise reduction along `R →+* S`
  (used with `ℤ →+* ZMod (p ^ (s+1))`).

Everything is elementary; the only Mathlib inputs are `Finset.range` sums
and basic `List.take`/`List.drop` lemmas.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

namespace Potency

/-- Words in `k` letters: the free monoid on `Fin k`, as bare lists. -/
abbrev Word (k : ℕ) := List (Fin k)

section ListHelpers

variable {α : Type*}

/-- `(l.take n).take m = l.take m` for `m ≤ n` (self-contained helper). -/
theorem take_take_of_le : ∀ (l : List α) {m n : ℕ}, m ≤ n → (l.take n).take m = l.take m
  | _, 0, _, _ => by simp
  | [], _ + 1, _, _ => by simp
  | _ :: _, _ + 1, 0, h => by omega
  | a :: l, m + 1, n + 1, h => by
    simpa using take_take_of_le l (Nat.le_of_succ_le_succ h)

/-- `(l.take m).drop n = (l.drop n).take (m - n)` (self-contained helper). -/
theorem drop_take' : ∀ (l : List α) (m n : ℕ), (l.take m).drop n = (l.drop n).take (m - n)
  | l, m, 0 => by simp
  | [], _, _ + 1 => by simp
  | _ :: _, 0, _ + 1 => by simp
  | a :: l, m + 1, n + 1 => by simpa using drop_take' l m n

/-- `(l.drop m).drop n = l.drop (m + n)` (self-contained helper). -/
theorem drop_drop' : ∀ (l : List α) (m n : ℕ), (l.drop m).drop n = l.drop (m + n)
  | _, 0, _ => by simp
  | [], _ + 1, _ => by simp
  | a :: l, m + 1, n => by simpa [Nat.succ_add] using drop_drop' l m n

end ListHelpers

/-- Noncommutative formal power series in `k` variables over `R`: arbitrary
coefficient functions on words, with convolution product.  `NC` is a `def`,
not an `abbrev`, so the pointwise `Pi` multiplication does not leak in; the
only instances are the ones declared below. -/
def NC (k : ℕ) (R : Type*) : Type _ := Word k → R

namespace NC

variable {k : ℕ} {R : Type*} [Ring R]

instance : AddCommGroup (NC k R) := Pi.addCommGroup

/-- The coefficient of the word `w` in `f`. -/
def coeff (f : NC k R) (w : Word k) : R := f w

theorem coeff_def (f : NC k R) (w : Word k) : coeff f w = f w := rfl

@[ext]
theorem ext {f g : NC k R} (h : ∀ w, coeff f w = coeff g w) : f = g := funext h

@[simp] theorem coeff_add (f g : NC k R) (w : Word k) :
    coeff (f + g) w = coeff f w + coeff g w := rfl

@[simp] theorem coeff_zero (w : Word k) : coeff (0 : NC k R) w = 0 := rfl

@[simp] theorem coeff_neg (f : NC k R) (w : Word k) : coeff (-f) w = -(coeff f w) := rfl

@[simp] theorem coeff_sub (f g : NC k R) (w : Word k) :
    coeff (f - g) w = coeff f w - coeff g w := rfl

@[simp] theorem coeff_nsmul (n : ℕ) (f : NC k R) (w : Word k) :
    coeff (n • f) w = n • coeff f w := rfl

@[simp] theorem coeff_zsmul (n : ℤ) (f : NC k R) (w : Word k) :
    coeff (n • f) w = n • coeff f w := rfl

instance : One (NC k R) := ⟨fun w => if w = [] then 1 else 0⟩

theorem coeff_one (w : Word k) : coeff (1 : NC k R) w = if w = [] then 1 else 0 := rfl

@[simp] theorem coeff_one_nil : coeff (1 : NC k R) ([] : Word k) = 1 := rfl

theorem coeff_one_ne_nil {w : Word k} (h : w ≠ []) : coeff (1 : NC k R) w = 0 := if_neg h

instance : NatCast (NC k R) := ⟨fun n w => if w = [] then (n : R) else 0⟩
instance : IntCast (NC k R) := ⟨fun n w => if w = [] then (n : R) else 0⟩

theorem coeff_natCast (n : ℕ) (w : Word k) :
    coeff (n : NC k R) w = if w = [] then (n : R) else 0 := rfl
theorem coeff_intCast (n : ℤ) (w : Word k) :
    coeff (n : NC k R) w = if w = [] then (n : R) else 0 := rfl

/-- Convolution product: the coefficient of `w` in `f * g` is the sum over
all two-part splittings of `w`. -/
instance : Mul (NC k R) :=
  ⟨fun f g w => ∑ i ∈ Finset.range (w.length + 1), f (w.take i) * g (w.drop i)⟩

theorem coeff_mul (f g : NC k R) (w : Word k) :
    coeff (f * g) w
      = ∑ i ∈ Finset.range (w.length + 1), coeff f (w.take i) * coeff g (w.drop i) := rfl

protected theorem one_mul (f : NC k R) : 1 * f = f := by
  ext w
  rw [coeff_mul]
  refine (Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _)) ?_).trans ?_
  · intro i hi hi0
    have hw : w ≠ [] := by
      rintro rfl
      simp only [Finset.mem_range, List.length_nil] at hi
      omega
    have : w.take i ≠ [] := by
      rw [Ne, List.take_eq_nil_iff]
      push_neg
      exact ⟨hi0, hw⟩
    rw [coeff_one_ne_nil this, zero_mul]
  · simp

protected theorem mul_one (f : NC k R) : f * 1 = f := by
  ext w
  rw [coeff_mul]
  refine (Finset.sum_eq_single_of_mem w.length
    (Finset.mem_range.mpr (Nat.lt_succ_self _)) ?_).trans ?_
  · intro i hi hine
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have : w.drop i ≠ [] := by
      rw [Ne, List.drop_eq_nil_iff]
      omega
    rw [coeff_one_ne_nil this, mul_zero]
  · rw [List.take_length, List.drop_length, coeff_one_nil, mul_one]

protected theorem mul_assoc (f g h : NC k R) : f * g * h = f * (g * h) := by
  ext w
  rw [coeff_mul, coeff_mul]
  have L1 : ∀ i ∈ Finset.range (w.length + 1),
      coeff (f * g) (w.take i) * coeff h (w.drop i)
        = ∑ j ∈ Finset.range (i + 1),
            coeff f (w.take j) * (coeff g ((w.drop j).take (i - j)) * coeff h (w.drop i)) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [coeff_mul, List.length_take, Nat.min_eq_left hi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    rw [take_take_of_le _ hj, drop_take', mul_assoc]
  have R1 : ∀ j ∈ Finset.range (w.length + 1),
      coeff f (w.take j) * coeff (g * h) (w.drop j)
        = ∑ t ∈ Finset.range (w.length - j + 1),
            coeff f (w.take j) * (coeff g ((w.drop j).take t) * coeff h (w.drop (j + t))) := by
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    rw [coeff_mul, List.length_drop, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [drop_drop']
  rw [Finset.sum_congr rfl L1, Finset.sum_congr rfl R1, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 - p.2⟩) (fun p => ⟨p.1 + p.2, p.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_sigma, Finset.mem_range] at hij
    have h1 : j < w.length + 1 := by omega
    have h2 : i - j < w.length - j + 1 := by omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩
  · rintro ⟨j, t⟩ hjt
    simp only [Finset.mem_sigma, Finset.mem_range] at hjt
    have h1 : j + t < w.length + 1 := by omega
    have h2 : j < j + t + 1 := by omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_sigma, Finset.mem_range] at hij
    have h1 : j + (i - j) = i := by omega
    show (⟨j + (i - j), j⟩ : Σ _ : ℕ, ℕ) = ⟨i, j⟩
    rw [h1]
  · rintro ⟨j, t⟩ hjt
    simp only [Finset.mem_sigma, Finset.mem_range] at hjt
    have h1 : j + t - j = t := by omega
    show (⟨j, j + t - j⟩ : Σ _ : ℕ, ℕ) = ⟨j, t⟩
    rw [h1]
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_sigma, Finset.mem_range] at hij
    have hji : j ≤ i := by omega
    simp only []
    rw [Nat.add_sub_cancel' hji]

protected theorem left_distrib (f g h : NC k R) : f * (g + h) = f * g + f * h := by
  ext w
  simp only [coeff_mul, coeff_add, mul_add, Finset.sum_add_distrib]

protected theorem right_distrib (f g h : NC k R) : (f + g) * h = f * h + g * h := by
  ext w
  simp only [coeff_mul, coeff_add, add_mul, Finset.sum_add_distrib]

protected theorem zero_mul (f : NC k R) : 0 * f = 0 := by
  ext w; simp [coeff_mul]

protected theorem mul_zero (f : NC k R) : f * 0 = 0 := by
  ext w; simp [coeff_mul]

protected theorem natCast_succ (n : ℕ) : ((n + 1 : ℕ) : NC k R) = (n : NC k R) + 1 := by
  ext w
  by_cases h : w = [] <;> simp [coeff_natCast, coeff_one, h]

instance instRing : Ring (NC k R) :=
  { (inferInstance : AddCommGroup (NC k R)) with
    mul := (· * ·)
    one := (1 : NC k R)
    natCast := fun n => (n : NC k R)
    intCast := fun n => (n : NC k R)
    mul_assoc := NC.mul_assoc
    one_mul := NC.one_mul
    mul_one := NC.mul_one
    left_distrib := NC.left_distrib
    right_distrib := NC.right_distrib
    zero_mul := NC.zero_mul
    mul_zero := NC.mul_zero
    natCast_zero := by ext w; simp [coeff_natCast]
    natCast_succ := NC.natCast_succ
    intCast_ofNat := by intro n; ext w; by_cases h : w = [] <;>
      simp [coeff_natCast, coeff_intCast, h]
    intCast_negSucc := by intro n; ext w; by_cases h : w = [] <;>
      simp [coeff_natCast, coeff_intCast, h, Int.negSucc_eq] }

/-- The constant term, as a ring homomorphism. -/
def constantCoeff : NC k R →+* R where
  toFun f := coeff f []
  map_one' := coeff_one_nil
  map_mul' f g := by
    rw [coeff_mul]
    simp
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem constantCoeff_apply (f : NC k R) : constantCoeff f = coeff f [] := rfl

/-- The `i`-th variable. -/
def X (i : Fin k) : NC k R := fun w => if w = [i] then 1 else 0

@[simp] theorem coeff_X (i : Fin k) (w : Word k) :
    coeff (X i : NC k R) w = if w = [i] then 1 else 0 := rfl

@[simp] theorem constantCoeff_X (i : Fin k) : constantCoeff (X i : NC k R) = 0 := by
  simp [constantCoeff_apply, coeff_X]

/-! ### Inverses of constant-term-one series -/

/-- Inverse coefficients of a constant-term-one series, by recursion on word
length: `g [] = 1` and, on a word of length `n + 1`,
`g w = -∑_{i=0}^{n} f (w.take (i+1)) * g (w.drop (i+1))`. -/
def invCoeff (f : NC k R) : ℕ → Word k → R
  | 0, _ => 1
  | n + 1, w =>
    -∑ i ∈ Finset.range (n + 1), f (w.take (i + 1)) * invCoeff f (n - i) (w.drop (i + 1))
termination_by n _ => n
decreasing_by omega

/-- The inverse series of a constant-term-one series. -/
def invSeries (f : NC k R) : NC k R := fun w => invCoeff f w.length w

@[simp] theorem constantCoeff_invSeries (f : NC k R) : constantCoeff (invSeries f) = 1 := by
  show invCoeff f ([] : Word k).length [] = 1
  simp [invCoeff]

theorem mul_invSeries (f : NC k R) (hf : constantCoeff f = 1) : f * invSeries f = 1 := by
  have hf' : f [] = 1 := hf
  ext w
  rw [coeff_mul]
  cases w with
  | nil =>
    rw [show ([] : Word k).length + 1 = 1 from rfl, Finset.sum_range_one]
    show f [] * invCoeff f 0 [] = NC.coeff 1 []
    rw [NC.coeff_one_nil, hf']
    simp [invCoeff]
  | cons a t =>
    rw [coeff_one_ne_nil (List.cons_ne_nil a t), Finset.sum_range_succ']
    simp only [coeff, invSeries, List.length_drop, List.length_cons, Nat.succ_sub_succ,
      List.take_zero, List.drop_zero, hf', one_mul]
    rw [invCoeff]
    exact add_neg_cancel _

theorem invSeries_mul (f : NC k R) (hf : constantCoeff f = 1) : invSeries f * f = 1 := by
  have h1 : f * invSeries f = 1 := mul_invSeries f hf
  have h2 : invSeries f * invSeries (invSeries f) = 1 :=
    mul_invSeries (invSeries f) (constantCoeff_invSeries f)
  calc invSeries f * f
      = invSeries f * f * (invSeries f * invSeries (invSeries f)) := by rw [h2, mul_one]
    _ = invSeries f * (f * invSeries f) * invSeries (invSeries f) := by
        rw [← mul_assoc, mul_assoc (invSeries f) f (invSeries f)]
    _ = invSeries f * invSeries (invSeries f) := by rw [h1, mul_one]
    _ = 1 := h2

/-- A series with constant term `1` is a unit. -/
def unitOfCT (f : NC k R) (hf : constantCoeff f = 1) : (NC k R)ˣ :=
  ⟨f, invSeries f, mul_invSeries f hf, invSeries_mul f hf⟩

@[simp] theorem unitOfCT_val (f : NC k R) (hf : constantCoeff f = 1) :
    ((unitOfCT f hf : (NC k R)ˣ) : NC k R) = f := rfl

end NC

/-! ### The truncated algebra -/

/-- Words of length at most `c`. -/
def BWord (k c : ℕ) : Type := {w : Word k // w.length ≤ c}

/-- The truncation of `NC k R` to words of length `≤ c`: coefficient
functions on bounded words, with truncated convolution.  A *finite* ring
when `R` is finite. -/
def TNC (k c : ℕ) (R : Type*) : Type _ := BWord k c → R

namespace TNC

variable {k c : ℕ} {R S : Type*} [Ring R] [Ring S]

instance : AddCommGroup (TNC k c R) := Pi.addCommGroup

/-- Truncated take (stays a bounded word). -/
def tk (w : BWord k c) (i : ℕ) : BWord k c :=
  ⟨w.1.take i, by rw [List.length_take]; exact le_trans (Nat.min_le_right _ _) w.2⟩

/-- Truncated drop (stays a bounded word). -/
def dr (w : BWord k c) (i : ℕ) : BWord k c :=
  ⟨w.1.drop i, by rw [List.length_drop]; exact le_trans (Nat.sub_le _ _) w.2⟩

@[simp] theorem tk_val (w : BWord k c) (i : ℕ) : (tk w i).1 = w.1.take i := rfl
@[simp] theorem dr_val (w : BWord k c) (i : ℕ) : (dr w i).1 = w.1.drop i := rfl

instance : One (TNC k c R) := ⟨fun w => if w.1 = [] then 1 else 0⟩
instance : Mul (TNC k c R) :=
  ⟨fun f g w => ∑ i ∈ Finset.range (w.1.length + 1), f (tk w i) * g (dr w i)⟩
instance : NatCast (TNC k c R) := ⟨fun n w => if w.1 = [] then (n : R) else 0⟩
instance : IntCast (TNC k c R) := ⟨fun n w => if w.1 = [] then (n : R) else 0⟩
instance : Pow (TNC k c R) ℕ := ⟨fun f n => npowRec n f⟩

theorem mul_apply (f g : TNC k c R) (w : BWord k c) :
    (f * g) w = ∑ i ∈ Finset.range (w.1.length + 1), f (tk w i) * g (dr w i) := rfl

theorem one_apply (w : BWord k c) : (1 : TNC k c R) w = if w.1 = [] then 1 else 0 := rfl

@[simp] theorem add_apply (f g : TNC k c R) (w : BWord k c) : (f + g) w = f w + g w := rfl
@[simp] theorem sub_apply (f g : TNC k c R) (w : BWord k c) : (f - g) w = f w - g w := rfl
@[simp] theorem neg_apply (f : TNC k c R) (w : BWord k c) : (-f) w = -(f w) := rfl
@[simp] theorem zero_apply (w : BWord k c) : (0 : TNC k c R) w = 0 := rfl
@[simp] theorem nsmul_apply (n : ℕ) (f : TNC k c R) (w : BWord k c) :
    (n • f) w = n • (f w) := rfl

end TNC

namespace NC

variable {k : ℕ} {R S : Type*} [Ring R] [Ring S]

/-- Truncation of a series to words of length `≤ c` (bare function). -/
def truncFun (c : ℕ) (f : NC k R) : TNC k c R := fun w => f w.1

theorem truncFun_surjective (k c : ℕ) (R : Type*) [Ring R] :
    Function.Surjective (truncFun (k := k) c (R := R)) := by
  intro F
  classical
  refine ⟨fun w => if h : w.length ≤ c then F ⟨w, h⟩ else 0, ?_⟩
  funext w
  show (if h : w.1.length ≤ c then F ⟨w.1, h⟩ else 0) = F w
  rw [dif_pos w.2]
  exact congrArg F (Subtype.ext rfl)

theorem truncFun_pow (c : ℕ) (f : NC k R) (n : ℕ) :
    truncFun c (f ^ n) = (truncFun c f) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc truncFun c (f ^ (n + 1)) = truncFun c (f ^ n * f) := by rw [pow_succ]
      _ = truncFun c (f ^ n) * truncFun c f := rfl
      _ = (truncFun c f) ^ n * truncFun c f := by rw [ih]
      _ = (truncFun c f) ^ (n + 1) := rfl

instance : Ring (TNC k c R) :=
  Function.Surjective.ring (truncFun c) (truncFun_surjective k c R)
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (truncFun_pow c) (fun _ => rfl) (fun _ => rfl)

/-- Truncation as a ring homomorphism. -/
def trunc (c : ℕ) : NC k R →+* TNC k c R where
  toFun := truncFun c
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem trunc_apply (c : ℕ) (f : NC k R) (w : BWord k c) :
    trunc c f w = coeff f w.1 := rfl

end NC

namespace TNC

variable {k c : ℕ} {R S : Type*} [Ring R] [Ring S]

/-- Coefficientwise reduction along a ring homomorphism `R →+* S`. -/
def mapCoeff (g : R →+* S) : TNC k c R →+* TNC k c S where
  toFun f := fun w => g (f w)
  map_one' := by
    funext w
    show g (if w.1 = [] then 1 else 0) = if w.1 = [] then 1 else 0
    split <;> simp
  map_mul' f₁ f₂ := by
    funext w
    show g (∑ i ∈ Finset.range (w.1.length + 1), f₁ (tk w i) * f₂ (dr w i))
      = ∑ i ∈ Finset.range (w.1.length + 1), g (f₁ (tk w i)) * g (f₂ (dr w i))
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_mul g _ _
  map_zero' := by funext w; exact map_zero g
  map_add' f₁ f₂ := by funext w; exact map_add g _ _

@[simp] theorem mapCoeff_apply (g : R →+* S) (f : TNC k c R) (w : BWord k c) :
    mapCoeff g f w = g (f w) := rfl

/-! ### Finiteness -/

theorem bword_finite (k c : ℕ) : Finite (BWord k c) := by
  classical
  refine Finite.of_injective
    (fun w : BWord k c =>
      ((fun i : Fin c => w.1[(i : ℕ)]?),
        (⟨w.1.length, Nat.lt_succ_of_le w.2⟩ : Fin (c + 1)))) ?_
  rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨hfun, hlen⟩ := h
  apply Subtype.ext
  apply List.ext_getElem?
  intro n
  by_cases hn : n < c
  · exact congrFun hfun ⟨n, hn⟩
  · have e1 : w₁[n]? = none := List.getElem?_eq_none (by omega)
    have e2 : w₂[n]? = none := List.getElem?_eq_none (by omega)
    rw [e1, e2]

instance [Finite R] : Finite (TNC k c R) := by
  have := bword_finite k c
  exact inferInstanceAs (Finite (BWord k c → R))

end TNC

end Potency
