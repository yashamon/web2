/-
# The Magnus homomorphism and its injectivity payload

This file defines the Magnus homomorphism
`magnus : FreeGroup (Fin k) →* (NC k ℤ)ˣ`, sending the `i`-th generator to
`1 + Xᵢ`, and proves the quantitative nonvanishing statement that powers the
potency theorem:

* `coeff_oneAddX_zpow` — the coefficients of `(1 + X j) ^ a` (`a : ℤ`) are
  supported on runs of `j`, with generalized binomial values `intBinom a s`.
* `sylls` — the run-length (syllable) decomposition of a reduced word.
* `coeff_syllProdU_exact` — for a product of syllable factors
  `(1 + X_{j₁})^{a₁} ⋯ (1 + X_{j_m})^{a_m}` and an adjacent-distinct monomial
  `M` of length `m`, the coefficient of `M` is `a₁ ⋯ a_m` when
  `M = [j₁, …, j_m]` and `0` otherwise.  The key counting: a factor can only
  emit a run of its own letter, and an adjacent-distinct word contains no run
  of length `≥ 2`, so `m` letters must come one from each factor, in order.
* `exists_coeff_ne_zero` — hence for `x ≠ 1` the series `magnus x` has a
  nonzero coefficient on the (nonempty) syllable monomial: **Magnus'
  embedding theorem**, in the pointed form the potency argument needs,
  self-contained.
-/
import Potency.NC
import Potency.Binom
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Potency

variable {k : ℕ}

/-! ### The Magnus map -/

/-- `1 + Xᵢ`, as a unit of `NC k ℤ`. -/
def oneAddX (i : Fin k) : (NC k ℤ)ˣ :=
  NC.unitOfCT (1 + NC.X i) (by rw [map_add, map_one, NC.constantCoeff_X, add_zero])

theorem oneAddX_val (i : Fin k) : ((oneAddX i : (NC k ℤ)ˣ) : NC k ℤ) = 1 + NC.X i := rfl

/-- The Magnus homomorphism `FreeGroup (Fin k) →* (NC k ℤ)ˣ`. -/
def magnus : FreeGroup (Fin k) →* (NC k ℤ)ˣ := FreeGroup.lift oneAddX

/-- The letter factor used by `FreeGroup.lift_mk`. -/
def letterFactor (p : Fin k × Bool) : (NC k ℤ)ˣ :=
  cond p.2 (oneAddX p.1) (oneAddX p.1)⁻¹

theorem magnus_of (i : Fin k) : magnus (FreeGroup.of i) = oneAddX i := by
  calc magnus (FreeGroup.of i) = magnus (FreeGroup.mk [(i, true)]) := rfl
    _ = ([(i, true)].map letterFactor).prod := FreeGroup.lift_mk
    _ = oneAddX i := by simp [letterFactor]

/-! ### Multiplication recurrences -/

theorem coeff_X_mul_nil (j : Fin k) {R : Type*} [Ring R] (f : NC k R) :
    NC.coeff (NC.X j * f) [] = 0 := by
  rw [NC.coeff_mul]
  simp [NC.coeff_X]

theorem coeff_X_mul_cons (j : Fin k) {R : Type*} [Ring R] (f : NC k R) (b : Fin k)
    (t : Word k) :
    NC.coeff (NC.X j * f) (b :: t) = if b = j then NC.coeff f t else 0 := by
  rw [NC.coeff_mul]
  refine (Finset.sum_eq_single_of_mem 1
    (Finset.mem_range.mpr (by rw [List.length_cons]; omega)) ?_).trans ?_
  · intro i hi hi1
    rw [Finset.mem_range, Nat.lt_succ_iff, List.length_cons] at hi
    have hne : (b :: t).take i ≠ [j] := by
      intro he
      have hlen := congrArg List.length he
      rw [List.length_take, List.length_cons] at hlen
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    rw [NC.coeff_X, if_neg hne, zero_mul]
  · have h1 : (b :: t).take 1 = [b] := rfl
    have h2 : (b :: t).drop 1 = t := rfl
    rw [h1, h2, NC.coeff_X]
    by_cases hbj : b = j
    · rw [if_pos (by rw [hbj]), if_pos hbj, one_mul]
    · rw [if_neg (by simpa using hbj), if_neg hbj, zero_mul]

theorem coeff_oneAddX_mul_nil (j : Fin k) (f : NC k ℤ) :
    NC.coeff (((oneAddX j : (NC k ℤ)ˣ) : NC k ℤ) * f) [] = NC.coeff f [] := by
  rw [oneAddX_val, add_mul, one_mul, NC.coeff_add, coeff_X_mul_nil, add_zero]

theorem coeff_oneAddX_mul_cons (j b : Fin k) (t : Word k) (f : NC k ℤ) :
    NC.coeff (((oneAddX j : (NC k ℤ)ˣ) : NC k ℤ) * f) (b :: t)
      = NC.coeff f (b :: t) + if b = j then NC.coeff f t else 0 := by
  rw [oneAddX_val, add_mul, one_mul, NC.coeff_add, coeff_X_mul_cons]

/-- The constant term of any integer power of `1 + X j` is `1`. -/
theorem constantCoeff_oneAddX_zpow (j : Fin k) (z : ℤ) :
    NC.coeff ((oneAddX j ^ z : (NC k ℤ)ˣ) : NC k ℤ) [] = 1 := by
  have h1 : Units.map (NC.constantCoeff (k := k) (R := ℤ)).toMonoidHom (oneAddX j) = 1 := by
    apply Units.ext
    show NC.constantCoeff ((oneAddX j : (NC k ℤ)ˣ) : NC k ℤ) = ((1 : ℤˣ) : ℤ)
    rw [oneAddX_val, map_add, map_one, NC.constantCoeff_X, add_zero]
    rfl
  have h2 : Units.map (NC.constantCoeff (k := k) (R := ℤ)).toMonoidHom (oneAddX j ^ z) = 1 := by
    rw [map_zpow, h1, one_zpow]
  have h3 := congrArg Units.val h2
  rw [Units.coe_map] at h3
  exact h3

/-! ### Coefficients of integer powers of `1 + X j` -/

/-- Coefficients of `(1 + X j) ^ a`, `a : ℤ`: supported on runs of `j`, with
generalized binomial values. -/
theorem coeff_oneAddX_zpow (j : Fin k) (a : ℤ) (w : Word k) :
    NC.coeff ((oneAddX j ^ a : (NC k ℤ)ˣ) : NC k ℤ) w
      = if w = List.replicate w.length j then intBinom a w.length else 0 := by
  induction a using Int.induction_on generalizing w with
  | zero =>
    rw [zpow_zero, Units.val_one]
    cases w with
    | nil => simp
    | cons b t =>
      rw [NC.coeff_one_ne_nil (List.cons_ne_nil _ _)]
      by_cases hr : b :: t = List.replicate (b :: t).length j
      · rw [if_pos hr, List.length_cons, intBinom_zero_left]
      · rw [if_neg hr]
  | succ n ih =>
    have hsplit : (oneAddX j ^ ((n : ℤ) + 1) : (NC k ℤ)ˣ)
        = oneAddX j * oneAddX j ^ (n : ℤ) := by
      rw [show ((n : ℤ) + 1) = 1 + (n : ℤ) by ring, zpow_add, zpow_one]
    rw [hsplit, Units.val_mul]
    cases w with
    | nil =>
      rw [coeff_oneAddX_mul_nil, ih]
      simp
    | cons b t =>
      rw [coeff_oneAddX_mul_cons, ih, ih, List.length_cons]
      by_cases hbj : b = j
      · rw [if_pos hbj]
        by_cases ht : t = List.replicate t.length j
        · have hr : b :: t = List.replicate (t.length + 1) j := by
            rw [List.replicate_succ, ← ht, hbj]
          rw [if_pos hr, if_pos hr, if_pos ht, intBinom_pascal]
        · have hr : ¬(b :: t = List.replicate (t.length + 1) j) := by
            rw [List.replicate_succ]
            simp only [List.cons.injEq]
            exact fun h => ht h.2
          rw [if_neg hr, if_neg hr, if_neg ht, add_zero]
      · rw [if_neg hbj, add_zero]
        have hr : ¬(b :: t = List.replicate (t.length + 1) j) := by
          rw [List.replicate_succ]
          simp only [List.cons.injEq]
          exact fun h => hbj h.1
        rw [if_neg hr, if_neg hr]
  | pred n ih =>
    have hsplit : (oneAddX j ^ (-(n : ℤ)) : (NC k ℤ)ˣ)
        = oneAddX j * oneAddX j ^ (-(n : ℤ) - 1) := by
      conv_lhs => rw [show (-(n : ℤ)) = 1 + (-(n : ℤ) - 1) by ring]
      rw [zpow_add, zpow_one]
    induction w with
    | nil =>
      rw [constantCoeff_oneAddX_zpow]
      simp
    | cons b t iht =>
      have hgoal := ih (b :: t)
      rw [hsplit, Units.val_mul, coeff_oneAddX_mul_cons, iht] at hgoal
      rw [List.length_cons] at hgoal ⊢
      by_cases hbj : b = j
      · rw [if_pos hbj] at hgoal
        by_cases ht : t = List.replicate t.length j
        · have hr : b :: t = List.replicate (t.length + 1) j := by
            rw [List.replicate_succ, ← ht, hbj]
          rw [if_pos hr, if_pos ht] at hgoal
          rw [if_pos hr]
          have hpas := intBinom_pascal (-(n : ℤ) - 1) t.length
          rw [show (-(n : ℤ) - 1) + 1 = -(n : ℤ) by ring] at hpas
          exact add_right_cancel (hgoal.trans hpas)
        · have hr : ¬(b :: t = List.replicate (t.length + 1) j) := by
            rw [List.replicate_succ]
            simp only [List.cons.injEq]
            exact fun h => ht h.2
          rw [if_neg hr, if_neg ht, add_zero] at hgoal
          rw [if_neg hr]
          exact hgoal
      · rw [if_neg hbj, add_zero] at hgoal
        have hr : ¬(b :: t = List.replicate (t.length + 1) j) := by
          rw [List.replicate_succ]
          simp only [List.cons.injEq]
          exact fun h => hbj h.1
        rw [if_neg hr] at hgoal
        rw [if_neg hr]
        exact hgoal

/-! ### Syllable decomposition -/

/-- Run-length grouping of a letter word: `sylls L` is the list of
(letter-with-sign, run length) pairs of maximal constant runs of `L`. -/
def sylls : List (Fin k × Bool) → List ((Fin k × Bool) × ℕ)
  | [] => []
  | a :: L =>
    match sylls L with
    | [] => [(a, 1)]
    | (b, n) :: S => if a = b then (b, n + 1) :: S else (a, 1) :: (b, n) :: S

@[simp] theorem sylls_nil : sylls ([] : List (Fin k × Bool)) = [] := rfl

theorem sylls_cons_of_eq_nil {a : Fin k × Bool} {L : List (Fin k × Bool)}
    (h : sylls L = []) : sylls (a :: L) = [(a, 1)] := by
  rw [sylls, h]

theorem sylls_cons_of_eq_cons_pos {a b : Fin k × Bool} {n : ℕ}
    {S : List ((Fin k × Bool) × ℕ)} {L : List (Fin k × Bool)}
    (h : sylls L = (b, n) :: S) (hab : a = b) :
    sylls (a :: L) = (b, n + 1) :: S := by
  rw [sylls, h]
  exact if_pos hab

theorem sylls_cons_of_eq_cons_neg {a b : Fin k × Bool} {n : ℕ}
    {S : List ((Fin k × Bool) × ℕ)} {L : List (Fin k × Bool)}
    (h : sylls L = (b, n) :: S) (hab : ¬ a = b) :
    sylls (a :: L) = (a, 1) :: (b, n) :: S := by
  rw [sylls, h]
  exact if_neg hab

theorem sylls_eq_nil_iff {L : List (Fin k × Bool)} : sylls L = [] ↔ L = [] := by
  constructor
  · intro h
    cases L with
    | nil => rfl
    | cons a L' =>
      rcases hS : sylls L' with _ | ⟨⟨b, n⟩, S⟩
      · rw [sylls_cons_of_eq_nil hS] at h
        exact absurd h (by simp)
      · by_cases hab : a = b
        · rw [sylls_cons_of_eq_cons_pos hS hab] at h
          exact absurd h (by simp)
        · rw [sylls_cons_of_eq_cons_neg hS hab] at h
          exact absurd h (by simp)
  · rintro rfl; rfl

theorem sylls_pos {L : List (Fin k × Bool)} : ∀ q ∈ sylls L, 1 ≤ q.2 := by
  induction L with
  | nil => intro q hq; simp at hq
  | cons a L ihL =>
    intro q hq
    rcases hS : sylls L with _ | ⟨⟨b, n⟩, S⟩
    · rw [sylls_cons_of_eq_nil hS] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact le_refl 1
    · by_cases hab : a = b
      · rw [sylls_cons_of_eq_cons_pos hS hab] at hq
        rcases List.mem_cons.mp hq with h | h
        · subst h
          show 1 ≤ n + 1
          omega
        · exact ihL q (by rw [hS]; exact List.mem_cons_of_mem _ h)
      · rw [sylls_cons_of_eq_cons_neg hS hab] at hq
        rcases List.mem_cons.mp hq with h | h
        · subst h
          exact le_refl 1
        · exact ihL q (by rw [hS]; exact h)

theorem sylls_head {L : List (Fin k × Bool)} {b : Fin k × Bool} {n : ℕ}
    {S : List ((Fin k × Bool) × ℕ)} (h : sylls L = (b, n) :: S) :
    ∃ L', L = b :: L' := by
  cases L with
  | nil => simp at h
  | cons a L' =>
    rcases hS : sylls L' with _ | ⟨⟨b', n'⟩, S'⟩
    · rw [sylls_cons_of_eq_nil hS] at h
      simp only [List.cons.injEq, Prod.mk.injEq] at h
      exact ⟨L', by rw [h.1.1]⟩
    · by_cases hab : a = b'
      · rw [sylls_cons_of_eq_cons_pos hS hab] at h
        simp only [List.cons.injEq, Prod.mk.injEq] at h
        exact ⟨L', by rw [hab, h.1.1]⟩
      · rw [sylls_cons_of_eq_cons_neg hS hab] at h
        simp only [List.cons.injEq, Prod.mk.injEq] at h
        exact ⟨L', by rw [h.1.1]⟩

/-- In a *reduced* word, adjacent syllables carry distinct letters: a maximal
run boundary within the same letter would force opposite signs, i.e. a
cancellation. -/
theorem sylls_chain {L : List (Fin k × Bool)} (hred : FreeGroup.IsReduced L) :
    List.IsChain (fun p q : (Fin k × Bool) × ℕ => p.1.1 ≠ q.1.1) (sylls L) := by
  induction L with
  | nil => simp
  | cons a L ihL =>
    have hredL : FreeGroup.IsReduced L := by
      cases L with
      | nil => exact FreeGroup.IsReduced.nil
      | cons b L' => exact (FreeGroup.isReduced_cons_cons.mp hred).2
    have hchainL := ihL hredL
    rcases hS : sylls L with _ | ⟨⟨b, n⟩, S⟩
    · rw [sylls_cons_of_eq_nil hS]
      exact List.isChain_singleton _
    · rw [hS] at hchainL
      by_cases hab : a = b
      · rw [sylls_cons_of_eq_cons_pos hS hab]
        cases S with
        | nil => exact List.isChain_singleton _
        | cons q S' =>
          rw [List.isChain_cons_cons] at hchainL ⊢
          exact hchainL
      · rw [sylls_cons_of_eq_cons_neg hS hab]
        obtain ⟨L', rfl⟩ := sylls_head hS
        have hne : a.1 ≠ b.1 := by
          intro h11
          have h22 := (FreeGroup.isReduced_cons_cons.mp hred).1 h11
          exact hab (Prod.ext h11 h22)
        rw [List.isChain_cons_cons]
        exact ⟨hne, hchainL⟩

/-! ### Regrouping the Magnus image along syllables -/

/-- The signed exponent of a syllable. -/
def syllExp (q : (Fin k × Bool) × ℕ) : ℤ := if q.1.2 then (q.2 : ℤ) else -(q.2 : ℤ)

/-- The product of syllable factors `(1 + X_j)^(±n)`. -/
def syllProdU (S : List ((Fin k × Bool) × ℕ)) : (NC k ℤ)ˣ :=
  (S.map fun q => oneAddX q.1.1 ^ syllExp q).prod

@[simp] theorem syllProdU_nil : syllProdU ([] : List ((Fin k × Bool) × ℕ)) = 1 := rfl

theorem syllProdU_cons (q : (Fin k × Bool) × ℕ) (S : List ((Fin k × Bool) × ℕ)) :
    syllProdU (q :: S) = oneAddX q.1.1 ^ syllExp q * syllProdU S := by
  rw [syllProdU, syllProdU, List.map_cons, List.prod_cons]

theorem letterFactor_eq_zpow (p : Fin k × Bool) :
    letterFactor p = oneAddX p.1 ^ (if p.2 then (1 : ℤ) else -1) := by
  rcases p with ⟨i, s⟩
  cases s
  · show (oneAddX i)⁻¹ = oneAddX i ^ (if false then (1 : ℤ) else -1)
    simp [zpow_neg, zpow_one]
  · show oneAddX i = oneAddX i ^ (if true then (1 : ℤ) else -1)
    simp

theorem letterProd_eq_syllProd (L : List (Fin k × Bool)) :
    (L.map letterFactor).prod = syllProdU (sylls L) := by
  induction L with
  | nil => rfl
  | cons a L ihL =>
    rw [List.map_cons, List.prod_cons, ihL]
    rcases hS : sylls L with _ | ⟨⟨b, n⟩, S⟩
    · rw [sylls_cons_of_eq_nil hS, letterFactor_eq_zpow]
      have hexp : (if a.2 then (1 : ℤ) else -1) = syllExp (a, 1) := by
        rcases a with ⟨i, s⟩
        cases s <;> simp [syllExp]
      rw [hexp, syllProdU_cons, syllProdU_nil, mul_one]
    · by_cases hab : a = b
      · rw [sylls_cons_of_eq_cons_pos hS hab, syllProdU_cons, syllProdU_cons, ← mul_assoc,
          letterFactor_eq_zpow, hab, ← zpow_add]
        have hexp : (if b.2 then (1 : ℤ) else -1) + syllExp (b, n) = syllExp (b, n + 1) := by
          rcases b with ⟨i, s⟩
          cases s <;> simp only [syllExp, if_true, if_false] <;> push_cast <;> ring
        rw [hexp]
      · rw [sylls_cons_of_eq_cons_neg hS hab, syllProdU_cons (a, 1), letterFactor_eq_zpow]
        have hexp : (if a.2 then (1 : ℤ) else -1) = syllExp (a, 1) := by
          rcases a with ⟨i, s⟩
          cases s <;> simp [syllExp]
        rw [hexp]

theorem magnus_toWord (x : FreeGroup (Fin k)) : magnus x = syllProdU (sylls x.toWord) := by
  rw [← letterProd_eq_syllProd]
  calc magnus x = magnus (FreeGroup.mk x.toWord) := by rw [FreeGroup.mk_toWord]
    _ = (x.toWord.map letterFactor).prod := FreeGroup.lift_mk

/-! ### The syllable-monomial coefficient -/

/-- An adjacent-distinct word contains no run of length `≥ 2`. -/
theorem take_not_replicate {M : Word k} (hM : List.IsChain (· ≠ ·) M) {i : ℕ}
    (h2 : 2 ≤ i) (hi : i ≤ M.length) (j : Fin k) :
    ¬ (M.take i = List.replicate (M.take i).length j) := by
  intro he
  rcases M with _ | ⟨x, M'⟩
  · simp at hi; omega
  rcases M' with _ | ⟨y, M''⟩
  · simp at hi; omega
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  have hxy : x ≠ y := (List.isChain_cons_cons.mp hM).1
  rw [show (x :: y :: M'').take (i' + 2) = x :: y :: M''.take i' from rfl] at he
  rw [List.length_cons, List.length_cons, List.replicate_succ, List.replicate_succ] at he
  simp only [List.cons.injEq] at he
  exact hxy (he.1.trans he.2.1.symm)

/-- **Vanishing** (Lemma A): a product of `m` syllable factors has zero
coefficient on every adjacent-distinct monomial of length `> m`. -/
theorem coeff_syllProdU_eq_zero (S : List ((Fin k × Bool) × ℕ)) :
    ∀ (M : Word k), List.IsChain (· ≠ ·) M → S.length < M.length →
      NC.coeff ((syllProdU S : (NC k ℤ)ˣ) : NC k ℤ) M = 0 := by
  induction S with
  | nil =>
    intro M hM hlen
    simp only [List.length_nil] at hlen
    have hMne : M ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
    show NC.coeff ((1 : (NC k ℤ)ˣ) : NC k ℤ) M = 0
    rw [Units.val_one]
    exact NC.coeff_one_ne_nil hMne
  | cons q S ihS =>
    intro M hM hlen
    rw [syllProdU_cons, Units.val_mul, NC.coeff_mul]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    rcases i with _ | _ | i
    · rw [List.drop_zero]
      have h0 : NC.coeff ((syllProdU S : (NC k ℤ)ˣ) : NC k ℤ) M = 0 := by
        apply ihS M hM
        rw [List.length_cons] at hlen
        omega
      rw [h0, mul_zero]
    · cases M with
      | nil => simp at hlen
      | cons b t =>
        rw [show (b :: t).drop 1 = t from rfl]
        have h1 : NC.coeff ((syllProdU S : (NC k ℤ)ˣ) : NC k ℤ) t = 0 := by
          apply ihS t hM.tail
          simp only [List.length_cons] at hlen
          omega
        rw [h1, mul_zero]
    · rw [coeff_oneAddX_zpow,
        if_neg (take_not_replicate hM (by omega) (by omega) _), zero_mul]

/-- **Exact length** (Lemma B): a product of `m` syllable factors, against an
adjacent-distinct monomial `M` of length exactly `m`, has coefficient the
product of the signed exponents if `M` is the syllable letter word, and `0`
otherwise. -/
theorem coeff_syllProdU_exact (S : List ((Fin k × Bool) × ℕ)) :
    ∀ (M : Word k), List.IsChain (· ≠ ·) M → M.length = S.length →
      NC.coeff ((syllProdU S : (NC k ℤ)ˣ) : NC k ℤ) M
        = if M = S.map (fun q => q.1.1) then (S.map syllExp).prod else 0 := by
  induction S with
  | nil =>
    intro M hM hlen
    rw [List.length_nil] at hlen
    cases M with
    | nil => simp [syllProdU]
    | cons b t => rw [List.length_cons] at hlen; omega
  | cons q S ihS =>
    intro M hM hlen
    cases M with
    | nil =>
      rw [List.length_nil, List.length_cons] at hlen
      omega
    | cons b t =>
      rw [List.length_cons, List.length_cons] at hlen
      rw [syllProdU_cons, Units.val_mul, NC.coeff_mul]
      have hsum : ∀ i ∈ Finset.range ((b :: t).length + 1), i ≠ 1 →
          NC.coeff ((oneAddX q.1.1 ^ syllExp q : (NC k ℤ)ˣ) : NC k ℤ) ((b :: t).take i)
            * NC.coeff ((syllProdU S : (NC k ℤ)ˣ) : NC k ℤ) ((b :: t).drop i) = 0 := by
        intro i hi hi1
        rw [Finset.mem_range, Nat.lt_succ_iff] at hi
        rcases i with _ | _ | i
        · rw [List.drop_zero]
          rw [coeff_syllProdU_eq_zero S (b :: t) hM (by rw [List.length_cons]; omega),
            mul_zero]
        · omega
        · rw [coeff_oneAddX_zpow,
            if_neg (take_not_replicate hM (by omega) (by omega) _), zero_mul]
      rw [Finset.sum_eq_single_of_mem 1
        (Finset.mem_range.mpr (by rw [List.length_cons]; omega)) hsum]
      rw [show (b :: t).take 1 = [b] from rfl, show (b :: t).drop 1 = t from rfl,
        coeff_oneAddX_zpow]
      rw [show List.replicate ([b] : Word k).length q.1.1 = [q.1.1] from rfl]
      rw [show ([b] : Word k).length = 1 from rfl, intBinom_one_right]
      rw [ihS t hM.tail (by omega)]
      simp only [List.map_cons]
      by_cases hbq : b = q.1.1
      · rw [if_pos (show ([b] : Word k) = [q.1.1] by rw [hbq])]
        by_cases ht : t = S.map (fun q => q.1.1)
        · rw [if_pos ht, if_pos (by rw [hbq, ht]), List.prod_cons]
        · rw [if_neg ht, mul_zero,
            if_neg (by simp only [List.cons.injEq]; exact fun h => ht h.2)]
      · rw [if_neg (by simpa using hbq), zero_mul,
          if_neg (by simp only [List.cons.injEq]; exact fun h => hbq h.1)]

/-! ### Magnus' theorem, pointed form -/

theorem int_list_prod_ne_zero : ∀ (l : List ℤ), (∀ x ∈ l, x ≠ 0) → l.prod ≠ 0
  | [], _ => one_ne_zero
  | a :: l, h => by
    rw [List.prod_cons]
    exact mul_ne_zero (h a List.mem_cons_self)
      (int_list_prod_ne_zero l fun x hx => h x (List.mem_cons_of_mem a hx))

/-- **Magnus, pointed form**: for `x ≠ 1` the series `magnus x` has a nonzero
coefficient on a nonempty word — namely, on its syllable monomial, where the
coefficient is the product of the signed syllable exponents. -/
theorem exists_coeff_ne_zero {x : FreeGroup (Fin k)} (hx : x ≠ 1) :
    ∃ M : Word k, M ≠ [] ∧ NC.coeff ((magnus x : (NC k ℤ)ˣ) : NC k ℤ) M ≠ 0 := by
  have hLne : x.toWord ≠ [] := fun h => hx (FreeGroup.toWord_eq_nil_iff.mp h)
  have hSne : sylls x.toWord ≠ [] := fun h => hLne (sylls_eq_nil_iff.mp h)
  refine ⟨(sylls x.toWord).map (fun q => q.1.1), ?_, ?_⟩
  · intro h
    exact hSne (List.map_eq_nil_iff.mp h)
  · rw [magnus_toWord]
    have hchain : List.IsChain (· ≠ ·) ((sylls x.toWord).map (fun q => q.1.1)) := by
      have hc := sylls_chain (FreeGroup.isReduced_toWord (x := x))
      exact (List.isChain_map _).mpr hc
    rw [coeff_syllProdU_exact _ _ hchain (by rw [List.length_map]), if_pos rfl]
    apply int_list_prod_ne_zero
    intro e he
    rw [List.mem_map] at he
    obtain ⟨q, hq, rfl⟩ := he
    have hpos := sylls_pos q hq
    rcases q with ⟨⟨i, s⟩, n⟩
    have hn : 1 ≤ n := hpos
    cases s <;> simp only [syllExp, if_true, if_false] <;> omega

/-- The constant term of `magnus x` is `1` for every `x`. -/
theorem constantCoeff_magnus (x : FreeGroup (Fin k)) :
    NC.coeff ((magnus x : (NC k ℤ)ˣ) : NC k ℤ) [] = 1 := by
  refine FreeGroup.induction_on x ?_ ?_ ?_ ?_
  · rw [map_one, Units.val_one, NC.coeff_one_nil]
  · intro i
    rw [magnus_of]
    show NC.coeff (1 + NC.X i) [] = 1
    rw [NC.coeff_add, NC.coeff_one_nil, NC.coeff_X]
    simp
  · intro i hi
    have h := constantCoeff_oneAddX_zpow i (-1)
    rw [zpow_neg_one] at h
    rw [map_inv, magnus_of]
    exact h
  · intro y z hy hz
    rw [map_mul, Units.val_mul, NC.coeff_mul]
    rw [show (([] : Word k).length + 1) = 1 from rfl, Finset.sum_range_one]
    show NC.coeff _ [] * NC.coeff _ [] = 1
    rw [hy, hz, one_mul]

end Potency
