import Stable.Comp

/-!
# ℕ-level helpers over `TuringModel`

Derived closure properties of the computable functions `ℕ → ℕ`, proved from the interface
`TuringModel` (no new axioms): the nowhere defined map, total primitive recursion, the
predecessor, iteration `Nat.repeat`, sums, two-argument precomposition and the bounded
universal quantifier.  Used by `Stable.Enc`.
-/

namespace Stable

open Classical

/-- `Nat.repeat f (n + 1) a = Nat.repeat f n (f a)` (iterating from the inside). -/
theorem repeat_succ_right {α : Type} (f : α → α) (n : ℕ) (a : α) :
    Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f ih

namespace TuringModel

variable {M : TuringModel}

/-- `eval T` is computable (by `T`). -/
theorem isComp_eval (T : M.Code) : M.IsComp (M.eval T) := ⟨T, fun _ => rfl⟩

/-- The nowhere defined map is computable (unbounded search with the constantly false
predicate). -/
theorem isComp_none : M.IsComp (fun _ => none) := by
  obtain ⟨T₀, hT₀⟩ := M.comp_mu (fun _ => false) (IsCompB.const false)
  refine ⟨T₀, fun a => ?_⟩
  cases h : M.eval T₀ a with
  | none => rfl
  | some k => exact absurd ((hT₀ a k).1 h).1 (by simp)

/-- The characteristic function of a computable set is a total computable map. -/
theorem IsCompSet.isCompT {P : ℕ → Prop} (h : M.IsCompSet P) :
    M.IsCompT (fun n => if P n then 1 else 0) := h

/-- `(f n).map g` for a computable partial `f` and a total computable `g`. -/
theorem IsComp.map {f : ℕ → Option ℕ} {g : ℕ → ℕ} (hf : M.IsComp f) (hg : M.IsCompT g) :
    M.IsComp (fun n => (f n).map g) := by
  have := IsComp.comp (M := M) hg hf
  exact this.congr fun n => by cases f n <;> rfl

/-- Sum of total computable maps. -/
theorem isCompT_add_of {f g : ℕ → ℕ} (hf : M.IsCompT f) (hg : M.IsCompT g) :
    M.IsCompT (fun n => f n + g n) := by
  have hadd : M.IsCompT (fun n => (M.unpair n).1 + (M.unpair n).2) := isComp_add
  have := hadd.comp (hf.pair hg)
  exact this.congr fun n => by simp [M.unpair_pair]

/-- Precomposition of a computable "binary" set (a set of codes `⟨a, b⟩`) with two total
computable maps. -/
theorem isCompSet_comp₂ {Q : ℕ → ℕ → Prop}
    (hQ : M.IsCompSet (fun m => Q (M.unpair m).1 (M.unpair m).2)) {F G : ℕ → ℕ}
    (hF : M.IsCompT F) (hG : M.IsCompT G) : M.IsCompSet (fun n => Q (F n) (G n)) := by
  have := hQ.comp (hF.pair hG)
  exact this.congr fun n => by simp [M.unpair_pair]

/-- Precomposition of a computable "binary" total map with two total computable maps. -/
theorem isCompT_comp₂ {r : ℕ → ℕ → ℕ}
    (hr : M.IsCompT (fun m => r (M.unpair m).1 (M.unpair m).2)) {F G : ℕ → ℕ}
    (hF : M.IsCompT F) (hG : M.IsCompT G) : M.IsCompT (fun n => r (F n) (G n)) := by
  have := hr.comp (hF.pair hG)
  exact this.congr fun n => by simp [M.unpair_pair]

/-- Total primitive recursion: `r a 0 = g a`, `r a (n+1) = h ⟨a, ⟨n, r a n⟩⟩`, as a function
of `⟨a, n⟩`. -/
theorem isCompT_primrec {g h : ℕ → ℕ} (hg : M.IsCompT g) (hh : M.IsCompT h) (r : ℕ → ℕ → ℕ)
    (h0 : ∀ a, r a 0 = g a) (hs : ∀ a n, r a (n + 1) = h (M.pair a (M.pair n (r a n)))) :
    M.IsCompT (fun m => r (M.unpair m).1 (M.unpair m).2) :=
  M.comp_primrec (fun n => some (g n)) (fun n => some (h n)) hg hh (fun a n => some (r a n))
    (fun a => congrArg some (h0 a)) (fun a n => congrArg some (hs a n))

/-- Total primitive recursion, evaluated at `(F n, G n)` for total computable `F`, `G`. -/
theorem isCompT_primrec_of {g h F G : ℕ → ℕ} (hg : M.IsCompT g) (hh : M.IsCompT h)
    (hF : M.IsCompT F) (hG : M.IsCompT G) (r : ℕ → ℕ → ℕ)
    (h0 : ∀ a, r a 0 = g a) (hs : ∀ a n, r a (n + 1) = h (M.pair a (M.pair n (r a n)))) :
    M.IsCompT (fun n => r (F n) (G n)) :=
  isCompT_comp₂ (isCompT_primrec hg hh r h0 hs) hF hG

/-- The predecessor `n ↦ n - 1` is computable. -/
theorem isCompT_pred : M.IsCompT (fun n => n - 1) :=
  isCompT_primrec_of (M := M) (g := fun _ => 0) (h := fun m => (M.unpair (M.unpair m).2).1)
    (F := fun _ => 0) (G := fun n => n) (isCompT_const 0) (isCompT_fst.comp isCompT_snd)
    (isCompT_const 0) isCompT_id (fun _ n => n - 1) (fun _ => rfl)
    (fun a n => by simp [M.unpair_pair])

/-- Iteration: `n ↦ f^[K n] (X n)` for total computable `f`, `K`, `X`. -/
theorem isCompT_repeat {f : ℕ → ℕ} (hf : M.IsCompT f) {K X : ℕ → ℕ} (hK : M.IsCompT K)
    (hX : M.IsCompT X) : M.IsCompT (fun n => Nat.repeat f (K n) (X n)) :=
  isCompT_primrec_of (M := M) (g := fun a => a) (h := fun m => f (M.unpair (M.unpair m).2).2)
    (F := X) (G := K) isCompT_id (hf.comp (isCompT_snd.comp isCompT_snd)) hX hK
    (fun a n => Nat.repeat f n a) (fun _ => rfl) (fun a n => by simp [M.unpair_pair, Nat.repeat])

/-- The bounded universal quantifier `∀ j < b, P a j`, as a set of codes `⟨a, b⟩`. -/
theorem isCompSet_ballLt {P : ℕ → ℕ → Prop}
    (hP : M.IsCompSet (fun m => P (M.unpair m).1 (M.unpair m).2)) :
    M.IsCompSet (fun m => ∀ j, j < (M.unpair m).2 → P (M.unpair m).1 j) := by
  -- the step: `⟨a, ⟨n, y⟩⟩ ↦ if P a n then y else 0`
  have hB : M.IsCompB (fun m => decide (P (M.unpair m).1 (M.unpair (M.unpair m).2).1)) :=
    (isCompSet_comp₂ hP isCompT_fst (isCompT_fst.comp isCompT_snd)).toB
  have hh := IsCompT.cases hB (isCompT_snd.comp isCompT_snd) (isCompT_const 0)
  -- (the `if` below may use `Nat.decidableBallLT`; `IsCompSet` uses the classical instance)
  refine IsComp.congr (f := fun m => some (if ∀ j, j < (M.unpair m).2 → P (M.unpair m).1 j
      then 1 else 0)) ?_ fun m => by
    dsimp only
    by_cases h : ∀ j, j < (M.unpair m).2 → P (M.unpair m).1 j
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
  exact isCompT_primrec (isCompT_const 1) hh (fun a n => if ∀ j, j < n → P a j then 1 else 0)
    (fun a => by rw [ite_eq_left (fun j hj => absurd hj (Nat.not_lt_zero j))])
    (fun a n => by
      simp only [M.unpair_pair]
      have hiff : (∀ j, j < n + 1 → P a j) ↔ (∀ j, j < n → P a j) ∧ P a n := by
        constructor
        · intro h'; exact ⟨fun j hj => h' j (Nat.lt_succ_of_lt hj), h' n (Nat.lt_succ_self n)⟩
        · rintro ⟨h', hn⟩ j hj
          rcases Nat.lt_or_ge j n with hlt | hge
          · exact h' j hlt
          · rw [Nat.le_antisymm (Nat.le_of_lt_succ hj) hge]; exact hn
      by_cases hn : P a n
      · by_cases hall : ∀ j, j < n → P a j
        · rw [ite_eq_left (hiff.2 ⟨hall, hn⟩), ite_eq_left hall]; simp [hn]
        · rw [ite_eq_right (fun h' => hall (hiff.1 h').1), ite_eq_right hall]; simp
      · rw [ite_eq_right (fun h' => hn (hiff.1 h').2)]; simp [hn])

/-- The bounded universal quantifier `∀ j < G n, P (F n) j` for total computable `F`, `G`. -/
theorem isCompSet_ballLt_of {P : ℕ → ℕ → Prop}
    (hP : M.IsCompSet (fun m => P (M.unpair m).1 (M.unpair m).2)) {F G : ℕ → ℕ}
    (hF : M.IsCompT F) (hG : M.IsCompT G) : M.IsCompSet (fun n => ∀ j, j < G n → P (F n) j) :=
  isCompSet_comp₂ (Q := fun a b => ∀ j, j < b → P a j) (isCompSet_ballLt hP) hF hG

/-- `⟨0, 0⟩ = 0`, i.e. `unpair 0 = (0, 0)` (the pairing is increasing and surjective). -/
theorem unpair_zero : M.unpair 0 = (0, 0) := by
  have h := M.pair_unpair 0
  have h1 : (M.unpair 0).1 = 0 := by
    refine Classical.byContradiction fun hne => ?_
    have := M.pair_lt_left (M.unpair 0).2 (Nat.pos_of_ne_zero hne)
    rw [h] at this; exact Nat.not_lt_zero _ this
  have h2 : (M.unpair 0).2 = 0 := by
    refine Classical.byContradiction fun hne => ?_
    have := M.pair_lt_right (M.unpair 0).1 (Nat.pos_of_ne_zero hne)
    rw [h] at this; exact Nat.not_lt_zero _ this
  exact Prod.ext h1 h2

/-- The pairing is injective. -/
theorem pair_inj {a b a' b' : ℕ} (h : M.pair a b = M.pair a' b') : a = a' ∧ b = b' := by
  have h' := congrArg M.unpair h
  rw [M.unpair_pair, M.unpair_pair] at h'
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

end TuringModel

end Stable
