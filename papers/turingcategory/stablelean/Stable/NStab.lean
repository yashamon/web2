import Stable.Machines

/-!
# `n`-decision maps and `n`-stability (Section 6.1 of the paper)

The paper indexes by `n ≥ 1`; here `m = n - 1` is the number of *additional* variables, so
"`(m+1)`-decided" is `NDec m`, "`(m+1)`-stable" is `NStable m`, and `Σ⁰_{m+2}` conditions are
`NSR m`.

* `NB B m` is `B × ℕ^m`, nested as `((B × ℕ) × ℕ) × …`, via the recursion `NB B (m+1) = NB (B × ℕ) m`
  (Definition 6.1: an `(m+1)`-decision map on `B` *is* an `m`-decision map on `B × ℕ`, through
  `(b, u, w̄) ↦ ((b, u), w̄)`).  An `(m+1)`-decision map on `B` is a map `NB B m → ℕ → Option Bool`.
* `NDec m D b` (Definition 6.1): `b` is `(m+1)`-decided by `D`; for `m = 0` this is `IsDecided`,
  and for `m+1` it is `∃ u, ¬ NDec m D (b, u)`.
* A map `M : ℕ^{m+1} → B × {±}` is `M : NB ℕ m → Option (B × Bool)`; the paper's tuple
  `(u_1, …, u_{m+1})` is `((u_{m+1}, u_1), u_2, …, u_m)`: the last variable is the base and `u_1` is
  next to it.  So the slice `M (u, ·)` of Definition 6.1 is `nslice m M u`, obtained by
  inserting `u` next to the base.  `NStable m M b`: for `m = 0` it is `IsStable`, and for `m+1`
  it is `∃ u, ¬ NStable m (nslice m M u) b`.
* `NRel A B m = A → NB B m → ℕ → ℕ → Prop` and `NSR m R a b` is the condition
  `∃ u₁ ∀ u₂ ⋯ u_{m+2}, R (a, b, u₁, …, u_{m+2})` with `m+2` alternating quantifiers, defined by the
  same recursion with a complement at each step (`compl`).
* Lemma 6.2, the `n`-stabilizer lemma: `n_stabilizer`.
* The correspondences `D ↦ M_D` (`MD`, for infinite `B`) and `M ↦ D_M` (`DM`) of Corollary 6.3,
  with `NStable m (MD m D) b ↔ NDec m D b` and `NDec m (DM m M) b ↔ NStable m M b`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-- `NB B m = B × ℕ^m`, nested to the left: `NB B (m+1) = NB (B × ℕ) m`. -/
@[reducible] def NB : Type → ℕ → Type
  | B, 0 => B
  | B, m + 1 => NB (B × ℕ) m

/-- The encoding of `NB B m` (iterated product encoding). -/
@[instance_reducible] def encNB : (m : ℕ) → {B : Type} → [Enc M B] → Enc M (NB B m)
  | 0, _, inst => inst
  | m + 1, _, _ => encNB m

instance instEncNB {B : Type} [Enc M B] (m : ℕ) : Enc M (NB B m) := encNB m

/-- The base element `b` of `((b, u₁), …, u_m)`. -/
def nbBase : (m : ℕ) → {B : Type} → NB B m → B
  | 0, _, b => b
  | m + 1, _, x => (nbBase m x).1

/-- Apply `f` at the base: `((b, u₁), …, u_m) ↦ ((f b, u₁), …, u_m)`. -/
def nbMapBase : (m : ℕ) → {B C : Type} → (B → C) → NB B m → NB C m
  | 0, _, _, f, b => f b
  | m + 1, _, _, f, x => nbMapBase m (fun p => (f p.1, p.2)) x

theorem nbBase_nbMapBase : ∀ (m : ℕ) {B C : Type} (f : B → C) (x : NB B m),
    nbBase m (nbMapBase m f x) = f (nbBase m x)
  | 0, _, _, _, _ => rfl
  | m + 1, _, _, f, x => by
    show (nbBase m (nbMapBase m (fun p => (f p.1, p.2)) x)).1 = f (nbBase m x).1
    rw [nbBase_nbMapBase m]

theorem nbMapBase_nbMapBase : ∀ (m : ℕ) {B C D : Type} (f : B → C) (g : C → D) (x : NB B m),
    nbMapBase m g (nbMapBase m f x) = nbMapBase m (fun b => g (f b)) x
  | 0, _, _, _, _, _, _ => rfl
  | m + 1, _, _, _, f, g, x => by
    show nbMapBase m (fun p => (g p.1, p.2)) (nbMapBase m (fun p => (f p.1, p.2)) x) =
      nbMapBase m (fun p => (g (f p.1), p.2)) x
    rw [nbMapBase_nbMapBase m]

theorem nbMapBase_id : ∀ (m : ℕ) {B : Type} (x : NB B m), nbMapBase m (fun b : B => b) x = x
  | 0, _, _ => rfl
  | m + 1, _, x => by
    show nbMapBase m (fun p : _ × ℕ => (p.1, p.2)) x = x
    exact nbMapBase_id m x

theorem nbMapBase_congr : ∀ (m : ℕ) {B C : Type} {f g : B → C}, (∀ b, f b = g b) →
    ∀ x : NB B m, nbMapBase m f x = nbMapBase m g x
  | 0, _, _, _, _, h, b => h b
  | m + 1, _, _, _, _, h, x => by
    show nbMapBase m _ x = nbMapBase m _ x
    exact nbMapBase_congr m (fun p => by rw [h p.1]) x

/-- `nbBase` is computable. -/
theorem compT_nbBase (m : ℕ) {B : Type} [Enc M B] : CompT M (fun x : NB B m => nbBase m x) := by
  induction m generalizing B with
  | zero => exact compT_id
  | succ m ih => exact (compT_fst (A := B) (B := ℕ)).comp (ih (B := B × ℕ))

/-- `nbMapBase m f` is computable when `f` is. -/
theorem compT_nbMapBase (m : ℕ) {B C : Type} [Enc M B] [Enc M C] {f : B → C} (hf : CompT M f) :
    CompT M (fun x : NB B m => nbMapBase m f x) := by
  induction m generalizing B C with
  | zero => exact hf
  | succ m ih =>
    exact ih (B := B × ℕ) (C := C × ℕ) (f := fun p => (f p.1, p.2))
      (CompT.pair (hf.comp compT_fst) compT_snd)

/-- `nbMapBase m (f x)` is computable in `(y, x)` when `f` is computable in `(x, b)`. -/
theorem compT_nbMapBase_param (m : ℕ) {X B C : Type} [Enc M X] [Enc M B] [Enc M C]
    {f : X → B → C} (hf : CompT M (fun q : X × B => f q.1 q.2)) :
    CompT M (fun p : NB B m × X => nbMapBase m (f p.2) p.1) := by
  induction m generalizing B C with
  | zero => exact hf.comp compT_swap
  | succ m ih =>
    exact ih (B := B × ℕ) (C := C × ℕ) (f := fun x p => (f x p.1, p.2))
      (CompT.pair (hf.comp (CompT.pair compT_fst (compT_fst.comp compT_snd)))
        (compT_snd.comp compT_snd))

/-- Replacing the base by a variable: `(y, c) ↦ nbMapBase m (fun _ => c) y` is computable. -/
theorem compT_nbMapBase_const (m : ℕ) {B C : Type} [Enc M B] [Enc M C] :
    CompT M (fun p : NB B m × C => nbMapBase m (fun _ => p.2) p.1) :=
  compT_nbMapBase_param m (f := fun (c : C) (_ : B) => c) compT_fst

/-- `t ≤ ⟨a, t⟩`, from the strict monotonicity of `⟨a, ·⟩`. -/
private theorem le_pair_right (a : ℕ) : ∀ t : ℕ, t ≤ M.pair a t
  | 0 => Nat.zero_le _
  | t + 1 => Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (le_pair_right a t) (M.pair_lt_right a (Nat.lt_succ_self t)))

theorem infinite_prod_nat {B : Type} [Enc M B] (b₀ : B) : Enc.Infinite M (B × ℕ) :=
  fun n => ⟨(b₀, n + 1),
    Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (le_pair_right (M := M) (e M b₀) (n + 1))⟩

/-- `NB B m` is infinite when `B` is (and for `m ≥ 1` always, as `B × ℕ` is infinite). -/
theorem infinite_NB (m : ℕ) {B : Type} [Enc M B] (hB : Enc.Infinite M B) :
    Enc.Infinite M (NB B m) := by
  induction m generalizing B with
  | zero => exact hB
  | succ m ih =>
    obtain ⟨b₀, _⟩ := hB 0
    exact ih (B := B × ℕ) (infinite_prod_nat b₀)

/-! ### `(m+1)`-decided and `(m+1)`-stable -/

/-- `b` is `(m+1)`-decided by the `(m+1)`-decision map `D : NB B m → ℕ → Option Bool`
(Definition 6.1). -/
def NDec : (m : ℕ) → {B : Type} → (NB B m → ℕ → Option Bool) → B → Prop
  | 0, _, D, b => IsDecided D b
  | m + 1, _, D, b => ∃ u, ¬ NDec m D (b, u)

/-- The slice `M (u, ·) : ℕ^{m+1} → B × {±}` of `M : ℕ^{m+2} → B × {±}`. -/
def nslice (m : ℕ) {B : Type} (Mp : NB ℕ (m + 1) → Option (B × Bool)) (u : ℕ) :
    NB ℕ m → Option (B × Bool) :=
  fun y => Mp (nbMapBase m (fun w => (w, u)) y)

/-- `b` is `(m+1)`-stable for `M : ℕ^{m+1} → B × {±}` (Definition 6.1). -/
def NStable : (m : ℕ) → {B : Type} → (NB ℕ m → Option (B × Bool)) → B → Prop
  | 0, _, Mp, b => IsStable Mp b
  | m + 1, _, Mp, b => ∃ u, ¬ NStable m (nslice m Mp u) b

theorem NDec_zero {B : Type} (D : NB B 0 → ℕ → Option Bool) (b : B) :
    NDec 0 D b ↔ IsDecided D b := Iff.rfl

theorem NDec_succ {B : Type} (m : ℕ) (D : NB B (m + 1) → ℕ → Option Bool) (b : B) :
    NDec (m + 1) D b ↔ ∃ u, ¬ NDec m (B := B × ℕ) D (b, u) := Iff.rfl

theorem NStable_zero {B : Type} (Mp : NB ℕ 0 → Option (B × Bool)) (b : B) :
    NStable 0 Mp b ↔ IsStable Mp b := Iff.rfl

theorem NStable_succ {B : Type} (m : ℕ) (Mp : NB ℕ (m + 1) → Option (B × Bool)) (b : B) :
    NStable (m + 1) Mp b ↔ ∃ u, ¬ NStable m (nslice m Mp u) b := Iff.rfl

theorem NDec.of_eq : ∀ (m : ℕ) {B : Type} {D D' : NB B m → ℕ → Option Bool},
    (∀ x w, D x w = D' x w) → ∀ b, NDec m D b ↔ NDec m D' b
  | 0, _, _, _, h, _ => ⟨IsDecided.of_eq h, IsDecided.of_eq fun x w => (h x w).symm⟩
  | m + 1, _, _, _, h, b => exists_congr fun u => not_congr (NDec.of_eq m h (b, u))

theorem NStable.of_eq : ∀ (m : ℕ) {B : Type} {Mp Mp' : NB ℕ m → Option (B × Bool)},
    (∀ y, Mp y = Mp' y) → ∀ b, NStable m Mp b ↔ NStable m Mp' b
  | 0, _, _, _, h, _ => ⟨IsStable.of_eq h, IsStable.of_eq fun y => (h y).symm⟩
  | m + 1, _, _, _, h, b => exists_congr fun u => not_congr
      (NStable.of_eq m (fun y => h (nbMapBase m (fun w => (w, u)) y)) b)

/-- Transport along a base map: `NDec m (D ∘ nbMapBase g) c ↔ NDec m D (g c)`. -/
theorem NDec_nbMapBase : ∀ (m : ℕ) {B C : Type} (D : NB C m → ℕ → Option Bool) (g : B → C) (c : B),
    NDec m (fun y w => D (nbMapBase m g y) w) c ↔ NDec m D (g c)
  | 0, _, _, _, _, _ => Iff.rfl
  | m + 1, B, C, D, g, c => exists_congr fun u => not_congr
      (NDec_nbMapBase m (B := B × ℕ) (C := C × ℕ) D (fun p : B × ℕ => (g p.1, p.2)) (c, u))

/-- Reassociation: `(m+1)`-deciding `(b, u)` with `D` on `B × ℕ` is `(m+1)`-deciding `b` with
`D` precomposed by the insertion of `u` at the base. -/
theorem NDec_assoc : ∀ (m : ℕ) {B : Type} (D : NB (B × ℕ) m → ℕ → Option Bool) (b : B) (u : ℕ),
    NDec m D (b, u) ↔ NDec m (fun y w => D (nbMapBase m (fun b => (b, u)) y) w) b :=
  fun m _ D b u => (NDec_nbMapBase m D (fun b => (b, u)) b).symm

/-! ### `Σ⁰_{m+2}` conditions: `NRel`, `NSR` (Lemma 6.2) -/

/-- Relations `R ⊂ A × B × ℕ^{m+2}`, the data of Lemma 6.2 for `n = m+1`. -/
def NRel (A B : Type) (m : ℕ) : Type := A → NB B m → ℕ → ℕ → Prop

/-- The complement of a relation. -/
def compl {A B : Type} {m : ℕ} (R : NRel A B m) : NRel A B m := fun a x u v => ¬ R a x u v

/-- `S_R (a) = {b | ∃ u₁ ∀ u₂ ⋯ u_{m+2}, R}` (Lemma 6.2), by the recursion
`NSR (m+1) R a b = ∃ u, ¬ NSR m (compl R) a (b, u)`. -/
def NSR : (m : ℕ) → {A B : Type} → NRel A B m → A → B → Prop
  | 0, _, _, R, a, b => ∃ u, ∀ v, R a b u v
  | m + 1, _, _, R, a, b => ∃ u, ¬ NSR m (compl R) a (b, u)

theorem NSR_zero {A B : Type} (R : NRel A B 0) (a : A) (b : B) :
    NSR 0 R a b ↔ ∃ u, ∀ v, R a b u v := Iff.rfl

theorem NSR_succ {A B : Type} (m : ℕ) (R : NRel A B (m + 1)) (a : A) (b : B) :
    NSR (m + 1) R a b ↔ ∃ u, ¬ NSR m (compl R) a (b, u) := Iff.rfl

/-- `R` is a computable subset of `A × B × ℕ^{m+2}`. -/
def NRelComp {A B : Type} [Enc M A] [Enc M B] (m : ℕ) (R : NRel A B m) : Prop :=
  CompSet M (fun q : A × NB B m × ℕ × ℕ => R q.1 q.2.1 q.2.2.1 q.2.2.2)

theorem NRelComp.compl {A B : Type} [Enc M A] [Enc M B] {m : ℕ} {R : NRel A B m}
    (h : NRelComp (M := M) m R) : NRelComp (M := M) m (compl R) := CompSet.not h

/-- `NSR` respects pointwise equivalence of relations. -/
theorem NSR_congr : ∀ (m : ℕ) {A B : Type} {R R' : NRel A B m},
    (∀ a x u v, R a x u v ↔ R' a x u v) → ∀ a b, NSR m R a b ↔ NSR m R' a b
  | 0, _, _, _, _, h, a, b => exists_congr fun u => forall_congr' fun v => h a b u v
  | m + 1, _, _, _, _, h, a, b => exists_congr fun u => not_congr
      (NSR_congr m (fun a x u v => not_congr (h a x u v)) a (b, u))

/-- `m`-fold complement. -/
def complPow {A B : Type} {m : ℕ} : ℕ → NRel A B m → NRel A B m
  | 0, R => R
  | k + 1, R => compl (complPow k R)

/-- `k`-fold negation of a proposition. -/
private def negPow : ℕ → Prop → Prop
  | 0, p => p
  | k + 1, p => ¬ negPow k p

/-- `complPow` pointwise: the relation level `m` (and the base type) only enter through the types. -/
private theorem complPow_apply {A B : Type} {m : ℕ} :
    ∀ (k : ℕ) (R : NRel A B m) a x u v, complPow k R a x u v ↔ negPow k (R a x u v)
  | 0, _, _, _, _, _ => Iff.rfl
  | k + 1, R, a, x, u, v => not_congr (complPow_apply k R a x u v)

/-- `n`-decidedness, unfolded: if `IsDecided D x ↔ ∃ u ∀ v, R a x u v` for all `x : NB B m`
(a `Σ⁰₂` description of the base case), then `NDec m D b ↔ NSR m (complPow m R) a b`. -/
theorem NDec_iff_NSR : ∀ (m : ℕ) {A B : Type} (D : NB B m → ℕ → Option Bool) (R : NRel A B m)
    (a : A), (∀ x, IsDecided D x ↔ ∃ u, ∀ v, R a x u v) → ∀ b, NDec m D b ↔ NSR m (complPow m R) a b
  | 0, _, _, _, _, _, h, b => h b
  | m + 1, A, B, D, R, a, h, b => by
    show (∃ u, ¬ NDec m D (b, u)) ↔
      ∃ u, ¬ NSR m (compl (compl (complPow (m := m + 1) m R))) a (b, u)
    refine exists_congr fun u => not_congr ?_
    refine (NDec_iff_NSR m (B := B × ℕ) D R a h (b, u)).trans
      (NSR_congr m (fun a x u v => ?_) a (b, u))
    exact (complPow_apply (B := B × ℕ) (m := m) m R a x u v).trans
      ((complPow_apply (B := B) (m := m + 1) m R a x u v).symm.trans Classical.not_not.symm)

/-- Transport along a base map: `NSR m (R ∘ nbMapBase f) a x ↔ NSR m R a (f x)`. -/
theorem NSR_nbMapBase : ∀ (m : ℕ) {A B C : Type} (R : NRel A C m) (f : B → C) (a : A) (b : B),
    NSR m (fun a x u v => R a (nbMapBase m f x) u v) a b ↔ NSR m R a (f b)
  | 0, _, _, _, _, _, _, _ => Iff.rfl
  | m + 1, _, B, C, R, f, a, b => exists_congr fun u => not_congr
      (NSR_nbMapBase m (B := B × ℕ) (C := C × ℕ) (compl R) (fun p : B × ℕ => (f p.1, p.2)) a (b, u))

private theorem NSR_true_false : ∀ (m : ℕ) {A B : Type} (a : A) (b : B),
    NSR m (fun _ _ _ _ => True) a b ∧ ¬ NSR m (fun _ _ _ _ => False) a b
  | 0, _, _, _, _ => ⟨⟨0, fun _ => trivial⟩, fun ⟨_, h⟩ => h 0⟩
  | m + 1, _, B, a, b =>
    ⟨⟨0, fun h => (NSR_true_false m (B := B × ℕ) a (b, 0)).2
        ((NSR_congr m (fun _ _ _ _ => ⟨fun h => h trivial, fun h => h.elim⟩) a (b, 0)).1 h)⟩,
     fun ⟨u, h⟩ => h ((NSR_congr m (fun _ _ _ _ => ⟨fun _ => trivial, fun _ h => h⟩) a (b, u)).2
        (NSR_true_false m (B := B × ℕ) a (b, u)).1)⟩

/-- The relation whose `NSR` is always true, resp. always false. -/
theorem NSR_true : ∀ (m : ℕ) {A B : Type} (a : A) (b : B), NSR m (fun _ _ _ _ => True) a b :=
  fun m _ _ a b => (NSR_true_false m a b).1

theorem NSR_false : ∀ (m : ℕ) {A B : Type} (a : A) (b : B), ¬ NSR m (fun _ _ _ _ => False) a b :=
  fun m _ _ a b => (NSR_true_false m a b).2

/-- Cases on a decidable property of the base: `NSR m (if P (base) then R₁ else R₂)`. -/
theorem NSR_ite : ∀ (m : ℕ) {A B : Type} (P : B → Prop) (R₁ R₂ : NRel A B m) (a : A) (b : B),
    NSR m (fun a x u v => if P (nbBase m x) then R₁ a x u v else R₂ a x u v) a b ↔
      if P b then NSR m R₁ a b else NSR m R₂ a b
  | 0, _, _, P, R₁, R₂, a, b => by
    by_cases hP : P b
    · rw [ite_eq_left hP]
      exact exists_congr fun u => forall_congr' fun v => by
        show (if P b then R₁ a b u v else R₂ a b u v) ↔ _
        rw [ite_eq_left hP]
    · rw [ite_eq_right hP]
      exact exists_congr fun u => forall_congr' fun v => by
        show (if P b then R₁ a b u v else R₂ a b u v) ↔ _
        rw [ite_eq_right hP]
  | m + 1, A, B, P, R₁, R₂, a, b => by
    have key : ∀ u, NSR m (compl (fun a x u v =>
        if P (nbBase (m + 1) x) then R₁ a x u v else R₂ a x u v)) a (b, u) ↔
          if P b then NSR m (compl R₁) a (b, u) else NSR m (compl R₂) a (b, u) := fun u =>
      (NSR_congr m (fun a x u v => by
          show (¬ if P (nbBase m x).1 then R₁ a x u v else R₂ a x u v) ↔
            if P (nbBase m x).1 then ¬ R₁ a x u v else ¬ R₂ a x u v
          by_cases hP : P (nbBase m x).1
          · rw [ite_eq_left hP, ite_eq_left hP]
          · rw [ite_eq_right hP, ite_eq_right hP]) a (b, u)).trans
        (NSR_ite m (B := B × ℕ) (fun p => P p.1) (compl R₁) (compl R₂) a (b, u))
    show (∃ u, ¬ NSR m (compl (fun a x u v =>
        if P (nbBase (m + 1) x) then R₁ a x u v else R₂ a x u v)) a (b, u)) ↔
      if P b then (∃ u, ¬ NSR m (compl R₁) a (b, u)) else ∃ u, ¬ NSR m (compl R₂) a (b, u)
    by_cases hP : P b
    · rw [ite_eq_left hP]
      exact exists_congr fun u => not_congr ((key u).trans (by rw [ite_eq_left hP]))
    · rw [ite_eq_right hP]
      exact exists_congr fun u => not_congr ((key u).trans (by rw [ite_eq_right hP]))

/-- Lemma 6.2 (`lemma_nstabilizer`): for computable `R ⊂ A × B × ℕ^{m+2}` there is a total
computable `(m+1)`-decision map `D_R : A × B × ℕ^{m+1} → {±}` with `D_R (a, ·)^{d_{m+1}} = S_R (a)`. -/
theorem n_stabilizer (m : ℕ) {A B : Type} [Enc M A] [Enc M B] (R : NRel A B m)
    (hR : NRelComp (M := M) m R) :
    ∃ D : A → NB B m → ℕ → Bool, CompT M (fun q : A × NB B m × ℕ => D q.1 q.2.1 q.2.2) ∧
      ∀ a b, NDec m (fun x w => some (D a x w)) b ↔ NSR m R a b := by
  induction m generalizing B with
  | zero => exact ⟨DR R, compT_DR hR, fun a b => isDecided_DR_iff R a b⟩
  | succ m ih =>
    obtain ⟨D, hD, hDR⟩ := ih (B := B × ℕ) (compl R) hR.compl
    exact ⟨D, hD, fun a b => exists_congr fun u => not_congr (hDR a (b, u))⟩

/-! ### Decision maps versus sequences at level `m+1` (Corollary 6.3) -/

/-- `D_M`: the `(m+1)`-decision map of `M : ℕ^{m+1} → B × {±}`: `D_M (b, ū) = ±` iff `M (ū) = (b, ±)`,
where the tuple `ū` is `((b, u₁), …, u_m)` with the base `b` replaced by the time `w`. -/
noncomputable def DM (m : ℕ) {B : Type} (Mp : NB ℕ m → Option (B × Bool)) :
    NB B m → ℕ → Option Bool :=
  fun x w => match Mp (nbMapBase m (fun _ => w) x) with
    | some (b', s) => if b' = nbBase m x then some s else none
    | none => none

theorem NDec_DM_iff : ∀ (m : ℕ) {B : Type} (Mp : NB ℕ m → Option (B × Bool)) (b : B),
    NDec m (DM m Mp) b ↔ NStable m Mp b
  | 0, _, Mp, b => (NDec.of_eq 0 (D' := decOfSeq Mp) (fun _ _ => rfl) b).trans
      (isDecided_decOfSeq_iff Mp b)
  | m + 1, B, Mp, b => by
    show (∃ u, ¬ NDec m (B := B × ℕ) (DM (m + 1) Mp) (b, u)) ↔ ∃ u, ¬ NStable m (nslice m Mp u) b
    refine exists_congr fun u => not_congr ?_
    refine (NDec_assoc m (DM (m + 1) Mp) b u).trans
      ((NDec.of_eq m (D' := DM m (nslice m Mp u)) (fun y w => ?_) b).trans
        (NDec_DM_iff m (nslice m Mp u) b))
    have e1 : nbMapBase (m + 1) (fun _ : B => w) (nbMapBase m (fun b => (b, u)) y) =
        nbMapBase m (fun w' => (w', u)) (nbMapBase m (fun _ => w) y) := by
      show nbMapBase m (fun p : B × ℕ => (w, p.2)) (nbMapBase m (fun b => (b, u)) y) = _
      rw [nbMapBase_nbMapBase, nbMapBase_nbMapBase]
    have e2 : nbBase (m + 1) (nbMapBase m (fun b => (b, u)) y) = nbBase m y := by
      show (nbBase m (nbMapBase m (fun b => (b, u)) y)).1 = _
      rw [nbBase_nbMapBase]
    unfold DM nslice
    rw [e1, e2]

theorem comp_DM (m : ℕ) {B : Type} [Enc M B] {Mp : NB ℕ m → Option (B × Bool)} (hM : Comp M Mp) :
    Comp M (fun p : NB B m × ℕ => DM m Mp p.1 p.2) := by
  -- `(x, w) ↦ (base x, M (x with base w))`, then keep the sign iff the first component is `base x`
  have h1 : Comp M (fun p : NB B m × ℕ =>
      (Mp (nbMapBase m (fun _ => p.2) p.1)).map (fun q => (nbBase m p.1, q))) :=
    (((compT_nbBase m).comp compT_fst).toComp.pair
        (hM.compT (compT_nbMapBase_const m (B := B) (C := ℕ)))).congr fun p => by
      cases Mp (nbMapBase m (fun _ => p.2) p.1) <;> simp [Option.bind, Option.map]
  have h2 : Comp M (fun q : B × (B × Bool) => if q.2.1 = q.1 then some q.2.2 else none) :=
    Comp.cases (compSet_eq (compT_fst.comp compT_snd) compT_fst) (compT_snd.comp compT_snd) comp_none
  refine (h2.comp h1).congr fun p => ?_
  unfold DM
  cases h : Mp (nbMapBase m (fun _ => p.2) p.1) with
  | none => simp [Option.bind]
  | some q => obtain ⟨b', s⟩ := q; simp [Option.bind, Option.map]

/-- `M_D`: the sequence of an `(m+1)`-decision map `D` on an infinite `B`:
`M_D (ι (b, t), ū) = (b, D ((b, ū), t))`. -/
noncomputable def MD (m : ℕ) {B : Type} [Enc M B] (D : NB B m → ℕ → Option Bool) :
    NB ℕ m → Option (B × Bool) :=
  fun y => (epsilonInv (M := M) B (M.unpair (nbBase m y)).1).bind fun b =>
    (D (nbMapBase m (fun _ => b) y) (M.unpair (nbBase m y)).2).map fun s => (b, s)

theorem NStable_MD_iff : ∀ (m : ℕ) {B : Type} [Enc M B] (D : NB B m → ℕ → Option Bool) (b : B),
    NStable m (MD (M := M) m D) b ↔ NDec m D b
  | 0, _, _, D, b => (NStable.of_eq 0 (Mp' := seqOfDec (M := M) D) (fun _ => rfl) b).trans
      (isStable_seqOfDec_iff D b)
  | m + 1, B, _, D, b => by
    show (∃ u, ¬ NStable m (nslice m (MD (M := M) (m + 1) D) u) b) ↔
      ∃ u, ¬ NDec m (B := B × ℕ) D (b, u)
    refine exists_congr fun u => not_congr ?_
    refine (NStable.of_eq m (Mp' := MD (M := M) m (fun y w => D (nbMapBase m (fun b => (b, u)) y) w))
        (fun y => ?_) b).trans
      ((NStable_MD_iff m (fun y w => D (nbMapBase m (fun b => (b, u)) y) w) b).trans
        (NDec_assoc m D b u).symm)
    have e2 : nbBase (m + 1) (nbMapBase m (fun w => (w, u)) y) = nbBase m y := by
      show (nbBase m (nbMapBase m (fun w => (w, u)) y)).1 = _
      rw [nbBase_nbMapBase]
    have e1 : ∀ b' : B, nbMapBase (m + 1) (fun _ : ℕ => b') (nbMapBase m (fun w => (w, u)) y) =
        nbMapBase m (fun b => (b, u)) (nbMapBase m (fun _ => b') y) := by
      intro b'
      show nbMapBase m (fun p : ℕ × ℕ => (b', p.2)) (nbMapBase m (fun w => (w, u)) y) = _
      rw [nbMapBase_nbMapBase, nbMapBase_nbMapBase]
    show MD (M := M) (m + 1) D (nbMapBase m (fun w => (w, u)) y) = _
    unfold MD
    rw [e2]
    simp only [e1]

theorem comp_MD (m : ℕ) {B : Type} [Enc M B] {D : NB B m → ℕ → Option Bool}
    (hD : Comp M (fun p : NB B m × ℕ => D p.1 p.2)) : Comp M (MD (M := M) m D) := by
  -- `y ↦ (ε⁻¹ (unpair (base y)).1, y)`, then `(b, y) ↦ (b, D (y with base b, (unpair (base y)).2))`
  have hbase : CompT M (fun y : NB ℕ m => nbBase m y) := compT_nbBase m
  have h1 : Comp M (fun y : NB ℕ m => (epsilonInv (M := M) B (M.unpair (nbBase m y)).1).map
      fun b => (b, y)) := by
    have := Comp.pair (M := M) ((comp_epsilonInv (A := B)).compT (compT_unpair_fst.comp hbase))
      (compT_id (A := NB ℕ m)).toComp
    exact this.congr fun y => by
      cases epsilonInv (M := M) B (M.unpair (nbBase m y)).1 <;> simp [Option.bind, Option.map]
  have hg : CompT M (fun p : B × NB ℕ m =>
      (nbMapBase m (fun _ => p.1) p.2, (M.unpair (nbBase m p.2)).2)) :=
    CompT.pair ((compT_nbMapBase_const m (B := ℕ) (C := B)).comp compT_swap)
      (compT_unpair_snd.comp (hbase.comp compT_snd))
  have h2 : Comp M (fun p : B × NB ℕ m =>
      (D (nbMapBase m (fun _ => p.1) p.2) (M.unpair (nbBase m p.2)).2).map fun s => (p.1, s)) :=
    (compT_fst.toComp.pair (hD.compT hg)).congr fun p => by
      cases D (nbMapBase m (fun _ => p.1) p.2) (M.unpair (nbBase m p.2)).2 <;>
        simp [Option.bind, Option.map]
  refine (h2.comp h1).congr fun y => ?_
  unfold MD
  cases epsilonInv (M := M) B (M.unpair (nbBase m y)).1 <;> simp [Option.bind, Option.map]

theorem MD_total (m : ℕ) {B : Type} [Enc M B] (hB : Enc.Infinite M B) {D : NB B m → ℕ → Option Bool}
    (hD : ∀ x w, D x w ≠ none) (y : NB ℕ m) : MD (M := M) m D y ≠ none := by
  unfold MD
  cases he : epsilonInv (M := M) B (M.unpair (nbBase m y)).1 with
  | none => exact absurd he (epsilonInv_isSome hB _)
  | some b =>
    simp only [Option.bind_some]
    cases hd : D (nbMapBase m (fun _ => b) y) (M.unpair (nbBase m y)).2 with
    | none => exact absurd hd (hD _ _)
    | some s => simp

end Stable
