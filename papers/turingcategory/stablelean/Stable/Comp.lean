/-!
# The model of computation (Proposition 2.4 of the paper, as an interface)

The paper works in a category `𝒮` of encoded sets whose morphisms are partial maps
computed by Turing machines, and isolates in Proposition 2.4 ("properties of `𝒮`")
exactly the computability facts that are used later.  Here these facts are packaged
as the fields of a structure `TuringModel`.  Everything else in the development is
*proved* from this interface.

* `Code`      — the set `𝒯` of Turing machines `ℕ → ℕ`;
* `run T n k` — the output of `*T(n)` if it halts within `k` steps (`none` otherwise);
* `eval T n`  — the partial function computed by `T` (`some y` iff `*T(n)` halts with output `y`);
* `code`      — the distinguished encoding `e_𝒯 : 𝒯 → ℕ`;
* `pair`/`unpair` — the fixed computable pairing bijection `⟨·,·⟩`, increasing in each argument.

A partial function `f : ℕ → Option ℕ` is *computable* when it is `eval T` for some `T`;
the axioms say that the computable partial functions contain the basic functions and are
closed under composition, pairing, definition by cases (on a total decidable predicate),
primitive recursion and unbounded search (`μ`), that the step relation `Halt'` is decidable,
that the universal function `U` is computable (part (2) of Proposition 2.4), and the
s-m-n theorem (part (3)).  All of these hold for the standard model (Turing machines, or
`Nat.Partrec.Code` of Mathlib).  Products, lists and the induced encodings (parts (1), (4))
are *constructed* from `pair` in `Stable.Enc`; definition by cases and primitive recursion
(part (6)) are the fields `comp_cases`, `comp_primrec`.
-/

namespace Stable

/-- The natural numbers (scoped, so that the library can be imported next to Mathlib). -/
scoped notation "ℕ" => Nat

open Classical

/-- A model of computation; see the module docstring.  `Option ℕ` models partial values
(`none` = undefined).  All computability statements are of the form `∃ T, ∀ n, eval T n = …`. -/
structure TuringModel where
  /-- The set `𝒯` of Turing machines `ℕ → ℕ`. -/
  Code : Type
  /-- `run T n k = some y` iff the computation `*T(n)` halts within `k` steps with output `y`. -/
  run : Code → ℕ → ℕ → Option ℕ
  run_mono : ∀ {T : Code} {n k k' y : ℕ}, k ≤ k' → run T n k = some y → run T n k' = some y
  /-- The partial function computed by `T`. -/
  eval : Code → ℕ → Option ℕ
  eval_iff : ∀ (T : Code) (n y : ℕ), eval T n = some y ↔ ∃ k, run T n k = some y
  /-- The distinguished encoding `e_𝒯 : 𝒯 → ℕ`. -/
  code : Code → ℕ
  code_inj : ∀ {T T' : Code}, code T = code T' → T = T'
  /-- `e_𝒯(𝒯) ⊂ ℕ` is a computable set. -/
  comp_code_mem : ∃ T₀, ∀ n, eval T₀ n = some (if ∃ T, code T = n then 1 else 0)
  /-- The fixed pairing bijection `⟨·,·⟩ : ℕ × ℕ → ℕ`. -/
  pair : ℕ → ℕ → ℕ
  unpair : ℕ → ℕ × ℕ
  unpair_pair : ∀ a b, unpair (pair a b) = (a, b)
  pair_unpair : ∀ n, pair (unpair n).1 (unpair n).2 = n
  pair_lt_left : ∀ {a a' : ℕ} (b : ℕ), a < a' → pair a b < pair a' b
  pair_lt_right : ∀ (a : ℕ) {b b' : ℕ}, b < b' → pair a b < pair a b'
  -- Basic computable functions.
  comp_const : ∀ c : ℕ, ∃ T₀, ∀ n, eval T₀ n = some c
  comp_succ : ∃ T₀, ∀ n, eval T₀ n = some (n + 1)
  comp_fst : ∃ T₀, ∀ n, eval T₀ n = some (unpair n).1
  comp_snd : ∃ T₀, ∀ n, eval T₀ n = some (unpair n).2
  comp_add : ∃ T₀, ∀ n, eval T₀ n = some ((unpair n).1 + (unpair n).2)
  comp_le : ∃ T₀, ∀ n, eval T₀ n = some (if (unpair n).1 ≤ (unpair n).2 then 1 else 0)
  comp_eq : ∃ T₀, ∀ n, eval T₀ n = some (if (unpair n).1 = (unpair n).2 then 1 else 0)
  -- Closure properties.
  /-- Composition `f ∘ g` of partial maps. -/
  comp_comp : ∀ (f g : ℕ → Option ℕ), (∃ T, ∀ n, eval T n = f n) → (∃ T, ∀ n, eval T n = g n) →
    ∃ T₀, ∀ n, eval T₀ n = (g n).bind f
  /-- Pairing `n ↦ ⟨f n, g n⟩` of partial maps (defined where both are). -/
  comp_pair : ∀ (f g : ℕ → Option ℕ), (∃ T, ∀ n, eval T n = f n) → (∃ T, ∀ n, eval T n = g n) →
    ∃ T₀, ∀ n, eval T₀ n = (f n).bind (fun a => (g n).map (pair a))
  /-- Definition by cases on a total decidable predicate `p`. -/
  comp_cases : ∀ (p : ℕ → Bool) (f g : ℕ → Option ℕ),
    (∃ T, ∀ n, eval T n = some (cond (p n) 1 0)) →
    (∃ T, ∀ n, eval T n = f n) → (∃ T, ∀ n, eval T n = g n) →
    ∃ T₀, ∀ n, eval T₀ n = cond (p n) (f n) (g n)
  /-- Primitive recursion: `r a 0 = g a`, `r a (n+1) = h ⟨a, ⟨n, r a n⟩⟩`, as a function of `⟨a, n⟩`. -/
  comp_primrec : ∀ (g h : ℕ → Option ℕ), (∃ T, ∀ n, eval T n = g n) → (∃ T, ∀ n, eval T n = h n) →
    ∀ r : ℕ → ℕ → Option ℕ, (∀ a, r a 0 = g a) →
    (∀ a n, r a (n + 1) = (r a n).bind (fun y => h (pair a (pair n y)))) →
    ∃ T₀, ∀ m, eval T₀ m = r (unpair m).1 (unpair m).2
  /-- Unbounded search: `μ k. p ⟨a, k⟩` for a total decidable predicate `p`. -/
  comp_mu : ∀ (p : ℕ → Bool), (∃ T, ∀ n, eval T n = some (cond (p n) 1 0)) →
    ∃ T₀, ∀ a k, eval T₀ a = some k ↔ (p (pair a k) = true ∧ ∀ k' < k, p (pair a k') = false)
  -- The universal machine (Proposition 2.4 (2)) and the s-m-n theorem (Proposition 2.4 (3)).
  /-- `Halt' ⊂ 𝒯 × ℕ × ℕ × ℕ` is decidable: `(T,n,k,y) ∈ Halt'` iff `*T(n)` halts within `k`
  steps with output `y`.  Stated on encoded inputs `⟨e_𝒯 T, ⟨n, ⟨k, y⟩⟩⟩`. -/
  comp_halt' : ∃ T₀, ∀ (T : Code) (n k y : ℕ),
    eval T₀ (pair (code T) (pair n (pair k y))) = some (if run T n k = some y then 1 else 0)
  /-- The universal function `U (T, n) = T (n)`, on encoded inputs. -/
  comp_univ : ∃ T₀, ∀ (T : Code) (n : ℕ), eval T₀ (pair (code T) n) = eval T n
  /-- s-m-n: from a computable `f` of `⟨a, b⟩` one gets a total computable `s : ℕ → 𝒯` with
  `s a` computing `b ↦ f ⟨a, b⟩`. -/
  comp_smn : ∀ (f : ℕ → Option ℕ), (∃ T, ∀ n, eval T n = f n) →
    ∃ s : ℕ → Code, (∃ T₀, ∀ a, eval T₀ a = some (code (s a))) ∧ ∀ a b, eval (s a) b = f (pair a b)

end Stable

namespace Stable

open Classical

namespace TuringModel

variable (M : TuringModel)

/-- `f : ℕ → Option ℕ` is computable: it is the partial function of some machine. -/
def IsComp (f : ℕ → Option ℕ) : Prop := ∃ T, ∀ n, M.eval T n = f n

/-- A total `Bool`-valued predicate on `ℕ` is computable (its characteristic function is). -/
def IsCompB (p : ℕ → Bool) : Prop := M.IsComp (fun n => some (cond (p n) 1 0))

/-- A set `P ⊂ ℕ` is computable (recursive): its characteristic function is computable. -/
def IsCompSet (P : ℕ → Prop) : Prop := M.IsComp (fun n => some (if P n then 1 else 0))

/-- A total function `ℕ → ℕ` is computable. -/
def IsCompT (f : ℕ → ℕ) : Prop := M.IsComp (fun n => some (f n))

variable {M}

theorem IsComp.congr {f g : ℕ → Option ℕ} (h : M.IsComp f) (e : ∀ n, f n = g n) : M.IsComp g := by
  obtain ⟨T, hT⟩ := h; exact ⟨T, fun n => (hT n).trans (e n)⟩

theorem isCompSet_iff_isCompB (P : ℕ → Prop) :
    M.IsCompSet P ↔ M.IsCompB (fun n => decide (P n)) := by
  unfold IsCompSet IsCompB
  constructor
  · intro h; refine h.congr fun n => ?_
    by_cases hP : P n <;> simp [hP]
  · intro h; refine h.congr fun n => ?_
    by_cases hP : P n <;> simp [hP]

theorem IsCompB.toSet {p : ℕ → Bool} (h : M.IsCompB p) : M.IsCompSet (fun n => p n = true) := by
  unfold IsCompSet; refine h.congr fun n => ?_
  cases hpn : p n <;> simp [hpn]

theorem IsCompSet.toB {P : ℕ → Prop} (h : M.IsCompSet P) : M.IsCompB (fun n => decide (P n)) :=
  (isCompSet_iff_isCompB P).1 h

/-- `eval T n = some y` is monotone in the step bound: the output is unique. -/
theorem run_unique {T : M.Code} {n k k' y y' : ℕ} (h : M.run T n k = some y)
    (h' : M.run T n k' = some y') : y = y' := by
  rcases Nat.le_total k k' with hk | hk
  · have := M.run_mono hk h; rw [this] at h'; exact Option.some.inj h'
  · have := M.run_mono hk h'; rw [this] at h; exact (Option.some.inj h).symm

theorem eval_eq_some_of_run {T : M.Code} {n k y : ℕ} (h : M.run T n k = some y) :
    M.eval T n = some y := (M.eval_iff T n y).2 ⟨k, h⟩

theorem eval_eq_none_iff {T : M.Code} {n : ℕ} : M.eval T n = none ↔ ∀ k, M.run T n k = none := by
  constructor
  · intro h k
    cases hk : M.run T n k with
    | none => rfl
    | some y => rw [eval_eq_some_of_run hk] at h; cases h
  · intro h
    cases he : M.eval T n with
    | none => rfl
    | some y =>
      obtain ⟨k, hk⟩ := (M.eval_iff T n y).1 he
      rw [h k] at hk; cases hk

/-- Basic computable functions, restated with `IsComp`. -/
theorem isComp_const (c : ℕ) : M.IsComp (fun _ => some c) := M.comp_const c
theorem isComp_succ : M.IsComp (fun n => some (n + 1)) := M.comp_succ
theorem isComp_fst : M.IsComp (fun n => some (M.unpair n).1) := M.comp_fst
theorem isComp_snd : M.IsComp (fun n => some (M.unpair n).2) := M.comp_snd
theorem isComp_add : M.IsComp (fun n => some ((M.unpair n).1 + (M.unpair n).2)) := M.comp_add
theorem isCompSet_le : M.IsCompSet (fun n => (M.unpair n).1 ≤ (M.unpair n).2) :=
  IsComp.congr M.comp_le fun n => by
    by_cases h : (M.unpair n).1 ≤ (M.unpair n).2 <;> simp [h]
theorem isCompSet_eq : M.IsCompSet (fun n => (M.unpair n).1 = (M.unpair n).2) :=
  IsComp.congr M.comp_eq fun n => by
    by_cases h : (M.unpair n).1 = (M.unpair n).2 <;> simp [h]
theorem isCompSet_code_mem : M.IsCompSet (fun n => ∃ T, M.code T = n) := M.comp_code_mem

theorem IsComp.comp {f g : ℕ → Option ℕ} (hf : M.IsComp f) (hg : M.IsComp g) :
    M.IsComp (fun n => (g n).bind f) := M.comp_comp f g hf hg

theorem IsComp.pair {f g : ℕ → Option ℕ} (hf : M.IsComp f) (hg : M.IsComp g) :
    M.IsComp (fun n => (f n).bind (fun a => (g n).map (M.pair a))) := M.comp_pair f g hf hg

theorem IsComp.cases {p : ℕ → Bool} {f g : ℕ → Option ℕ} (hp : M.IsCompB p) (hf : M.IsComp f)
    (hg : M.IsComp g) : M.IsComp (fun n => cond (p n) (f n) (g n)) := M.comp_cases p f g hp hf hg

theorem IsCompT.comp {f g : ℕ → ℕ} (hf : M.IsCompT f) (hg : M.IsCompT g) :
    M.IsCompT (fun n => f (g n)) := by
  have := IsComp.comp (M := M) hf hg
  exact this.congr fun n => by simp [Option.bind]

theorem IsCompT.pair {f g : ℕ → ℕ} (hf : M.IsCompT f) (hg : M.IsCompT g) :
    M.IsCompT (fun n => M.pair (f n) (g n)) := by
  have := IsComp.pair (M := M) hf hg
  exact this.congr fun n => by simp [Option.bind, Option.map]

theorem isCompT_id : M.IsCompT (fun n => n) := by
  have := IsCompT.pair (M := M) M.comp_fst M.comp_snd
  exact this.congr fun n => by simp [M.pair_unpair]

theorem isCompT_const (c : ℕ) : M.IsCompT (fun _ => c) := M.comp_const c
theorem isCompT_fst : M.IsCompT (fun n => (M.unpair n).1) := M.comp_fst
theorem isCompT_snd : M.IsCompT (fun n => (M.unpair n).2) := M.comp_snd
theorem isCompT_succ : M.IsCompT (fun n => n + 1) := M.comp_succ

/-- A total computable function is a computable partial function. -/
theorem IsCompT.isComp {f : ℕ → ℕ} (hf : M.IsCompT f) : M.IsComp (fun n => some (f n)) := hf

/-- Precomposition of a set with a total computable map. -/
theorem IsCompSet.comp {P : ℕ → Prop} {g : ℕ → ℕ} (hP : M.IsCompSet P) (hg : M.IsCompT g) :
    M.IsCompSet (fun n => P (g n)) := by
  have := IsComp.comp (M := M) hP hg
  exact this.congr fun n => by simp [Option.bind]

theorem IsCompB.comp {p : ℕ → Bool} {g : ℕ → ℕ} (hp : M.IsCompB p) (hg : M.IsCompT g) :
    M.IsCompB (fun n => p (g n)) := by
  have := IsComp.comp (M := M) hp hg
  exact this.congr fun n => by simp [Option.bind]

theorem IsCompT.cases {p : ℕ → Bool} {f g : ℕ → ℕ} (hp : M.IsCompB p) (hf : M.IsCompT f)
    (hg : M.IsCompT g) : M.IsCompT (fun n => cond (p n) (f n) (g n)) := by
  have := IsComp.cases (M := M) hp hf hg
  exact this.congr fun n => by cases hpn : p n <;> simp [hpn]

theorem IsCompB.not {p : ℕ → Bool} (hp : M.IsCompB p) : M.IsCompB (fun n => !(p n)) := by
  have := IsCompT.cases (M := M) hp (isCompT_const 0) (isCompT_const 1)
  exact this.congr fun n => by cases hpn : p n <;> simp [hpn]

theorem IsCompB.and {p q : ℕ → Bool} (hp : M.IsCompB p) (hq : M.IsCompB q) :
    M.IsCompB (fun n => p n && q n) := by
  have := IsCompT.cases (M := M) hp hq (isCompT_const 0)
  exact this.congr fun n => by cases hpn : p n <;> cases hqn : q n <;> simp [hpn, hqn]

theorem IsCompB.or {p q : ℕ → Bool} (hp : M.IsCompB p) (hq : M.IsCompB q) :
    M.IsCompB (fun n => p n || q n) := by
  have := IsCompT.cases (M := M) hp (isCompT_const 1) hq
  exact this.congr fun n => by cases hpn : p n <;> cases hqn : q n <;> simp [hpn, hqn]

theorem IsCompB.const (b : Bool) : M.IsCompB (fun _ => b) := by
  cases b
  · exact (isCompT_const (M := M) 0).congr fun n => by simp
  · exact (isCompT_const (M := M) 1).congr fun n => by simp

theorem IsCompSet.not {P : ℕ → Prop} (hP : M.IsCompSet P) : M.IsCompSet (fun n => ¬ P n) := by
  have := (hP.toB).not
  rw [isCompSet_iff_isCompB]
  exact this.congr fun n => by by_cases h : P n <;> simp [h]

theorem IsCompSet.and {P Q : ℕ → Prop} (hP : M.IsCompSet P) (hQ : M.IsCompSet Q) :
    M.IsCompSet (fun n => P n ∧ Q n) := by
  have := (hP.toB).and hQ.toB
  rw [isCompSet_iff_isCompB]
  exact this.congr fun n => by by_cases h : P n <;> by_cases h' : Q n <;> simp [h, h']

theorem IsCompSet.or {P Q : ℕ → Prop} (hP : M.IsCompSet P) (hQ : M.IsCompSet Q) :
    M.IsCompSet (fun n => P n ∨ Q n) := by
  have := (hP.toB).or hQ.toB
  rw [isCompSet_iff_isCompB]
  exact this.congr fun n => by by_cases h : P n <;> by_cases h' : Q n <;> simp [h, h']

theorem IsCompSet.congr {P Q : ℕ → Prop} (hP : M.IsCompSet P) (e : ∀ n, P n ↔ Q n) :
    M.IsCompSet Q := by
  unfold IsCompSet at *; exact hP.congr fun n => by
    by_cases h : P n
    · simp [h, (e n).1 h]
    · have h' : ¬ Q n := fun hq => h ((e n).2 hq)
      simp [h, h']

theorem isCompSet_true : M.IsCompSet (fun _ => True) :=
  (isCompT_const (M := M) 1).congr fun n => by simp

theorem isCompSet_false : M.IsCompSet (fun _ => False) :=
  (isCompT_const (M := M) 0).congr fun n => by simp

/-- Comparison of two total computable functions. -/
theorem isCompSet_le_of {f g : ℕ → ℕ} (hf : M.IsCompT f) (hg : M.IsCompT g) :
    M.IsCompSet (fun n => f n ≤ g n) := by
  have := IsCompSet.comp (M := M) isCompSet_le (hf.pair hg)
  exact this.congr fun n => by simp [M.unpair_pair]

theorem isCompSet_eq_of {f g : ℕ → ℕ} (hf : M.IsCompT f) (hg : M.IsCompT g) :
    M.IsCompSet (fun n => f n = g n) := by
  have := IsCompSet.comp (M := M) isCompSet_eq (hf.pair hg)
  exact this.congr fun n => by simp [M.unpair_pair]

theorem isCompSet_lt_of {f g : ℕ → ℕ} (hf : M.IsCompT f) (hg : M.IsCompT g) :
    M.IsCompSet (fun n => f n < g n) := by
  have := isCompSet_le_of (M := M) (isCompT_succ.comp hf) hg
  exact this.congr fun n => by simp [Nat.lt_iff_add_one_le]

end TuringModel

end Stable
