import Mathlib.Computability.PartrecCode
import Mathlib.Computability.RE
import Stable

/-!
# The standard model of `Stable.TuringModel`

We instantiate the interface `Stable.TuringModel` (Proposition 2.4 of the paper) with Mathlib's
partial recursive codes `Nat.Partrec.Code`:

* `Code := Nat.Partrec.Code`, `run c n k := Nat.Partrec.Code.evaln k c n` (bounded evaluation);
* `eval c n` is the `Option`-valued version of `Nat.Partrec.Code.eval c n` (classically decided
  domain);
* `code := Encodable.encode` (a bijection `Code ≃ ℕ`, since `Code` is `Denumerable`);
* `pair := Nat.pair`, `unpair := Nat.unpair`.

Every computability field is reduced to Mathlib through one bridge lemma, `isComp_iff`:
`f : ℕ → Option ℕ` is computed by a code iff `fun n => (f n : Part ℕ)` is `Nat.Partrec`.
The result `mathlibModel` uses no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace StableModel

open Nat.Partrec (Code)
open Encodable Denumerable

/-! ### `Part ℕ` versus `Option ℕ` -/

/-- Classical conversion of a partial value into an `Option`. -/
noncomputable def toOpt (p : Part Nat) : Option Nat :=
  @Part.toOption _ p (Classical.dec _)

theorem toOpt_eq_some_iff {p : Part Nat} {y : Nat} : toOpt p = some y ↔ y ∈ p :=
  @Part.toOption_eq_some_iff _ p (Classical.dec _) y

theorem toOpt_coe (o : Option Nat) : toOpt (o : Part Nat) = o := by
  cases h : toOpt (o : Part Nat) with
  | some y => exact (Part.mem_ofOption.1 (toOpt_eq_some_iff.1 h)).symm
  | none =>
    cases o with
    | none => rfl
    | some a =>
      have : toOpt ((some a : Option Nat) : Part Nat) = some a :=
        toOpt_eq_some_iff.2 (Part.mem_ofOption.2 rfl)
      rw [h] at this
      exact this

/-- `Option.bind` commutes with the coercion `Option ℕ → Part ℕ`. -/
theorem coe_bind (o : Option Nat) (f : Nat → Option Nat) :
    ((o.bind f : Option Nat) : Part Nat) = (o : Part Nat).bind (fun a => (f a : Part Nat)) := by
  cases o <;> simp [Part.coe_none, Part.coe_some, Part.bind_none, Part.bind_some]

/-! ### Evaluation of codes as `Option`-valued functions -/

/-- The partial function computed by a code, with values in `Option ℕ`. -/
noncomputable def evalOpt (c : Code) (n : Nat) : Option Nat := toOpt (c.eval n)

theorem evalOpt_eq_some_iff {c : Code} {n y : Nat} : evalOpt c n = some y ↔ y ∈ c.eval n :=
  toOpt_eq_some_iff

/-- `f` is computed by some code. -/
def IsComp (f : Nat → Option Nat) : Prop := ∃ c : Code, ∀ n, evalOpt c n = f n

/-- **Bridge lemma.** `f : ℕ → Option ℕ` is computed by a code iff it is partial recursive. -/
theorem isComp_iff (f : Nat → Option Nat) :
    IsComp f ↔ Nat.Partrec (fun n => (f n : Part Nat)) := by
  constructor
  · rintro ⟨c, hc⟩
    refine (Nat.Partrec.Code.exists_code.2 ⟨c, rfl⟩).of_eq fun n => ?_
    ext y
    rw [← evalOpt_eq_some_iff, hc n, Part.mem_ofOption]
    rfl
  · intro h
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 h
    exact ⟨c, fun n => by rw [evalOpt, hc]; exact toOpt_coe (f n)⟩

/-- A total computable function is computed by a code. -/
theorem isComp_of_computable {F : Nat → Nat} (hF : Computable F) :
    IsComp (fun n => some (F n)) :=
  (isComp_iff _).2 ((Partrec.nat_iff.1 hF).of_eq fun _ => (Part.coe_some _).symm)

theorem computable_of_isComp {F : Nat → Nat} (h : IsComp (fun n => some (F n))) : Computable F :=
  Partrec.nat_iff.2 (((isComp_iff _).1 h).of_eq fun _ => Part.coe_some _)

/-- A `Bool`-valued predicate with computable characteristic function is `Computable`. -/
theorem computable_bool {p : Nat → Bool} (h : IsComp (fun n => some (cond (p n) 1 0))) :
    Computable p := by
  have h1 : Computable (fun n => cond (p n) 1 0) := computable_of_isComp h
  refine Computable.encode_iff.1 (h1.of_eq fun n => ?_)
  cases p n <;> rfl

theorem isComp_of_primrec {F : Nat → Nat} (hF : Primrec F) : IsComp (fun n => some (F n)) :=
  isComp_of_computable hF.to_comp

/-! ### The individual fields -/

theorem primrec_u1 : Primrec (fun n : Nat => (Nat.unpair n).1) := Primrec.fst.comp Primrec.unpair
theorem primrec_u2 : Primrec (fun n : Nat => (Nat.unpair n).2) := Primrec.snd.comp Primrec.unpair

open Classical in
theorem isComp_code_mem :
    ∃ T₀ : Code, ∀ n, evalOpt T₀ n = some (if ∃ T : Code, encode T = n then 1 else 0) := by
  refine ⟨Code.const 1, fun n => ?_⟩
  have hn : ∃ T : Code, encode T = n := ⟨ofNat Code n, encode_ofNat n⟩
  rw [ite_eq_left hn, evalOpt, Nat.Partrec.Code.eval_const, ← Part.coe_some]
  exact toOpt_coe _

theorem isComp_const (c : Nat) : ∃ T₀ : Code, ∀ n, evalOpt T₀ n = some c :=
  isComp_of_primrec (Primrec.const c)

theorem isComp_succ : ∃ T₀ : Code, ∀ n, evalOpt T₀ n = some (n + 1) :=
  isComp_of_primrec Primrec.succ

theorem isComp_fst : ∃ T₀ : Code, ∀ n, evalOpt T₀ n = some (Nat.unpair n).1 :=
  isComp_of_primrec primrec_u1

theorem isComp_snd : ∃ T₀ : Code, ∀ n, evalOpt T₀ n = some (Nat.unpair n).2 :=
  isComp_of_primrec primrec_u2

theorem isComp_add :
    ∃ T₀ : Code, ∀ n, evalOpt T₀ n = some ((Nat.unpair n).1 + (Nat.unpair n).2) :=
  isComp_of_primrec (Primrec.nat_add.comp primrec_u1 primrec_u2)

open Classical in
theorem isComp_le : ∃ T₀ : Code, ∀ n,
    evalOpt T₀ n = some (if (Nat.unpair n).1 ≤ (Nat.unpair n).2 then 1 else 0) :=
  isComp_of_primrec
    (Primrec.ite (Primrec.nat_le.comp primrec_u1 primrec_u2) (Primrec.const 1) (Primrec.const 0))

open Classical in
theorem isComp_eq : ∃ T₀ : Code, ∀ n,
    evalOpt T₀ n = some (if (Nat.unpair n).1 = (Nat.unpair n).2 then 1 else 0) :=
  isComp_of_primrec
    (Primrec.ite (Primrec.eq.comp primrec_u1 primrec_u2) (Primrec.const 1) (Primrec.const 0))

theorem isComp_comp (f g : Nat → Option Nat) (hf : IsComp f) (hg : IsComp g) :
    IsComp (fun n => (g n).bind f) := by
  rw [isComp_iff] at hf hg ⊢
  exact (Nat.Partrec.comp hf hg).of_eq fun n => (coe_bind (g n) f).symm

theorem isComp_pair (f g : Nat → Option Nat) (hf : IsComp f) (hg : IsComp g) :
    IsComp (fun n => (f n).bind (fun a => (g n).map (Nat.pair a))) := by
  rw [isComp_iff] at hf hg ⊢
  refine (Nat.Partrec.pair hf hg).of_eq fun n => ?_
  cases f n <;> cases g n <;> simp [Seq.seq, Part.coe_none, Part.coe_some]

theorem isComp_cases (p : Nat → Bool) (f g : Nat → Option Nat)
    (hp : IsComp (fun n => some (cond (p n) 1 0))) (hf : IsComp f) (hg : IsComp g) :
    IsComp (fun n => cond (p n) (f n) (g n)) := by
  have hpc : Computable p := computable_bool hp
  rw [isComp_iff] at hf hg ⊢
  refine (Partrec.nat_iff.1 (Partrec.cond hpc (Partrec.nat_iff.2 hf)
    (Partrec.nat_iff.2 hg))).of_eq fun n => ?_
  cases p n <;> rfl

theorem isComp_primrec (g h : Nat → Option Nat) (hg : IsComp g) (hh : IsComp h)
    (r : Nat → Nat → Option Nat) (h0 : ∀ a, r a 0 = g a)
    (hs : ∀ a n, r a (n + 1) = (r a n).bind (fun y => h (Nat.pair a (Nat.pair n y)))) :
    IsComp (fun m => r (Nat.unpair m).1 (Nat.unpair m).2) := by
  rw [isComp_iff] at hg hh ⊢
  refine (Nat.Partrec.prec hg hh).of_eq fun m => ?_
  simp only [Nat.unpaired]
  generalize (Nat.unpair m).1 = a
  generalize (Nat.unpair m).2 = n
  induction n with
  | zero => rw [h0]; rfl
  | succ n ih =>
    rw [hs, coe_bind, ← ih]
    rfl

/-- Membership in an unbounded search over a total `Bool`-valued predicate. -/
theorem mem_rfind_some {q : Nat → Bool} {k : Nat} :
    k ∈ Nat.rfind (fun j => Part.some (q j)) ↔ q k = true ∧ ∀ j < k, q j = false := by
  refine Nat.mem_rfind.trans ?_
  simp only [Part.mem_some_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, fun j hj => (h2 hj).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, fun hj => (h2 _ hj).symm⟩

theorem isComp_mu (p : Nat → Bool) (hp : IsComp (fun n => some (cond (p n) 1 0))) :
    ∃ T₀ : Code, ∀ a k, evalOpt T₀ a = some k ↔
      (p (Nat.pair a k) = true ∧ ∀ k' < k, p (Nat.pair a k') = false) := by
  have hpc : Computable p := computable_bool hp
  have h2 : Computable₂ (fun a k => p (Nat.pair a k)) := hpc.comp₂ Primrec₂.natPair.to_comp
  have h3 : Partrec (fun a => Nat.rfind (fun k => Part.some (p (Nat.pair a k)))) :=
    Partrec.rfind h2.partrec₂
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 h3)
  refine ⟨c, fun a k => ?_⟩
  rw [evalOpt_eq_some_iff, hc]
  exact mem_rfind_some (q := fun j => p (Nat.pair a j))

/-- The characteristic function of `Halt'` on encoded inputs `⟨e T, ⟨n, ⟨k, y⟩⟩⟩`. -/
def haltFn (m : Nat) : Nat :=
  if Code.evaln (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).1 (ofNat Code (Nat.unpair m).1)
      (Nat.unpair (Nat.unpair m).2).1 = some (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).2
  then 1 else 0

theorem primrec_haltFn : Primrec haltFn := by
  have hc : Primrec (fun m : Nat => ofNat Code (Nat.unpair m).1) :=
    (Primrec.ofNat Code).comp primrec_u1
  have hn : Primrec (fun m : Nat => (Nat.unpair (Nat.unpair m).2).1) := primrec_u1.comp primrec_u2
  have hk : Primrec (fun m : Nat => (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).1) :=
    primrec_u1.comp (primrec_u2.comp primrec_u2)
  have hy : Primrec (fun m : Nat => (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).2) :=
    primrec_u2.comp (primrec_u2.comp primrec_u2)
  have he : Primrec (fun m : Nat => Code.evaln (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).1
      (ofNat Code (Nat.unpair m).1) (Nat.unpair (Nat.unpair m).2).1) :=
    Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hc).pair hn)
  exact Primrec.ite (Primrec.eq.comp he (Primrec.option_some.comp hy))
    (Primrec.const 1) (Primrec.const 0)

theorem isComp_halt' : ∃ T₀ : Code, ∀ (T : Code) (n k y : Nat),
    evalOpt T₀ (Nat.pair (encode T) (Nat.pair n (Nat.pair k y))) =
      some (if Code.evaln k T n = some y then 1 else 0) := by
  obtain ⟨T₀, hT₀⟩ := isComp_of_primrec primrec_haltFn
  refine ⟨T₀, fun T n k y => ?_⟩
  rw [hT₀]
  simp only [haltFn, Nat.unpair_pair, ofNat_encode]

theorem isComp_univ : ∃ T₀ : Code, ∀ (T : Code) (n : Nat),
    evalOpt T₀ (Nat.pair (encode T) n) = evalOpt T n := by
  have h : Partrec (fun m : Nat => Code.eval (ofNat Code (Nat.unpair m).1) (Nat.unpair m).2) :=
    Nat.Partrec.Code.eval_part.comp ((Computable.ofNat Code).comp primrec_u1.to_comp)
      primrec_u2.to_comp
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 h)
  refine ⟨u, fun T n => ?_⟩
  simp only [evalOpt, hu, Nat.unpair_pair, ofNat_encode]

theorem isComp_smn (f : Nat → Option Nat) (hf : IsComp f) :
    ∃ s : Nat → Code, (∃ T₀ : Code, ∀ a, evalOpt T₀ a = some (encode (s a))) ∧
      ∀ a b, evalOpt (s a) b = f (Nat.pair a b) := by
  obtain ⟨T, hT⟩ := hf
  refine ⟨fun a => Code.curry T a, isComp_of_primrec ?_, fun a b => ?_⟩
  · exact Primrec.encode.comp (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const T) Primrec.id)
  · rw [evalOpt, Nat.Partrec.Code.eval_curry]
    exact hT _

/-! ### The model -/

/-- **The standard model** of `Stable.TuringModel`: Mathlib's partial recursive codes
`Nat.Partrec.Code`, with `run c n k := evaln k c n`, `eval` the (classical) `Option` version of
`Nat.Partrec.Code.eval`, `code := Encodable.encode` and Cantor-style pairing `Nat.pair`. All the
computability axioms of the interface are discharged from Mathlib's theory of partial recursive
functions (`Nat.Partrec.Code.exists_code`, `primrec_evaln`, `eval_part`, `smn`). -/
noncomputable def mathlibModel : Stable.TuringModel where
  Code := Code
  run c n k := Code.evaln k c n
  run_mono hk h := Code.evaln_mono hk h
  eval := evalOpt
  eval_iff _ _ _ := evalOpt_eq_some_iff.trans Code.evaln_complete
  code := encode
  code_inj h := encode_injective h
  comp_code_mem := isComp_code_mem
  pair := Nat.pair
  unpair := Nat.unpair
  unpair_pair := Nat.unpair_pair
  pair_unpair := Nat.pair_unpair
  pair_lt_left := Nat.pair_lt_pair_left
  pair_lt_right := Nat.pair_lt_pair_right
  comp_const := isComp_const
  comp_succ := isComp_succ
  comp_fst := isComp_fst
  comp_snd := isComp_snd
  comp_add := isComp_add
  comp_le := isComp_le
  comp_eq := isComp_eq
  comp_comp := isComp_comp
  comp_pair := isComp_pair
  comp_cases := isComp_cases
  comp_primrec := isComp_primrec
  comp_mu := isComp_mu
  comp_halt' := isComp_halt'
  comp_univ := isComp_univ
  comp_smn := isComp_smn

end StableModel

#print axioms StableModel.mathlibModel
