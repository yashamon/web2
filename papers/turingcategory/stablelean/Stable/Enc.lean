import Stable.Comp
import Stable.Prim

/-!
# Encoded sets and computable maps (Section 2.1 of the paper)

An *encoded set* `(A, e_A)` is a set with an injective map `e_A : A → ℕ` whose image is a
computable subset of `ℕ` (Definition 2.1).  A partial map `f : A → B` is *computable*
(Definition 2.3) if there is a machine `T` with `e_B ∘ f = T ∘ e_A` as partial maps, i.e.
`eval T (e_A a) = (f a).map e_B` for all `a`.  This file sets up encodings (`Enc`), the
distinguished encodings of `ℕ`, `{±}` (= `Bool`, with `- ↦ 0`, `+ ↦ 1`), `𝒯`, products
(part (1) of Proposition 2.4), lists (part (4)), options, computable subsets and the induced
encoding, and proves the closure properties used in the paper from the interface
`TuringModel`.
-/

namespace Stable

open Classical

/-- An encoding of the type `A` (an object `(A, e_A)` of the category `𝒮`). -/
class Enc (M : TuringModel) (A : Type) where
  /-- The encoding map `e_A`. -/
  e : A → ℕ
  inj : ∀ {a b : A}, e a = e b → a = b
  /-- `e_A (A) ⊂ ℕ` is computable. -/
  img : M.IsCompSet (fun n => ∃ a, e a = n)

namespace Enc

variable {M : TuringModel}

/-- The partial inverse `e_A⁻¹ : ℕ → A` of the encoding (equation (3.12) of the paper). -/
noncomputable def decode (A : Type) [Enc M A] (n : ℕ) : Option A :=
  if h : ∃ a : A, e M a = n then some (choose h) else none

theorem decode_e {A : Type} [Enc M A] (a : A) : decode (M := M) A (e M a) = some a := by
  unfold decode
  have h : ∃ a' : A, e M a' = e M a := ⟨a, rfl⟩
  rw [dite_eq_left h]
  exact congrArg some (inj (choose_spec h))

theorem decode_eq_some_iff {A : Type} [Enc M A] {n : ℕ} {a : A} :
    decode (M := M) A n = some a ↔ e M a = n := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i h'
      have := choose_spec h'
      cases h; exact this
    · cases h
  · rintro rfl; exact decode_e a

theorem decode_eq_none_iff {A : Type} [Enc M A] {n : ℕ} :
    decode (M := M) A n = none ↔ ∀ a : A, e M a ≠ n := by
  unfold decode
  constructor
  · intro h a ha
    rw [dite_eq_left ⟨a, ha⟩] at h; cases h
  · intro h
    rw [dite_eq_right]; rintro ⟨a, ha⟩; exact h a ha

/-- `(decode n).map e` is `some n` on the image and `none` off it. -/
theorem map_e_decode {A : Type} [Enc M A] (n : ℕ) :
    (decode (M := M) A n).map (e M) = if ∃ a : A, e M a = n then some n else none := by
  by_cases h : ∃ a : A, e M a = n
  · obtain ⟨a, rfl⟩ := h
    rw [decode_e, ite_eq_left ⟨a, rfl⟩]; rfl
  · rw [decode_eq_none_iff.2 (fun a ha => h ⟨a, ha⟩), ite_eq_right h]; rfl

end Enc

export Enc (e)

/-! ## Computable maps between encoded sets -/

variable {M : TuringModel}

/-- `f : A → B` (a partial map) is computable, Definition 2.3: some `T` satisfies
`e_B ∘ f = T ∘ e_A`. -/
def Comp (M : TuringModel) {A B : Type} [Enc M A] [Enc M B] (f : A → Option B) : Prop :=
  ∃ T : M.Code, ∀ a, M.eval T (e M a) = (f a).map (e M)

/-- `T` computes `f` (the commutative diagram of Definition 2.3). -/
def Computes (M : TuringModel) {A B : Type} [Enc M A] [Enc M B] (T : M.Code) (f : A → Option B) :
    Prop := ∀ a, M.eval T (e M a) = (f a).map (e M)

/-- A total map `f : A → B` is computable. -/
def CompT (M : TuringModel) {A B : Type} [Enc M A] [Enc M B] (f : A → B) : Prop :=
  Comp M (fun a => some (f a))

/-- A subset `P ⊂ A` is computable: `e_A (P) ⊂ ℕ` is a computable subset of `ℕ`. -/
def CompSet (M : TuringModel) {A : Type} [Enc M A] (P : A → Prop) : Prop :=
  M.IsCompSet (fun n => ∃ a, e M a = n ∧ P a)

/-! ## The distinguished encodings -/

/-- `ℕ` with the identity encoding. -/
instance encNat : Enc M ℕ where
  e := fun n => n
  inj := fun h => h
  img := TuringModel.isCompSet_true.congr fun n => ⟨fun _ => ⟨n, rfl⟩, fun _ => trivial⟩

/-- `{±}` as `Bool`, with `e(-) = e(false) = 0` and `e(+) = e(true) = 1`. -/
instance encBool : Enc M Bool where
  e := fun b => cond b 1 0
  inj := by intro a b h; cases a <;> cases b <;> first | rfl | (simp at h)
  img := by
    have h1 := TuringModel.isCompSet_le_of (M := M) TuringModel.isCompT_id (TuringModel.isCompT_const 1)
    refine h1.congr fun n => ?_
    constructor
    · intro h
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h0
      · exact ⟨false, h0.symm⟩
      · exact ⟨true, h0.symm⟩
    · rintro ⟨b, rfl⟩; cases b <;> simp

/-- The one-point set, encoded by `0`. -/
instance encUnit : Enc M Unit where
  e := fun _ => 0
  inj := fun _ => rfl
  img := (TuringModel.isCompSet_eq_of TuringModel.isCompT_id (TuringModel.isCompT_const 0)).congr
    fun _ => ⟨fun h => ⟨(), h.symm⟩, fun ⟨_, h⟩ => h.symm⟩

/-- `𝒯` with its distinguished encoding `e_𝒯 = code`. -/
instance encCode : Enc M M.Code where
  e := M.code
  inj := M.code_inj
  img := TuringModel.isCompSet_code_mem

/-- The product encoding `e_{A × B} (a, b) = ⟨e_A a, e_B b⟩` (Proposition 2.4 (1)). -/
instance encProd {A B : Type} [Enc M A] [Enc M B] : Enc M (A × B) where
  e := fun p => M.pair (e M p.1) (e M p.2)
  inj := by
    intro p q h
    have h' := congrArg M.unpair h
    rw [M.unpair_pair, M.unpair_pair] at h'
    have h1 : e M p.1 = e M q.1 := congrArg Prod.fst h'
    have h2 : e M p.2 = e M q.2 := congrArg Prod.snd h'
    exact Prod.ext (Enc.inj h1) (Enc.inj h2)
  img := by
    have h := TuringModel.IsCompSet.and (M := M)
      ((Enc.img (M := M) (A := A)).comp TuringModel.isCompT_fst)
      ((Enc.img (M := M) (A := B)).comp TuringModel.isCompT_snd)
    refine h.congr fun n => ?_
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨(a, b), ?_⟩
      show M.pair (e M a) (e M b) = n
      rw [ha, hb, M.pair_unpair]
    · rintro ⟨⟨a, b⟩, rfl⟩
      show (∃ a', e M a' = (M.unpair (M.pair (e M a) (e M b))).1) ∧
        ∃ b', e M b' = (M.unpair (M.pair (e M a) (e M b))).2
      rw [M.unpair_pair]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩

/-- `Option A`, with `none ↦ 0` and `some a ↦ e_A a + 1`; used for partial values returned
by total maps (bounded searches). -/
instance encOption {A : Type} [Enc M A] : Enc M (Option A) where
  e := fun o => match o with | none => 0 | some a => e M a + 1
  inj := by
    intro o o' h
    cases o <;> cases o' <;> simp at h
    · rfl
    · rw [Enc.inj h]
  img := by
    -- `n` is a code iff `n = 0` or `n - 1 ∈ e_A (A)`
    have h := (TuringModel.isCompSet_eq_of (M := M) TuringModel.isCompT_id
      (TuringModel.isCompT_const 0)).or
      ((TuringModel.isCompSet_le_of (M := M) (TuringModel.isCompT_const 1)
        TuringModel.isCompT_id).and ((Enc.img (M := M) (A := A)).comp TuringModel.isCompT_pred))
    refine h.congr fun n => ?_
    constructor
    · rintro (h0 | ⟨h1, a, ha⟩)
      · exact ⟨none, h0.symm⟩
      · exact ⟨some a, by show e M a + 1 = n; omega⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inl rfl
      | some a =>
        exact Or.inr ⟨by show 1 ≤ e M a + 1; omega, a, by show e M a = e M a + 1 - 1; omega⟩

/-- The code of a list of numbers: `⟨length, ⟨x₀, ⟨x₁, … ⟨x_{n-1}, 0⟩⟩⟩⟩`. -/
def listCode (M : TuringModel) (l : List ℕ) : ℕ :=
  M.pair l.length (l.foldr (fun x acc => M.pair x acc) 0)

private theorem listCode_inj {A : Type} [Enc M A] :
    ∀ {l l' : List A}, listCode M (l.map (e M)) = listCode M (l'.map (e M)) → l = l' := by
  intro l l' h
  unfold listCode at h
  obtain ⟨hlen, hfold⟩ := TuringModel.pair_inj h
  rw [List.length_map, List.length_map] at hlen
  clear h
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases l' with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.map_cons, List.foldr_cons] at hfold
      obtain ⟨hxy, hrest⟩ := TuringModel.pair_inj hfold
      rw [Enc.inj hxy, ih (l' := ys) (by simpa using hlen) hrest]

/-- Iterated tails of the code `foldr pair 0 xs` (with `tl x = (unpair x).2`). -/
private theorem repeat_tl_foldr (xs : List ℕ) : ∀ j, j ≤ xs.length →
    Nat.repeat (fun x => (M.unpair x).2) j (xs.foldr (fun x acc => M.pair x acc) 0) =
      (xs.drop j).foldr (fun x acc => M.pair x acc) 0 := by
  induction xs with
  | nil => intro j hj; obtain rfl := Nat.le_zero.1 hj; rfl
  | cons x xs ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      simp only [repeat_succ_right, List.foldr_cons, M.unpair_pair, List.drop_succ_cons]
      exact ih j (by simpa using hj)

private theorem hd_repeat_tl_foldr (xs : List ℕ) (j : ℕ) (hj : j < xs.length) :
    (M.unpair (Nat.repeat (fun x => (M.unpair x).2) j
      (xs.foldr (fun x acc => M.pair x acc) 0))).1 = xs[j] := by
  rw [repeat_tl_foldr xs j (Nat.le_of_lt hj), List.drop_eq_getElem_cons hj]
  simp only [List.foldr_cons, M.unpair_pair]

private theorem exists_list_of {A : Type} [Enc M A] : ∀ (L c : ℕ),
    Nat.repeat (fun x => (M.unpair x).2) L c = 0 →
    (∀ j, j < L → ∃ a : A, e M a = (M.unpair (Nat.repeat (fun x => (M.unpair x).2) j c)).1) →
    ∃ l : List A, l.length = L ∧ (l.map (e M)).foldr (fun x acc => M.pair x acc) 0 = c := by
  intro L
  induction L with
  | zero => intro c h0 _; exact ⟨[], rfl, h0.symm⟩
  | succ L ih =>
    intro c h0 hall
    rw [repeat_succ_right] at h0
    obtain ⟨l', hl', hc'⟩ := ih (M.unpair c).2 h0 (fun j hj => by
      have := hall (j + 1) (Nat.succ_lt_succ hj)
      rw [repeat_succ_right] at this
      exact this)
    obtain ⟨a, ha⟩ := hall 0 (Nat.zero_lt_succ L)
    refine ⟨a :: l', by simp [hl'], ?_⟩
    simp only [List.map_cons, List.foldr_cons, hc']
    rw [ha]
    exact M.pair_unpair c

/-- `n = ⟨L, c⟩` is the code of a list iff `tl^[L] c = 0` and the first `L` heads are codes. -/
private theorem listCode_img {A : Type} [Enc M A] (n : ℕ) :
    (∃ l : List A, listCode M (l.map (e M)) = n) ↔
      (Nat.repeat (fun x => (M.unpair x).2) (M.unpair n).1 (M.unpair n).2 = 0 ∧
        ∀ j, j < (M.unpair n).1 → ∃ a : A,
          e M a = (M.unpair (Nat.repeat (fun x => (M.unpair x).2) j (M.unpair n).2)).1) := by
  constructor
  · rintro ⟨l, rfl⟩
    unfold listCode
    rw [M.unpair_pair]
    simp only [List.length_map]
    constructor
    · rw [repeat_tl_foldr _ _ (by simp), List.drop_of_length_le (by simp)]
      rfl
    · intro j hj
      refine ⟨l[j], ?_⟩
      rw [hd_repeat_tl_foldr _ j (by simpa using hj), List.getElem_map]
  · rintro ⟨h0, hall⟩
    obtain ⟨l, hl, hc⟩ := exists_list_of _ _ h0 hall
    refine ⟨l, ?_⟩
    unfold listCode
    rw [List.length_map, hl, hc, M.pair_unpair]

/-- The list encoding `e_{L(A)}` (Proposition 2.4 (4)). -/
instance encList {A : Type} [Enc M A] : Enc M (List A) where
  e := fun l => listCode M (l.map (e M))
  inj := by
    intro l l' h
    exact listCode_inj h
  img := by
    have hrep : ∀ {K X : ℕ → ℕ}, M.IsCompT K → M.IsCompT X →
        M.IsCompT (fun n => Nat.repeat (fun x => (M.unpair x).2) (K n) (X n)) :=
      fun hK hX => TuringModel.isCompT_repeat TuringModel.isCompT_snd hK hX
    have h1 := TuringModel.isCompSet_eq_of (M := M)
      (hrep TuringModel.isCompT_fst TuringModel.isCompT_snd) (TuringModel.isCompT_const 0)
    have h2 := TuringModel.isCompSet_ballLt_of (M := M)
      (P := fun n j => ∃ a : A,
        e M a = (M.unpair (Nat.repeat (fun x => (M.unpair x).2) j (M.unpair n).2)).1)
      ((Enc.img (M := M) (A := A)).comp (TuringModel.isCompT_fst.comp
        (hrep TuringModel.isCompT_snd (TuringModel.isCompT_snd.comp TuringModel.isCompT_fst))))
      TuringModel.isCompT_id TuringModel.isCompT_fst
    exact (h1.and h2).congr fun n => (listCode_img n).symm

/-- Encoded sets whose image is infinite ("infinite" objects of `𝒮`). -/
def Enc.Infinite (M : TuringModel) (A : Type) [Enc M A] : Prop := ∀ n : ℕ, ∃ a : A, n < e M a

/-- The induced encoding on a computable subset `P ⊂ A`. -/
@[instance_reducible]
noncomputable def Enc.restrict {A : Type} [Enc M A] (P : A → Prop) (hP : CompSet M P) :
    Enc M {a // P a} where
  e := fun a => e M a.1
  inj := fun h => Subtype.ext (Enc.inj h)
  img := hP.congr fun n => by
    constructor
    · rintro ⟨a, rfl, ha⟩; exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩; exact ⟨a, rfl, ha⟩

/-! ## Closure properties of computable maps -/

section Closure

variable {A B C D : Type} [Enc M A] [Enc M B] [Enc M C] [Enc M D]

/-! Private helpers: unfolding the distinguished encodings, and transport from `ℕ`. -/

private theorem e_nat' (n : ℕ) : e M n = n := rfl
private theorem e_bool' (b : Bool) : e M b = cond b 1 0 := rfl
private theorem e_prod' (p : A × B) : e M p = M.pair (e M p.1) (e M p.2) := rfl
private theorem e_none' : e M (none : Option A) = 0 := rfl
private theorem e_some' (a : A) : e M (some a) = e M a + 1 := rfl
private theorem e_list' (l : List A) : e M l = listCode M (l.map (e M)) := rfl

private theorem exists_e_eq_and_iff {P : A → Prop} {a : A} :
    (∃ a', e M a' = e M a ∧ P a') ↔ P a :=
  ⟨fun ⟨_, ha', hp⟩ => (Enc.inj ha') ▸ hp, fun hp => ⟨a, rfl, hp⟩⟩

private theorem comp_of_isComp_e {f : A → Option B} {F : ℕ → Option ℕ} (hF : M.IsComp F)
    (h : ∀ a, (f a).map (e M) = F (e M a)) : Comp M f := by
  obtain ⟨T, hT⟩ := hF
  exact ⟨T, fun a => (hT (e M a)).trans (h a).symm⟩

private theorem compT_of_isCompT_e {f : A → B} {F : ℕ → ℕ} (hF : M.IsCompT F)
    (h : ∀ a, e M (f a) = F (e M a)) : CompT M f := by
  obtain ⟨T, hT⟩ := hF
  refine ⟨T, fun a => ?_⟩
  rw [hT, Option.map_some, h]

private theorem compSet_of_isCompSet_e {P : A → Prop} {R : ℕ → Prop} (hR : M.IsCompSet R)
    (h : ∀ a, P a ↔ R (e M a)) : CompSet M P :=
  TuringModel.IsCompSet.congr ((Enc.img (M := M) (A := A)).and hR) fun n => by
    constructor
    · rintro ⟨⟨a, rfl⟩, hr⟩; exact ⟨a, rfl, (h a).2 hr⟩
    · rintro ⟨a, rfl, hp⟩; exact ⟨⟨a, rfl⟩, (h a).1 hp⟩

/-- A characteristic function that is correct on the image of `e_A` gives a computable set
(patched with `0` off the image). -/
private theorem compSet_of_eval {P : A → Prop} {T : M.Code}
    (hT : ∀ a, M.eval T (e M a) = some (if P a then 1 else 0)) : CompSet M P := by
  have h := TuringModel.IsComp.cases (Enc.img (M := M) (A := A)).toB
    (TuringModel.isComp_eval T) (TuringModel.isComp_const 0)
  refine TuringModel.IsComp.congr h fun n => ?_
  dsimp only
  by_cases hn : ∃ a : A, e M a = n
  · obtain ⟨a, rfl⟩ := hn
    rw [decide_eq_true (⟨a, rfl⟩ : ∃ a' : A, e M a' = e M a), Bool.cond_true, hT a]
    by_cases hp : P a
    · rw [ite_eq_left hp, ite_eq_left ((exists_e_eq_and_iff (P := P) (a := a)).2 hp)]
    · rw [ite_eq_right hp, ite_eq_right (fun h' => hp ((exists_e_eq_and_iff (P := P) (a := a)).1 h'))]
  · rw [decide_eq_false hn, Bool.cond_false, ite_eq_right (fun ⟨a, ha, _⟩ => hn ⟨a, ha⟩)]

theorem Comp.congr {f g : A → Option B} (hf : Comp M f) (h : ∀ a, f a = g a) : Comp M g := by
  obtain ⟨T, hT⟩ := hf; exact ⟨T, fun a => (hT a).trans (congrArg _ (h a))⟩

theorem CompT.congr {f g : A → B} (hf : CompT M f) (h : ∀ a, f a = g a) : CompT M g :=
  Comp.congr hf fun a => congrArg some (h a)

theorem CompSet.congr {P Q : A → Prop} (hP : CompSet M P) (h : ∀ a, P a ↔ Q a) : CompSet M Q :=
  TuringModel.IsCompSet.congr hP fun n => by
    constructor
    · rintro ⟨a, rfl, ha⟩; exact ⟨a, rfl, (h a).1 ha⟩
    · rintro ⟨a, rfl, ha⟩; exact ⟨a, rfl, (h a).2 ha⟩

theorem Comp.of_computes {T : M.Code} {f : A → Option B} (h : Computes M T f) : Comp M f := ⟨T, h⟩

theorem CompT.toComp {f : A → B} (hf : CompT M f) : Comp M (fun a => some (f a)) := hf

/-- Transport to `ℕ`: `f` is computable iff `e_B ∘ f ∘ e_A⁻¹ : ℕ → ℕ` is computable
(the explicit description after Definition 2.3). -/
theorem comp_iff_isComp (f : A → Option B) :
    Comp M f ↔ M.IsComp (fun n => (Enc.decode (M := M) A n).bind (fun a => (f a).map (e M))) := by
  constructor
  · rintro ⟨T, hT⟩
    have h := TuringModel.IsComp.cases (Enc.img (M := M) (A := A)).toB
      (TuringModel.isComp_eval T) TuringModel.isComp_none
    refine h.congr fun n => ?_
    by_cases hn : ∃ a : A, e M a = n
    · obtain ⟨a, rfl⟩ := hn
      rw [decide_eq_true (⟨a, rfl⟩ : ∃ a' : A, e M a' = e M a), Bool.cond_true, hT a,
        Enc.decode_e, Option.bind_some]
    · rw [decide_eq_false hn, Bool.cond_false,
        Enc.decode_eq_none_iff.2 (fun a ha => hn ⟨a, ha⟩), Option.bind_none]
  · rintro ⟨T, hT⟩
    refine ⟨T, fun a => ?_⟩
    simp only [hT, Enc.decode_e, Option.bind_some]

/-- Composition of computable partial maps. -/
theorem Comp.comp {f : B → Option C} {g : A → Option B} (hf : Comp M f) (hg : Comp M g) :
    Comp M (fun a => (g a).bind f) := by
  obtain ⟨Tf, hTf⟩ := hf
  obtain ⟨Tg, hTg⟩ := hg
  refine comp_of_isComp_e ((TuringModel.isComp_eval Tf).comp (TuringModel.isComp_eval Tg))
    fun a => ?_
  rw [hTg]
  cases g a with
  | none => rfl
  | some b => exact (hTf b).symm

theorem CompT.comp {f : B → C} {g : A → B} (hf : CompT M f) (hg : CompT M g) :
    CompT M (fun a => f (g a)) := by
  have := Comp.comp (M := M) hf hg
  exact this.congr fun a => by simp [Option.bind]

theorem Comp.compT {f : B → Option C} {g : A → B} (hf : Comp M f) (hg : CompT M g) :
    Comp M (fun a => f (g a)) := by
  have := Comp.comp (M := M) hf hg
  exact this.congr fun a => by simp [Option.bind]

theorem CompT.comp' {f : B → C} {g : A → Option B} (hf : CompT M f) (hg : Comp M g) :
    Comp M (fun a => (g a).map f) := by
  have := Comp.comp (M := M) hf hg
  exact this.congr fun a => by cases g a <;> simp [Option.bind, Option.map]

theorem compT_id : CompT M (fun a : A => a) :=
  compT_of_isCompT_e TuringModel.isCompT_id fun _ => rfl

theorem compT_const (b : B) : CompT M (fun _ : A => b) :=
  compT_of_isCompT_e (TuringModel.isCompT_const (e M b)) fun _ => rfl

/-- The encoding map itself is computable, `A → ℕ`. -/
theorem compT_e : CompT M (fun a : A => e M a) :=
  compT_of_isCompT_e TuringModel.isCompT_id fun _ => rfl

/-- Lemma 3.11 (`lemma_inverse`): `e_A⁻¹ : ℕ → A` is computable. -/
theorem comp_decode : Comp M (fun n : ℕ => Enc.decode (M := M) A n) := by
  have h := TuringModel.IsComp.cases (Enc.img (M := M) (A := A)).toB
    (TuringModel.isCompT_id (M := M)) TuringModel.isComp_none
  refine comp_of_isComp_e h fun n => ?_
  rw [Enc.map_e_decode, e_nat']
  by_cases hn : ∃ a : A, e M a = n <;> simp [hn]

/-- The nowhere defined map is computable. -/
theorem comp_none : Comp M (fun _ : A => (none : Option B)) :=
  comp_of_isComp_e TuringModel.isComp_none fun _ => rfl

/-- Definition by cases (Proposition 2.4 (6a)). -/
theorem Comp.cases {P : A → Prop} {f g : A → Option B} (hP : CompSet M P) (hf : Comp M f)
    (hg : Comp M g) : Comp M (fun a => if P a then f a else g a) := by
  obtain ⟨Tf, hTf⟩ := hf
  obtain ⟨Tg, hTg⟩ := hg
  have h := TuringModel.IsComp.cases (TuringModel.IsCompSet.toB hP)
    (TuringModel.isComp_eval Tf) (TuringModel.isComp_eval Tg)
  refine comp_of_isComp_e h fun a => ?_
  by_cases hpa : P a
  · rw [ite_eq_left hpa, decide_eq_true ((exists_e_eq_and_iff (P := P) (a := a)).2 hpa),
      Bool.cond_true, hTf]
  · rw [ite_eq_right hpa, decide_eq_false (fun h' => hpa ((exists_e_eq_and_iff (P := P) (a := a)).1 h')),
      Bool.cond_false, hTg]

theorem CompT.cases {P : A → Prop} {f g : A → B} (hP : CompSet M P) (hf : CompT M f)
    (hg : CompT M g) : CompT M (fun a => if P a then f a else g a) := by
  have := Comp.cases (M := M) hP hf hg
  exact this.congr fun a => by by_cases h : P a <;> simp [h]

/-- Restricting a partial map to a computable subset (undefined outside it). -/
theorem Comp.restrictTo {P : A → Prop} {f : A → Option B} (hP : CompSet M P) (hf : Comp M f) :
    Comp M (fun a => if P a then f a else none) :=
  Comp.cases hP hf comp_none

/-! ### Products -/

theorem compT_fst : CompT M (fun p : A × B => p.1) :=
  compT_of_isCompT_e TuringModel.isCompT_fst fun p => by simp only [e_prod', M.unpair_pair]

theorem compT_snd : CompT M (fun p : A × B => p.2) :=
  compT_of_isCompT_e TuringModel.isCompT_snd fun p => by simp only [e_prod', M.unpair_pair]

/-- Proposition 2.4 (1b): pairing of partial maps. -/
theorem Comp.pair {f : A → Option B} {g : A → Option C} (hf : Comp M f) (hg : Comp M g) :
    Comp M (fun a => (f a).bind (fun b => (g a).map (fun c => (b, c)))) := by
  obtain ⟨Tf, hTf⟩ := hf
  obtain ⟨Tg, hTg⟩ := hg
  refine comp_of_isComp_e ((TuringModel.isComp_eval Tf).pair (TuringModel.isComp_eval Tg))
    fun a => ?_
  rw [hTf, hTg]
  cases f a <;> cases g a <;> rfl

theorem CompT.pair {f : A → B} {g : A → C} (hf : CompT M f) (hg : CompT M g) :
    CompT M (fun a => (f a, g a)) := by
  have := Comp.pair (M := M) hf hg
  exact this.congr fun a => by simp [Option.bind, Option.map]

/-- Proposition 2.4 (1c): `f × g`. -/
theorem Comp.prodMap {f : A → Option B} {g : C → Option D} (hf : Comp M f) (hg : Comp M g) :
    Comp M (fun p : A × C => (f p.1).bind (fun b => (g p.2).map (fun d => (b, d)))) :=
  Comp.pair (hf.compT compT_fst) (hg.compT compT_snd)

theorem CompT.prodMap {f : A → B} {g : C → D} (hf : CompT M f) (hg : CompT M g) :
    CompT M (fun p : A × C => (f p.1, g p.2)) :=
  CompT.pair (hf.comp compT_fst) (hg.comp compT_snd)

theorem compT_swap : CompT M (fun p : A × B => (p.2, p.1)) := CompT.pair compT_snd compT_fst

theorem compT_assoc : CompT M (fun p : (A × B) × C => (p.1.1, (p.1.2, p.2))) :=
  CompT.pair (compT_fst.comp compT_fst) (CompT.pair (compT_snd.comp compT_fst) compT_snd)

theorem compT_unassoc : CompT M (fun p : A × (B × C) => ((p.1, p.2.1), p.2.2)) :=
  CompT.pair (CompT.pair compT_fst (compT_fst.comp compT_snd)) (compT_snd.comp compT_snd)

/-! ### Computable subsets -/

theorem compSet_iff_compT_decide (P : A → Prop) :
    CompSet M P ↔ CompT M (fun a => decide (P a)) := by
  constructor
  · intro hP
    refine compT_of_isCompT_e (F := fun n => if ∃ a, e M a = n ∧ P a then 1 else 0) hP
      fun a => ?_
    rw [e_bool']
    by_cases h : P a
    · rw [ite_eq_left ((exists_e_eq_and_iff (P := P) (a := a)).2 h)]; simp [h]
    · rw [ite_eq_right (fun h' => h ((exists_e_eq_and_iff (P := P) (a := a)).1 h'))]; simp [h]
  · rintro ⟨T, hT⟩
    refine compSet_of_eval (T := T) fun a => ?_
    rw [hT a, Option.map_some, e_bool']
    by_cases h : P a <;> simp [h]

theorem CompSet.toCompT {P : A → Prop} (h : CompSet M P) : CompT M (fun a => decide (P a)) :=
  (compSet_iff_compT_decide P).1 h

theorem CompT.toCompSet {p : A → Bool} (h : CompT M p) : CompSet M (fun a => p a = true) := by
  rw [compSet_iff_compT_decide]
  exact h.congr fun a => by cases p a <;> simp

theorem CompSet.and {P Q : A → Prop} (hP : CompSet M P) (hQ : CompSet M Q) :
    CompSet M (fun a => P a ∧ Q a) := by
  refine TuringModel.IsCompSet.congr (TuringModel.IsCompSet.and hP hQ) fun n => ?_
  constructor
  · rintro ⟨⟨a, rfl, hp⟩, ⟨b, hb, hq⟩⟩
    exact ⟨a, rfl, hp, (Enc.inj hb) ▸ hq⟩
  · rintro ⟨a, rfl, hp, hq⟩
    exact ⟨⟨a, rfl, hp⟩, ⟨a, rfl, hq⟩⟩

theorem CompSet.or {P Q : A → Prop} (hP : CompSet M P) (hQ : CompSet M Q) :
    CompSet M (fun a => P a ∨ Q a) := by
  refine TuringModel.IsCompSet.congr (TuringModel.IsCompSet.or hP hQ) fun n => ?_
  constructor
  · rintro (⟨a, rfl, hp⟩ | ⟨a, rfl, hq⟩)
    · exact ⟨a, rfl, Or.inl hp⟩
    · exact ⟨a, rfl, Or.inr hq⟩
  · rintro ⟨a, rfl, hp | hq⟩
    · exact Or.inl ⟨a, rfl, hp⟩
    · exact Or.inr ⟨a, rfl, hq⟩

theorem CompSet.not {P : A → Prop} (hP : CompSet M P) : CompSet M (fun a => ¬ P a) := by
  refine TuringModel.IsCompSet.congr
    ((Enc.img (M := M) (A := A)).and (TuringModel.IsCompSet.not hP)) fun n => ?_
  constructor
  · rintro ⟨⟨a, rfl⟩, hn⟩
    exact ⟨a, rfl, fun hp => hn ⟨a, rfl, hp⟩⟩
  · rintro ⟨a, rfl, hp⟩
    exact ⟨⟨a, rfl⟩, fun ⟨b, hb, hq⟩ => hp ((Enc.inj hb) ▸ hq)⟩

theorem CompSet.imp {P Q : A → Prop} (hP : CompSet M P) (hQ : CompSet M Q) :
    CompSet M (fun a => P a → Q a) :=
  (hP.not.or hQ).congr fun a => by
    constructor
    · rintro (h | h) hp
      · exact absurd hp h
      · exact h
    · intro h; by_cases hp : P a
      · exact Or.inr (h hp)
      · exact Or.inl hp

theorem compSet_true : CompSet M (fun _ : A => True) :=
  compSet_of_isCompSet_e TuringModel.isCompSet_true fun _ => Iff.rfl

theorem compSet_false : CompSet M (fun _ : A => False) :=
  compSet_of_isCompSet_e TuringModel.isCompSet_false fun _ => Iff.rfl

/-- Preimage of a computable set under a total computable map. -/
theorem CompSet.comp {P : B → Prop} {g : A → B} (hP : CompSet M P) (hg : CompT M g) :
    CompSet M (fun a => P (g a)) :=
  (compSet_iff_compT_decide _).2 (CompT.comp hP.toCompT hg)

/-- Preimage of a computable subset of `ℕ` under a total computable map `A → ℕ`. -/
private theorem compSet_of_isCompSet {F : A → ℕ} {Q : ℕ → Prop} (hF : CompT M F)
    (hQ : M.IsCompSet Q) : CompSet M (fun a => Q (F a)) :=
  CompSet.comp (compSet_of_isCompSet_e (A := ℕ) (P := Q) hQ fun _ => Iff.rfl) hF

private theorem CompT.npair {f g : A → ℕ} (hf : CompT M f) (hg : CompT M g) :
    CompT M (fun a => M.pair (f a) (g a)) :=
  CompT.comp (compT_e (A := ℕ × ℕ)) (CompT.pair hf hg)

/-- Equality of two total computable maps is decidable. -/
theorem compSet_eq {f g : A → B} (hf : CompT M f) (hg : CompT M g) :
    CompSet M (fun a => f a = g a) :=
  (compSet_of_isCompSet (CompT.npair (compT_e.comp hf) (compT_e.comp hg))
    TuringModel.isCompSet_eq).congr fun a => by
      simp only [M.unpair_pair]
      exact ⟨Enc.inj, congrArg (e M)⟩

theorem compSet_le {f g : A → ℕ} (hf : CompT M f) (hg : CompT M g) :
    CompSet M (fun a => f a ≤ g a) :=
  (compSet_of_isCompSet (CompT.npair hf hg) TuringModel.isCompSet_le).congr fun a => by
    simp only [M.unpair_pair]

theorem compT_succ : CompT M (fun n : ℕ => n + 1) :=
  compT_of_isCompT_e TuringModel.isCompT_succ fun _ => rfl

theorem compSet_lt {f g : A → ℕ} (hf : CompT M f) (hg : CompT M g) :
    CompSet M (fun a => f a < g a) :=
  (compSet_le (compT_succ.comp hf) hg).congr fun a => by simp [Nat.lt_iff_add_one_le]

/-- The domain of a computable *total-on-a-computable-set* map: `f a` is defined iff `P a`,
provided `P` is computable; used to turn `Option`-valued total maps into partial maps. -/
theorem Comp.ofOption {f : A → Option B} (hf : CompT M f) : Comp M f := by
  obtain ⟨T, hT⟩ := hf
  -- decoding `Option`: `0 ↦ undefined`, `m + 1 ↦ m`
  have hD := TuringModel.IsComp.cases
    (TuringModel.isCompSet_eq_of (M := M) TuringModel.isCompT_id (TuringModel.isCompT_const 0)).toB
    TuringModel.isComp_none TuringModel.isCompT_pred
  refine comp_of_isComp_e (hD.comp (TuringModel.isComp_eval T)) fun a => ?_
  rw [hT a, Option.map_some]
  cases f a <;> simp [e_some', e_none']

/-- Conversely a computable partial map with computable domain gives a total `Option`-valued
computable map. -/
theorem CompT.ofComp {f : A → Option B} (hf : Comp M f) (hdom : CompSet M (fun a => f a ≠ none)) :
    CompT M f := by
  have hsome : CompT M (fun b : B => (some b : Option B)) :=
    compT_of_isCompT_e TuringModel.isCompT_succ fun _ => rfl
  have h := Comp.cases hdom (CompT.comp' hsome hf) (compT_const (A := A) (none : Option B))
  refine h.congr fun a => ?_
  cases f a <;> simp

theorem compT_some : CompT M (fun b : B => (some b : Option B)) :=
  compT_of_isCompT_e TuringModel.isCompT_succ fun _ => rfl

theorem comp_optionId : Comp M (fun o : Option B => o) := Comp.ofOption compT_id

/-- The ℕ-level version `(a, t) ↦ (⟨a, t⟩ ∈ e_{A×ℕ}(P))` of a predicate `P` on `A × ℕ`. -/
private def codeSet2 (P : A → ℕ → Prop) (a t : ℕ) : Prop :=
  ∃ p : A × ℕ, e M p = M.pair a t ∧ P p.1 p.2

private theorem codeSet2_e {P : A → ℕ → Prop} (x : A) (t : ℕ) :
    codeSet2 (M := M) P (e M x) t ↔ P x t :=
  exists_e_eq_and_iff (a := (x, t)) (P := fun p : A × ℕ => P p.1 p.2)

private theorem isCompSet_codeSet2 {P : A → ℕ → Prop}
    (hP : CompSet M (fun p : A × ℕ => P p.1 p.2)) :
    M.IsCompSet (fun m => codeSet2 (M := M) P (M.unpair m).1 (M.unpair m).2) :=
  TuringModel.IsCompSet.congr hP fun m => by
    unfold codeSet2; rw [M.pair_unpair]

/-- The bounded universal quantifier `∀ j < t, P a j` (over the second coordinate). -/
theorem CompSet.ballLt {P : A → ℕ → Prop} (hP : CompSet M (fun p : A × ℕ => P p.1 p.2)) :
    CompSet M (fun p : A × ℕ => ∀ j, j < p.2 → P p.1 j) := by
  refine compSet_of_isCompSet_e (TuringModel.isCompSet_ballLt (isCompSet_codeSet2 hP))
    fun p => ?_
  simp only [e_prod', e_nat', M.unpair_pair]
  exact forall_congr' fun j => imp_congr_right fun _ => (codeSet2_e p.1 j).symm

theorem CompSet.ballLe {P : A → ℕ → Prop} (hP : CompSet M (fun p : A × ℕ => P p.1 p.2)) :
    CompSet M (fun p : A × ℕ => ∀ j, j ≤ p.2 → P p.1 j) := by
  have h := CompSet.ballLt (M := M) hP
  have h' : CompSet M (fun p : A × ℕ => ∀ j, j < p.2 + 1 → P p.1 j) :=
    h.comp (CompT.pair compT_fst (compT_succ.comp compT_snd))
  exact h'.congr fun p => by
    constructor
    · intro hh j hj; exact hh j (Nat.lt_succ_of_le hj)
    · intro hh j hj; exact hh j (Nat.le_of_lt_succ hj)

theorem CompSet.bexLt {P : A → ℕ → Prop} (hP : CompSet M (fun p : A × ℕ => P p.1 p.2)) :
    CompSet M (fun p : A × ℕ => ∃ j, j < p.2 ∧ P p.1 j) := by
  have h := (CompSet.ballLt (M := M) (P := fun a j => ¬ P a j) hP.not).not
  exact h.congr fun p => by
    constructor
    · intro hh
      refine Classical.byContradiction fun hc => ?_
      exact hh fun j hj hp => hc ⟨j, hj, hp⟩
    · rintro ⟨j, hj, hp⟩ hh; exact hh j hj hp

/-! ### Bounded and unbounded search -/

/-- The least `u ≤ t` with `P a u`, if any. -/
noncomputable def bmin (P : A → ℕ → Prop) (a : A) : ℕ → Option ℕ
  | 0 => if P a 0 then some 0 else none
  | t + 1 => match bmin P a t with
    | some u => some u
    | none => if P a (t + 1) then some (t + 1) else none

private theorem bmin_none_imp {P : A → ℕ → Prop} {a : A} {t : ℕ} (h : bmin P a t = none) :
    ∀ u, u ≤ t → ¬ P a u := by
  induction t with
  | zero =>
    intro u hu hp
    obtain rfl := Nat.le_zero.1 hu
    simp [bmin, hp] at h
  | succ t ih =>
    intro u hu hp
    cases hb : bmin P a t with
    | some v => simp [bmin, hb] at h
    | none =>
      rcases Nat.lt_or_ge u (t + 1) with hlt | hge
      · exact ih hb u (Nat.le_of_lt_succ hlt) hp
      · obtain rfl := Nat.le_antisymm hu hge
        simp [bmin, hb, hp] at h

private theorem bmin_none_of {P : A → ℕ → Prop} {a : A} {t : ℕ} (h : ∀ u, u ≤ t → ¬ P a u) :
    bmin P a t = none := by
  induction t with
  | zero => simp [bmin, h 0 (Nat.le_refl 0)]
  | succ t ih =>
    have hb : bmin P a t = none := ih (fun u hu => h u (Nat.le_succ_of_le hu))
    simp [bmin, hb, h (t + 1) (Nat.le_refl _)]

private theorem bmin_some_imp {P : A → ℕ → Prop} {a : A} {t u : ℕ} (h : bmin P a t = some u) :
    u ≤ t ∧ P a u ∧ ∀ u', u' < u → ¬ P a u' := by
  induction t generalizing u with
  | zero =>
    by_cases hp : P a 0
    · simp [bmin, hp] at h
      subst h
      exact ⟨Nat.le_refl 0, hp, fun u' hu' => absurd hu' (Nat.not_lt_zero u')⟩
    · simp [bmin, hp] at h
  | succ t ih =>
    cases hb : bmin P a t with
    | some v =>
      simp [bmin, hb] at h
      subst h
      obtain ⟨h1, h2, h3⟩ := ih hb
      exact ⟨Nat.le_succ_of_le h1, h2, h3⟩
    | none =>
      by_cases hp : P a (t + 1)
      · simp [bmin, hb, hp] at h
        subst h
        exact ⟨Nat.le_refl _, hp, fun u' hu' => bmin_none_imp hb u' (Nat.le_of_lt_succ hu')⟩
      · simp [bmin, hb, hp] at h

theorem bmin_eq_some_iff {P : A → ℕ → Prop} {a : A} {t u : ℕ} :
    bmin P a t = some u ↔ u ≤ t ∧ P a u ∧ ∀ u' < u, ¬ P a u' := by
  constructor
  · exact bmin_some_imp
  · rintro ⟨hut, hpu, hmin⟩
    cases hb : bmin P a t with
    | none => exact absurd hpu (bmin_none_imp hb u hut)
    | some v =>
      obtain ⟨_, hpv, hminv⟩ := bmin_some_imp hb
      rcases Nat.lt_trichotomy u v with huv | huv | huv
      · exact absurd hpu (hminv u huv)
      · rw [huv]
      · exact absurd hpv (hmin v huv)

theorem bmin_eq_none_iff {P : A → ℕ → Prop} {a : A} {t : ℕ} :
    bmin P a t = none ↔ ∀ u ≤ t, ¬ P a u :=
  ⟨bmin_none_imp, bmin_none_of⟩

/-- `bmin` only depends on the predicate `P a ·`. -/
private theorem bmin_congr {A' : Type} {P : A → ℕ → Prop} {P' : A' → ℕ → Prop} {a : A} {a' : A'}
    (h : ∀ u, P a u ↔ P' a' u) (t : ℕ) : bmin P a t = bmin P' a' t := by
  apply Option.ext
  intro u
  rw [bmin_eq_some_iff, bmin_eq_some_iff]
  simp only [h]

/-- Bounded minimization is computable (from primitive recursion and cases). -/
theorem compT_bmin {P : A → ℕ → Prop} (hP : CompSet M (fun p : A × ℕ => P p.1 p.2)) :
    CompT M (fun p : A × ℕ => bmin P p.1 p.2) := by
  have hQ := isCompSet_codeSet2 hP
  -- the step `⟨a, ⟨t, y⟩⟩ ↦ if y = 0 then (if Q a (t + 1) then t + 2 else 0) else y`
  -- on encoded values `y = e (bmin Q a t)` (`e none = 0`, `e (some u) = u + 1`)
  have hB1 := (TuringModel.isCompSet_eq_of (M := M)
    (TuringModel.isCompT_snd.comp TuringModel.isCompT_snd) (TuringModel.isCompT_const 0)).toB
  have hB2 : M.IsCompB (fun m => decide (codeSet2 (M := M) P (M.unpair m).1
      ((M.unpair (M.unpair m).2).1 + 1))) :=
    (TuringModel.isCompSet_comp₂ hQ TuringModel.isCompT_fst
      (TuringModel.isCompT_succ.comp (TuringModel.isCompT_fst.comp TuringModel.isCompT_snd))).toB
  have hh := TuringModel.IsCompT.cases hB1
    (TuringModel.IsCompT.cases hB2
      (TuringModel.isCompT_succ.comp (TuringModel.isCompT_succ.comp
        (TuringModel.isCompT_fst.comp TuringModel.isCompT_snd)))
      (TuringModel.isCompT_const 0))
    (TuringModel.isCompT_snd.comp TuringModel.isCompT_snd)
  have hg : M.IsCompT (fun a => if codeSet2 (M := M) P a 0 then 1 else 0) :=
    TuringModel.isCompSet_comp₂ hQ TuringModel.isCompT_id (TuringModel.isCompT_const 0)
  have hr := TuringModel.isCompT_primrec hg hh
    (fun a t => e M (bmin (codeSet2 (M := M) P) a t))
    (fun a => by
      by_cases h : codeSet2 (M := M) P a 0 <;> simp [bmin, h, e_some', e_none', e_nat'])
    (fun a t => by
      simp only [M.unpair_pair]
      cases hb : bmin (codeSet2 (M := M) P) a t with
      | none =>
        by_cases h : codeSet2 (M := M) P a (t + 1) <;>
          simp [bmin, hb, h, e_some', e_none', e_nat']
      | some u => simp [bmin, hb, e_some', e_nat'])
  refine compT_of_isCompT_e hr fun p => ?_
  simp only [e_prod', e_nat', M.unpair_pair]
  rw [bmin_congr (fun u => (codeSet2_e (M := M) (P := P) p.1 u).symm)]

/-- There is a least witness. -/
theorem exists_least {P : ℕ → Prop} (h : ∃ k, P k) : ∃ k, P k ∧ ∀ k' < k, ¬ P k' := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ n, ∀ m, m < n → ¬ P m := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ n ih =>
      intro m hm hp
      rcases Nat.lt_or_ge m n with hlt | hge
      · exact ih m hlt hp
      · obtain rfl := Nat.le_antisymm (Nat.le_of_lt_succ hm) hge
        exact hne ⟨m, hp, ih⟩
  obtain ⟨k, hk⟩ := h
  exact hall (k + 1) k (Nat.lt_succ_self k) hk

/-- Unbounded search `μ k. P a k` (undefined if there is no witness). -/
noncomputable def mu (P : A → ℕ → Prop) (a : A) : Option ℕ :=
  if h : ∃ k, P a k then some (choose (exists_least h)) else none

theorem mu_eq_some_iff {P : A → ℕ → Prop} {a : A} {k : ℕ} :
    mu P a = some k ↔ P a k ∧ ∀ k' < k, ¬ P a k' := by
  unfold mu
  by_cases h : ∃ k, P a k
  · rw [dite_eq_left h]
    have hc := choose_spec (exists_least h)
    constructor
    · intro hk
      obtain rfl := Option.some.inj hk
      exact hc
    · intro hk
      refine congrArg some ?_
      rcases Nat.lt_trichotomy (choose (exists_least h)) k with hlt | heq | hgt
      · exact absurd hc.1 (hk.2 _ hlt)
      · exact heq
      · exact absurd hk.1 (hc.2 _ hgt)
  · rw [dite_eq_right h]
    constructor
    · intro hk; cases hk
    · intro hk; exact absurd ⟨k, hk.1⟩ h

theorem mu_eq_none_iff {P : A → ℕ → Prop} {a : A} : mu P a = none ↔ ∀ k, ¬ P a k := by
  unfold mu
  by_cases h : ∃ k, P a k
  · rw [dite_eq_left h]
    constructor
    · intro hc; cases hc
    · intro hall; obtain ⟨k, hk⟩ := h; exact absurd hk (hall k)
  · rw [dite_eq_right h]
    exact ⟨fun _ k hk => h ⟨k, hk⟩, fun _ => rfl⟩

theorem comp_mu {P : A → ℕ → Prop} (hP : CompSet M (fun p : A × ℕ => P p.1 p.2)) :
    Comp M (fun a => mu P a) := by
  obtain ⟨T, hT⟩ := M.comp_mu
    (fun n => decide (codeSet2 (M := M) P (M.unpair n).1 (M.unpair n).2))
    (isCompSet_codeSet2 hP).toB
  refine ⟨T, fun x => ?_⟩
  show M.eval T (e M x) = (mu P x).map (fun n => n)
  rw [Option.map_id']
  apply Option.ext
  intro k
  rw [hT, mu_eq_some_iff]
  simp only [M.unpair_pair, decide_eq_true_eq, decide_eq_false_iff_not, codeSet2_e]

/-! ### Lists -/

theorem compT_length : CompT M (fun l : List A => l.length) :=
  compT_of_isCompT_e TuringModel.isCompT_fst fun l => by
    simp only [e_nat', e_list', listCode, M.unpair_pair, List.length_map]

/-- The map `P (l, i) = l(i)` of Proposition 2.4 (4b). -/
theorem comp_nth : Comp M (fun p : List A × ℕ => p.1[p.2]?) := by
  -- on `⟨⟨L, c⟩, i⟩`: if `i < L` then the head of `tl^[i] c`, else undefined
  have hF := TuringModel.IsComp.cases
    (TuringModel.isCompSet_lt_of TuringModel.isCompT_snd
      (TuringModel.isCompT_fst.comp TuringModel.isCompT_fst)).toB
    (TuringModel.isCompT_fst.comp (TuringModel.isCompT_repeat TuringModel.isCompT_snd
      TuringModel.isCompT_snd (TuringModel.isCompT_snd.comp TuringModel.isCompT_fst)))
    (TuringModel.isComp_none (M := M))
  refine comp_of_isComp_e hF fun p => ?_
  obtain ⟨l, i⟩ := p
  simp only [e_prod', e_nat', e_list', listCode, M.unpair_pair, List.length_map]
  by_cases hi : i < l.length
  · have h1 := hd_repeat_tl_foldr (M := M) (l.map (e M)) i (by simpa using hi)
    rw [List.getElem_map] at h1
    rw [List.getElem?_eq_getElem hi]
    simp [hi, h1]
  · rw [List.getElem?_eq_none_iff.2 (Nat.le_of_not_lt hi)]
    simp [hi]

/-- The total map `(l, i) ↦ l[i]?` into `Option A`. -/
theorem compT_nthOpt : CompT M (fun p : List A × ℕ => p.1[p.2]?) := by
  -- `comp_nth` is a partial map with the computable domain `p.2 < length p.1`
  refine CompT.ofComp comp_nth ((compSet_lt compT_snd (compT_length.comp compT_fst)).congr
    fun p => ?_)
  show p.2 < p.1.length ↔ p.1[p.2]? ≠ none
  rw [ne_eq, List.getElem?_eq_none_iff, Nat.not_le]

/-- `∃ b, f a = some b ∧ Φ a b` is decidable for total computable `f : A → Option B` and
decidable `Φ`. -/
theorem CompSet.exists_eq_some {f : A → Option B} (hf : CompT M f) {Φ : A → B → Prop}
    (hΦ : CompSet M (fun p : A × B => Φ p.1 p.2)) :
    CompSet M (fun a => ∃ b, f a = some b ∧ Φ a b) := by
  -- on the code `⟨e a, e (f a)⟩`: `e (f a) ≠ 0` (i.e. `f a ≠ none`) and
  -- `⟨e a, e (f a) - 1⟩ ∈ e (Φ)`
  have hQ : M.IsCompSet (fun n => 1 ≤ (M.unpair n).2 ∧
      ∃ p : A × B, e M p = M.pair (M.unpair n).1 ((M.unpair n).2 - 1) ∧ Φ p.1 p.2) :=
    (TuringModel.isCompSet_le_of (TuringModel.isCompT_const 1) TuringModel.isCompT_snd).and
      (TuringModel.IsCompSet.comp hΦ
        (TuringModel.isCompT_fst.pair (TuringModel.isCompT_pred.comp TuringModel.isCompT_snd)))
  refine (compSet_of_isCompSet (CompT.npair compT_e (compT_e.comp hf)) hQ).congr fun a => ?_
  simp only [M.unpair_pair]
  cases h : f a with
  | none => simp [e_none']
  | some b =>
    rw [e_some', Nat.add_sub_cancel]
    constructor
    · rintro ⟨_, hb⟩
      exact ⟨b, rfl, (exists_e_eq_and_iff (P := fun p : A × B => Φ p.1 p.2) (a := (a, b))).1 hb⟩
    · rintro ⟨b', hb', hΦb⟩
      cases hb'
      exact ⟨Nat.le_add_left 1 _,
        (exists_e_eq_and_iff (P := fun p : A × B => Φ p.1 p.2) (a := (a, b))).2 hΦb⟩

/-- Decoding a parameter: `∃ q : X, e q = u ∧ Φ y q` is decidable in `(y, u)`. -/
theorem CompSet.exists_decode {X : Type} [Enc M X] {Φ : A → X → Prop}
    (hΦ : CompSet M (fun p : A × X => Φ p.1 p.2)) :
    CompSet M (fun p : A × ℕ => ∃ q : X, e M q = p.2 ∧ Φ p.1 q) := by
  -- the two sets of codes coincide: both are `{⟨e a, e q⟩ | Φ a q}`
  refine TuringModel.IsCompSet.congr hΦ fun n => ?_
  constructor
  · rintro ⟨⟨a, q⟩, rfl, h⟩
    exact ⟨(a, e M q), rfl, q, rfl, h⟩
  · rintro ⟨⟨a, n'⟩, rfl, q, hq, h⟩
    refine ⟨(a, q), ?_, h⟩
    show M.pair (e M a) (e M q) = M.pair (e M a) n'
    rw [hq]

theorem CompSet.forall_decode {X : Type} [Enc M X] {Φ : A → X → Prop}
    (hΦ : CompSet M (fun p : A × X => Φ p.1 p.2)) :
    CompSet M (fun p : A × ℕ => ∀ q : X, e M q = p.2 → Φ p.1 q) := by
  have h := (CompSet.exists_decode (M := M) (Φ := fun a q => ¬ Φ a q) hΦ.not).not
  exact h.congr fun p => by
    constructor
    · intro hh q hq
      exact Classical.byContradiction fun hc => hh ⟨q, hq, hc⟩
    · rintro hh ⟨q, hq, hc⟩; exact hc (hh q hq)

/-- A computable map defined on a computable subset `P` (given with the induced encoding)
extends to a computable partial map, undefined off `P`. -/
theorem Comp.ofRestrict {P : A → Prop} (hP : CompSet M P) {f : A → B}
    (hf : @CompT M {a // P a} B (Enc.restrict P hP) _ (fun a => f a.1)) :
    Comp M (fun a => if P a then some (f a) else none) := by
  -- the machine computing `f` on `P`, patched to diverge off `P`
  obtain ⟨T, hT⟩ := hf
  have h := TuringModel.IsComp.cases (TuringModel.IsCompSet.toB hP)
    (TuringModel.isComp_eval T) TuringModel.isComp_none
  refine comp_of_isComp_e h fun a => ?_
  by_cases hpa : P a
  · rw [ite_eq_left hpa, decide_eq_true ((exists_e_eq_and_iff (P := P) (a := a)).2 hpa),
      Bool.cond_true]
    exact (hT ⟨a, hpa⟩).symm
  · rw [ite_eq_right hpa, decide_eq_false (fun h' => hpa ((exists_e_eq_and_iff (P := P) (a := a)).1 h')),
      Bool.cond_false]
    rfl

/-! ### The universal machine, `Halt'` and s-m-n at the level of encoded sets -/

/-- `Halt' ⊂ 𝒯 × ℕ × ℕ × ℕ` is a computable subset (Proposition 2.4 (2)). -/
theorem compSet_halt' :
    CompSet M (fun q : M.Code × ℕ × ℕ × ℕ => M.run q.1 q.2.1 q.2.2.1 = some q.2.2.2) := by
  obtain ⟨T₀, hT₀⟩ := M.comp_halt'
  refine compSet_of_eval (T := T₀) fun q => ?_
  obtain ⟨T, n, k, y⟩ := q
  have h := hT₀ T n k y
  by_cases hr : M.run T n k = some y
  · rw [ite_eq_left hr] at h
    rw [ite_eq_left hr]; exact h
  · rw [ite_eq_right hr] at h
    rw [ite_eq_right hr]; exact h

/-- The universal map `U : 𝒯 × ℕ → ℕ` is computable (Proposition 2.4 (2)). -/
theorem comp_univ : Comp M (fun p : M.Code × ℕ => M.eval p.1 p.2) := by
  obtain ⟨T₀, hT₀⟩ := M.comp_univ
  refine ⟨T₀, fun p => ?_⟩
  show M.eval T₀ (M.pair (M.code p.1) p.2) = (M.eval p.1 p.2).map (fun n => n)
  rw [hT₀, Option.map_id']

/-- Proposition 2.4 (3), the s-m-n theorem: from computable `f : A × B → C` a total computable
`s : A → 𝒯` with `s a` computing `f (a, ·)`. -/
theorem smn {f : A × B → Option C} (hf : Comp M f) :
    ∃ s : A → M.Code, CompT M s ∧ ∀ a, Computes M (s a) (fun b => f (a, b)) := by
  obtain ⟨Tf, hTf⟩ := hf
  obtain ⟨s, ⟨T₀, hT₀⟩, hs⟩ := M.comp_smn (M.eval Tf) (TuringModel.isComp_eval Tf)
  refine ⟨fun a => s (e M a), ⟨T₀, fun a => hT₀ (e M a)⟩, fun a b => ?_⟩
  rw [hs]
  exact hTf (a, b)

/-! ### Infinite encoded sets and the bijection `ε_A : A → ℕ` -/

/-- The number of codes `m < n` in the image of `e_A`. -/
noncomputable def countBelow (A : Type) [Enc M A] : ℕ → ℕ
  | 0 => 0
  | n + 1 => countBelow A n + (if ∃ a : A, e M a = n then 1 else 0)

/-- `ε_A (a)` = the number of elements of `e_A (A)` smaller than `e_A (a)`. -/
noncomputable def epsilon (a : A) : ℕ := countBelow (M := M) A (e M a)

/-- `countBelow` is computable (primitive recursion). -/
private theorem isCompT_countBelow : M.IsCompT (fun n => countBelow (M := M) A n) := by
  have hh : M.IsCompT (fun m => (M.unpair (M.unpair m).2).2 +
      (if ∃ a : A, e M a = (M.unpair (M.unpair m).2).1 then 1 else 0)) :=
    TuringModel.isCompT_add_of (TuringModel.isCompT_snd.comp TuringModel.isCompT_snd)
      ((Enc.img (M := M) (A := A)).comp (TuringModel.isCompT_fst.comp TuringModel.isCompT_snd))
  exact TuringModel.isCompT_primrec_of (TuringModel.isCompT_const 0) hh
    (TuringModel.isCompT_const 0) TuringModel.isCompT_id (fun _ n => countBelow (M := M) A n)
    (fun _ => rfl) (fun a n => by simp only [M.unpair_pair, countBelow])

private theorem countBelow_mono {m n : ℕ} (h : m ≤ n) :
    countBelow (M := M) A m ≤ countBelow (M := M) A n := by
  induction n with
  | zero => obtain rfl := Nat.le_zero.1 h; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · refine Nat.le_trans (ih (Nat.le_of_lt_succ hlt)) ?_
      simp only [countBelow]
      exact Nat.le_add_right _ _
    · obtain rfl := Nat.le_antisymm h hge
      exact Nat.le_refl _

private theorem countBelow_succ_e (a : A) :
    countBelow (M := M) A (e M a + 1) = countBelow (M := M) A (e M a) + 1 := by
  simp only [countBelow]
  rw [ite_eq_left ⟨a, rfl⟩]

theorem compT_epsilon : CompT M (fun a : A => epsilon (M := M) a) :=
  compT_of_isCompT_e (isCompT_countBelow (A := A)) fun _ => rfl

theorem epsilon_strictMono {a b : A} (h : e M a < e M b) :
    epsilon (M := M) a < epsilon (M := M) b := by
  unfold epsilon
  have h1 := countBelow_succ_e (M := M) a
  have h2 := countBelow_mono (M := M) (A := A) (show e M a + 1 ≤ e M b from h)
  omega

theorem epsilon_inj {a b : A} (h : epsilon (M := M) a = epsilon (M := M) b) : a = b := by
  rcases Nat.lt_trichotomy (e M a) (e M b) with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (epsilon_strictMono hlt))
  · exact Enc.inj heq
  · exact absurd h.symm (Nat.ne_of_lt (epsilon_strictMono hgt))

/-- For infinite `A`, `ε_A` is surjective. -/
theorem epsilon_surj (hA : Enc.Infinite M A) (k : ℕ) : ∃ a : A, epsilon (M := M) a = k := by
  -- `countBelow` is unbounded
  have hunb : ∀ k, ∃ n, k ≤ countBelow (M := M) A n := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha⟩ := hA n
      refine ⟨e M a + 1, ?_⟩
      rw [countBelow_succ_e]
      have := countBelow_mono (M := M) (A := A) (Nat.le_of_lt ha)
      omega
  -- it increases by at most one per step, so the value `k` is attained at a code
  have key : ∀ n, k + 1 ≤ countBelow (M := M) A n → ∃ a : A, epsilon (M := M) a = k := by
    intro n
    induction n with
    | zero => intro h; simp [countBelow] at h
    | succ n ih =>
      intro h
      by_cases hn : k + 1 ≤ countBelow (M := M) A n
      · exact ih hn
      · by_cases hc : ∃ a : A, e M a = n
        · obtain ⟨a, rfl⟩ := hc
          refine ⟨a, ?_⟩
          unfold epsilon
          rw [countBelow_succ_e] at h
          omega
        · simp only [countBelow, ite_eq_right hc] at h
          omega
  obtain ⟨n, hn⟩ := hunb (k + 1)
  exact key n hn

/-- The inverse of `ε_A`: the element of `A` with `ε_A a = k`, found by an unbounded search. -/
noncomputable def epsilonInv (A : Type) [Enc M A] (k : ℕ) : Option A :=
  (mu (fun (k : ℕ) n => ∃ a : A, e M a = n ∧ epsilon (M := M) a = k) k).bind (Enc.decode (M := M) A)

theorem comp_epsilonInv : Comp M (fun k : ℕ => epsilonInv (M := M) A k) := by
  -- `⟨k, n⟩ ↦ (n ∈ e_A (A) ∧ countBelow n = k)`
  have hR := ((Enc.img (M := M) (A := A)).comp TuringModel.isCompT_snd).and
    (TuringModel.isCompSet_eq_of ((isCompT_countBelow (A := A)).comp TuringModel.isCompT_snd)
      TuringModel.isCompT_fst)
  have hP : CompSet M (fun p : ℕ × ℕ =>
      (fun (k : ℕ) n => ∃ a : A, e M a = n ∧ epsilon (M := M) a = k) p.1 p.2) := by
    refine compSet_of_isCompSet_e hR fun p => ?_
    obtain ⟨k, n⟩ := p
    simp only [e_prod', e_nat', M.unpair_pair]
    constructor
    · rintro ⟨a, rfl, h⟩; exact ⟨⟨a, rfl⟩, h⟩
    · rintro ⟨⟨a, rfl⟩, h⟩; exact ⟨a, rfl, h⟩
  exact Comp.comp comp_decode
    (comp_mu (P := fun (k : ℕ) n => ∃ a : A, e M a = n ∧ epsilon (M := M) a = k) hP)

theorem epsilonInv_epsilon (a : A) : epsilonInv (M := M) A (epsilon (M := M) a) = some a := by
  unfold epsilonInv
  have h : mu (fun (k : ℕ) n => ∃ a : A, e M a = n ∧ epsilon (M := M) a = k)
      (epsilon (M := M) a) = some (e M a) := by
    rw [mu_eq_some_iff]
    refine ⟨⟨a, rfl, rfl⟩, fun n hn hex => ?_⟩
    obtain ⟨b, rfl, hbe⟩ := hex
    exact absurd hbe (Nat.ne_of_lt (epsilon_strictMono hn))
  rw [h, Option.bind_some, Enc.decode_e]

theorem epsilonInv_eq_some_iff {k : ℕ} {a : A} :
    epsilonInv (M := M) A k = some a ↔ epsilon (M := M) a = k := by
  constructor
  · intro h
    unfold epsilonInv at h
    cases hmu : mu (fun (k : ℕ) n => ∃ a : A, e M a = n ∧ epsilon (M := M) a = k) k with
    | none => rw [hmu] at h; cases h
    | some n =>
      rw [hmu, Option.bind_some, Enc.decode_eq_some_iff] at h
      obtain ⟨⟨b, hb, hbk⟩, _⟩ := mu_eq_some_iff.1 hmu
      subst h
      exact (Enc.inj hb) ▸ hbk
  · rintro rfl; exact epsilonInv_epsilon a

/-- For infinite `A`, `ε_A⁻¹` is total. -/
theorem epsilonInv_isSome (hA : Enc.Infinite M A) (k : ℕ) : epsilonInv (M := M) A k ≠ none := by
  obtain ⟨a, ha⟩ := epsilon_surj hA k
  rw [epsilonInv_eq_some_iff.2 ha]
  exact Option.some_ne_none a

end Closure

end Stable
