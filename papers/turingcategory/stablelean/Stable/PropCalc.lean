import Stable.Logic

/-!
# Derived connectives and propositional reasoning (for Appendix B)

`Language` provides `¬`, `∧` and the rules of `Logic.lean`. Here we define `∨`, `→`, `↔` from them,
the extension `F ∪ {a}` of a theory, finite conjunctions and disjunctions, logical equivalence, and the
derived rules used in `Undefinable.lean`: deduction theorem, modus ponens, case analysis, `∨`-rules,
`↔`-rules and congruence of logical equivalence.
-/

namespace Stable

namespace Language

variable {M : TuringModel} (L : Language M)

/-- `F ∪ {a}`. -/
def ext (F : L.Sent → Prop) (a : L.Sent) : L.Sent → Prop := fun β => F β ∨ β = a

/-- `F ∪ l` for a list `l`. -/
def extList (F : L.Sent → Prop) (l : List L.Sent) : L.Sent → Prop := fun β => F β ∨ β ∈ l

/-- The empty theory. -/
def empty : L.Sent → Prop := fun _ => False

/-- The theory `{a}`. -/
def single (a : L.Sent) : L.Sent → Prop := fun β => β = a

/-- `a ∨ b := ¬(¬a ∧ ¬b)`. -/
def or (a b : L.Sent) : L.Sent := L.neg (L.and (L.neg a) (L.neg b))

/-- `a → b := ¬(a ∧ ¬b)`. -/
def imp (a b : L.Sent) : L.Sent := L.neg (L.and a (L.neg b))

/-- `a ↔ b := (a → b) ∧ (b → a)`. -/
def iff (a b : L.Sent) : L.Sent := L.and (L.imp a b) (L.imp b a)

/-- Logical validity. -/
def Valid (a : L.Sent) : Prop := L.Deriv L.empty a

/-- Logical equivalence. -/
def Equiv (a b : L.Sent) : Prop := L.Deriv (L.single a) b ∧ L.Deriv (L.single b) a

/-- Finite conjunction, `⋀ [] = z`. -/
def conjList (z : L.Sent) : List L.Sent → L.Sent
  | [] => z
  | a :: l => L.and a (conjList z l)

/-- Finite disjunction, `⋁ [] = z`. -/
def disjList (z : L.Sent) : List L.Sent → L.Sent
  | [] => z
  | a :: l => L.or a (disjList z l)

variable {L}

/-! ### Structural lemmas -/

theorem deriv_ext_self (F : L.Sent → Prop) (a : L.Sent) : L.Deriv (L.ext F a) a :=
  L.deriv_of_mem (Or.inr rfl)

theorem deriv_ext_of {F : L.Sent → Prop} {b : L.Sent} (a : L.Sent) (h : L.Deriv F b) :
    L.Deriv (L.ext F a) b :=
  L.deriv_mono (fun _ hβ => Or.inl hβ) h

theorem deriv_ext_mono {F G : L.Sent → Prop} {a b : L.Sent} (hFG : ∀ β, F β → G β)
    (h : L.Deriv (L.ext F a) b) : L.Deriv (L.ext G a) b :=
  L.deriv_mono (fun β hβ => hβ.elim (fun h' => Or.inl (hFG β h')) Or.inr) h

theorem deriv_ext_swap {F : L.Sent → Prop} {a b c : L.Sent} (h : L.Deriv (L.ext (L.ext F a) b) c) :
    L.Deriv (L.ext (L.ext F b) a) c :=
  L.deriv_mono (fun β hβ => by
    rcases hβ with (hβ | hβ) | hβ
    · exact Or.inl (Or.inl hβ)
    · exact Or.inr hβ
    · exact Or.inl (Or.inr hβ)) h

/-- Cut with a single sentence: `F ⊢ a` and `F ∪ {a} ⊢ b` give `F ⊢ b`. -/
theorem deriv_cut_ext {F : L.Sent → Prop} {a b : L.Sent} (ha : L.Deriv F a)
    (h : L.Deriv (L.ext F a) b) : L.Deriv F b :=
  L.deriv_cut (fun β hβ => by
    rcases hβ with hβ | hβ
    · exact L.deriv_of_mem hβ
    · rw [hβ]; exact ha) h

theorem deriv_single_self (a : L.Sent) : L.Deriv (L.single a) a := L.deriv_of_mem rfl

theorem deriv_of_single {F : L.Sent → Prop} {a b : L.Sent} (ha : L.Deriv F a)
    (h : L.Deriv (L.single a) b) : L.Deriv F b :=
  L.deriv_cut (fun β (hβ : β = a) => by rw [hβ]; exact ha) h

theorem deriv_of_valid {F : L.Sent → Prop} {a : L.Sent} (h : L.Valid a) : L.Deriv F a :=
  L.deriv_mono (fun _ hβ => hβ.elim) h

theorem deriv_ext_single {a b : L.Sent} (h : L.Deriv (L.ext L.empty a) b) : L.Deriv (L.single a) b :=
  L.deriv_mono (fun _ hβ => hβ.elim (fun h => h.elim) id) h

theorem deriv_single_ext {a b : L.Sent} (h : L.Deriv (L.single a) b) : L.Deriv (L.ext L.empty a) b :=
  L.deriv_mono (fun _ hβ => Or.inr hβ) h

theorem deriv_ext_of_single {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv (L.single a) b) :
    L.Deriv (L.ext F a) b :=
  L.deriv_mono (fun _ hβ => Or.inr hβ) h

/-! ### Negation -/

/-- `F ∪ {a} ⊢ b` and `F ∪ {a} ⊢ ¬b` give `F ⊢ ¬a`. -/
theorem deriv_neg_of {F : L.Sent → Prop} {a b : L.Sent} (h₁ : L.Deriv (L.ext F a) b)
    (h₂ : L.Deriv (L.ext F a) (L.neg b)) : L.Deriv F (L.neg a) :=
  L.deriv_neg_intro fun _ => L.deriv_explosion h₁ h₂

/-- Case analysis on `c`. -/
theorem deriv_cases {F : L.Sent → Prop} {a c : L.Sent} (h₁ : L.Deriv (L.ext F c) a)
    (h₂ : L.Deriv (L.ext F (L.neg c)) a) : L.Deriv F a := by
  apply L.deriv_dne
  apply L.deriv_neg_intro
  intro γ
  -- in `F ∪ {¬a}`: derive `¬c`, then `a`, then explode
  have hnc : L.Deriv (L.ext F (L.neg a)) (L.neg c) := by
    refine deriv_neg_of (b := a) ?_ ?_
    · exact deriv_ext_swap (deriv_ext_of _ h₁)
    · exact deriv_ext_of _ (deriv_ext_self F (L.neg a))
  have ha : L.Deriv (L.ext F (L.neg a)) a :=
    deriv_cut_ext hnc (deriv_ext_swap (deriv_ext_of _ h₂))
  exact L.deriv_explosion ha (deriv_ext_self F (L.neg a))

theorem deriv_of_neg_neg {F : L.Sent → Prop} {a : L.Sent} (h : L.Deriv F (L.neg (L.neg a))) :
    L.Deriv F a := L.deriv_dne h

/-- From `F ⊢ ¬a` and `F ⊢ a` everything follows. -/
theorem deriv_of_contra {F : L.Sent → Prop} {a b : L.Sent} (h₁ : L.Deriv F a)
    (h₂ : L.Deriv F (L.neg a)) : L.Deriv F b := L.deriv_explosion h₁ h₂

/-! ### Implication -/

/-- Deduction theorem. -/
theorem deriv_imp_intro {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv (L.ext F a) b) :
    L.Deriv F (L.imp a b) := by
  apply L.deriv_neg_intro
  intro γ
  have ha : L.Deriv (L.ext F (L.and a (L.neg b))) a :=
    L.deriv_and_left (deriv_ext_self F _)
  have hnb : L.Deriv (L.ext F (L.and a (L.neg b))) (L.neg b) :=
    L.deriv_and_right (deriv_ext_self F _)
  have hb : L.Deriv (L.ext F (L.and a (L.neg b))) b :=
    deriv_cut_ext ha (deriv_ext_swap (deriv_ext_of _ h))
  exact L.deriv_explosion hb hnb

/-- Modus ponens. -/
theorem deriv_mp {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.imp a b)) (ha : L.Deriv F a) :
    L.Deriv F b := by
  apply L.deriv_dne
  apply L.deriv_neg_intro
  intro γ
  have h1 : L.Deriv (L.ext F (L.neg b)) (L.and a (L.neg b)) :=
    L.deriv_and_intro (deriv_ext_of _ ha) (deriv_ext_self F _)
  exact L.deriv_explosion h1 (deriv_ext_of _ h)

/-- `F ∪ {a} ⊢ b` from `F ⊢ a → b`. -/
theorem deriv_ext_of_imp {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.imp a b)) :
    L.Deriv (L.ext F a) b :=
  deriv_mp (deriv_ext_of _ h) (deriv_ext_self F a)

theorem deriv_imp_self (F : L.Sent → Prop) (a : L.Sent) : L.Deriv F (L.imp a a) :=
  deriv_imp_intro (deriv_ext_self F a)

theorem deriv_imp_trans {F : L.Sent → Prop} {a b c : L.Sent} (h₁ : L.Deriv F (L.imp a b))
    (h₂ : L.Deriv F (L.imp b c)) : L.Deriv F (L.imp a c) :=
  deriv_imp_intro (deriv_mp (deriv_ext_of _ h₂) (deriv_ext_of_imp h₁))

/-- Contraposition: `F ⊢ a → b` and `F ⊢ ¬b` give `F ⊢ ¬a`. -/
theorem deriv_neg_of_imp {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.imp a b))
    (hb : L.Deriv F (L.neg b)) : L.Deriv F (L.neg a) :=
  deriv_neg_of (deriv_ext_of_imp h) (deriv_ext_of _ hb)

/-- `F ⊢ a → b` and `F ∪ {b}` inconsistent (witnessed by `c`) give `F ⊢ ¬a`. -/
theorem deriv_imp_neg_of_neg {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.imp a b)) :
    L.Deriv F (L.imp (L.neg b) (L.neg a)) :=
  deriv_imp_intro (deriv_neg_of_imp (deriv_ext_of _ h) (deriv_ext_self F _))

/-! ### Disjunction -/

theorem deriv_or_inl {F : L.Sent → Prop} {a : L.Sent} (b : L.Sent) (h : L.Deriv F a) :
    L.Deriv F (L.or a b) := by
  apply L.deriv_neg_intro
  intro γ
  exact L.deriv_explosion (deriv_ext_of _ h) (L.deriv_and_left (deriv_ext_self F _))

theorem deriv_or_inr {F : L.Sent → Prop} {b : L.Sent} (a : L.Sent) (h : L.Deriv F b) :
    L.Deriv F (L.or a b) := by
  apply L.deriv_neg_intro
  intro γ
  exact L.deriv_explosion (deriv_ext_of _ h) (L.deriv_and_right (deriv_ext_self F _))

/-- Disjunction elimination. -/
theorem deriv_or_elim {F : L.Sent → Prop} {a b c : L.Sent} (h : L.Deriv F (L.or a b))
    (h₁ : L.Deriv (L.ext F a) c) (h₂ : L.Deriv (L.ext F b) c) : L.Deriv F c := by
  refine deriv_cases (c := a) h₁ ?_
  refine deriv_cases (c := b) (deriv_ext_swap (deriv_ext_of _ h₂)) ?_
  -- `F ∪ {¬a, ¬b}` is inconsistent with `a ∨ b`
  have h3 : L.Deriv (L.ext (L.ext F (L.neg a)) (L.neg b)) (L.and (L.neg a) (L.neg b)) :=
    L.deriv_and_intro (deriv_ext_of _ (deriv_ext_self F _)) (deriv_ext_self _ _)
  exact L.deriv_explosion h3 (deriv_ext_of _ (deriv_ext_of _ h))

/-- Disjunction elimination with the disjunction as a hypothesis. -/
theorem deriv_or_elim' {F : L.Sent → Prop} {a b c : L.Sent} (h₁ : L.Deriv (L.ext F a) c)
    (h₂ : L.Deriv (L.ext F b) c) : L.Deriv (L.ext F (L.or a b)) c :=
  deriv_or_elim (deriv_ext_self F _) (deriv_ext_swap (deriv_ext_of _ h₁))
    (deriv_ext_swap (deriv_ext_of _ h₂))

/-! ### Biconditional -/

theorem deriv_iff_intro {F : L.Sent → Prop} {a b : L.Sent} (h₁ : L.Deriv (L.ext F a) b)
    (h₂ : L.Deriv (L.ext F b) a) : L.Deriv F (L.iff a b) :=
  L.deriv_and_intro (deriv_imp_intro h₁) (deriv_imp_intro h₂)

theorem deriv_iff_mp {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.iff a b))
    (ha : L.Deriv F a) : L.Deriv F b :=
  deriv_mp (L.deriv_and_left h) ha

theorem deriv_iff_mpr {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.iff a b))
    (hb : L.Deriv F b) : L.Deriv F a :=
  deriv_mp (L.deriv_and_right h) hb

theorem deriv_iff_symm {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.iff a b)) :
    L.Deriv F (L.iff b a) :=
  L.deriv_and_intro (L.deriv_and_right h) (L.deriv_and_left h)

theorem deriv_iff_refl (F : L.Sent → Prop) (a : L.Sent) : L.Deriv F (L.iff a a) :=
  deriv_iff_intro (deriv_ext_self F a) (deriv_ext_self F a)

theorem deriv_iff_trans {F : L.Sent → Prop} {a b c : L.Sent} (h₁ : L.Deriv F (L.iff a b))
    (h₂ : L.Deriv F (L.iff b c)) : L.Deriv F (L.iff a c) :=
  deriv_iff_intro (deriv_iff_mp (deriv_ext_of _ h₂) (deriv_iff_mp (deriv_ext_of _ h₁) (deriv_ext_self F a)))
    (deriv_iff_mpr (deriv_ext_of _ h₁) (deriv_iff_mpr (deriv_ext_of _ h₂) (deriv_ext_self F c)))

/-- `F ⊢ a ↔ b` from `F ⊢ a` and `F ⊢ b`. -/
theorem deriv_iff_of_both {F : L.Sent → Prop} {a b : L.Sent} (ha : L.Deriv F a) (hb : L.Deriv F b) :
    L.Deriv F (L.iff a b) :=
  deriv_iff_intro (deriv_ext_of _ hb) (deriv_ext_of _ ha)

/-- `F ⊢ a ↔ b` from `F ⊢ ¬a` and `F ⊢ ¬b`. -/
theorem deriv_iff_of_both_neg {F : L.Sent → Prop} {a b : L.Sent} (ha : L.Deriv F (L.neg a))
    (hb : L.Deriv F (L.neg b)) : L.Deriv F (L.iff a b) :=
  deriv_iff_intro (L.deriv_explosion (deriv_ext_self F a) (deriv_ext_of _ ha))
    (L.deriv_explosion (deriv_ext_self F b) (deriv_ext_of _ hb))

/-- Congruence of `↔` with `¬`. -/
theorem deriv_iff_neg {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.iff a b)) :
    L.Deriv F (L.iff (L.neg a) (L.neg b)) :=
  deriv_iff_intro
    (deriv_neg_of_imp (deriv_ext_of _ (L.deriv_and_right h)) (deriv_ext_self F _))
    (deriv_neg_of_imp (deriv_ext_of _ (L.deriv_and_left h)) (deriv_ext_self F _))

/-- Congruence of `↔` with `∧`. -/
theorem deriv_iff_and {F : L.Sent → Prop} {a b c d : L.Sent} (h₁ : L.Deriv F (L.iff a c))
    (h₂ : L.Deriv F (L.iff b d)) : L.Deriv F (L.iff (L.and a b) (L.and c d)) :=
  deriv_iff_intro
    (L.deriv_and_intro (deriv_iff_mp (deriv_ext_of _ h₁) (L.deriv_and_left (deriv_ext_self F _)))
      (deriv_iff_mp (deriv_ext_of _ h₂) (L.deriv_and_right (deriv_ext_self F _))))
    (L.deriv_and_intro (deriv_iff_mpr (deriv_ext_of _ h₁) (L.deriv_and_left (deriv_ext_self F _)))
      (deriv_iff_mpr (deriv_ext_of _ h₂) (L.deriv_and_right (deriv_ext_self F _))))

/-- Transport of derivability along `F ⊢ a ↔ b`. -/
theorem deriv_of_iff {F : L.Sent → Prop} {a b : L.Sent} (h : L.Deriv F (L.iff a b)) :
    L.Deriv F a ↔ L.Deriv F b :=
  ⟨deriv_iff_mp h, deriv_iff_mpr h⟩

/-! ### Logical equivalence -/

namespace Equiv

variable {a b c : L.Sent}

theorem refl (a : L.Sent) : L.Equiv a a := ⟨deriv_single_self a, deriv_single_self a⟩

theorem symm (h : L.Equiv a b) : L.Equiv b a := ⟨h.2, h.1⟩

theorem trans (h₁ : L.Equiv a b) (h₂ : L.Equiv b c) : L.Equiv a c :=
  ⟨deriv_of_single h₁.1 h₂.1, deriv_of_single h₂.2 h₁.2⟩

/-- `F ⊢ a` iff `F ⊢ b`, for equivalent `a`, `b`. -/
theorem deriv_iff (h : L.Equiv a b) (F : L.Sent → Prop) : L.Deriv F a ↔ L.Deriv F b :=
  ⟨fun ha => deriv_of_single ha h.1, fun hb => deriv_of_single hb h.2⟩

theorem valid_iff (h : L.Equiv a b) : L.Valid a ↔ L.Valid b := h.deriv_iff _

theorem neg (h : L.Equiv a b) : L.Equiv (L.neg a) (L.neg b) :=
  ⟨deriv_neg_of (b := a) (deriv_ext_of_single h.2) (deriv_ext_of _ (deriv_single_self _)),
    deriv_neg_of (b := b) (deriv_ext_of_single h.1) (deriv_ext_of _ (deriv_single_self _))⟩

theorem and {a' b' : L.Sent} (h₁ : L.Equiv a a') (h₂ : L.Equiv b b') :
    L.Equiv (L.and a b) (L.and a' b') :=
  ⟨L.deriv_and_intro (deriv_of_single (L.deriv_and_left (deriv_single_self _)) h₁.1)
      (deriv_of_single (L.deriv_and_right (deriv_single_self _)) h₂.1),
    L.deriv_and_intro (deriv_of_single (L.deriv_and_left (deriv_single_self _)) h₁.2)
      (deriv_of_single (L.deriv_and_right (deriv_single_self _)) h₂.2)⟩

/-- Equivalence from a valid biconditional. -/
theorem of_valid_iff (h : L.Valid (L.iff a b)) : L.Equiv a b :=
  ⟨deriv_iff_mp (deriv_of_valid h) (deriv_single_self a),
    deriv_iff_mpr (deriv_of_valid h) (deriv_single_self b)⟩

theorem to_deriv_iff (h : L.Equiv a b) (F : L.Sent → Prop) : L.Deriv F (L.iff a b) :=
  deriv_iff_intro (deriv_ext_of_single h.1) (deriv_ext_of_single h.2)

end Equiv

/-! ### Finite conjunctions and disjunctions -/

theorem deriv_conjList_of_mem {F : L.Sent → Prop} {z a : L.Sent} {l : List L.Sent}
    (h : L.Deriv F (L.conjList z l)) (ha : a ∈ l) : L.Deriv F a := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
    cases ha with
    | head => exact L.deriv_and_left h
    | tail _ ha' => exact ih (L.deriv_and_right h) ha'

theorem deriv_conjList_head {F : L.Sent → Prop} {z : L.Sent} {l : List L.Sent}
    (h : L.Deriv F (L.conjList z l)) : L.Deriv F z := by
  induction l with
  | nil => exact h
  | cons x l ih => exact ih (L.deriv_and_right h)

theorem deriv_conjList {F : L.Sent → Prop} {z : L.Sent} {l : List L.Sent} (hz : L.Deriv F z)
    (h : ∀ a, a ∈ l → L.Deriv F a) : L.Deriv F (L.conjList z l) := by
  induction l with
  | nil => exact hz
  | cons x l ih =>
    exact L.deriv_and_intro (h x (List.Mem.head _)) (ih fun a ha => h a (List.Mem.tail _ ha))

theorem deriv_disjList_of_mem {F : L.Sent → Prop} {z a : L.Sent} {l : List L.Sent}
    (ha : a ∈ l) (h : L.Deriv F a) : L.Deriv F (L.disjList z l) := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
    cases ha with
    | head => exact deriv_or_inl _ h
    | tail _ ha' => exact deriv_or_inr _ (ih ha')

/-- Elimination of a finite disjunction. -/
theorem deriv_disjList_elim {F : L.Sent → Prop} {z c : L.Sent} {l : List L.Sent}
    (h : L.Deriv F (L.disjList z l)) (hl : ∀ a, a ∈ l → L.Deriv (L.ext F a) c)
    (hz : L.Deriv (L.ext F z) c) : L.Deriv F c := by
  induction l generalizing F with
  | nil => exact deriv_cut_ext h hz
  | cons x l ih =>
    refine deriv_or_elim h (hl x (List.Mem.head _)) ?_
    refine ih (deriv_ext_self F _) (fun a ha => ?_) (deriv_ext_swap (deriv_ext_of _ hz))
    exact deriv_ext_swap (deriv_ext_of _ (hl a (List.Mem.tail _ ha)))

theorem deriv_disjList_of_z {F : L.Sent → Prop} {z : L.Sent} (h : L.Deriv F z) (l : List L.Sent) :
    L.Deriv F (L.disjList z l) := by
  induction l with
  | nil => exact h
  | cons x l ih => exact deriv_or_inr _ ih

theorem deriv_disjList_mono {F : L.Sent → Prop} {z : L.Sent} {l l' : List L.Sent}
    (hl : ∀ a, a ∈ l → a ∈ l') (h : L.Deriv F (L.disjList z l)) : L.Deriv F (L.disjList z l') :=
  deriv_disjList_elim h (fun a ha => deriv_disjList_of_mem (hl a ha) (deriv_ext_self F a))
    (deriv_disjList_of_z (deriv_ext_self F z) l')

/-- `F ∪ l ⊢ d` gives `F ⊢ d ∨ ⋁ (¬a : a ∈ l)`. -/
theorem deriv_or_disjList_neg {F : L.Sent → Prop} {z d : L.Sent} {l : List L.Sent}
    (h : L.Deriv (L.extList F l) d) : L.Deriv F (L.or d (L.disjList z (l.map L.neg))) := by
  induction l generalizing F with
  | nil =>
    refine deriv_or_inl _ (L.deriv_mono (fun β hβ => ?_) h)
    rcases hβ with hβ | hβ
    · exact hβ
    · cases hβ
  | cons x l ih =>
    have h' : L.Deriv (L.extList (L.ext F x) l) d := L.deriv_mono (fun β hβ => by
      rcases hβ with hβ | hβ
      · exact Or.inl (Or.inl hβ)
      · cases hβ with
        | head => exact Or.inl (Or.inr rfl)
        | tail _ hβ' => exact Or.inr hβ') h
    have ih' := ih h'
    -- case analysis on `x`
    refine deriv_cases (c := x) ?_ ?_
    · refine deriv_or_elim ih' (deriv_or_inl _ (deriv_ext_self _ _)) ?_
      exact deriv_or_inr _ (deriv_or_inr _ (deriv_ext_self _ _))
    · exact deriv_or_inr _ (deriv_or_inl _ (deriv_ext_self F _))

/-- Deduction theorem for a list of hypotheses: `F ∪ l ⊢ d` gives `F ⊢ ⋀ l → d`. -/
theorem deriv_imp_conjList {F : L.Sent → Prop} {z d : L.Sent} {l : List L.Sent}
    (h : L.Deriv (L.extList F l) d) : L.Deriv F (L.imp (L.conjList z l) d) := by
  refine deriv_imp_intro (L.deriv_cut (fun β hβ => ?_) h)
  rcases hβ with hβ | hβ
  · exact deriv_ext_of _ (L.deriv_of_mem hβ)
  · exact deriv_conjList_of_mem (deriv_ext_self F _) hβ

/-- Conversely, `F ⊢ ⋀ l → d` gives `F ∪ l ⊢ d`, provided `F ⊢ z`. -/
theorem deriv_extList_of_imp_conjList {F : L.Sent → Prop} {z d : L.Sent} {l : List L.Sent}
    (hz : L.Deriv F z) (h : L.Deriv F (L.imp (L.conjList z l) d)) : L.Deriv (L.extList F l) d := by
  have h1 : L.Deriv (L.extList F l) (L.conjList z l) :=
    deriv_conjList (L.deriv_mono (fun β hβ => Or.inl hβ) hz) fun a ha => L.deriv_of_mem (Or.inr ha)
  exact deriv_mp (L.deriv_mono (fun β hβ => Or.inl hβ) h) h1

end Language

end Stable
