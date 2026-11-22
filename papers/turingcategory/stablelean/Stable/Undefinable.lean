import Stable.PropCalc
import Stable.Incompleteness
import Stable.NSigma

/-!
# A translation inducing an undefinable theory (Appendix B, Proposition B.7)

We prove, relative to the interface `UndefData` below, that there is a `2`-translation
`j : 𝓐 → 𝓐`, the identity on `Σ⁰₂` and `Π⁰₂` sentences, with `PA_{j,𝓐}` not arithmetical
(not `Σ⁰ₙ` for any `n`, in the sense of `IsSigmaNSet`), and `PA`, `Q` `1`- and `2`-consistent
relative to `j`. More precisely (`undefinable_family`) there is a sequence of sentences `ε n`,
not depending on `X`, such that for every `X ⊂ ℕ` some such `j = j_X` satisfies
`¬ε n ∈ PA_{j,𝓐} ↔ n ∈ X`; non-arithmeticity follows by counting (`exists_undefinable`), since
only countably many sets of sentences are arithmetical.

`UndefData` collects, as assumptions, the classical facts the proof uses beyond `Arith`
(the manuscript cites Hájek–Pudlák for them) and the syntax it needs:

* sentences are generated from *prime* sentences (atomic, or beginning with a quantifier) by `¬`
  and `∧` (the other connectives being abbreviations), with unique readability (`destruct`) and a
  size function for recursion;
* `Δ₀` is closed under subformulas, a `Σ⁰₂` or `Π⁰₂` sentence that is a negation or a conjunction
  is `Δ₀`, and `wrap s` (in the manuscript `∀y (y = y ∧ s)`) is a prime sentence logically
  equivalent to `s`, injective in `s`, and in `Σ⁰₂ ∪ Π⁰₂` only if `s` is `Δ₀`;
* every axiom of `Q` is logically equivalent to a sentence of `𝓑` (the Boolean combinations of
  `Σ⁰₂` and `Π⁰₂` sentences);
* `PA`: a sound c.e. theory containing `Q`, with a finite fragment `PA_r` (a sentence) proving `Q`;
* the partial truth definition `Sat_𝓑` for `𝓑` (fact (1) of the appendix), the arithmetized
  completeness theorem for `Σ⁰₃`-definable theories (fact (2)), both over `PA_r`; definable
  theories are an abstract type `Def3` closed under adding finitely many sentences;
* fact (3) in the form used: for every false sentence `s` there is a true `Π⁰₃` sentence `d` with
  `Tr_𝓑 ⊬ d ∨ s`.

The incompleteness of `PA + w` for true `w`, used in the construction, is derived from the
formalized Theorem 1.5 (`first_incompleteness`) with the identity translation.
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-! ### `𝓑`: Boolean combinations of `Σ⁰₂` and `Π⁰₂` sentences -/

namespace Arith

variable (A : Arith M)

/-- The set `𝓑` of Boolean combinations of `Σ⁰₂` and `Π⁰₂` sentences. -/
inductive InB : A.Sent → Prop
  | sigma {a : A.Sent} : A.IsSigma 2 a → InB a
  | pi {a : A.Sent} : A.IsPi 2 a → InB a
  | neg {a : A.Sent} : InB a → InB (A.neg a)
  | and {a b : A.Sent} : InB a → InB b → InB (A.and a b)

/-- `Tr_𝓑`: the true sentences of `𝓑`. -/
def TrB : A.Sent → Prop := fun β => A.InB β ∧ A.TrueN β

end Arith

/-! ### The interface -/

/-- The data and classical facts of Appendix B; see the module docstring. -/
structure UndefData (A : Arith M) where
  -- syntax: unique readability
  /-- `destruct s = none` iff `s` is prime, `some (inl a)` iff `s = ¬a`, `some (inr (a, b))` iff
  `s = a ∧ b`. -/
  destruct : A.Sent → Option (A.Sent ⊕ (A.Sent × A.Sent))
  destruct_neg : ∀ a, destruct (A.neg a) = some (Sum.inl a)
  destruct_and : ∀ a b, destruct (A.and a b) = some (Sum.inr (a, b))
  destruct_inl : ∀ s a, destruct s = some (Sum.inl a) → s = A.neg a
  destruct_inr : ∀ s a b, destruct s = some (Sum.inr (a, b)) → s = A.and a b
  size : A.Sent → ℕ
  size_neg : ∀ a, size a < size (A.neg a)
  size_and_left : ∀ a b, size a < size (A.and a b)
  size_and_right : ∀ a b, size b < size (A.and a b)
  -- syntax of the hierarchy
  delta0_neg : ∀ a, A.IsSigma 0 (A.neg a) → A.IsSigma 0 a
  delta0_and : ∀ a b, A.IsSigma 0 (A.and a b) → A.IsSigma 0 a ∧ A.IsSigma 0 b
  sigma2_neg_delta0 : ∀ a, A.IsSigma 2 (A.neg a) → A.IsSigma 0 (A.neg a)
  sigma2_and_delta0 : ∀ a b, A.IsSigma 2 (A.and a b) → A.IsSigma 0 (A.and a b)
  pi2_neg_delta0 : ∀ a, A.IsPi 2 (A.neg a) → A.IsSigma 0 (A.neg a)
  pi2_and_delta0 : ∀ a b, A.IsPi 2 (A.and a b) → A.IsSigma 0 (A.and a b)
  /-- `wrap s`, in the manuscript `∀y (y = y ∧ s)`. -/
  wrap : A.Sent → A.Sent
  wrap_prime : ∀ s, destruct (wrap s) = none
  wrap_inj : ∀ s t, wrap s = wrap t → s = t
  wrap_sigma2 : ∀ s, A.IsSigma 2 (wrap s) → A.IsSigma 0 s
  wrap_pi2 : ∀ s, A.IsPi 2 (wrap s) → A.IsSigma 0 s
  wrap_equiv : ∀ s, A.Equiv (wrap s) s
  /-- Each axiom of `Q` is logically equivalent to a sentence of `𝓑`. -/
  Q_equivB : ∀ q, A.Q q → ∃ β, A.InB β ∧ A.Equiv q β
  -- `PA`
  PA : A.Sent → Prop
  PA_sound : ∀ β, PA β → A.TrueN β
  PA_Q : ∀ q, A.Q q → PA q
  PA_ce : ∃ f : ℕ → A.Sent, CompT M f ∧ ∀ β, PA β ↔ ∃ k, f k = β
  /-- The conjunction of the axioms of a finite fragment of `PA`. -/
  PAr : A.Sent
  PA_PAr : A.Deriv PA PAr
  PAr_Q : ∀ q, A.Q q → A.Deriv (A.single PAr) q
  -- `Σ⁰₃`-definable theories, the partial truth definition and the arithmetized completeness theorem
  /-- `Σ⁰₃`-definable theories `τ`; `tau τ β` is the sentence `τ (⌜β⌝)`. -/
  Def3 : Type
  tau : Def3 → A.Sent → A.Sent
  /-- The sentence `Con_τ`. -/
  con : Def3 → A.Sent
  con_true : ∀ τ, A.Consistent (fun β => A.TrueN (tau τ β)) → A.TrueN (con τ)
  /-- `Sat_𝓑`: fact (1). -/
  satDef : Def3
  sat_tarski : ∀ β, A.InB β → A.Deriv (A.single PAr) (A.iff β (tau satDef β))
  sat_inB : ∀ β, A.TrueN (tau satDef β) → A.InB β
  /-- `τ ∨ "v ∈ l"`. -/
  addFin : Def3 → List A.Sent → Def3
  addFin_mem : ∀ τ l β, β ∈ l → A.Deriv (A.single PAr) (tau (addFin τ l) β)
  addFin_of : ∀ τ l β, A.Deriv (A.single (tau τ β)) (tau (addFin τ l) β)
  addFin_true : ∀ τ l β, A.TrueN (tau (addFin τ l) β) → A.TrueN (tau τ β) ∨ β ∈ l
  /-- Fact (2): the arithmetized completeness theorem. For `x_τ := PA_r ∧ Con_τ` there is an
  interpretation `β ↦ β^ι` commuting with the connectives, with `S ⊢ β` implying
  `{x_τ} ∪ S^ι ⊢ β^ι`, and `{x_τ} ⊢ τ (⌜β⌝) → β^ι` for every `β`. -/
  act : ∀ τ, ∃ tr : A.Sent → A.Sent,
    (∀ a, tr (A.neg a) = A.neg (tr a)) ∧ (∀ a b, tr (A.and a b) = A.and (tr a) (tr b)) ∧
    (∀ (S : A.Sent → Prop) β, A.Deriv S β →
      A.Deriv (fun γ => γ = A.and PAr (con τ) ∨ ∃ δ, S δ ∧ γ = tr δ) (tr β)) ∧
    (∀ β, A.Deriv (A.single (A.and PAr (con τ))) (A.imp (tau τ β) (tr β)))
  /-- Fact (3) in the form used: a false `s` and `Tr_𝓑` do not exhaust the true `Π⁰₃` sentences. -/
  pi3_indep : ∀ s, ¬ A.TrueN s →
    ∃ d, A.IsPi 3 d ∧ A.TrueN d ∧ ¬ A.Deriv A.TrB (A.or d s)

namespace UndefData

variable {A : Arith M}

/-! ### Consequences of unique readability -/

/-- `s` is a prime sentence. -/
def Prime (D : UndefData A) (s : A.Sent) : Prop := D.destruct s = none

theorem neg_inj (D : UndefData A) {a b : A.Sent} (h : A.neg a = A.neg b) : a = b := by
  have h1 := D.destruct_neg a
  rw [h, D.destruct_neg b] at h1
  cases h1; rfl

theorem and_inj (D : UndefData A) {a b c d : A.Sent} (h : A.and a b = A.and c d) : a = c ∧ b = d := by
  have h1 := D.destruct_and a b
  rw [h, D.destruct_and c d] at h1
  cases h1; exact ⟨rfl, rfl⟩

theorem neg_ne_and (D : UndefData A) (a b c : A.Sent) : A.neg a ≠ A.and b c := by
  intro h
  have h1 := D.destruct_neg a
  rw [h, D.destruct_and] at h1
  cases h1

theorem prime_ne_neg {D : UndefData A} {p : A.Sent} (hp : D.Prime p) (a : A.Sent) : p ≠ A.neg a := by
  intro h; unfold Prime at hp; rw [h, D.destruct_neg] at hp; cases hp

theorem prime_ne_and {D : UndefData A} {p : A.Sent} (hp : D.Prime p) (a b : A.Sent) : p ≠ A.and a b := by
  intro h; unfold Prime at hp; rw [h, D.destruct_and] at hp; cases hp

theorem cases (D : UndefData A) (s : A.Sent) : D.Prime s ∨ (∃ a, s = A.neg a) ∨ (∃ a b, s = A.and a b) := by
  cases h : D.destruct s with
  | none => exact Or.inl h
  | some x =>
    cases x with
    | inl a => exact Or.inr (Or.inl ⟨a, D.destruct_inl s a h⟩)
    | inr ab => exact Or.inr (Or.inr ⟨ab.1, ab.2, D.destruct_inr s ab.1 ab.2 h⟩)

/-! ### Consequences for the hierarchy -/

/-- A `Σ⁰₂` sentence that is a negation has a `Σ⁰₂` (indeed `Δ₀`) body. -/
theorem sigma2_of_neg (D : UndefData A) {a : A.Sent} (h : A.IsSigma 2 (A.neg a)) : A.IsSigma 2 a :=
  A.sigma_of_delta0 (D.delta0_neg a (D.sigma2_neg_delta0 a h)) 2

theorem sigma2_of_and (D : UndefData A) {a b : A.Sent} (h : A.IsSigma 2 (A.and a b)) :
    A.IsSigma 2 a ∧ A.IsSigma 2 b :=
  ⟨A.sigma_of_delta0 (D.delta0_and a b (D.sigma2_and_delta0 a b h)).1 2,
    A.sigma_of_delta0 (D.delta0_and a b (D.sigma2_and_delta0 a b h)).2 2⟩

theorem pi2_of_neg (D : UndefData A) {a : A.Sent} (h : A.IsPi 2 (A.neg a)) : A.IsPi 2 a :=
  A.pi_of_delta0 (D.delta0_neg a (D.pi2_neg_delta0 a h)) 2

theorem pi2_of_and (D : UndefData A) {a b : A.Sent} (h : A.IsPi 2 (A.and a b)) :
    A.IsPi 2 a ∧ A.IsPi 2 b :=
  ⟨A.pi_of_delta0 (D.delta0_and a b (D.pi2_and_delta0 a b h)).1 2,
    A.pi_of_delta0 (D.delta0_and a b (D.pi2_and_delta0 a b h)).2 2⟩

/-- `Q` is sound, being part of `PA`. -/
theorem Q_sound (D : UndefData A) {q : A.Sent} (hq : A.Q q) : A.TrueN q := D.PA_sound q (D.PA_Q q hq)

theorem trueN_PAr (D : UndefData A) : A.TrueN D.PAr := A.sound _ _ D.PA_sound D.PA_PAr

/-- Soundness of a theory extended by true sentences. -/
theorem consistent_of_true {F : A.Sent → Prop} (hF : ∀ β, F β → A.TrueN β) : A.Consistent F := by
  obtain ⟨α, hα, hαt⟩ := A.exists_true_delta0
  refine ⟨A.neg α, fun h => ?_⟩
  exact (A.trueN_neg α).1 (A.sound F _ hF h) hαt


/-! ### The identity translation and the incompleteness of `PA + w` -/

/-- The identity translation `𝓐 → 𝓐`. -/
def idTrans (A : Arith M) : Translation A.toLanguage A.toLanguage where
  i := fun α => α
  inj := fun h => h
  map_neg := fun _ => rfl
  map_and := fun _ _ => rfl
  map_deriv := fun _ _ h => A.deriv_mono (fun β hβ => ⟨β, hβ, rfl⟩) h

theorem idTrans_isN2 (A : Arith M) : (idTrans A).IsNTranslation 2 := by
  obtain ⟨T, hT⟩ := (compT_id (M := M) (A := A.Sent))
  exact ⟨T, fun σ => hT σ.1⟩

/-- A sequence that never withdraws stabilizes to its range. -/
theorem isStable_of_all_true {B : Type} {N : ℕ → Option (B × Bool)}
    (hN : ∀ k x, N k = some x → x.2 = true) (b : B) :
    IsStable N b ↔ ∃ k, N k = some (b, true) := by
  constructor
  · rintro ⟨m, hm, _⟩; exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, hm, fun n _ s hs => hN n (b, s) hs⟩

/-- The sequence enumerating `PA + w`: `w` first, then the enumeration `f` of `PA`. -/
noncomputable def seqPA (f : ℕ → A.Sent) (w : A.Sent) (k : ℕ) : Option (A.Sent × Bool) :=
  some (if k = 0 then w else f (k - 1), true)

theorem comp_seqPA {f : ℕ → A.Sent} (hf : CompT M f) (w : A.Sent) : Comp M (seqPA f w) := by
  have h1 : CompT M (fun k : ℕ => if k = 0 then w else f (k - 1)) := by
    have := CompT.cases (M := M) (P := fun k : ℕ => k = 0) (f := fun _ => w) (g := fun k => f (k - 1))
      (compSet_eq compT_id (compT_const 0)) (compT_const w) (hf.comp compT_pred)
    exact this.congr fun k => by by_cases h : k = 0 <;> simp [h]
  exact (CompT.pair h1 (compT_const true)).toComp

theorem stab_seqPA (D : UndefData A) {f : ℕ → A.Sent} (hf : ∀ β, D.PA β ↔ ∃ k, f k = β) (w β : A.Sent) :
    Stab (seqPA f w) β ↔ A.ext D.PA w β := by
  show IsStable (seqPA f w) β ↔ _
  rw [isStable_of_all_true (fun k x hx => by
    simp only [seqPA, Option.some.injEq] at hx
    rw [← hx])]
  constructor
  · rintro ⟨k, hk⟩
    simp only [seqPA, Option.some.injEq, Prod.mk.injEq] at hk
    by_cases h : k = 0
    · rw [ite_eq_left h] at hk; exact Or.inr hk.1.symm
    · rw [ite_eq_right h] at hk; exact Or.inl ((hf β).2 ⟨k - 1, hk.1⟩)
  · rintro (hβ | hβ)
    · obtain ⟨k, hk⟩ := (hf β).1 hβ
      exact ⟨k + 1, by simp [seqPA, hk]⟩
    · exact ⟨0, by simp [seqPA, hβ]⟩

/-- `PA + w` is incomplete for true `w`: some true sentence is not provable in it. This is
Theorem 1.5 (3) and (1) for the identity translation and a machine enumerating `PA + w`. -/
theorem exists_true_not_deriv (D : UndefData A) {w : A.Sent} (hw : A.TrueN w) :
    ∃ b, A.TrueN b ∧ ¬ A.Deriv (A.ext D.PA w) b := by
  obtain ⟨f, hfc, hf⟩ := D.PA_ce
  obtain ⟨G, _, hG⟩ := first_incompleteness (idTrans A) (idTrans_isN2 A)
  obtain ⟨T, hT⟩ := comp_seqPA hfc w
  have hTN : StablyComputes (M := M) T (seqPA f w) := stablyComputes_of_computes hT
  have hStab : ∀ β, Stab (seqPA f w) β ↔ A.ext D.PA w β := stab_seqPA D hf w
  have hsound : ∀ β, Stab (seqPA f w) β → A.TrueN β := fun β hβ => by
    rcases (hStab β).1 hβ with h | h
    · exact D.PA_sound β h
    · rw [h]; exact hw
  have hone : (idTrans A).OneConsistent (Stab (seqPA f w)) := by
    refine ⟨fun q hq => ?_, fun σ hσ hd => ?_⟩
    · rw [Translation.derivI_iff]
      exact A.deriv_of_mem ((hStab q).2 (Or.inl (D.PA_Q q hq)))
    · rw [Translation.derivI_iff] at hd
      have ht : A.TrueN σ := A.sound _ _ hsound hd
      obtain ⟨v, hv⟩ := (A.trueN_sigma 0 σ hσ).1 ht
      refine ⟨v, fun h => ?_⟩
      rw [Translation.derivI_iff] at h
      exact (A.trueN_neg _).1 (A.sound _ _ hsound h) hv
  obtain ⟨h1, _, h3⟩ := hG T _ hTN
  refine ⟨G T, h3 hone, fun h => h1 hone ?_⟩
  rw [Translation.derivI_iff]
  exact A.deriv_mono (fun β hβ => (hStab β).2 hβ) h


/-! ### Fixed sentences `⊥`, `⊤`, and `b^ℕ` -/

/-- A fixed true `Δ₀` sentence `a₀`. -/
noncomputable def a0 (A : Arith M) : A.Sent := choose A.exists_true_delta0

/-- `⊥ := a₀ ∧ ¬a₀`. -/
noncomputable def bot (A : Arith M) : A.Sent := A.and (a0 A) (A.neg (a0 A))

/-- `⊤ := ¬⊥`. -/
noncomputable def top (A : Arith M) : A.Sent := A.neg (bot A)

theorem deriv_of_bot {F : A.Sent → Prop} (c : A.Sent) : A.Deriv (A.ext F (bot A)) c :=
  A.deriv_explosion (A.deriv_and_left (A.deriv_ext_self F _)) (A.deriv_and_right (A.deriv_ext_self F _))

theorem deriv_top (F : A.Sent → Prop) : A.Deriv F (top A) :=
  A.deriv_neg_intro fun c => deriv_of_bot c

theorem not_trueN_bot : ¬ A.TrueN (bot A) := by
  intro h
  rw [bot, A.trueN_and, A.trueN_neg] at h
  exact h.2 h.1

theorem trueN_top : A.TrueN (top A) := (A.trueN_neg _).2 not_trueN_bot

theorem trueN_or {a b : A.Sent} : A.TrueN (A.or a b) ↔ A.TrueN a ∨ A.TrueN b := by
  unfold Language.or
  rw [A.trueN_neg, A.trueN_and, A.trueN_neg, A.trueN_neg]
  constructor
  · intro h
    by_cases ha : A.TrueN a
    · exact Or.inl ha
    · exact Or.inr (Classical.byContradiction fun hb => h ⟨ha, hb⟩)
  · rintro (h | h) ⟨h1, h2⟩
    · exact h1 h
    · exact h2 h

theorem trueN_disjList {z : A.Sent} {l : List A.Sent} :
    A.TrueN (A.disjList z l) ↔ A.TrueN z ∨ ∃ a, a ∈ l ∧ A.TrueN a := by
  induction l with
  | nil =>
    simp only [Language.disjList]
    exact ⟨Or.inl, fun h => h.elim id fun ⟨a, ha, _⟩ => by cases ha⟩
  | cons x l ih =>
    simp only [Language.disjList]
    rw [trueN_or, ih]
    constructor
    · rintro (h | h | ⟨a, ha, hat⟩)
      · exact Or.inr ⟨x, List.Mem.head _, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, List.Mem.tail _ ha, hat⟩
    · rintro (h | ⟨a, ha, hat⟩)
      · exact Or.inr (Or.inl h)
      · cases ha with
        | head => exact Or.inl hat
        | tail _ ha' => exact Or.inr (Or.inr ⟨a, ha', hat⟩)

theorem trueN_conjList {z : A.Sent} {l : List A.Sent} :
    A.TrueN (A.conjList z l) ↔ A.TrueN z ∧ ∀ a, a ∈ l → A.TrueN a := by
  induction l with
  | nil =>
    simp only [Language.conjList]
    exact ⟨fun h => ⟨h, fun a ha => by cases ha⟩, fun h => h.1⟩
  | cons x l ih =>
    simp only [Language.conjList]
    rw [A.trueN_and, ih]
    constructor
    · rintro ⟨hx, hz, hl⟩
      refine ⟨hz, fun a ha => ?_⟩
      cases ha with
      | head => exact hx
      | tail _ ha' => exact hl a ha'
    · rintro ⟨hz, hl⟩
      exact ⟨hl x (List.Mem.head _), hz, fun a ha => hl a (List.Mem.tail _ ha)⟩

/-- `b^ℕ`: `b` if true, `¬b` otherwise. -/
noncomputable def bN (A : Arith M) (b : A.Sent) : A.Sent := if A.TrueN b then b else A.neg b

theorem trueN_bN (b : A.Sent) : A.TrueN (bN A b) := by
  unfold bN
  by_cases h : A.TrueN b
  · rw [ite_eq_left h]; exact h
  · rw [ite_eq_right h]; exact (A.trueN_neg b).2 h

theorem bN_of_true {b : A.Sent} (h : A.TrueN b) : bN A b = b := by unfold bN; rw [ite_eq_left h]

theorem bN_of_false {b : A.Sent} (h : ¬ A.TrueN b) : bN A b = A.neg b := by unfold bN; rw [ite_eq_right h]

/-- The sentences with code `≤ n`. -/
noncomputable def firstN (A : Arith M) (n : ℕ) : List A.Sent :=
  (List.range (n + 1)).filterMap (Enc.decode (M := M) A.Sent)

theorem mem_firstN {n : ℕ} {b : A.Sent} : b ∈ firstN A n ↔ e M b ≤ n := by
  unfold firstN
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hdk⟩
    rw [List.mem_range] at hk
    rw [Enc.decode_eq_some_iff] at hdk
    omega
  · intro h
    exact ⟨e M b, List.mem_range.2 (by omega), Enc.decode_e b⟩


/-! ### The construction: stages `(d_n, ε_n, x_n, ι_n)` -/

/-- The data produced at stage `n`. -/
structure Stage (A : Arith M) where
  d : A.Sent
  eps : A.Sent
  x : A.Sent
  tr : A.Sent → A.Sent

/-- Choice of a sentence with a property, if one exists (`a₀` otherwise). -/
noncomputable def pick (A : Arith M) (P : A.Sent → Prop) : A.Sent := @Classical.epsilon _ ⟨a0 A⟩ P

theorem pick_spec {P : A.Sent → Prop} (h : ∃ b, P b) : P (pick A P) := by
  haveI : Nonempty A.Sent := ⟨a0 A⟩
  exact Classical.epsilon_spec h

section Stages

variable (D : UndefData A)

/-- The true finite part at stage `n`: `b^ℕ` for the sentences `b` with code `≤ n`, and `¬ε_m` for
`m < n`. -/
noncomputable def lTp (n : ℕ) (prev : List (Stage A)) : List A.Sent :=
  (firstN A n).map (bN A) ++ prev.map (fun st => A.neg st.eps)

/-- `ρ_n` of the manuscript: the disjunction of the negations of the sentences of `lTp`. -/
noncomputable def sNp (n : ℕ) (prev : List (Stage A)) : A.Sent :=
  A.disjList (bot A) ((lTp n prev).map A.neg)

/-- `d_n`. -/
noncomputable def dNp (n : ℕ) (prev : List (Stage A)) : A.Sent :=
  pick A fun d => A.IsPi 3 d ∧ A.TrueN d ∧ ¬ A.Deriv A.TrB (A.or d (sNp n prev))

/-- `τ_n`. -/
noncomputable def tauNp (n : ℕ) (prev : List (Stage A)) : D.Def3 :=
  D.addFin D.satDef (lTp n prev ++ [A.neg (dNp n prev)])

/-- `x_n := PA_r ∧ Con_{τ_n}`. -/
noncomputable def xNp (n : ℕ) (prev : List (Stage A)) : A.Sent := A.and D.PAr (D.con (tauNp D n prev))

/-- `w_n`. -/
noncomputable def wNp (n : ℕ) (prev : List (Stage A)) : A.Sent :=
  A.conjList (top A) (xNp D n prev :: (lTp n prev ++ prev.map Stage.d ++ [dNp n prev]))

/-- The true sentence `b_{t(n)}` not provable in `PA + w_n`. -/
noncomputable def btNp (n : ℕ) (prev : List (Stage A)) : A.Sent :=
  pick A fun b => A.TrueN b ∧ ¬ A.Deriv (A.ext D.PA (wNp D n prev)) b

/-- Stage `n`, given the earlier stages. -/
noncomputable def step (n : ℕ) (prev : List (Stage A)) : Stage A where
  d := dNp n prev
  eps := A.and (wNp D n prev) (A.neg (btNp D n prev))
  x := xNp D n prev
  tr := choose (D.act (tauNp D n prev))

/-- The stages `0, …, n - 1`. -/
noncomputable def stages : ℕ → List (Stage A)
  | 0 => []
  | n + 1 => stages n ++ [step D n (stages n)]

/-- Stage `n`. -/
noncomputable def stage (n : ℕ) : Stage A := step D n (stages D n)

theorem stages_eq (n : ℕ) : stages D n = (List.range n).map (stage D) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show stages D n ++ [stage D n] = _
    rw [ih, List.range_succ, List.map_append]
    rfl

/-- Abbreviations. -/
noncomputable def dN (n : ℕ) : A.Sent := (stage D n).d
noncomputable def epsN (n : ℕ) : A.Sent := (stage D n).eps
noncomputable def xN (n : ℕ) : A.Sent := (stage D n).x
noncomputable def trN (n : ℕ) : A.Sent → A.Sent := (stage D n).tr
noncomputable def lT (n : ℕ) : List A.Sent := lTp n (stages D n)
noncomputable def sN (n : ℕ) : A.Sent := sNp n (stages D n)
noncomputable def tauN (n : ℕ) : D.Def3 := tauNp D n (stages D n)
noncomputable def wN (n : ℕ) : A.Sent := wNp D n (stages D n)
noncomputable def btN (n : ℕ) : A.Sent := btNp D n (stages D n)

theorem dN_eq (n : ℕ) : dN D n = dNp n (stages D n) := rfl
theorem epsN_eq (n : ℕ) : epsN D n = A.and (wN D n) (A.neg (btN D n)) := rfl
theorem xN_eq (n : ℕ) : xN D n = A.and D.PAr (D.con (tauN D n)) := rfl
theorem trN_eq (n : ℕ) : trN D n = choose (D.act (tauN D n)) := rfl
theorem tauN_eq (n : ℕ) : tauN D n = D.addFin D.satDef (lT D n ++ [A.neg (dN D n)]) := rfl
theorem map_d_stages (n : ℕ) : (stages D n).map Stage.d = (List.range n).map (dN D) := by
  rw [stages_eq, List.map_map]; rfl

theorem map_eps_stages (n : ℕ) :
    (stages D n).map (fun st => A.neg st.eps) = (List.range n).map (fun m => A.neg (epsN D m)) := by
  rw [stages_eq, List.map_map]; rfl

theorem wN_eq (n : ℕ) :
    wN D n = A.conjList (top A) (xN D n :: (lT D n ++ (List.range n).map (dN D) ++ [dN D n])) := by
  show A.conjList (top A) (xN D n :: (lT D n ++ (stages D n).map Stage.d ++ [dN D n])) = _
  rw [map_d_stages]
theorem sN_eq (n : ℕ) : sN D n = A.disjList (bot A) ((lT D n).map A.neg) := rfl
theorem lT_eq (n : ℕ) : lT D n = (firstN A n).map (bN A) ++ (List.range n).map (fun m => A.neg (epsN D m)) := by
  show (firstN A n).map (bN A) ++ (stages D n).map (fun st => A.neg st.eps) = _
  rw [map_eps_stages]

theorem mem_lT {n : ℕ} {b : A.Sent} :
    b ∈ lT D n ↔ (∃ c, e M c ≤ n ∧ b = bN A c) ∨ ∃ m, m < n ∧ b = A.neg (epsN D m) := by
  rw [lT_eq, List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact Or.inl ⟨c, mem_firstN.1 hc, rfl⟩
    · exact Or.inr ⟨m, List.mem_range.1 hm, rfl⟩
  · rintro (⟨c, hc, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact Or.inl ⟨c, mem_firstN.2 hc, rfl⟩
    · exact Or.inr ⟨m, List.mem_range.2 hm, rfl⟩

/-- The specification of `ι_n` (fact (2)). -/
theorem trN_spec (n : ℕ) :
    (∀ a, trN D n (A.neg a) = A.neg (trN D n a)) ∧
    (∀ a b, trN D n (A.and a b) = A.and (trN D n a) (trN D n b)) ∧
    (∀ (S : A.Sent → Prop) β, A.Deriv S β →
      A.Deriv (fun γ => γ = xN D n ∨ ∃ δ, S δ ∧ γ = trN D n δ) (trN D n β)) ∧
    (∀ β, A.Deriv (A.single (xN D n)) (A.imp (D.tau (tauN D n) β) (trN D n β))) :=
  choose_spec (D.act (tauN D n))

theorem trN_neg (n : ℕ) (a : A.Sent) : trN D n (A.neg a) = A.neg (trN D n a) := (trN_spec D n).1 a
theorem trN_and (n : ℕ) (a b : A.Sent) : trN D n (A.and a b) = A.and (trN D n a) (trN D n b) :=
  (trN_spec D n).2.1 a b

/-- `⊢ b` gives `{x_n} ⊢ b^{ι_n}`. -/
theorem x_deriv_tr_of_valid (n : ℕ) {b : A.Sent} (h : A.Valid b) :
    A.Deriv (A.single (xN D n)) (trN D n b) := by
  have := (trN_spec D n).2.2.1 _ b h
  refine A.deriv_mono (fun γ hγ => ?_) this
  rcases hγ with hγ | ⟨δ, hδ, _⟩
  · exact hγ
  · exact hδ.elim

/-- `{a} ⊢ b` gives `{x_n} ⊢ a^{ι_n} → b^{ι_n}`. -/
theorem x_deriv_tr_imp (n : ℕ) {a b : A.Sent} (h : A.Deriv (A.single a) b) :
    A.Deriv (A.single (xN D n)) (A.imp (trN D n a) (trN D n b)) := by
  have := (trN_spec D n).2.2.1 _ b h
  refine Language.deriv_imp_intro (A.deriv_mono (fun γ hγ => ?_) this)
  rcases hγ with hγ | ⟨δ, hδ, hγ⟩
  · exact Or.inl hγ
  · exact Or.inr (by rw [hγ, show δ = a from hδ])

/-- `{x_n} ⊢ β^{ι_n}` for `β` in the finite part of `U_n`. -/
theorem x_deriv_tr_of_mem (n : ℕ) {β : A.Sent} (h : β ∈ lT D n ++ [A.neg (dN D n)]) :
    A.Deriv (A.single (xN D n)) (trN D n β) := by
  have h1 : A.Deriv (A.single (xN D n)) D.PAr := A.deriv_and_left (A.deriv_single_self _)
  have h2 : A.Deriv (A.single (xN D n)) (D.tau (tauN D n) β) :=
    A.deriv_of_single h1 (D.addFin_mem _ _ β h)
  exact Language.deriv_mp ((trN_spec D n).2.2.2 β) h2

/-- Fibre preservation: `{x_n} ⊢ β ↔ β^{ι_n}` for `β ∈ 𝓑`. -/
theorem x_deriv_iff_tr_of_inB (n : ℕ) {β : A.Sent} (hβ : A.InB β) :
    A.Deriv (A.single (xN D n)) (A.iff β (trN D n β)) := by
  have hPAr : A.Deriv (A.single (xN D n)) D.PAr := A.deriv_and_left (A.deriv_single_self _)
  -- `{x_n} ⊢ γ → γ^{ι_n}` for `γ ∈ 𝓑`
  have key : ∀ γ, A.InB γ → A.Deriv (A.single (xN D n)) (A.imp γ (trN D n γ)) := fun γ hγ => by
    have t1 : A.Deriv (A.single (xN D n)) (A.iff γ (D.tau D.satDef γ)) :=
      A.deriv_of_single hPAr (D.sat_tarski γ hγ)
    have t2 : A.Deriv (A.single (xN D n)) (A.imp (D.tau D.satDef γ) (D.tau (tauN D n) γ)) :=
      Language.deriv_imp_intro (A.deriv_ext_of_single (D.addFin_of D.satDef _ γ))
    exact Language.deriv_imp_trans (A.deriv_and_left t1)
      (Language.deriv_imp_trans t2 ((trN_spec D n).2.2.2 γ))
  refine Language.deriv_iff_intro (Language.deriv_ext_of_imp (key β hβ)) ?_
  have h2 := key (A.neg β) (Arith.InB.neg hβ)
  rw [trN_neg] at h2
  have h3 := Language.deriv_imp_neg_of_neg h2
  exact A.deriv_dne (Language.deriv_mp (A.deriv_ext_of _ h3) (A.deriv_dni (A.deriv_ext_self _ _)))

end Stages


/-! ### Truth of the derived connectives -/

theorem trueN_imp {a b : A.Sent} : A.TrueN (A.imp a b) ↔ (A.TrueN a → A.TrueN b) := by
  unfold Language.imp
  rw [A.trueN_neg, A.trueN_and, A.trueN_neg]
  constructor
  · intro h ha; exact Classical.byContradiction fun hb => h ⟨ha, hb⟩
  · rintro h ⟨ha, hb⟩; exact hb (h ha)

theorem trueN_iff {a b : A.Sent} : A.TrueN (A.iff a b) ↔ (A.TrueN a ↔ A.TrueN b) := by
  unfold Language.iff
  rw [A.trueN_and, trueN_imp, trueN_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ### The invariant of the construction -/

section Invariant

variable (D : UndefData A)

/-- The invariant at stage `n`: `d_n`, `x_n`, `w_n`, `b_{t(n)}` are true, `PA + w_n ⊬ b_{t(n)}`, and
`ε_n` is false. -/
def Good (n : ℕ) : Prop :=
  A.TrueN (dN D n) ∧ A.TrueN (xN D n) ∧ A.TrueN (wN D n) ∧ A.TrueN (btN D n) ∧
    ¬ A.Deriv (A.ext D.PA (wN D n)) (btN D n) ∧ ¬ A.TrueN (epsN D n)

theorem trueN_lT_of (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (epsN D m)) :
    ∀ b, b ∈ lT D n → A.TrueN b := by
  intro b hb
  rcases (mem_lT D).1 hb with ⟨c, _, rfl⟩ | ⟨m, hm, rfl⟩
  · exact trueN_bN c
  · exact (A.trueN_neg _).2 (ih m hm)

theorem not_trueN_sN (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (epsN D m)) : ¬ A.TrueN (sN D n) := by
  rw [sN_eq, trueN_disjList]
  rintro (h | ⟨a, ha, hat⟩)
  · exact not_trueN_bot h
  · rw [List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact (A.trueN_neg b).1 hat (trueN_lT_of D n ih b hb)

theorem dN_spec (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (epsN D m)) :
    A.IsPi 3 (dN D n) ∧ A.TrueN (dN D n) ∧ ¬ A.Deriv A.TrB (A.or (dN D n) (sN D n)) :=
  pick_spec (D.pi3_indep _ (not_trueN_sN D n ih))

/-- `U_n` is consistent. -/
theorem consistent_U (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (epsN D m)) :
    A.Consistent (fun β => A.TrueN (D.tau (tauN D n) β)) := by
  refine ⟨dN D n, fun h => ?_⟩
  have hsub : ∀ β, A.TrueN (D.tau (tauN D n) β) →
      A.ext (A.extList A.TrB (lT D n)) (A.neg (dN D n)) β := by
    intro β hβ
    rw [tauN_eq] at hβ
    rcases D.addFin_true _ _ β hβ with h1 | h1
    · have hB := D.sat_inB β h1
      have hT : A.TrueN (A.iff β (D.tau D.satDef β)) :=
        A.sound _ _ (fun γ (hγ : γ = D.PAr) => by rw [hγ]; exact D.trueN_PAr) (D.sat_tarski β hB)
      exact Or.inl (Or.inl ⟨hB, (trueN_iff.1 hT).2 h1⟩)
    · rw [List.mem_append, List.mem_singleton] at h1
      rcases h1 with h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1
  have h2 : A.Deriv (A.ext (A.extList A.TrB (lT D n)) (A.neg (dN D n))) (dN D n) :=
    A.deriv_mono hsub h
  have h3 : A.Deriv (A.extList A.TrB (lT D n)) (dN D n) :=
    A.deriv_dne (Language.deriv_neg_of h2 (A.deriv_ext_self _ _))
  have h4 := Language.deriv_or_disjList_neg (z := bot A) h3
  exact (dN_spec D n ih).2.2 (by rw [sN_eq]; exact h4)

theorem trueN_xN_of (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (epsN D m)) : A.TrueN (xN D n) := by
  rw [xN_eq, A.trueN_and]
  exact ⟨D.trueN_PAr, D.con_true _ (consistent_U D n ih)⟩

theorem trueN_wN_of (n : ℕ) (ih : ∀ m, m < n → Good D m) : A.TrueN (wN D n) := by
  have ihe : ∀ m, m < n → ¬ A.TrueN (epsN D m) := fun m hm => (ih m hm).2.2.2.2.2
  rw [wN_eq, trueN_conjList]
  refine ⟨trueN_top, fun a ha => ?_⟩
  rw [List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact trueN_xN_of D n ihe
  · rw [List.mem_append, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | ha
    · exact trueN_lT_of D n ihe a ha
    · rw [List.mem_map] at ha
      obtain ⟨m, hm, rfl⟩ := ha
      exact (ih m (List.mem_range.1 hm)).1
    · rw [ha]; exact (dN_spec D n ihe).2.1

theorem btN_spec (n : ℕ) (hw : A.TrueN (wN D n)) :
    A.TrueN (btN D n) ∧ ¬ A.Deriv (A.ext D.PA (wN D n)) (btN D n) :=
  pick_spec (exists_true_not_deriv D hw)

theorem good_aux : ∀ n m, m < n → Good D m := by
  intro n
  induction n with
  | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
  | succ n ih =>
    intro m hm
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with h | rfl
    · exact ih m h
    · have ihe : ∀ k, k < m → ¬ A.TrueN (epsN D k) := fun k hk => (ih k hk).2.2.2.2.2
      have hd := dN_spec D m ihe
      have hx := trueN_xN_of D m ihe
      have hw := trueN_wN_of D m ih
      have hb := btN_spec D m hw
      refine ⟨hd.2.1, hx, hw, hb.1, hb.2, fun h => ?_⟩
      rw [epsN_eq, A.trueN_and, A.trueN_neg] at h
      exact h.2 hb.1

theorem good (n : ℕ) : Good D n := good_aux D (n + 1) n (Nat.lt_succ_self n)

theorem not_trueN_epsN (n : ℕ) : ¬ A.TrueN (epsN D n) := (good D n).2.2.2.2.2
theorem trueN_dN (n : ℕ) : A.TrueN (dN D n) := (good D n).1
theorem trueN_xN (n : ℕ) : A.TrueN (xN D n) := (good D n).2.1
theorem trueN_wN (n : ℕ) : A.TrueN (wN D n) := (good D n).2.2.1
theorem trueN_btN (n : ℕ) : A.TrueN (btN D n) := (good D n).2.2.2.1
theorem not_deriv_btN (n : ℕ) : ¬ A.Deriv (A.ext D.PA (wN D n)) (btN D n) := (good D n).2.2.2.2.1

/-- `PA + ε_n` is consistent. -/
theorem consistent_PA_epsN (n : ℕ) : A.Consistent (A.ext D.PA (epsN D n)) := by
  refine ⟨btN D n, fun h => not_deriv_btN D n ?_⟩
  have h1 : A.Deriv (A.ext (A.ext D.PA (wN D n)) (A.neg (btN D n))) (btN D n) := by
    refine Language.deriv_cut_ext (a := epsN D n) ?_ ?_
    · exact A.deriv_and_intro (A.deriv_ext_of _ (A.deriv_ext_self _ _)) (A.deriv_ext_self _ _)
    · exact A.deriv_mono (fun β hβ => by
        rcases hβ with hβ | hβ
        · exact Or.inl (Or.inl (Or.inl hβ))
        · exact Or.inr hβ) h
  exact A.deriv_dne (Language.deriv_neg_of h1 (A.deriv_ext_self _ _))

end Invariant


/-! ### Properties of `ε_n` -/

section Properties

variable (D : UndefData A)

theorem eps_deriv_wN (n : ℕ) : A.Deriv (A.single (epsN D n)) (wN D n) :=
  A.deriv_and_left (A.deriv_single_self (epsN D n))

theorem eps_deriv_conj (n : ℕ) {c : A.Sent}
    (hc : c ∈ xN D n :: (lT D n ++ (List.range n).map (dN D) ++ [dN D n])) :
    A.Deriv (A.single (epsN D n)) c := by
  have h := eps_deriv_wN D n
  rw [wN_eq] at h
  exact Language.deriv_conjList_of_mem h hc

theorem eps_deriv_x (n : ℕ) : A.Deriv (A.single (epsN D n)) (xN D n) :=
  eps_deriv_conj D n (List.Mem.head _)

theorem eps_deriv_lT (n : ℕ) {c : A.Sent} (hc : c ∈ lT D n) : A.Deriv (A.single (epsN D n)) c :=
  eps_deriv_conj D n (List.Mem.tail _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hc)))))

theorem eps_deriv_bN (n : ℕ) {c : A.Sent} (hc : e M c ≤ n) : A.Deriv (A.single (epsN D n)) (bN A c) :=
  eps_deriv_lT D n ((mem_lT D).2 (Or.inl ⟨c, hc, rfl⟩))

theorem eps_deriv_neg_eps_lt (n : ℕ) {m : ℕ} (hm : m < n) :
    A.Deriv (A.single (epsN D n)) (A.neg (epsN D m)) :=
  eps_deriv_lT D n ((mem_lT D).2 (Or.inr ⟨m, hm, rfl⟩))

theorem eps_deriv_d_lt (n : ℕ) {m : ℕ} (hm : m < n) : A.Deriv (A.single (epsN D n)) (dN D m) :=
  eps_deriv_conj D n (List.Mem.tail _ (List.mem_append.2 (Or.inl (List.mem_append.2
    (Or.inr (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩))))))

theorem eps_deriv_d (n : ℕ) : A.Deriv (A.single (epsN D n)) (dN D n) :=
  eps_deriv_conj D n (List.Mem.tail _ (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))))

/-- `{ε_n} ⊢ c` whenever `{x_n} ⊢ c`. -/
theorem eps_deriv_of_x (n : ℕ) {c : A.Sent} (h : A.Deriv (A.single (xN D n)) c) :
    A.Deriv (A.single (epsN D n)) c :=
  A.deriv_of_single (eps_deriv_x D n) h

theorem x_deriv_tr_neg_d (n : ℕ) : A.Deriv (A.single (xN D n)) (A.neg (trN D n (dN D n))) := by
  have := x_deriv_tr_of_mem D n (β := A.neg (dN D n))
    (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
  rwa [trN_neg] at this

theorem x_deriv_tr_neg_eps_lt (n : ℕ) {m : ℕ} (hm : m < n) :
    A.Deriv (A.single (xN D n)) (A.neg (trN D n (epsN D m))) := by
  have := x_deriv_tr_of_mem D n (β := A.neg (epsN D m))
    (List.mem_append.2 (Or.inl ((mem_lT D).2 (Or.inr ⟨m, hm, rfl⟩))))
  rwa [trN_neg] at this

theorem x_deriv_tr_bN (n : ℕ) {c : A.Sent} (hc : e M c ≤ n) :
    A.Deriv (A.single (xN D n)) (trN D n (bN A c)) :=
  x_deriv_tr_of_mem D n (List.mem_append.2 (Or.inl ((mem_lT D).2 (Or.inl ⟨c, hc, rfl⟩))))

/-- Equation (B.8): `{ε_n} ⊢ b ↔ b^{ι_n}` for `k(b) ≤ n`. -/
theorem eps_deriv_iff_tr (n : ℕ) {b : A.Sent} (hb : e M b ≤ n) :
    A.Deriv (A.single (epsN D n)) (A.iff b (trN D n b)) := by
  have h1 := eps_deriv_bN D n hb
  have h2 := eps_deriv_of_x D n (x_deriv_tr_bN D n hb)
  by_cases ht : A.TrueN b
  · rw [bN_of_true ht] at h1 h2
    exact Language.deriv_iff_of_both h1 h2
  · rw [bN_of_false ht, trN_neg] at h2
    rw [bN_of_false ht] at h1
    exact Language.deriv_iff_of_both_neg h1 h2

/-- The `ε_n` are pairwise inconsistent. -/
theorem eps_deriv_neg_eps (n : ℕ) {m : ℕ} (hm : m ≠ n) :
    A.Deriv (A.single (epsN D n)) (A.neg (epsN D m)) := by
  rcases Nat.lt_or_gt_of_ne hm with h | h
  · exact eps_deriv_neg_eps_lt D n h
  · have := eps_deriv_neg_eps_lt D m h
    exact Language.deriv_neg_of (A.deriv_ext_of _ (A.deriv_single_self _)) (A.deriv_ext_of_single this)

/-- `{ε_n}` is consistent. -/
theorem consistent_eps (n : ℕ) : A.Consistent (A.single (epsN D n)) := by
  obtain ⟨c, hc⟩ := consistent_PA_epsN D n
  exact ⟨c, fun h => hc (A.deriv_mono (fun β (hβ : β = epsN D n) => Or.inr hβ) h)⟩

theorem lt_code_eps (n : ℕ) : n < e M (epsN D n) := by
  refine Classical.byContradiction fun h => ?_
  have h1 := eps_deriv_bN D n (c := epsN D n) (Nat.le_of_not_lt h)
  rw [bN_of_false (not_trueN_epsN D n)] at h1
  obtain ⟨c, hc⟩ := consistent_eps D n
  exact hc (A.deriv_explosion (A.deriv_single_self _) h1)

theorem lt_code_neg_eps (n : ℕ) : n < e M (A.neg (epsN D n)) := by
  refine Classical.byContradiction fun h => ?_
  have h1 := eps_deriv_bN D n (c := A.neg (epsN D n)) (Nat.le_of_not_lt h)
  rw [bN_of_true ((A.trueN_neg _).2 (not_trueN_epsN D n))] at h1
  obtain ⟨c, hc⟩ := consistent_eps D n
  exact hc (A.deriv_explosion (A.deriv_single_self _) h1)

end Properties


/-! ### The map `θ` -/

section Theta

variable (D : UndefData A) (X : ℕ → Prop)

/-- `X_K`: the elements of `X` below `K`. -/
noncomputable def Xlist (K : ℕ) : List ℕ := (List.range K).filter (fun n => decide (X n))

theorem mem_Xlist {K n : ℕ} : n ∈ Xlist X K ↔ n < K ∧ X n := by
  unfold Xlist
  rw [List.mem_filter, List.mem_range, decide_eq_true_iff]

theorem Xlist_succ (K : ℕ) : Xlist X (K + 1) = Xlist X K ++ (if X K then [K] else []) := by
  unfold Xlist
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : X K
  · simp [h]
  · simp [h]

/-- `D_K := ⋁_{n ∈ X_K} ε_n`. -/
noncomputable def bigD (K : ℕ) : A.Sent := A.disjList (bot A) ((Xlist X K).map (epsN D))

/-- `θ_K (b)`. -/
noncomputable def thetaK (K : ℕ) (b : A.Sent) : A.Sent :=
  A.or (A.and b (A.neg (bigD D X K)))
    (A.disjList (bot A) ((Xlist X K).map (fun n => A.and (trN D n b) (epsN D n))))

/-- `θ (b) := θ_{k(b)+1} (b)`. -/
noncomputable def theta (b : A.Sent) : A.Sent := thetaK D X (e M b + 1) b

theorem eps_deriv_bigD {K n : ℕ} (hn : n ∈ Xlist X K) : A.Deriv (A.single (epsN D n)) (bigD D X K) :=
  Language.deriv_disjList_of_mem (List.mem_map.2 ⟨n, hn, rfl⟩) (A.deriv_single_self _)

theorem deriv_neg_disjList {F : A.Sent → Prop} {z : A.Sent} {l : List A.Sent}
    (hl : ∀ a, a ∈ l → A.Deriv F (A.neg a)) (hz : A.Deriv F (A.neg z)) :
    A.Deriv F (A.neg (A.disjList z l)) := by
  refine Language.deriv_neg_of (b := z) ?_ (A.deriv_ext_of _ hz)
  refine Language.deriv_disjList_elim (A.deriv_ext_self F _) (fun a ha => ?_) (A.deriv_ext_self _ _)
  exact A.deriv_explosion (A.deriv_ext_self _ _) (A.deriv_ext_of _ (A.deriv_ext_of _ (hl a ha)))

/-- `{ε_n} ⊢ ¬D_K` when `n ∉ X_K`. -/
theorem eps_deriv_neg_bigD {K n : ℕ} (hn : n ∉ Xlist X K) :
    A.Deriv (A.single (epsN D n)) (A.neg (bigD D X K)) := by
  refine deriv_neg_disjList (fun a ha => ?_) ?_
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    exact eps_deriv_neg_eps D n (fun h => hn (h ▸ hm))
  · exact A.deriv_neg_intro fun c => deriv_of_bot c

/-- `θ_K (b)` is `b^{ι_n}` on the models of `ε_n`, `n ∈ X_K`. -/
theorem thetaK_pos {K n : ℕ} (hn : n ∈ Xlist X K) (b : A.Sent) :
    A.Deriv (A.single (epsN D n)) (A.iff (thetaK D X K b) (trN D n b)) := by
  refine Language.deriv_iff_intro ?_ ?_
  · refine Language.deriv_or_elim' ?_ ?_
    · exact A.deriv_explosion (A.deriv_ext_of _ (eps_deriv_bigD D X hn))
        (A.deriv_and_right (A.deriv_ext_self _ _))
    · refine Language.deriv_disjList_elim (A.deriv_ext_self _ _) (fun a ha => ?_) (deriv_of_bot _)
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
      by_cases hmn : m = n
      · rw [hmn]; exact A.deriv_and_left (A.deriv_ext_self _ _)
      · exact A.deriv_explosion (A.deriv_and_right (A.deriv_ext_self _ _))
          (A.deriv_ext_of _ (A.deriv_ext_of _ (eps_deriv_neg_eps D n hmn)))
  · refine Language.deriv_or_inr _ (Language.deriv_disjList_of_mem (List.mem_map.2 ⟨n, hn, rfl⟩) ?_)
    exact A.deriv_and_intro (A.deriv_ext_self _ _) (A.deriv_ext_of _ (A.deriv_single_self _))

/-- `θ_K (b)` is `b` on the models of `¬D_K`. -/
theorem thetaK_neg (K : ℕ) (b : A.Sent) :
    A.Deriv (A.single (A.neg (bigD D X K))) (A.iff (thetaK D X K b) b) := by
  refine Language.deriv_iff_intro ?_ ?_
  · refine Language.deriv_or_elim' (A.deriv_and_left (A.deriv_ext_self _ _)) ?_
    refine Language.deriv_disjList_elim (A.deriv_ext_self _ _) (fun a ha => ?_) (deriv_of_bot _)
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    refine A.deriv_explosion (α := bigD D X K) ?_ ?_
    · exact A.deriv_of_single (A.deriv_and_right (A.deriv_ext_self _ _)) (eps_deriv_bigD D X hm)
    · exact A.deriv_ext_of _ (A.deriv_ext_of _ (A.deriv_single_self _))
  · exact Language.deriv_or_inl _ (A.deriv_and_intro (A.deriv_ext_self _ _)
      (A.deriv_ext_of _ (A.deriv_single_self _)))

/-- Case analysis along `X_K`. -/
theorem thetaK_cases {F : A.Sent → Prop} {K : ℕ} {c : A.Sent}
    (h1 : ∀ n, n ∈ Xlist X K → A.Deriv (A.ext F (epsN D n)) c)
    (h2 : A.Deriv (A.ext F (A.neg (bigD D X K))) c) : A.Deriv F c := by
  refine Language.deriv_cases (c := bigD D X K) ?_ h2
  refine Language.deriv_disjList_elim (A.deriv_ext_self F _) (fun a ha => ?_) (deriv_of_bot _)
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 ha
  exact Language.deriv_ext_swap (A.deriv_ext_of _ (h1 n hn))

theorem thetaK_and (K : ℕ) (a b : A.Sent) :
    A.Valid (A.iff (thetaK D X K (A.and a b)) (A.and (thetaK D X K a) (thetaK D X K b))) := by
  refine thetaK_cases D X (K := K) (fun n hn => ?_) ?_
  · have t1 := A.deriv_ext_of_single (F := A.empty) (thetaK_pos D X hn (A.and a b))
    have t2 := A.deriv_ext_of_single (F := A.empty) (thetaK_pos D X hn a)
    have t3 := A.deriv_ext_of_single (F := A.empty) (thetaK_pos D X hn b)
    rw [trN_and] at t1
    exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm (Language.deriv_iff_and t2 t3))
  · have t1 := A.deriv_ext_of_single (F := A.empty) (thetaK_neg D X K (A.and a b))
    have t2 := A.deriv_ext_of_single (F := A.empty) (thetaK_neg D X K a)
    have t3 := A.deriv_ext_of_single (F := A.empty) (thetaK_neg D X K b)
    exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm (Language.deriv_iff_and t2 t3))

theorem thetaK_negc (K : ℕ) (a : A.Sent) :
    A.Valid (A.iff (thetaK D X K (A.neg a)) (A.neg (thetaK D X K a))) := by
  refine thetaK_cases D X (K := K) (fun n hn => ?_) ?_
  · have t1 := A.deriv_ext_of_single (F := A.empty) (thetaK_pos D X hn (A.neg a))
    have t2 := A.deriv_ext_of_single (F := A.empty) (thetaK_pos D X hn a)
    rw [trN_neg] at t1
    exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm (Language.deriv_iff_neg t2))
  · have t1 := A.deriv_ext_of_single (F := A.empty) (thetaK_neg D X K (A.neg a))
    have t2 := A.deriv_ext_of_single (F := A.empty) (thetaK_neg D X K a)
    exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm (Language.deriv_iff_neg t2))

theorem bigD_mono {K K' : ℕ} (h : K ≤ K') {F : A.Sent → Prop} (hd : A.Deriv F (bigD D X K)) :
    A.Deriv F (bigD D X K') :=
  Language.deriv_disjList_mono (fun a ha => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 ha
    rw [mem_Xlist] at hn
    exact List.mem_map.2 ⟨n, (mem_Xlist X).2 ⟨Nat.lt_of_lt_of_le hn.1 h, hn.2⟩, rfl⟩) hd

/-- `θ_K (b)` and `θ_{K+1} (b)` are equivalent for `k(b) ≤ K`. -/
theorem thetaK_succ {K : ℕ} {b : A.Sent} (hb : e M b ≤ K) :
    A.Valid (A.iff (thetaK D X K b) (thetaK D X (K + 1) b)) := by
  refine thetaK_cases D X (K := K + 1) (fun n hn => ?_) ?_
  · by_cases hnK : n ∈ Xlist X K
    · have t1 := A.deriv_ext_of_single (F := A.empty) (thetaK_pos D X hnK b)
      have t2 := A.deriv_ext_of_single (F := A.empty) (thetaK_pos D X hn b)
      exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm t2)
    · -- then `n = K`
      have hnK' : n = K := by
        rw [mem_Xlist] at hn hnK
        exact Classical.byContradiction fun h => hnK ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn.1) h, hn.2⟩
      have t1 : A.Deriv (A.single (epsN D n)) (A.iff (thetaK D X K b) b) :=
        A.deriv_of_single (eps_deriv_neg_bigD D X hnK) (thetaK_neg D X K b)
      have t2 : A.Deriv (A.single (epsN D n)) (A.iff b (trN D n b)) :=
        eps_deriv_iff_tr D n (hnK' ▸ hb)
      have t3 := thetaK_pos D X hn b
      exact A.deriv_ext_of_single (F := A.empty)
        (Language.deriv_iff_trans t1 (Language.deriv_iff_trans t2 (Language.deriv_iff_symm t3)))
  · have hK : A.Deriv (A.single (A.neg (bigD D X (K + 1)))) (A.neg (bigD D X K)) :=
      Language.deriv_neg_of (bigD_mono D X (Nat.le_succ K) (A.deriv_ext_self _ _))
        (A.deriv_ext_of _ (A.deriv_single_self _))
    have t1 : A.Deriv (A.single (A.neg (bigD D X (K + 1)))) (A.iff (thetaK D X K b) b) :=
      A.deriv_of_single hK (thetaK_neg D X K b)
    have t2 := thetaK_neg D X (K + 1) b
    exact A.deriv_ext_of_single (F := A.empty) (Language.deriv_iff_trans t1 (Language.deriv_iff_symm t2))

theorem theta_iff_thetaK (b : A.Sent) : ∀ d : ℕ, A.Valid (A.iff (theta D X b) (thetaK D X (e M b + 1 + d) b))
  | 0 => Language.deriv_iff_refl _ _
  | d + 1 => Language.deriv_iff_trans (theta_iff_thetaK b d)
      (thetaK_succ D X (K := e M b + 1 + d) (by omega))

theorem theta_equiv_thetaK {b : A.Sent} {K : ℕ} (hK : e M b + 1 ≤ K) : A.Equiv (theta D X b) (thetaK D X K b) := by
  obtain ⟨d, rfl⟩ : ∃ d, K = e M b + 1 + d := ⟨K - (e M b + 1), by omega⟩
  exact Language.Equiv.of_valid_iff (theta_iff_thetaK D X b d)

/-- `θ` commutes with `∧` up to logical equivalence. -/
theorem theta_and (a b : A.Sent) : A.Equiv (theta D X (A.and a b)) (A.and (theta D X a) (theta D X b)) := by
  let K := e M a + e M b + e M (A.and a b) + 1
  have h1 := theta_equiv_thetaK D X (b := A.and a b) (K := K) (by omega)
  have h2 := theta_equiv_thetaK D X (b := a) (K := K) (by omega)
  have h3 := theta_equiv_thetaK D X (b := b) (K := K) (by omega)
  exact h1.trans ((Language.Equiv.of_valid_iff (thetaK_and D X K a b)).trans
    (Language.Equiv.and h2.symm h3.symm))

/-- `θ` commutes with `¬` up to logical equivalence. -/
theorem theta_neg (a : A.Sent) : A.Equiv (theta D X (A.neg a)) (A.neg (theta D X a)) := by
  let K := e M a + e M (A.neg a) + 1
  have h1 := theta_equiv_thetaK D X (b := A.neg a) (K := K) (by omega)
  have h2 := theta_equiv_thetaK D X (b := a) (K := K) (by omega)
  exact h1.trans ((Language.Equiv.of_valid_iff (thetaK_negc D X K a)).trans h2.symm.neg)

/-- `θ` fixes, up to logical equivalence, every sentence logically equivalent to one of `𝓑`. -/
theorem theta_equiv_of_inB {b β : A.Sent} (hb : A.Equiv b β) (hβ : A.InB β) : A.Equiv (theta D X b) b := by
  refine Language.Equiv.of_valid_iff (thetaK_cases D X (K := e M b + 1) (fun n hn => ?_) ?_)
  · have t1 := thetaK_pos D X hn b
    -- `{x_n} ⊢ b^ι ↔ β^ι ↔ β ↔ b`
    have t2 : A.Deriv (A.single (xN D n)) (A.iff (trN D n b) (trN D n β)) :=
      A.deriv_and_intro (x_deriv_tr_imp D n hb.1) (x_deriv_tr_imp D n hb.2)
    have t3 := x_deriv_iff_tr_of_inB D n hβ
    have t4 : A.Deriv (A.single (xN D n)) (A.iff (trN D n b) b) :=
      Language.deriv_iff_trans t2 (Language.deriv_iff_trans (Language.deriv_iff_symm t3) (hb.symm.to_deriv_iff _))
    exact A.deriv_ext_of_single (F := A.empty) (Language.deriv_iff_trans t1 (eps_deriv_of_x D n t4))
  · exact A.deriv_ext_of_single (F := A.empty) (thetaK_neg D X _ b)

theorem theta_equiv_inB {β : A.Sent} (hβ : A.InB β) : A.Equiv (theta D X β) β :=
  theta_equiv_of_inB D X (Language.Equiv.refl β) hβ

/-- `θ` preserves logical validity. -/
theorem theta_valid {b : A.Sent} (h : A.Valid b) : A.Valid (theta D X b) := by
  refine thetaK_cases D X (K := e M b + 1) (fun n hn => ?_) ?_
  · have t1 := A.deriv_ext_of_single (F := A.empty) (thetaK_pos D X hn b)
    exact Language.deriv_iff_mpr t1 (A.deriv_ext_of_single (eps_deriv_of_x D n (x_deriv_tr_of_valid D n h)))
  · exact Language.deriv_iff_mpr (A.deriv_ext_of_single (F := A.empty) (thetaK_neg D X _ b)) (A.deriv_ext_of _ h)

/-- The encoding, first half: for `n ∈ X`, `θ (¬ε_n)` is logically valid. -/
theorem theta_neg_eps_valid {n : ℕ} (hn : X n) : A.Valid (theta D X (A.neg (epsN D n))) := by
  have hnK : n ∈ Xlist X (e M (A.neg (epsN D n)) + 1) :=
    (mem_Xlist X).2 ⟨Nat.lt_succ_of_lt (lt_code_neg_eps D n), hn⟩
  refine thetaK_cases D X (K := e M (A.neg (epsN D n)) + 1) (fun m hm => ?_) ?_
  · have t1 := thetaK_pos D X hm (A.neg (epsN D n))
    rw [trN_neg] at t1
    -- `{ε_m} ⊢ ¬ (ε_n)^{ι_m}`
    have t2 : A.Deriv (A.single (epsN D m)) (A.neg (trN D m (epsN D n))) := by
      rcases Nat.lt_trichotomy m n with h | rfl | h
      · -- `m < n`: `ε_n ⊢ d_m` and `{x_m} ⊢ ¬ d_m^{ι_m}`
        exact eps_deriv_of_x D m (Language.deriv_neg_of_imp (x_deriv_tr_imp D m (eps_deriv_d_lt D n h))
          (x_deriv_tr_neg_d D m))
      · exact eps_deriv_of_x D m (Language.deriv_neg_of_imp (x_deriv_tr_imp D m (eps_deriv_d D m))
          (x_deriv_tr_neg_d D m))
      · exact eps_deriv_of_x D m (x_deriv_tr_neg_eps_lt D m h)
    exact A.deriv_ext_of_single (F := A.empty) (Language.deriv_iff_mpr t1 t2)
  · have t1 := thetaK_neg D X (e M (A.neg (epsN D n)) + 1) (A.neg (epsN D n))
    have t2 : A.Deriv (A.single (A.neg (bigD D X (e M (A.neg (epsN D n)) + 1)))) (A.neg (epsN D n)) :=
      Language.deriv_neg_of (eps_deriv_bigD D X hnK |> A.deriv_ext_of_single)
        (A.deriv_ext_of _ (A.deriv_single_self _))
    exact A.deriv_ext_of_single (F := A.empty) (Language.deriv_iff_mpr t1 t2)

/-- The encoding, second half: for `n ∉ X`, `PA ⊬ θ (¬ε_n)`. -/
theorem not_deriv_PA_theta_neg_eps {n : ℕ} (hn : ¬ X n) : ¬ A.Deriv D.PA (theta D X (A.neg (epsN D n))) := by
  intro h
  have hnK : n ∉ Xlist X (e M (A.neg (epsN D n)) + 1) := fun hm => hn ((mem_Xlist X).1 hm).2
  have t1 : A.Deriv (A.single (epsN D n)) (A.iff (theta D X (A.neg (epsN D n))) (A.neg (epsN D n))) :=
    A.deriv_of_single (eps_deriv_neg_bigD D X hnK) (thetaK_neg D X _ _)
  obtain ⟨c, hc⟩ := consistent_PA_epsN D n
  apply hc
  have h2 : A.Deriv (A.ext D.PA (epsN D n)) (A.neg (epsN D n)) :=
    Language.deriv_iff_mp (A.deriv_ext_of_single t1) (A.deriv_ext_of _ h)
  exact A.deriv_explosion (A.deriv_ext_self _ _) h2

end Theta


/-! ### The translation `j` -/

section TranslationJ

variable (D : UndefData A) (X : ℕ → Prop)

set_option linter.unusedVariables false in -- `h` is used in `decreasing_by`
/-- `j` on sentences: the identity on prime `Σ⁰₂` and `Π⁰₂` sentences, `wrap (θ p)` on the other prime
sentences, extended over `¬` and `∧`. -/
noncomputable def jmap : A.Sent → A.Sent
  | s =>
    match h : D.destruct s with
    | none => if A.IsSigma 2 s ∨ A.IsPi 2 s then s else D.wrap (theta D X s)
    | some (Sum.inl a) => A.neg (jmap a)
    | some (Sum.inr (a, b)) => A.and (jmap a) (jmap b)
termination_by s => D.size s
decreasing_by
  all_goals simp_wf
  · show D.size a < D.size s
    rw [D.destruct_inl s a h]; exact D.size_neg a
  · show D.size a < D.size s
    rw [D.destruct_inr s a b h]; exact D.size_and_left a b
  · show D.size b < D.size s
    rw [D.destruct_inr s a b h]; exact D.size_and_right a b

theorem jmap_neg (a : A.Sent) : jmap D X (A.neg a) = A.neg (jmap D X a) := by
  rw [jmap]
  split
  · rename_i h; rw [D.destruct_neg] at h; cases h
  · rename_i a' h; rw [D.destruct_neg] at h; cases h; rfl
  · rename_i a' b' h; rw [D.destruct_neg] at h; cases h

theorem jmap_and (a b : A.Sent) : jmap D X (A.and a b) = A.and (jmap D X a) (jmap D X b) := by
  rw [jmap]
  split
  · rename_i h; rw [D.destruct_and] at h; cases h
  · rename_i a' h; rw [D.destruct_and] at h; cases h
  · rename_i a' b' h; rw [D.destruct_and] at h; cases h; rfl

theorem jmap_prime {p : A.Sent} (hp : D.Prime p) :
    jmap D X p = if A.IsSigma 2 p ∨ A.IsPi 2 p then p else D.wrap (theta D X p) := by
  rw [jmap]
  split
  · rfl
  · rename_i a' h; rw [show D.destruct p = none from hp] at h; cases h
  · rename_i a' b' h; rw [show D.destruct p = none from hp] at h; cases h

theorem jmap_prime_of {p : A.Sent} (hp : D.Prime p) (h : A.IsSigma 2 p ∨ A.IsPi 2 p) : jmap D X p = p := by
  rw [jmap_prime D X hp, ite_eq_left h]

theorem jmap_prime_of_not {p : A.Sent} (hp : D.Prime p) (h : ¬ (A.IsSigma 2 p ∨ A.IsPi 2 p)) :
    jmap D X p = D.wrap (theta D X p) := by
  rw [jmap_prime D X hp, ite_eq_right h]

/-- Induction on the size of a sentence. -/
theorem size_induction {P : A.Sent → Prop}
    (h : ∀ s, (∀ t, D.size t < D.size s → P t) → P s) : ∀ s, P s := by
  have : ∀ k s, D.size s < k → P s := by
    intro k
    induction k with
    | zero => intro s hs; exact absurd hs (Nat.not_lt_zero _)
    | succ k ih => intro s hs; exact h s fun t ht => ih t (Nat.lt_of_lt_of_le ht (Nat.le_of_lt_succ hs))
  exact fun s => this (D.size s + 1) s (Nat.lt_succ_self _)

/-- `j` is the identity on `Σ⁰₂` sentences. -/
theorem jmap_sigma2 : ∀ s, A.IsSigma 2 s → jmap D X s = s := by
  refine size_induction D fun s ih hs => ?_
  rcases D.cases s with hp | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · exact jmap_prime_of D X hp (Or.inl hs)
  · rw [jmap_neg, ih a (D.size_neg a) (D.sigma2_of_neg hs)]
  · rw [jmap_and, ih a (D.size_and_left a b) (D.sigma2_of_and hs).1,
      ih b (D.size_and_right a b) (D.sigma2_of_and hs).2]

/-- `j` is the identity on `Π⁰₂` sentences. -/
theorem jmap_pi2 : ∀ s, A.IsPi 2 s → jmap D X s = s := by
  refine size_induction D fun s ih hs => ?_
  rcases D.cases s with hp | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · exact jmap_prime_of D X hp (Or.inr hs)
  · rw [jmap_neg, ih a (D.size_neg a) (D.pi2_of_neg hs)]
  · rw [jmap_and, ih a (D.size_and_left a b) (D.pi2_of_and hs).1,
      ih b (D.size_and_right a b) (D.pi2_of_and hs).2]

/-- `j` is the identity on `𝓑`. -/
theorem jmap_inB {β : A.Sent} (hβ : A.InB β) : jmap D X β = β := by
  induction hβ with
  | sigma h => exact jmap_sigma2 D X _ h
  | pi h => exact jmap_pi2 D X _ h
  | neg _ ih => rw [jmap_neg, ih]
  | and _ _ ih₁ ih₂ => rw [jmap_and, ih₁, ih₂]

/-- `j (b)` is logically equivalent to `θ (b)`. -/
theorem jmap_equiv_theta : ∀ s, A.Equiv (jmap D X s) (theta D X s) := by
  refine size_induction D fun s ih => ?_
  rcases D.cases s with hp | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · by_cases h : A.IsSigma 2 s ∨ A.IsPi 2 s
    · rw [jmap_prime_of D X hp h]
      exact (theta_equiv_inB D X (h.elim Arith.InB.sigma Arith.InB.pi)).symm
    · rw [jmap_prime_of_not D X hp h]
      exact D.wrap_equiv _
  · rw [jmap_neg]
    exact (ih a (D.size_neg a)).neg.trans (theta_neg D X a).symm
  · rw [jmap_and]
    exact (Language.Equiv.and (ih a (D.size_and_left a b)) (ih b (D.size_and_right a b))).trans
      (theta_and D X a b).symm

/-- `Δ₀` is closed under the subformula `t` of `θ_K (t)`. -/
theorem delta0_of_thetaK {K : ℕ} {t : A.Sent} (h : A.IsSigma 0 (thetaK D X K t)) : A.IsSigma 0 t := by
  unfold thetaK Language.or at h
  have h1 := D.delta0_neg _ h
  have h2 := (D.delta0_and _ _ h1).1
  have h3 := D.delta0_neg _ h2
  exact (D.delta0_and _ _ h3).1

/-- `wrap (θ p)` is not in `Σ⁰₂ ∪ Π⁰₂` for `p ∉ Σ⁰₂ ∪ Π⁰₂`. -/
theorem wrap_theta_not {p : A.Sent} (h : ¬ (A.IsSigma 2 p ∨ A.IsPi 2 p)) :
    ¬ (A.IsSigma 2 (D.wrap (theta D X p)) ∨ A.IsPi 2 (D.wrap (theta D X p))) := by
  rintro (h1 | h1)
  · exact h (Or.inl (A.sigma_of_delta0 (delta0_of_thetaK D X (D.wrap_sigma2 _ h1)) 2))
  · exact h (Or.inl (A.sigma_of_delta0 (delta0_of_thetaK D X (D.wrap_pi2 _ h1)) 2))

/-- `θ_K (s) = θ_{K'} (t)` forces `s = t` (the first conjunct of the first disjunct). -/
theorem eq_of_thetaK_eq {K K' : ℕ} {s t : A.Sent} (h : thetaK D X K s = thetaK D X K' t) : s = t := by
  unfold thetaK Language.or at h
  have h1 := D.neg_inj h
  have h2 := (D.and_inj h1).1
  have h3 := D.neg_inj h2
  exact (D.and_inj h3).1

/-- `j` is injective. -/
theorem jmap_inj : ∀ s t, jmap D X s = jmap D X t → s = t := by
  refine size_induction D fun s ih t hst => ?_
  rcases D.cases s with hps | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;>
    rcases D.cases t with hpt | ⟨a', rfl⟩ | ⟨a', b', rfl⟩
  · -- prime, prime
    by_cases hs : A.IsSigma 2 s ∨ A.IsPi 2 s <;> by_cases ht : A.IsSigma 2 t ∨ A.IsPi 2 t
    · rw [jmap_prime_of D X hps hs, jmap_prime_of D X hpt ht] at hst; exact hst
    · rw [jmap_prime_of D X hps hs, jmap_prime_of_not D X hpt ht] at hst
      exact absurd (hst ▸ hs) (wrap_theta_not D X ht)
    · rw [jmap_prime_of_not D X hps hs, jmap_prime_of D X hpt ht] at hst
      exact absurd (hst ▸ ht) (wrap_theta_not D X hs)
    · rw [jmap_prime_of_not D X hps hs, jmap_prime_of_not D X hpt ht] at hst
      exact eq_of_thetaK_eq D X (D.wrap_inj _ _ hst)
  · -- prime, neg
    rw [jmap_neg] at hst
    by_cases hs : A.IsSigma 2 s ∨ A.IsPi 2 s
    · rw [jmap_prime_of D X hps hs] at hst; exact absurd hst (D.prime_ne_neg hps _)
    · rw [jmap_prime_of_not D X hps hs] at hst
      exact absurd hst (D.prime_ne_neg (D.wrap_prime _) _)
  · -- prime, and
    rw [jmap_and] at hst
    by_cases hs : A.IsSigma 2 s ∨ A.IsPi 2 s
    · rw [jmap_prime_of D X hps hs] at hst; exact absurd hst (D.prime_ne_and hps _ _)
    · rw [jmap_prime_of_not D X hps hs] at hst
      exact absurd hst (D.prime_ne_and (D.wrap_prime _) _ _)
  · -- neg, prime
    rw [jmap_neg] at hst
    by_cases ht : A.IsSigma 2 t ∨ A.IsPi 2 t
    · rw [jmap_prime_of D X hpt ht] at hst; exact absurd hst.symm (D.prime_ne_neg hpt _)
    · rw [jmap_prime_of_not D X hpt ht] at hst
      exact absurd hst.symm (D.prime_ne_neg (D.wrap_prime _) _)
  · -- neg, neg
    rw [jmap_neg, jmap_neg] at hst
    rw [ih a (D.size_neg a) a' (D.neg_inj hst)]
  · -- neg, and
    rw [jmap_neg, jmap_and] at hst
    exact absurd hst (D.neg_ne_and _ _ _)
  · -- and, prime
    rw [jmap_and] at hst
    by_cases ht : A.IsSigma 2 t ∨ A.IsPi 2 t
    · rw [jmap_prime_of D X hpt ht] at hst; exact absurd hst.symm (D.prime_ne_and hpt _ _)
    · rw [jmap_prime_of_not D X hpt ht] at hst
      exact absurd hst.symm (D.prime_ne_and (D.wrap_prime _) _ _)
  · -- and, neg
    rw [jmap_and, jmap_neg] at hst
    exact absurd hst.symm (D.neg_ne_and _ _ _)
  · -- and, and
    rw [jmap_and, jmap_and] at hst
    obtain ⟨h1, h2⟩ := D.and_inj hst
    rw [ih a (D.size_and_left a b) a' h1, ih b (D.size_and_right a b) b' h2]

theorem jmap_imp (a b : A.Sent) : jmap D X (A.imp a b) = A.imp (jmap D X a) (jmap D X b) := by
  unfold Language.imp; rw [jmap_neg, jmap_and, jmap_neg]

theorem jmap_conjList (z : A.Sent) (l : List A.Sent) :
    jmap D X (A.conjList z l) = A.conjList (jmap D X z) (l.map (jmap D X)) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [Language.conjList, List.map_cons]; rw [jmap_and, ih]

theorem deriv_neg_and_neg_self (F : A.Sent → Prop) (x : A.Sent) : A.Deriv F (A.neg (A.and x (A.neg x))) :=
  A.deriv_neg_intro fun _ =>
    A.deriv_explosion (A.deriv_and_left (A.deriv_ext_self F _)) (A.deriv_and_right (A.deriv_ext_self F _))

/-- The translation `j` (Definition 2.6). -/
noncomputable def jTrans : Translation A.toLanguage A.toLanguage where
  i := jmap D X
  inj := fun h => jmap_inj D X _ _ h
  map_neg := jmap_neg D X
  map_and := jmap_and D X
  map_deriv := fun S α h => by
    obtain ⟨l, hl, hd⟩ := A.deriv_compact h
    -- `⊢ ⋀ l → α`
    have h1 : A.Valid (A.imp (A.conjList (top A) l) α) :=
      Language.deriv_imp_conjList (A.deriv_mono (fun β hβ => Or.inr hβ) hd)
    have h2 := theta_valid D X h1
    have h3 : A.Valid (jmap D X (A.imp (A.conjList (top A) l) α)) :=
      ((jmap_equiv_theta D X _).valid_iff).2 h2
    rw [jmap_imp, jmap_conjList] at h3
    have h4 : A.Deriv (A.extList A.empty (l.map (jmap D X))) (jmap D X α) :=
      Language.deriv_extList_of_imp_conjList (z := jmap D X (top A)) (by
        unfold top bot; rw [jmap_neg, jmap_and, jmap_neg]; exact deriv_neg_and_neg_self _ _)
        (A.deriv_of_valid h3)
    refine A.deriv_mono (fun β hβ => ?_) h4
    rcases hβ with hβ | hβ
    · exact hβ.elim
    · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
      exact ⟨γ, hl γ hγ, rfl⟩

theorem jTrans_i (s : A.Sent) : (jTrans D X).i s = jmap D X s := rfl

/-- `j` is a `2`-translation. -/
theorem jTrans_isN2 : (jTrans D X).IsNTranslation 2 := by
  obtain ⟨T, hT⟩ := (compT_id (M := M) (A := A.Sent))
  refine ⟨T, fun σ => ?_⟩
  show M.eval T (e M σ.1) = (some (jmap D X σ.1)).map (e M)
  rw [jmap_sigma2 D X σ.1 σ.2]
  exact hT σ.1

/-- `j` is the identity on `Σ⁰₂ ∪ Π⁰₂`. -/
theorem jTrans_id {α : A.Sent} (h : A.IsSigma 2 α ∨ A.IsPi 2 α) : (jTrans D X).i α = α :=
  h.elim (jmap_sigma2 D X α) (jmap_pi2 D X α)

/-- Soundness and `Q ⊆ F` give `1`- and `2`-consistency relative to `j`. -/
theorem jTrans_twoConsistent {F : A.Sent → Prop} (hF : ∀ β, F β → A.TrueN β) (hQ : ∀ q, A.Q q → F q) :
    (jTrans D X).TwoConsistent F := by
  have hinst : ∀ σ v, A.IsSigma 2 σ → jmap D X (A.neg (A.instS σ v)) = A.neg (A.instS σ v) := by
    intro σ v hσ
    rw [jmap_neg, jmap_pi2 D X _ (A.pi_succ 1 _ (A.instS_pi 1 σ v hσ))]
  have hclause : ∀ σ, A.IsSigma 2 σ → (jTrans D X).DerivI F σ →
      ∃ v, ¬ (jTrans D X).DerivI F (A.neg (A.instS σ v)) := by
    intro σ hσ hd
    rw [Translation.derivI_iff, jTrans_i, jmap_sigma2 D X σ hσ] at hd
    obtain ⟨v, hv⟩ := (A.trueN_sigma 1 σ hσ).1 (A.sound _ _ hF hd)
    refine ⟨v, fun h => ?_⟩
    rw [Translation.derivI_iff, jTrans_i, hinst σ v hσ] at h
    exact (A.trueN_neg _).1 (A.sound _ _ hF h) hv
  refine ⟨⟨fun q hq => ?_, fun σ hσ hd => hclause σ (A.sigma_succ 1 σ hσ) hd⟩, hclause⟩
  rw [Translation.derivI_iff, jTrans_i]
  obtain ⟨β, hβ, hqβ⟩ := D.Q_equivB q hq
  have h1 : A.Equiv (jmap D X q) q := (jmap_equiv_theta D X q).trans (theta_equiv_of_inB D X hqβ hβ)
  exact (h1.deriv_iff F).2 (A.deriv_of_mem (hQ q hq))

theorem jTrans_oneConsistent {F : A.Sent → Prop} (hF : ∀ β, F β → A.TrueN β) (hQ : ∀ q, A.Q q → F q) :
    (jTrans D X).OneConsistent F := (jTrans_twoConsistent D X hF hQ).1

/-- The encoding: `¬ε_n ∈ F_{j,𝓐}` iff `n ∈ X`, for every `F ⊆ PA`, in particular for `F = PA` and
`F = Q`. -/
theorem induced_neg_eps_iff {F : A.Sent → Prop} (hFPA : ∀ β, F β → D.PA β) (n : ℕ) :
    (jTrans D X).induced F (A.neg (epsN D n)) ↔ X n := by
  show A.Deriv F (jmap D X (A.neg (epsN D n))) ↔ X n
  rw [(jmap_equiv_theta D X _).deriv_iff F]
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    exact not_deriv_PA_theta_neg_eps D X hn (A.deriv_mono hFPA h)
  · intro hn
    exact A.deriv_of_valid (theta_neg_eps_valid D X hn)

end TranslationJ


/-! ### Proposition B.7 -/

section Main

variable (D : UndefData A)

/-- Proposition B.7, family form: a sequence `ε_n` of false sentences consistent with `PA` such that
for every `X ⊂ ℕ` there is a `2`-translation `j_X : 𝓐 → 𝓐`, the identity on `Σ⁰₂ ∪ Π⁰₂`, with `PA` and
`Q` `1`- and `2`-consistent relative to `j_X`, and `¬ε_n ∈ PA_{j_X,𝓐}` iff `n ∈ X` (likewise for `Q`).
The sequence `ε_n` does not depend on `X`. -/
theorem undefinable_family :
    ∃ eps : ℕ → A.Sent, (∀ n, ¬ A.TrueN (eps n)) ∧ (∀ n, A.Consistent (A.ext D.PA (eps n))) ∧
    ∀ X : ℕ → Prop, ∃ j : Translation A.toLanguage A.toLanguage,
      j.IsNTranslation 2 ∧ (∀ α, A.IsSigma 2 α ∨ A.IsPi 2 α → j.i α = α) ∧
      j.OneConsistent D.PA ∧ j.TwoConsistent D.PA ∧ j.OneConsistent A.Q ∧ j.TwoConsistent A.Q ∧
      ∀ n, (j.induced D.PA (A.neg (eps n)) ↔ X n) ∧ (j.induced A.Q (A.neg (eps n)) ↔ X n) :=
  ⟨epsN D, not_trueN_epsN D, consistent_PA_epsN D, fun X =>
    ⟨jTrans D X, jTrans_isN2 D X, fun _ h => jTrans_id D X h,
      jTrans_oneConsistent D X D.PA_sound D.PA_Q, jTrans_twoConsistent D X D.PA_sound D.PA_Q,
      jTrans_oneConsistent D X (fun _ hq => D.Q_sound hq) (fun _ hq => hq),
      jTrans_twoConsistent D X (fun _ hq => D.Q_sound hq) (fun _ hq => hq),
      fun n => ⟨induced_neg_eps_iff D X (fun _ h => h) n,
        induced_neg_eps_iff D X D.PA_Q n⟩⟩⟩

/-- Cantor's theorem: no `g : ℕ → (ℕ → Prop)` is surjective. -/
theorem cantor (g : ℕ → (ℕ → Prop)) : ∃ X : ℕ → Prop, ∀ n, g n ≠ X := by
  refine ⟨fun n => ¬ g n n, fun n h => ?_⟩
  have h1 : g n n = ¬ g n n := congrFun h n
  exact iff_not_self (Iff.of_eq h1)

end Main

/-- A set of sentences is arithmetical if it is `Σ⁰_{m+2}` for some `m` (`IsSigmaNSet`); as
`Σ⁰₁ ⊂ Σ⁰₂`, this covers every level of the hierarchy. -/
def Arithmetical (S : A.Sent → Prop) : Prop := ∃ m, IsSigmaNSet (M := M) m S

/-- The relation computed by the machine `T`, read as a relation on `Unit × 𝓐 × ℕ^{m+2}`. -/
def relOf (m : ℕ) (T : M.Code) : NRel Unit A.Sent m :=
  fun u x v w => M.eval T (e M ((u, x, v, w) : Unit × NB A.Sent m × ℕ × ℕ)) = some 1

/-- The `Σ⁰_{m+2}` set determined by the machine `T`. -/
def setOfCode (m : ℕ) (T : M.Code) : A.Sent → Prop := fun b => NSR m (relOf (A := A) m T) () b

theorem eq_setOfCode_of_isSigmaNSet {m : ℕ} {S : A.Sent → Prop} (h : IsSigmaNSet (M := M) m S) :
    ∃ T : M.Code, S = setOfCode (A := A) m T := by
  obtain ⟨R, ⟨T, hT⟩, hS⟩ := h
  refine ⟨T, funext fun b => propext ?_⟩
  rw [hS b]
  refine NSR_congr m (fun u x v w => ?_) () b
  have hq : M.eval T (e M ((u, x, v, w) : Unit × NB A.Sent m × ℕ × ℕ)) =
      some (if (∃ q : Unit × NB A.Sent m × ℕ × ℕ,
        e M q = e M ((u, x, v, w) : Unit × NB A.Sent m × ℕ × ℕ) ∧ R q.1 q.2.1 q.2.2.1 q.2.2.2)
        then 1 else 0) := hT _
  show R u x v w ↔ M.eval T (e M ((u, x, v, w) : Unit × NB A.Sent m × ℕ × ℕ)) = some 1
  rw [hq]
  by_cases hR : R u x v w
  · have hex : ∃ q : Unit × NB A.Sent m × ℕ × ℕ,
        e M q = e M ((u, x, v, w) : Unit × NB A.Sent m × ℕ × ℕ) ∧ R q.1 q.2.1 q.2.2.1 q.2.2.2 :=
      ⟨(u, x, v, w), rfl, hR⟩
    rw [ite_eq_left hex]
    exact ⟨fun _ => rfl, fun _ => hR⟩
  · have hex : ¬ ∃ q : Unit × NB A.Sent m × ℕ × ℕ,
        e M q = e M ((u, x, v, w) : Unit × NB A.Sent m × ℕ × ℕ) ∧ R q.1 q.2.1 q.2.2.1 q.2.2.2 := by
      rintro ⟨q, hq1, hq2⟩
      rw [Enc.inj hq1] at hq2
      exact hR hq2
    rw [ite_eq_right hex]
    exact ⟨fun h => absurd h hR, fun h => absurd (Option.some.inj h) (by decide)⟩

/-- An enumeration of all arithmetical sets of sentences, indexed by `ℕ`. -/
noncomputable def arithEnum (c : ℕ) : A.Sent → Prop :=
  match Enc.decode (M := M) (ℕ × M.Code) c with
  | some (m, T) => setOfCode (A := A) m T
  | none => fun _ => False

theorem exists_arithEnum_eq {S : A.Sent → Prop} (h : Arithmetical (A := A) S) :
    ∃ c, arithEnum (A := A) c = S := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨T, rfl⟩ := eq_setOfCode_of_isSigmaNSet hm
  refine ⟨e M ((m, T) : ℕ × M.Code), ?_⟩
  unfold arithEnum
  rw [Enc.decode_e]

section Main2

variable (D : UndefData A)

/-- Proposition B.7: some `2`-translation `j : 𝓐 → 𝓐`, the identity on `Σ⁰₂ ∪ Π⁰₂`, with `PA` and
`Q` `1`- and `2`-consistent relative to it, induces non-arithmetical theories `PA_{j,𝓐}` and
`Q_{j,𝓐}`. (By counting: `X ↦ PA_{j_X,𝓐}` is injective, and there are only countably many
arithmetical sets of sentences.) -/
theorem exists_undefinable :
    ∃ j : Translation A.toLanguage A.toLanguage,
      j.IsNTranslation 2 ∧ (∀ α, A.IsSigma 2 α ∨ A.IsPi 2 α → j.i α = α) ∧
      j.OneConsistent D.PA ∧ j.TwoConsistent D.PA ∧ j.OneConsistent A.Q ∧ j.TwoConsistent A.Q ∧
      ¬ Arithmetical (A := A) (j.induced D.PA) ∧ ¬ Arithmetical (A := A) (j.induced A.Q) := by
  obtain ⟨eps, _, _, hX⟩ := undefinable_family D
  let j : (ℕ → Prop) → Translation A.toLanguage A.toLanguage := fun X => Classical.choose (hX X)
  have hj : ∀ X, (j X).IsNTranslation 2 ∧ (∀ α, A.IsSigma 2 α ∨ A.IsPi 2 α → (j X).i α = α) ∧
      (j X).OneConsistent D.PA ∧ (j X).TwoConsistent D.PA ∧ (j X).OneConsistent A.Q ∧
      (j X).TwoConsistent A.Q ∧
      ∀ n, ((j X).induced D.PA (A.neg (eps n)) ↔ X n) ∧ ((j X).induced A.Q (A.neg (eps n)) ↔ X n) :=
    fun X => Classical.choose_spec (hX X)
  -- the induced theories determine `X`
  have hinjPA : ∀ X Y, (j X).induced D.PA = (j Y).induced D.PA → X = Y := by
    intro X Y h
    funext n
    apply propext
    rw [← ((hj X).2.2.2.2.2.2 n).1, ← ((hj Y).2.2.2.2.2.2 n).1, h]
  have hinjQ : ∀ X Y, (j X).induced A.Q = (j Y).induced A.Q → X = Y := by
    intro X Y h
    funext n
    apply propext
    rw [← ((hj X).2.2.2.2.2.2 n).2, ← ((hj Y).2.2.2.2.2.2 n).2, h]
  -- the sets `X` with `PA_{j_X,𝓐}` or `Q_{j_X,𝓐}` arithmetical are enumerated by `g`
  let target : ℕ → (ℕ → Prop) → (A.Sent → Prop) := fun k X =>
    if k % 2 = 0 then (j X).induced D.PA else (j X).induced A.Q
  let g : ℕ → (ℕ → Prop) := fun k =>
    if h : ∃ X, arithEnum (A := A) (k / 2) = target k X then Classical.choose h else fun _ => False
  obtain ⟨X₀, hX₀⟩ := cantor g
  refine ⟨j X₀, (hj X₀).1, (hj X₀).2.1, (hj X₀).2.2.1, (hj X₀).2.2.2.1, (hj X₀).2.2.2.2.1,
    (hj X₀).2.2.2.2.2.1, fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨c, hc⟩ := exists_arithEnum_eq ha
    have hex : ∃ X, arithEnum (A := A) ((2 * c) / 2) = target (2 * c) X := by
      refine ⟨X₀, ?_⟩
      show arithEnum (A := A) ((2 * c) / 2) = (if (2 * c) % 2 = 0 then (j X₀).induced D.PA else (j X₀).induced A.Q)
      rw [ite_eq_left (by omega), show (2 * c) / 2 = c by omega]
      exact hc
    apply hX₀ (2 * c)
    show (if h : ∃ X, arithEnum (A := A) ((2 * c) / 2) = target (2 * c) X then Classical.choose h
      else fun _ => False) = X₀
    rw [dite_eq_left hex]
    exact hinjPA _ _ (by
      have h1 : arithEnum (A := A) ((2 * c) / 2) = (j (Classical.choose hex)).induced D.PA := by
        have := Classical.choose_spec hex
        rwa [show target (2 * c) (Classical.choose hex) =
          (j (Classical.choose hex)).induced D.PA from ite_eq_left (by omega)] at this
      rw [← h1, show (2 * c) / 2 = c by omega, hc])
  · obtain ⟨c, hc⟩ := exists_arithEnum_eq ha
    have hex : ∃ X, arithEnum (A := A) ((2 * c + 1) / 2) = target (2 * c + 1) X := by
      refine ⟨X₀, ?_⟩
      show arithEnum (A := A) ((2 * c + 1) / 2) =
        (if (2 * c + 1) % 2 = 0 then (j X₀).induced D.PA else (j X₀).induced A.Q)
      rw [ite_eq_right (by omega), show (2 * c + 1) / 2 = c by omega]
      exact hc
    apply hX₀ (2 * c + 1)
    show (if h : ∃ X, arithEnum (A := A) ((2 * c + 1) / 2) = target (2 * c + 1) X then Classical.choose h
      else fun _ => False) = X₀
    rw [dite_eq_left hex]
    exact hinjQ _ _ (by
      have h1 : arithEnum (A := A) ((2 * c + 1) / 2) = (j (Classical.choose hex)).induced A.Q := by
        have := Classical.choose_spec hex
        rwa [show target (2 * c + 1) (Classical.choose hex) =
          (j (Classical.choose hex)).induced A.Q from ite_eq_right (by omega)] at this
      rw [← h1, show (2 * c + 1) / 2 = c by omega, hc])

end Main2

end UndefData

end Stable
