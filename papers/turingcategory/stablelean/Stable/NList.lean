import Stable.NStab

/-!
# Closure properties of `Σ⁰_{m+2}` conditions (Section 6.2, "the constructions")

The paper obtains `Dec^n`, `C^n` and `Spec^n` by observing that the relevant conditions "are of the
form of Lemma 6.2", using (i) case distinctions in the first quantifier, (ii) an existential over an
encoded set absorbed into the first quantifier, and (iii) a bounded universal quantifier over the
entries of a list, "absorbed by quantifying over lists of witnesses".  This file proves these
closure properties of the class of conditions `NSR m R` (`R` computable), uniformly in the
parameter `a : A`:

* `NSR_exists_absorb`: `∃ q : X, NSR m R a (b, q)`;
* `NSR_or_absorb`: `NSR m R₁ a b ∨ NSR m R₂ a b`;
* `NSR_and_dec`: `P b ∧ NSR m R a b` for a computable `P`;
* `NSR_comp_base`: `NSR m R a (f b)` for a total computable `f`;
* `NSR_exists_nth_absorb`: `∃ j < length l, NSR m R a (l[j])`;
* `NSR_forall_nth_absorb`: `∀ j < length l, NSR m R a (l[j])`.
Each is stated as the existence of a computable `R'` with `NSR m R'` equal to the given condition.
Auxiliary closure properties, also public: `NSR_ite_dec` (cases on a computable predicate on the
base), `NSR_imp_dec` (`P b → NSR m R a b`), `NSR_not_succ` (`¬ NSR m Q a b` as an `NSR (m+1)`
condition) and `NSR_exists_rel` (`∃ q, Q b q ∧ NSR m R a (f (b, q))` for computable `Q`, `f`).

Proof pattern: no induction on `m` is needed.  Level `0` is a manipulation of the matrix; at level
`m + 1` the first quantifier `∃ u` is transformed and the rest is handled at level `m` by
`NSR_nbMapBase`, `NSR_ite`, `NSR_true`/`NSR_false` and `NSR_congr` (Stable/NStab.lean).
-/

namespace Stable

open Classical

variable {M : TuringModel} {A B : Type} [Enc M A] [Enc M B]

/-! ### Computable relations: transport along a base map, cases, constants -/

/-- Transport of a computable relation along a total computable base map. -/
private theorem nrelComp_mapBase (m : ℕ) {C : Type} [Enc M C] {R : NRel A C m}
    (hR : NRelComp (M := M) m R) {f : B → C} (hf : CompT M f) :
    NRelComp (M := M) m (fun a x u v => R a (nbMapBase m f x) u v) :=
  CompSet.comp hR (CompT.pair compT_fst
    (CompT.pair ((compT_nbMapBase m hf).comp (compT_fst.comp compT_snd)) (compT_snd.comp compT_snd)))

/-- Cases on a computable property of the base. -/
private theorem nrelComp_ite (m : ℕ) {P : B → Prop} (hP : CompSet M P) {R₁ R₂ : NRel A B m}
    (h₁ : NRelComp (M := M) m R₁) (h₂ : NRelComp (M := M) m R₂) :
    NRelComp (M := M) m (fun a x u v => if P (nbBase m x) then R₁ a x u v else R₂ a x u v) := by
  have hP' : CompSet M (fun q : A × NB B m × ℕ × ℕ => P (nbBase m q.2.1)) :=
    CompSet.comp hP ((compT_nbBase m).comp (compT_fst.comp compT_snd))
  refine CompSet.congr ((hP'.and h₁).or (hP'.not.and h₂)) fun q => ?_
  show _ ↔ if P (nbBase m q.2.1) then R₁ q.1 q.2.1 q.2.2.1 q.2.2.2 else R₂ q.1 q.2.1 q.2.2.1 q.2.2.2
  by_cases h : P (nbBase m q.2.1)
  · rw [ite_eq_left h]
    exact ⟨fun h' => h'.elim And.right (fun h'' => absurd h h''.1), fun h' => Or.inl ⟨h, h'⟩⟩
  · rw [ite_eq_right h]
    exact ⟨fun h' => h'.elim (fun h'' => absurd h''.1 h) And.right, fun h' => Or.inr ⟨h, h'⟩⟩

private theorem nrelComp_true (m : ℕ) :
    NRelComp (M := M) (A := A) (B := B) m (fun _ _ _ _ => True) := compSet_true

private theorem nrelComp_false (m : ℕ) :
    NRelComp (M := M) (A := A) (B := B) m (fun _ _ _ _ => False) := compSet_false

/-! ### Base maps and decidable predicates on the base -/

/-- Precomposition with a total computable base map. -/
theorem NSR_comp_base (m : ℕ) {C : Type} [Enc M C] (R : NRel A C m) (hR : NRelComp (M := M) m R)
    {f : B → C} (hf : CompT M f) :
    ∃ R' : NRel A B m, NRelComp (M := M) m R' ∧ ∀ a b, NSR m R' a b ↔ NSR m R a (f b) :=
  ⟨fun a x u v => R a (nbMapBase m f x) u v, nrelComp_mapBase m hR hf,
    fun a b => NSR_nbMapBase m R f a b⟩

/-- Cases on a computable predicate on the base. -/
theorem NSR_ite_dec (m : ℕ) {P : B → Prop} (hP : CompSet M P) {R₁ R₂ : NRel A B m}
    (h₁ : NRelComp (M := M) m R₁) (h₂ : NRelComp (M := M) m R₂) :
    ∃ R' : NRel A B m, NRelComp (M := M) m R' ∧
      ∀ a b, NSR m R' a b ↔ if P b then NSR m R₁ a b else NSR m R₂ a b :=
  ⟨_, nrelComp_ite m hP h₁ h₂, fun a b => NSR_ite m P R₁ R₂ a b⟩

/-- Conjunction with a computable predicate on the base. -/
theorem NSR_and_dec (m : ℕ) (R : NRel A B m) (hR : NRelComp (M := M) m R) {P : B → Prop}
    (hP : CompSet M P) :
    ∃ R' : NRel A B m, NRelComp (M := M) m R' ∧ ∀ a b, NSR m R' a b ↔ P b ∧ NSR m R a b := by
  obtain ⟨R', hR', h⟩ := NSR_ite_dec m hP hR (nrelComp_false (M := M) (A := A) (B := B) m)
  refine ⟨R', hR', fun a b => (h a b).trans ?_⟩
  by_cases hb : P b
  · rw [ite_eq_left hb]; exact ⟨fun h' => ⟨hb, h'⟩, fun h' => h'.2⟩
  · rw [ite_eq_right hb]; exact ⟨fun h' => absurd h' (NSR_false m a b), fun h' => absurd h'.1 hb⟩

/-- Implication from a computable predicate on the base. -/
theorem NSR_imp_dec (m : ℕ) (R : NRel A B m) (hR : NRelComp (M := M) m R) {P : B → Prop}
    (hP : CompSet M P) :
    ∃ R' : NRel A B m, NRelComp (M := M) m R' ∧ ∀ a b, NSR m R' a b ↔ (P b → NSR m R a b) := by
  obtain ⟨R', hR', h⟩ := NSR_ite_dec m hP hR (nrelComp_true (M := M) (A := A) (B := B) m)
  refine ⟨R', hR', fun a b => (h a b).trans ?_⟩
  by_cases hb : P b
  · rw [ite_eq_left hb]; exact ⟨fun h' _ => h', fun h' => h' hb⟩
  · rw [ite_eq_right hb]; exact ⟨fun _ h' => absurd h' hb, fun _ => NSR_true m a b⟩

/-- The negation of a `Σ⁰_{m+2}` condition is a `Σ⁰_{m+3}` condition (dummy first quantifier). -/
theorem NSR_not_succ (m : ℕ) (Q : NRel A B m) (hQ : NRelComp (M := M) m Q) :
    ∃ R' : NRel A B (m + 1), NRelComp (M := M) (m + 1) R' ∧
      ∀ a b, NSR (m + 1) R' a b ↔ ¬ NSR m Q a b := by
  refine ⟨fun a x u v => ¬ Q a (nbMapBase m (fun p : B × ℕ => p.1) x) u v,
    NRelComp.compl (nrelComp_mapBase (B := B × ℕ) m hQ (compT_fst (A := B) (B := ℕ))),
    fun a b => ?_⟩
  have key : ∀ u : ℕ, NSR m (compl (B := B × ℕ) (m := m)
      (fun a x u v => ¬ Q a (nbMapBase m (fun p : B × ℕ => p.1) x) u v)) a (b, u) ↔
        NSR m Q a b := fun u =>
    (NSR_congr m (R := compl (B := B × ℕ) (m := m)
        (fun a x u v => ¬ Q a (nbMapBase m (fun p : B × ℕ => p.1) x) u v))
      (R' := fun a x u v => Q a (nbMapBase m (fun p : B × ℕ => p.1) x) u v)
      (fun _ _ _ _ => not_not) a (b, u)).trans
      (NSR_nbMapBase m Q (fun p : B × ℕ => p.1) a (b, u))
  exact ⟨fun ⟨u, hu⟩ h => hu ((key u).2 h), fun h => ⟨0, fun h' => h ((key 0).1 h')⟩⟩

/-! ### Absorbing an existential over an encoded set into the first quantifier -/

/-- The image of an encoding is a computable subset of `ℕ`. -/
private theorem compSet_img {X : Type} [Enc M X] : CompSet M (fun n : ℕ => ∃ q : X, e M q = n) :=
  TuringModel.IsCompSet.congr (Enc.img (M := M) (A := X)) fun n =>
    ⟨fun h => ⟨n, rfl, h⟩, fun ⟨_, h1, q, h2⟩ => ⟨q, h2.trans h1⟩⟩

/-- The decoding `e_X⁻¹`, patched with a default value off the image, is total computable. -/
private theorem compT_decodeD {X : Type} [Enc M X] (x₀ : X) :
    CompT M (fun n : ℕ => (Enc.decode (M := M) X n).getD x₀) := by
  refine Comp.congr (Comp.cases (compSet_img (M := M) (X := X)) (comp_decode (M := M) (A := X))
    (compT_const (M := M) (A := ℕ) x₀)) fun n => ?_
  show (if ∃ q : X, e M q = n then Enc.decode (M := M) X n else some x₀) =
    some ((Enc.decode (M := M) X n).getD x₀)
  by_cases h : ∃ q : X, e M q = n
  · obtain ⟨q, rfl⟩ := h
    rw [ite_eq_left ⟨q, rfl⟩, Enc.decode_e]; rfl
  · rw [ite_eq_right h, Enc.decode_eq_none_iff.2 (fun q hq => h ⟨q, hq⟩)]; rfl

/-- Level `0`: `∃ q ∃ u ∀ v, R a (b, q) u v ↔ ∃ ⟨e q, u⟩ ∀ v, …`. -/
private theorem NSR_exists_absorb_zero {X : Type} [Enc M X] (R : NRel A (B × X) 0)
    (hR : NRelComp (M := M) 0 R) :
    ∃ R' : NRel A B 0, NRelComp (M := M) 0 R' ∧
      ∀ a b, NSR 0 R' a b ↔ ∃ q : X, NSR 0 R a (b, q) := by
  have hΦ : CompSet M (fun p : (A × B × ℕ × ℕ) × X =>
      R p.1.1 (p.1.2.1, p.2) (M.unpair p.1.2.2.1).2 p.1.2.2.2) :=
    CompSet.comp hR (CompT.pair (compT_fst.comp compT_fst)
      (CompT.pair (CompT.pair (compT_fst.comp (compT_snd.comp compT_fst)) compT_snd)
        (CompT.pair
          (compT_unpair_snd.comp (compT_fst.comp (compT_snd.comp (compT_snd.comp compT_fst))))
          (compT_snd.comp (compT_snd.comp (compT_snd.comp compT_fst))))))
  have hD := CompSet.comp (CompSet.exists_decode (M := M) (X := X)
      (Φ := fun (t : A × B × ℕ × ℕ) (q : X) => R t.1 (t.2.1, q) (M.unpair t.2.2.1).2 t.2.2.2) hΦ)
    (CompT.pair compT_id (compT_unpair_fst.comp (compT_fst.comp (compT_snd.comp compT_snd))))
  refine ⟨fun a b u v => ∃ q : X, e M q = (M.unpair u).1 ∧ R a (b, q) (M.unpair u).2 v, hD,
    fun a b => ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu⟩
    obtain ⟨q₀, hq₀, _⟩ := hu 0
    refine ⟨q₀, (M.unpair u).2, fun v => ?_⟩
    obtain ⟨q, hq, hr⟩ := hu v
    rwa [Enc.inj (hq.trans hq₀.symm)] at hr
  · rintro ⟨q, u, hu⟩
    refine ⟨M.pair (e M q) u, fun v => ⟨q, ?_, ?_⟩⟩
    · rw [M.unpair_pair]
    · rw [M.unpair_pair]; exact hu v

/-- Level `m + 1`: `∃ q ∃ u ¬ N ((b, q), u) ↔ ∃ ⟨e q, u⟩ ¬ N ((b, q), u)`, where the inner condition
is transported along the decoding `(b, ⟨n, u⟩) ↦ ((b, e⁻¹ n), u)` and made `True` off the image. -/
private theorem NSR_exists_absorb_succ (m : ℕ) {X : Type} [Enc M X] (R : NRel A (B × X) (m + 1))
    (hR : NRelComp (M := M) (m + 1) R) :
    ∃ R' : NRel A B (m + 1), NRelComp (M := M) (m + 1) R' ∧
      ∀ a b, NSR (m + 1) R' a b ↔ ∃ q : X, NSR (m + 1) R a (b, q) := by
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    have hdec : ∀ q : X, (Enc.decode (M := M) X (e M q)).getD x₀ = q := fun q => by
      rw [Enc.decode_e]; rfl
    have hg : CompT M (fun p : B × ℕ =>
        ((p.1, (Enc.decode (M := M) X (M.unpair p.2).1).getD x₀), (M.unpair p.2).2)) :=
      CompT.pair (CompT.pair compT_fst ((compT_decodeD x₀).comp (compT_unpair_fst.comp compT_snd)))
        (compT_unpair_snd.comp compT_snd)
    have hP : CompSet M (fun p : B × ℕ => ∃ q : X, e M q = (M.unpair p.2).1) :=
      CompSet.comp (P := fun n : ℕ => ∃ q : X, e M q = n) (g := fun p : B × ℕ => (M.unpair p.2).1)
        (compSet_img (X := X)) (compT_unpair_fst.comp compT_snd)
    obtain ⟨T, hT, hTe⟩ := NSR_comp_base m (C := (B × X) × ℕ)
      (compl (B := (B × X) × ℕ) (m := m) R) hR.compl hg
    obtain ⟨S, hS, hSe⟩ := NSR_imp_dec m T hT hP
    refine ⟨fun a x u v => ¬ S a x u v, hS.compl, fun a b => ?_⟩
    have key : ∀ u, NSR m (compl (B := B × ℕ) (m := m) (fun a x u v => ¬ S a x u v)) a (b, u) ↔
        ((∃ q : X, e M q = (M.unpair u).1) →
          NSR m (compl (B := (B × X) × ℕ) (m := m) R) a
            ((b, (Enc.decode (M := M) X (M.unpair u).1).getD x₀), (M.unpair u).2)) := fun u =>
      (NSR_congr m (R := compl (B := B × ℕ) (m := m) (fun a x u v => ¬ S a x u v)) (R' := S)
        (fun _ _ _ _ => not_not) a (b, u)).trans
        ((hSe a (b, u)).trans (imp_congr_right fun _ => hTe a (b, u)))
    show (∃ u, ¬ NSR m (compl (B := B × ℕ) (m := m) (fun a x u v => ¬ S a x u v)) a (b, u)) ↔
      ∃ q : X, ∃ u, ¬ NSR m (compl (B := (B × X) × ℕ) (m := m) R) a ((b, q), u)
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨⟨q, hq⟩, hN⟩ := not_imp.1 (fun h => hu ((key u).2 h))
      refine ⟨q, (M.unpair u).2, ?_⟩
      rwa [← hq, hdec] at hN
    · rintro ⟨q, u, hu⟩
      refine ⟨M.pair (e M q) u, fun h => ?_⟩
      have h' := (key _).1 h ⟨q, by rw [M.unpair_pair]⟩
      rw [M.unpair_pair, hdec] at h'
      exact hu h'
  · refine ⟨fun _ _ _ _ => False, nrelComp_false (m + 1), fun a b =>
      ⟨fun h => absurd h (NSR_false (m + 1) a b), fun ⟨q, _⟩ => absurd ⟨q⟩ hX⟩⟩

/-- An existential over an encoded set, absorbed into the first quantifier. -/
theorem NSR_exists_absorb (m : ℕ) {X : Type} [Enc M X] (R : NRel A (B × X) m)
    (hR : NRelComp (M := M) m R) :
    ∃ R' : NRel A B m, NRelComp (M := M) m R' ∧ ∀ a b, NSR m R' a b ↔ ∃ q : X, NSR m R a (b, q) := by
  cases m with
  | zero => exact NSR_exists_absorb_zero R hR
  | succ m => exact NSR_exists_absorb_succ m R hR

/-- A disjunction of two conditions (case distinction in the first quantifier). -/
theorem NSR_or_absorb (m : ℕ) (R₁ R₂ : NRel A B m) (h₁ : NRelComp (M := M) m R₁)
    (h₂ : NRelComp (M := M) m R₂) :
    ∃ R' : NRel A B m, NRelComp (M := M) m R' ∧ ∀ a b, NSR m R' a b ↔ NSR m R₁ a b ∨ NSR m R₂ a b := by
  -- `∃ s : Bool, if s then NSR m R₁ a b else NSR m R₂ a b`
  obtain ⟨T₁, hT₁, e₁⟩ := NSR_comp_base m R₁ h₁ (compT_fst (A := B) (B := Bool))
  obtain ⟨T₂, hT₂, e₂⟩ := NSR_comp_base m R₂ h₂ (compT_fst (A := B) (B := Bool))
  obtain ⟨T, hT, eT⟩ := NSR_ite_dec m (P := fun p : B × Bool => p.2 = true)
    (CompT.toCompSet (compT_snd (A := B) (B := Bool))) hT₁ hT₂
  obtain ⟨R', hR', e'⟩ := NSR_exists_absorb m T hT
  refine ⟨R', hR', fun a b => (e' a b).trans ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs⟩
    have hs' := (eT a (b, s)).1 hs
    cases s with
    | true =>
      rw [ite_eq_left (rfl : (b, true).2 = true)] at hs'
      exact Or.inl ((e₁ a (b, true)).1 hs')
    | false =>
      rw [ite_eq_right (Bool.false_ne_true : (b, false).2 ≠ true)] at hs'
      exact Or.inr ((e₂ a (b, false)).1 hs')
  · rintro (h | h)
    · refine ⟨true, (eT a (b, true)).2 ?_⟩
      rw [ite_eq_left rfl]; exact (e₁ a (b, true)).2 h
    · refine ⟨false, (eT a (b, false)).2 ?_⟩
      rw [ite_eq_right Bool.false_ne_true]; exact (e₂ a (b, false)).2 h

/-! ### Bounded quantifiers over the entries of a list -/

/-- An existential over a computable relation `Q b q`, with the condition evaluated at a
computable function of `(b, q)`. -/
theorem NSR_exists_rel (m : ℕ) {X C : Type} [Enc M X] [Enc M C] {Q : B → X → Prop}
    (hQ : CompSet M (fun p : B × X => Q p.1 p.2)) {f : B × X → C} (hf : CompT M f)
    (R : NRel A C m) (hR : NRelComp (M := M) m R) :
    ∃ R' : NRel A B m, NRelComp (M := M) m R' ∧
      ∀ a b, NSR m R' a b ↔ ∃ q : X, Q b q ∧ NSR m R a (f (b, q)) := by
  obtain ⟨R₁, hR₁, e₁⟩ := NSR_comp_base m R hR hf
  obtain ⟨R₂, hR₂, e₂⟩ := NSR_and_dec m R₁ hR₁ hQ
  obtain ⟨R₃, hR₃, e₃⟩ := NSR_exists_absorb m R₂ hR₂
  exact ⟨R₃, hR₃, fun a b => (e₃ a b).trans
    (exists_congr fun q => (e₂ a (b, q)).trans (and_congr_right' (e₁ a (b, q))))⟩

/-- A bounded existential over the entries of a list. -/
theorem NSR_exists_nth_absorb (m : ℕ) (R : NRel A B m) (hR : NRelComp (M := M) m R) :
    ∃ R' : NRel A (List B) m, NRelComp (M := M) m R' ∧
      ∀ a (l : List B), NSR m R' a l ↔ ∃ j, j < l.length ∧ ∃ b, l[j]? = some b ∧ NSR m R a b := by
  have hQ : CompSet M (fun p : List B × (ℕ × B) => p.1[p.2.1]? = some p.2.2) :=
    compSet_eq (compT_nthOpt.comp (CompT.pair compT_fst (compT_fst.comp compT_snd)))
      (compT_some.comp (compT_snd.comp compT_snd))
  obtain ⟨R', hR', e'⟩ := NSR_exists_rel m (Q := fun (l : List B) (q : ℕ × B) => l[q.1]? = some q.2)
    hQ (f := fun r : List B × (ℕ × B) => r.2.2) (compT_snd.comp compT_snd) R hR
  refine ⟨R', hR', fun a l => (e' a l).trans ⟨?_, ?_⟩⟩
  · rintro ⟨⟨j, b⟩, hb, hN⟩
    exact ⟨j, (List.getElem?_eq_some_iff.1 hb).1, b, hb, hN⟩
  · rintro ⟨j, _, b, hb, hN⟩
    exact ⟨(j, b), hb, hN⟩

/-- Lists of witnesses: from `∀ j < n, ∃ u, P j u` a list `ū` of length `n` with `P j ū[j]`. -/
private theorem list_choice {P : ℕ → ℕ → Prop} : ∀ n : ℕ, (∀ j, j < n → ∃ u, P j u) →
    ∃ us : List ℕ, us.length = n ∧ ∀ j w, us[j]? = some w → P j w
  | 0, _ => ⟨[], rfl, fun j w h => by simp at h⟩
  | n + 1, h => by
    obtain ⟨us, hlen, hus⟩ := list_choice n (fun j hj => h j (Nat.lt_succ_of_lt hj))
    obtain ⟨u, hu⟩ := h n (Nat.lt_succ_self n)
    refine ⟨us ++ [u], by simp [hlen], fun j w hw => ?_⟩
    rcases Nat.lt_or_ge j n with hj | hj
    · rw [List.getElem?_append_left (by omega)] at hw
      exact hus j w hw
    · rw [List.getElem?_append_right (by omega), List.getElem?_singleton] at hw
      by_cases h0 : j - us.length = 0
      · rw [ite_eq_left h0] at hw
        cases hw
        have : j = n := by omega
        subst this; exact hu
      · rw [ite_eq_right h0] at hw; cases hw

/-- `∀ b, f y = some b → Φ y b` is decidable for total computable `f` and decidable `Φ`. -/
private theorem compSet_forall_eq_some {Y Z : Type} [Enc M Y] [Enc M Z] {f : Y → Option Z}
    (hf : CompT M f) {Φ : Y → Z → Prop} (hΦ : CompSet M (fun p : Y × Z => Φ p.1 p.2)) :
    CompSet M (fun y => ∀ z, f y = some z → Φ y z) :=
  CompSet.congr (CompSet.not (CompSet.exists_eq_some hf (Φ := fun y z => ¬ Φ y z) hΦ.not))
    fun _ => ⟨fun h z hz => Classical.byContradiction fun hc => h ⟨z, hz, hc⟩,
      fun h ⟨z, hz, hc⟩ => hc (h z hz)⟩

/-- Level `0`: the first quantifier ranges over lists of witnesses `ū` (with `|ū| = |l|`), the
second over pairs `⟨j, v⟩`. -/
private theorem NSR_forall_nth_absorb_zero (R : NRel A B 0) (hR : NRelComp (M := M) 0 R) :
    ∃ R' : NRel A (List B) 0, NRelComp (M := M) 0 R' ∧
      ∀ a (l : List B), NSR 0 R' a l ↔ ∀ j, j < l.length → ∃ b, l[j]? = some b ∧ NSR 0 R a b := by
  have hΦ : NRelComp (M := M) 0 (fun a (p : List B × List ℕ) (_ V : ℕ) =>
      p.2.length = p.1.length ∧ ∀ b, p.1[(M.unpair V).1]? = some b →
        ∀ w, p.2[(M.unpair V).1]? = some w → R a b w (M.unpair V).2) := by
    have hlen : CompSet M (fun t : A × (List B × List ℕ) × ℕ × ℕ =>
        t.2.1.2.length = t.2.1.1.length) :=
      compSet_eq (compT_length.comp (compT_snd.comp (compT_fst.comp compT_snd)))
        (compT_length.comp (compT_fst.comp (compT_fst.comp compT_snd)))
    have hR' : CompSet M (fun r : ((A × (List B × List ℕ) × ℕ × ℕ) × B) × ℕ =>
        R r.1.1.1 r.1.2 r.2 (M.unpair r.1.1.2.2.2).2) :=
      CompSet.comp hR (CompT.pair (compT_fst.comp (compT_fst.comp compT_fst))
        (CompT.pair (compT_snd.comp compT_fst) (CompT.pair compT_snd
          (compT_unpair_snd.comp (compT_snd.comp (compT_snd.comp (compT_snd.comp
            (compT_fst.comp compT_fst))))))))
    have hw : CompSet M (fun p : (A × (List B × List ℕ) × ℕ × ℕ) × B =>
        ∀ w, p.1.2.1.2[(M.unpair p.1.2.2.2).1]? = some w → R p.1.1 p.2 w (M.unpair p.1.2.2.2).2) :=
      compSet_forall_eq_some
        (compT_nthOpt.comp (CompT.pair (compT_snd.comp (compT_fst.comp (compT_snd.comp compT_fst)))
          (compT_unpair_fst.comp (compT_snd.comp (compT_snd.comp (compT_snd.comp compT_fst))))))
        (Φ := fun p w => R p.1.1 p.2 w (M.unpair p.1.2.2.2).2) hR'
    have hb : CompSet M (fun t : A × (List B × List ℕ) × ℕ × ℕ =>
        ∀ b, t.2.1.1[(M.unpair t.2.2.2).1]? = some b →
          ∀ w, t.2.1.2[(M.unpair t.2.2.2).1]? = some w → R t.1 b w (M.unpair t.2.2.2).2) :=
      compSet_forall_eq_some
        (compT_nthOpt.comp (CompT.pair (compT_fst.comp (compT_fst.comp compT_snd))
          (compT_unpair_fst.comp (compT_snd.comp (compT_snd.comp compT_snd)))))
        (Φ := fun t b => ∀ w, t.2.1.2[(M.unpair t.2.2.2).1]? = some w →
          R t.1 b w (M.unpair t.2.2.2).2) hw
    exact hlen.and hb
  obtain ⟨R', hR', e'⟩ := NSR_exists_absorb 0 _ hΦ
  refine ⟨R', hR', fun a l => (e' a l).trans ⟨?_, ?_⟩⟩
  · rintro ⟨us, _, hV⟩ j hj
    have hlen : us.length = l.length := (hV 0).1
    refine ⟨l[j], List.getElem?_eq_getElem hj, us[j]'(by omega), fun v => ?_⟩
    have h := (hV (M.pair j v)).2
    rw [M.unpair_pair] at h
    exact h _ (List.getElem?_eq_getElem hj) _ (List.getElem?_eq_getElem _)
  · intro h
    obtain ⟨us, hlen, hus⟩ := list_choice (P := fun j w => ∀ b, l[j]? = some b → ∀ v, R a b w v)
      l.length (fun j hj => by
        obtain ⟨b, hb, u, hu⟩ := h j hj
        exact ⟨u, fun b' hb' => by rw [hb] at hb'; cases hb'; exact hu⟩)
    exact ⟨us, 0, fun V => ⟨hlen, fun b hb w hw => hus _ w hw b hb _⟩⟩

/-- Level `m + 1`: `∀ j < |l|, ∃ u, ¬ N (l[j], u)` iff some list `ū` with `|ū| = |l|` has
`¬ ∃ j, N (l[j], ū[j])`, and the bounded existential is absorbed at level `m`. -/
private theorem NSR_forall_nth_absorb_succ (m : ℕ) (R : NRel A B (m + 1))
    (hR : NRelComp (M := M) (m + 1) R) :
    ∃ R' : NRel A (List B) (m + 1), NRelComp (M := M) (m + 1) R' ∧
      ∀ a (l : List B), NSR (m + 1) R' a l ↔
        ∀ j, j < l.length → ∃ b, l[j]? = some b ∧ NSR (m + 1) R a b := by
  have hQ : CompSet M (fun p : (List B × List ℕ) × (ℕ × (B × ℕ)) =>
      p.1.1[p.2.1]? = some p.2.2.1 ∧ p.1.2[p.2.1]? = some p.2.2.2) :=
    (compSet_eq (compT_nthOpt.comp (CompT.pair (compT_fst.comp compT_fst) (compT_fst.comp compT_snd)))
      (compT_some.comp (compT_fst.comp (compT_snd.comp compT_snd)))).and
    (compSet_eq (compT_nthOpt.comp (CompT.pair (compT_snd.comp compT_fst) (compT_fst.comp compT_snd)))
      (compT_some.comp (compT_snd.comp (compT_snd.comp compT_snd))))
  obtain ⟨Q₁, hQ₁, e₁⟩ := NSR_exists_rel m
    (Q := fun (p : List B × List ℕ) (q : ℕ × (B × ℕ)) => p.1[q.1]? = some q.2.1 ∧ p.2[q.1]? = some q.2.2)
    hQ (f := fun r : (List B × List ℕ) × (ℕ × (B × ℕ)) => r.2.2) (compT_snd.comp compT_snd)
    (compl (B := B × ℕ) (m := m) R) hR.compl
  obtain ⟨Q₂, hQ₂, e₂⟩ := NSR_imp_dec m Q₁ hQ₁ (P := fun p : List B × List ℕ => p.2.length = p.1.length)
    (compSet_eq (compT_length.comp compT_snd) (compT_length.comp compT_fst))
  obtain ⟨Q₃, hQ₃, e₃⟩ := NSR_not_succ m Q₂ hQ₂
  obtain ⟨R', hR', e'⟩ := NSR_exists_absorb (m + 1) Q₃ hQ₃
  refine ⟨R', hR', fun a l => (e' a l).trans ?_⟩
  have key : ∀ us : List ℕ, NSR (m + 1) Q₃ a (l, us) ↔ (us.length = l.length ∧
      ∀ (j : ℕ) b w, l[j]? = some b → us[j]? = some w →
        ¬ NSR m (compl (B := B × ℕ) (m := m) R) a (b, w)) := by
    intro us
    refine (e₃ a (l, us)).trans ((not_congr (e₂ a (l, us))).trans ?_)
    constructor
    · intro h
      obtain ⟨hlen, hN⟩ := not_imp.1 h
      exact ⟨hlen, fun j b w hb hw hc => hN ((e₁ a (l, us)).2 ⟨(j, (b, w)), ⟨hb, hw⟩, hc⟩)⟩
    · rintro ⟨hlen, hall⟩ h
      obtain ⟨⟨j, b, w⟩, ⟨hb, hw⟩, hc⟩ := (e₁ a (l, us)).1 (h hlen)
      exact hall j b w hb hw hc
  constructor
  · rintro ⟨us, hus⟩ j hj
    obtain ⟨hlen, hall⟩ := (key us).1 hus
    exact ⟨l[j], List.getElem?_eq_getElem hj, (NSR_succ m R a l[j]).2
      ⟨us[j]'(by omega), hall j _ _ (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem _)⟩⟩
  · intro h
    obtain ⟨us, hlen, hus⟩ := list_choice
      (P := fun j w => ∀ b, l[j]? = some b → ¬ NSR m (compl (B := B × ℕ) (m := m) R) a (b, w))
      l.length (fun j hj => by
        obtain ⟨b, hb, hN⟩ := h j hj
        obtain ⟨u, hu⟩ := (NSR_succ m R a b).1 hN
        exact ⟨u, fun b' hb' => by rw [hb] at hb'; cases hb'; exact hu⟩)
    exact ⟨us, (key us).2 ⟨hlen, fun j b w hb hw => hus j w hw b hb⟩⟩

/-- A bounded universal over the entries of a list, absorbed by quantifying over lists of
witnesses (Section 6.2). -/
theorem NSR_forall_nth_absorb (m : ℕ) (R : NRel A B m) (hR : NRelComp (M := M) m R) :
    ∃ R' : NRel A (List B) m, NRelComp (M := M) m R' ∧
      ∀ a (l : List B), NSR m R' a l ↔ ∀ j, j < l.length → ∃ b, l[j]? = some b ∧ NSR m R a b := by
  cases m with
  | zero => exact NSR_forall_nth_absorb_zero R hR
  | succ m => exact NSR_forall_nth_absorb_succ m R hR

end Stable
