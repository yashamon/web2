import Stable.PropCalc

/-!
# Perturbing the identity translation along pairwise inconsistent sentences

This file is the language-independent core of Appendix B (the maps `θ_K`, `θ` and the translation
built from them), in the generality needed for Proposition B.10.

Let `𝓛` be a language with unique readability (`SentSyntax`). A `Perturb 𝓛` consists of *stages*
`s`, each with a sentence `E s`, a map `act s : 𝓛 → 𝓛` and a level `lvl s ∈ ℕ`, such that: the
`E s` are pairwise inconsistent; `act s` commutes with `¬` and `∧`; `{E s} ⊢ act s b` for logically
valid `b`; `{E s} ⊢ b ↔ act s b` when the code of `b` is at most `lvl s`; and for every `K` there are
only finitely many stages of level `< K` (`below K`). In the manuscript `E s` holds in a structure
`M` iff `M` is to be replaced by the structure `M^{(s)}`, and `act s b` says "`M^{(s)} ⊨ b`".

For a set `Y` of stages, `θ (b)` says: `act s b` on the models of `E s`, `s ∈ Y`, and `b` elsewhere.
`θ` commutes with the connectives up to logical equivalence and preserves validity; so replacing
each prime sentence `p` by `wrap (θ p)`, or by `wrap p` for `p` in a set `P0` of prime sentences
fixed by all `act s`, gives a translation `𝓛 → 𝓛` (`Perturb.trans`).
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-! ### Unique readability -/

/-- Sentences are generated from *prime* sentences by `¬` and `∧`, with unique readability
(`destruct`), a size function for recursion, and `wrap s` (in the manuscript `∀y (y = y ∧ s)`): a
prime sentence logically equivalent to `s`, injective in `s`. -/
structure SentSyntax (L : Language M) where
  /-- `destruct s = none` iff `s` is prime, `some (inl a)` iff `s = ¬a`, `some (inr (a, b))` iff
  `s = a ∧ b`. -/
  destruct : L.Sent → Option (L.Sent ⊕ (L.Sent × L.Sent))
  destruct_neg : ∀ a, destruct (L.neg a) = some (Sum.inl a)
  destruct_and : ∀ a b, destruct (L.and a b) = some (Sum.inr (a, b))
  destruct_inl : ∀ s a, destruct s = some (Sum.inl a) → s = L.neg a
  destruct_inr : ∀ s a b, destruct s = some (Sum.inr (a, b)) → s = L.and a b
  size : L.Sent → ℕ
  size_neg : ∀ a, size a < size (L.neg a)
  size_and_left : ∀ a b, size a < size (L.and a b)
  size_and_right : ∀ a b, size b < size (L.and a b)
  wrap : L.Sent → L.Sent
  wrap_prime : ∀ s, destruct (wrap s) = none
  wrap_inj : ∀ s t, wrap s = wrap t → s = t
  wrap_equiv : ∀ s, L.Equiv (wrap s) s

namespace SentSyntax

variable {L : Language M}

/-- `s` is a prime sentence. -/
def Prime (S : SentSyntax L) (s : L.Sent) : Prop := S.destruct s = none

theorem neg_inj (S : SentSyntax L) {a b : L.Sent} (h : L.neg a = L.neg b) : a = b := by
  have h1 := S.destruct_neg a
  rw [h, S.destruct_neg b] at h1
  cases h1; rfl

theorem and_inj (S : SentSyntax L) {a b c d : L.Sent} (h : L.and a b = L.and c d) : a = c ∧ b = d := by
  have h1 := S.destruct_and a b
  rw [h, S.destruct_and c d] at h1
  cases h1; exact ⟨rfl, rfl⟩

theorem neg_ne_and (S : SentSyntax L) (a b c : L.Sent) : L.neg a ≠ L.and b c := by
  intro h
  have h1 := S.destruct_neg a
  rw [h, S.destruct_and] at h1
  cases h1

theorem prime_ne_neg {S : SentSyntax L} {p : L.Sent} (hp : S.Prime p) (a : L.Sent) : p ≠ L.neg a := by
  intro h; unfold Prime at hp; rw [h, S.destruct_neg] at hp; cases hp

theorem prime_ne_and {S : SentSyntax L} {p : L.Sent} (hp : S.Prime p) (a b : L.Sent) : p ≠ L.and a b := by
  intro h; unfold Prime at hp; rw [h, S.destruct_and] at hp; cases hp

theorem cases (S : SentSyntax L) (s : L.Sent) :
    S.Prime s ∨ (∃ a, s = L.neg a) ∨ (∃ a b, s = L.and a b) := by
  cases h : S.destruct s with
  | none => exact Or.inl h
  | some x =>
    cases x with
    | inl a => exact Or.inr (Or.inl ⟨a, S.destruct_inl s a h⟩)
    | inr ab => exact Or.inr (Or.inr ⟨ab.1, ab.2, S.destruct_inr s ab.1 ab.2 h⟩)

/-- Induction on the size of a sentence. -/
theorem size_induction (S : SentSyntax L) {P : L.Sent → Prop}
    (h : ∀ s, (∀ t, S.size t < S.size s → P t) → P s) : ∀ s, P s := by
  have : ∀ k s, S.size s < k → P s := by
    intro k
    induction k with
    | zero => intro s hs; exact absurd hs (Nat.not_lt_zero _)
    | succ k ih => intro s hs; exact h s fun t ht => ih t (Nat.lt_of_lt_of_le ht (Nat.le_of_lt_succ hs))
  exact fun s => this (S.size s + 1) s (Nat.lt_succ_self _)

end SentSyntax

/-- Boolean combinations of sentences in `P`. -/
inductive BoolOver (L : Language M) (P : L.Sent → Prop) : L.Sent → Prop
  | prime {p : L.Sent} : P p → BoolOver L P p
  | neg {a : L.Sent} : BoolOver L P a → BoolOver L P (L.neg a)
  | and {a b : L.Sent} : BoolOver L P a → BoolOver L P b → BoolOver L P (L.and a b)

/-! ### Generic propositional helpers -/

namespace Language

variable {L : Language M}

/-- `⊥ := z ∧ ¬z`. -/
def botOf (L : Language M) (z : L.Sent) : L.Sent := L.and z (L.neg z)

/-- `⊤ := ¬⊥`. -/
def topOf (L : Language M) (z : L.Sent) : L.Sent := L.neg (L.botOf z)

theorem deriv_of_botOf {F : L.Sent → Prop} (z c : L.Sent) : L.Deriv (L.ext F (L.botOf z)) c :=
  L.deriv_explosion (L.deriv_and_left (deriv_ext_self F _)) (L.deriv_and_right (deriv_ext_self F _))

theorem deriv_topOf (F : L.Sent → Prop) (z : L.Sent) : L.Deriv F (L.topOf z) :=
  L.deriv_neg_intro fun c => deriv_of_botOf z c

theorem deriv_neg_botOf (F : L.Sent → Prop) (z : L.Sent) : L.Deriv F (L.neg (L.botOf z)) :=
  deriv_topOf F z

theorem deriv_neg_disjList {F : L.Sent → Prop} {z : L.Sent} {l : List L.Sent}
    (hl : ∀ a, a ∈ l → L.Deriv F (L.neg a)) (hz : L.Deriv F (L.neg z)) :
    L.Deriv F (L.neg (L.disjList z l)) := by
  refine deriv_neg_of (b := z) ?_ (deriv_ext_of _ hz)
  refine deriv_disjList_elim (deriv_ext_self F _) (fun a ha => ?_) (deriv_ext_self _ _)
  exact L.deriv_explosion (deriv_ext_self _ _) (deriv_ext_of _ (deriv_ext_of _ (hl a ha)))

/-- From `F ⊢ z`, `F ⊢ z'` and `F ⊢ (z → p) ↔ (z' → p')`: `F ⊢ p ↔ p'`. -/
theorem deriv_iff_of_imp_iff {F : L.Sent → Prop} {z z' p p' : L.Sent} (hz : L.Deriv F z)
    (hz' : L.Deriv F z') (h : L.Deriv F (L.iff (L.imp z p) (L.imp z' p'))) : L.Deriv F (L.iff p p') := by
  refine deriv_iff_intro ?_ ?_
  · have h1 : L.Deriv (L.ext F p) (L.imp z p) := deriv_imp_intro (deriv_ext_of _ (deriv_ext_self F p))
    exact deriv_mp (deriv_iff_mp (deriv_ext_of _ h) h1) (deriv_ext_of _ hz')
  · have h1 : L.Deriv (L.ext F p') (L.imp z' p') := deriv_imp_intro (deriv_ext_of _ (deriv_ext_self F p'))
    exact deriv_mp (deriv_iff_mpr (deriv_ext_of _ h) h1) (deriv_ext_of _ hz)

/-- From `F ⊢ z`, `F ⊢ z'` and `F ⊢ (z ∧ p) ↔ (z' ∧ p')`: `F ⊢ p ↔ p'`. -/
theorem deriv_iff_of_and_iff {F : L.Sent → Prop} {z z' p p' : L.Sent} (hz : L.Deriv F z)
    (hz' : L.Deriv F z') (h : L.Deriv F (L.iff (L.and z p) (L.and z' p'))) : L.Deriv F (L.iff p p') := by
  refine deriv_iff_intro ?_ ?_
  · exact L.deriv_and_right (deriv_iff_mp (deriv_ext_of _ h)
      (L.deriv_and_intro (deriv_ext_of _ hz) (deriv_ext_self F p)))
  · exact L.deriv_and_right (deriv_iff_mpr (deriv_ext_of _ h)
      (L.deriv_and_intro (deriv_ext_of _ hz') (deriv_ext_self F p')))

/-- The sentences with code `≤ n`. -/
noncomputable def firstN (L : Language M) (n : ℕ) : List L.Sent :=
  (List.range (n + 1)).filterMap (Enc.decode (M := M) L.Sent)

theorem mem_firstN {n : ℕ} {b : L.Sent} : b ∈ L.firstN n ↔ e M b ≤ n := by
  unfold firstN
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hdk⟩
    rw [List.mem_range] at hk
    rw [Enc.decode_eq_some_iff] at hdk
    omega
  · intro h
    exact ⟨e M b, List.mem_range.2 (by omega), Enc.decode_e b⟩

/-! ### Complete conjunctions over a finite list -/

/-- The complete conjunctions over the list `Γ`: one for each assignment of truth values to its
entries (`t` is a logically valid sentence closing the conjunction). -/
def vals (L : Language M) (t : L.Sent) : List L.Sent → List L.Sent
  | [] => [t]
  | b :: Γ => (vals L t Γ).map (L.and b) ++ (vals L t Γ).map (L.and (L.neg b))

theorem mem_vals_cons {t b ψ : L.Sent} {Γ : List L.Sent} :
    ψ ∈ L.vals t (b :: Γ) ↔ ∃ ψ₁, ψ₁ ∈ L.vals t Γ ∧ (ψ = L.and b ψ₁ ∨ ψ = L.and (L.neg b) ψ₁) := by
  show ψ ∈ (L.vals t Γ).map (L.and b) ++ (L.vals t Γ).map (L.and (L.neg b)) ↔ _
  rw [List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨ψ₁, h, rfl⟩ | ⟨ψ₁, h, rfl⟩)
    · exact ⟨ψ₁, h, Or.inl rfl⟩
    · exact ⟨ψ₁, h, Or.inr rfl⟩
  · rintro ⟨ψ₁, h, rfl | rfl⟩
    · exact Or.inl ⟨ψ₁, h, rfl⟩
    · exact Or.inr ⟨ψ₁, h, rfl⟩

/-- A complete conjunction decides every entry of `Γ`. -/
theorem vals_decide {t : L.Sent} : ∀ {Γ : List L.Sent} {ψ b : L.Sent}, ψ ∈ L.vals t Γ → b ∈ Γ →
    L.Deriv (L.single ψ) b ∨ L.Deriv (L.single ψ) (L.neg b)
  | [], _, _, _, hb => by cases hb
  | c :: Γ, ψ, b, hψ, hb => by
    obtain ⟨ψ₁, h₁, hψ⟩ := mem_vals_cons.1 hψ
    rw [List.mem_cons] at hb
    rcases hb with rfl | hb
    · rcases hψ with rfl | rfl
      · exact Or.inl (L.deriv_and_left (deriv_single_self _))
      · exact Or.inr (L.deriv_and_left (deriv_single_self _))
    · have h2 : L.Deriv (L.single ψ) ψ₁ := by
        rcases hψ with rfl | rfl <;> exact L.deriv_and_right (deriv_single_self _)
      rcases vals_decide h₁ hb with h | h
      · exact Or.inl (deriv_of_single h2 h)
      · exact Or.inr (deriv_of_single h2 h)

/-- Distinct complete conjunctions are inconsistent with each other. -/
theorem vals_excl {t : L.Sent} : ∀ {Γ : List L.Sent} {ψ ψ' : L.Sent}, ψ ∈ L.vals t Γ →
    ψ' ∈ L.vals t Γ → ψ ≠ ψ' → L.Deriv (L.single ψ) (L.neg ψ')
  | [], ψ, ψ', hψ, hψ', hne => by
    rw [show L.vals t [] = [t] from rfl, List.mem_singleton] at hψ hψ'
    exact absurd (hψ.trans hψ'.symm) hne
  | c :: Γ, ψ, ψ', hψ, hψ', hne => by
    obtain ⟨ψ₁, h₁, hψ⟩ := mem_vals_cons.1 hψ
    obtain ⟨ψ₂, h₂, hψ'⟩ := mem_vals_cons.1 hψ'
    -- the inductive case: same first conjunct
    have same : ∀ u : L.Sent, ψ = L.and u ψ₁ → ψ' = L.and u ψ₂ → L.Deriv (L.single ψ) (L.neg ψ') := by
      intro u hu hu'
      have hne' : ψ₁ ≠ ψ₂ := fun h => hne (by rw [hu, hu', h])
      have ih := vals_excl h₁ h₂ hne'
      have h3 : L.Deriv (L.single ψ) (L.neg ψ₂) :=
        deriv_of_single (by rw [hu]; exact L.deriv_and_right (deriv_single_self _)) ih
      rw [hu']
      exact deriv_neg_of (b := ψ₂) (L.deriv_and_right (deriv_ext_self _ _)) (deriv_ext_of _ h3)
    rcases hψ with hu | hu <;> rcases hψ' with hu' | hu'
    · exact same c hu hu'
    · rw [hu, hu']
      exact deriv_neg_of (b := c) (deriv_ext_of _ (L.deriv_and_left (deriv_single_self _)))
        (L.deriv_and_left (deriv_ext_self _ _))
    · rw [hu, hu']
      exact deriv_neg_of (b := c) (L.deriv_and_left (deriv_ext_self _ _))
        (deriv_ext_of _ (L.deriv_and_left (deriv_single_self _)))
    · exact same (L.neg c) hu hu'

/-- Some complete conjunction holds. -/
theorem deriv_disj_vals {F : L.Sent → Prop} {t z : L.Sent} (ht : L.Deriv F t) :
    ∀ Γ : List L.Sent, L.Deriv F (L.disjList z (L.vals t Γ))
  | [] => deriv_disjList_of_mem (List.Mem.head _) ht
  | c :: Γ => by
    have ih := deriv_disj_vals (z := z) ht Γ
    have step : ∀ u : L.Sent, (∀ ψ₁, ψ₁ ∈ L.vals t Γ → L.and u ψ₁ ∈ L.vals t (c :: Γ)) →
        L.Deriv (L.ext F u) (L.disjList z (L.vals t (c :: Γ))) := by
      intro u hu
      refine deriv_disjList_elim (deriv_ext_of u ih) (fun ψ₁ hψ₁ => ?_)
        (deriv_disjList_of_z (deriv_ext_self _ z) _)
      exact deriv_disjList_of_mem (hu ψ₁ hψ₁)
        (L.deriv_and_intro (deriv_ext_of _ (deriv_ext_self F u)) (deriv_ext_self _ ψ₁))
    refine deriv_cases (c := c) (step c fun ψ₁ h => ?_) (step (L.neg c) fun ψ₁ h => ?_)
    · exact mem_vals_cons.2 ⟨ψ₁, h, Or.inl rfl⟩
    · exact mem_vals_cons.2 ⟨ψ₁, h, Or.inr rfl⟩

end Language

/-! ### Translations and the derived connectives -/

namespace Translation

variable {L' L : Language M} (i : Translation L' L)

theorem map_imp (a b : L'.Sent) : i.i (L'.imp a b) = L.imp (i.i a) (i.i b) := by
  unfold Language.imp; rw [i.map_neg, i.map_and, i.map_neg]

theorem map_iff (a b : L'.Sent) : i.i (L'.iff a b) = L.iff (i.i a) (i.i b) := by
  unfold Language.iff; rw [i.map_and, i.map_imp, i.map_imp]

theorem map_conjList (z : L'.Sent) (l : List L'.Sent) :
    i.i (L'.conjList z l) = L.conjList (i.i z) (l.map i.i) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [Language.conjList, List.map_cons]; rw [i.map_and, ih]

theorem map_botOf (z : L'.Sent) : i.i (L'.botOf z) = L.botOf (i.i z) := by
  unfold Language.botOf; rw [i.map_and, i.map_neg]

theorem map_topOf (z : L'.Sent) : i.i (L'.topOf z) = L.topOf (i.i z) := by
  unfold Language.topOf; rw [i.map_neg, i.map_botOf]

/-- `{a} ⊢ b` gives `{i a} ⊢ i b`. -/
theorem deriv_single {a b : L'.Sent} (h : L'.Deriv (L'.single a) b) :
    L.Deriv (L.single (i.i a)) (i.i b) := by
  refine L.deriv_mono (fun β hβ => ?_) (i.map_deriv _ _ h)
  obtain ⟨γ, hγ, rfl⟩ := hβ
  exact congrArg i.i hγ

/-- `F ∪ {a} ⊢ b` gives `i (F) ∪ {i a} ⊢ i b`, in the form used. -/
theorem deriv_ext {F : L'.Sent → Prop} {G : L.Sent → Prop} {a b : L'.Sent}
    (hF : ∀ γ, F γ → L.Deriv G (i.i γ)) (h : L'.Deriv (L'.ext F a) b) :
    L.Deriv (L.ext G (i.i a)) (i.i b) := by
  refine L.deriv_cut (fun β hβ => ?_) (i.map_deriv _ _ h)
  obtain ⟨γ, hγ, rfl⟩ := hβ
  rcases hγ with hγ | hγ
  · exact Language.deriv_ext_of _ (hF γ hγ)
  · rw [hγ]; exact Language.deriv_ext_self _ _

end Translation

/-! ### Stages -/

/-- A system of stages; see the module docstring. Only the *live* stages matter. -/
structure Perturb (L : Language M) where
  /-- The stages. -/
  I : Type
  E : I → L.Sent
  act : I → L.Sent → L.Sent
  lvl : I → ℕ
  live : I → Prop
  /-- The live stages of level `< K`. -/
  below : ℕ → List I
  mem_below : ∀ K s, s ∈ below K ↔ live s ∧ lvl s < K
  /-- A sentence, used to form `⊥ := z0 ∧ ¬z0`. -/
  z0 : L.Sent
  excl : ∀ s t, live s → live t → s ≠ t → L.Deriv (L.single (E s)) (L.neg (E t))
  act_neg : ∀ s a, act s (L.neg a) = L.neg (act s a)
  act_and : ∀ s a b, act s (L.and a b) = L.and (act s a) (act s b)
  act_valid : ∀ s b, live s → L.Valid b → L.Deriv (L.single (E s)) (act s b)
  act_ev : ∀ s b, live s → e M b ≤ lvl s → L.Deriv (L.single (E s)) (L.iff b (act s b))

namespace Perturb

variable {L : Language M} (P : Perturb L) (Y : P.I → Prop)

/-- The stages of `Y` of level `< K`. -/
noncomputable def Xlist (K : ℕ) : List P.I := (P.below K).filter (fun s => decide (Y s))

theorem mem_Xlist {K : ℕ} {s : P.I} : s ∈ P.Xlist Y K ↔ P.live s ∧ P.lvl s < K ∧ Y s := by
  unfold Xlist
  rw [List.mem_filter, P.mem_below, decide_eq_true_iff, and_assoc]

/-- `D_K := ⋁ E s` over the stages of `Y` of level `< K`. -/
noncomputable def bigD (K : ℕ) : L.Sent := L.disjList (L.botOf P.z0) ((P.Xlist Y K).map P.E)

/-- `θ_K (b)`. -/
noncomputable def thetaK (K : ℕ) (b : L.Sent) : L.Sent :=
  L.or (L.and b (L.neg (P.bigD Y K)))
    (L.disjList (L.botOf P.z0) ((P.Xlist Y K).map (fun s => L.and (P.act s b) (P.E s))))

/-- `θ (b) := θ_{k(b)+1} (b)`. -/
noncomputable def theta (b : L.Sent) : L.Sent := P.thetaK Y (e M b + 1) b

theorem E_deriv_bigD {K : ℕ} {s : P.I} (hs : s ∈ P.Xlist Y K) :
    L.Deriv (L.single (P.E s)) (P.bigD Y K) :=
  Language.deriv_disjList_of_mem (List.mem_map.2 ⟨s, hs, rfl⟩) (Language.deriv_single_self _)

/-- `{E s} ⊢ ¬D_K` when `s` is live and not among the stages of `D_K`. -/
theorem E_deriv_neg_bigD {K : ℕ} {s : P.I} (hl : P.live s) (hs : s ∉ P.Xlist Y K) :
    L.Deriv (L.single (P.E s)) (L.neg (P.bigD Y K)) := by
  refine Language.deriv_neg_disjList (fun a ha => ?_) (Language.deriv_neg_botOf _ _)
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
  exact P.excl s t hl ((P.mem_Xlist Y).1 ht).1 (fun h => hs (h ▸ ht))

/-- `θ_K (b)` is `act s b` on the models of `E s`, for `s` among the stages of `D_K`. -/
theorem thetaK_pos {K : ℕ} {s : P.I} (hs : s ∈ P.Xlist Y K) (b : L.Sent) :
    L.Deriv (L.single (P.E s)) (L.iff (P.thetaK Y K b) (P.act s b)) := by
  have hl := ((P.mem_Xlist Y).1 hs).1
  refine Language.deriv_iff_intro ?_ ?_
  · refine Language.deriv_or_elim' ?_ ?_
    · exact L.deriv_explosion (Language.deriv_ext_of _ (P.E_deriv_bigD Y hs))
        (L.deriv_and_right (Language.deriv_ext_self _ _))
    · refine Language.deriv_disjList_elim (Language.deriv_ext_self _ _) (fun a ha => ?_)
        (Language.deriv_of_botOf _ _)
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
      by_cases hts : t = s
      · rw [hts]; exact L.deriv_and_left (Language.deriv_ext_self _ _)
      · exact L.deriv_explosion (L.deriv_and_right (Language.deriv_ext_self _ _))
          (Language.deriv_ext_of _ (Language.deriv_ext_of _
            (P.excl s t hl ((P.mem_Xlist Y).1 ht).1 (fun h => hts h.symm))))
  · refine Language.deriv_or_inr _ (Language.deriv_disjList_of_mem (List.mem_map.2 ⟨s, hs, rfl⟩) ?_)
    exact L.deriv_and_intro (Language.deriv_ext_self _ _)
      (Language.deriv_ext_of _ (Language.deriv_single_self _))

/-- `θ_K (b)` is `b` on the models of `¬D_K`. -/
theorem thetaK_neg (K : ℕ) (b : L.Sent) :
    L.Deriv (L.single (L.neg (P.bigD Y K))) (L.iff (P.thetaK Y K b) b) := by
  refine Language.deriv_iff_intro ?_ ?_
  · refine Language.deriv_or_elim' (L.deriv_and_left (Language.deriv_ext_self _ _)) ?_
    refine Language.deriv_disjList_elim (Language.deriv_ext_self _ _) (fun a ha => ?_)
      (Language.deriv_of_botOf _ _)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
    refine L.deriv_explosion (α := P.bigD Y K) ?_ ?_
    · exact Language.deriv_of_single (L.deriv_and_right (Language.deriv_ext_self _ _))
        (P.E_deriv_bigD Y ht)
    · exact Language.deriv_ext_of _ (Language.deriv_ext_of _ (Language.deriv_single_self _))
  · exact Language.deriv_or_inl _ (L.deriv_and_intro (Language.deriv_ext_self _ _)
      (Language.deriv_ext_of _ (Language.deriv_single_self _)))

/-- Case analysis along the stages of `D_K`. -/
theorem thetaK_cases {F : L.Sent → Prop} {K : ℕ} {c : L.Sent}
    (h1 : ∀ s, s ∈ P.Xlist Y K → L.Deriv (L.ext F (P.E s)) c)
    (h2 : L.Deriv (L.ext F (L.neg (P.bigD Y K))) c) : L.Deriv F c := by
  refine Language.deriv_cases (c := P.bigD Y K) ?_ h2
  refine Language.deriv_disjList_elim (Language.deriv_ext_self F _) (fun a ha => ?_)
    (Language.deriv_of_botOf _ _)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
  exact Language.deriv_ext_swap (Language.deriv_ext_of _ (h1 s hs))

theorem thetaK_and (K : ℕ) (a b : L.Sent) :
    L.Valid (L.iff (P.thetaK Y K (L.and a b)) (L.and (P.thetaK Y K a) (P.thetaK Y K b))) := by
  refine P.thetaK_cases Y (K := K) (fun s hs => ?_) ?_
  · have t1 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_pos Y hs (L.and a b))
    have t2 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_pos Y hs a)
    have t3 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_pos Y hs b)
    rw [P.act_and] at t1
    exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm (Language.deriv_iff_and t2 t3))
  · have t1 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_neg Y K (L.and a b))
    have t2 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_neg Y K a)
    have t3 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_neg Y K b)
    exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm (Language.deriv_iff_and t2 t3))

theorem thetaK_negc (K : ℕ) (a : L.Sent) :
    L.Valid (L.iff (P.thetaK Y K (L.neg a)) (L.neg (P.thetaK Y K a))) := by
  refine P.thetaK_cases Y (K := K) (fun s hs => ?_) ?_
  · have t1 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_pos Y hs (L.neg a))
    have t2 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_pos Y hs a)
    rw [P.act_neg] at t1
    exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm (Language.deriv_iff_neg t2))
  · have t1 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_neg Y K (L.neg a))
    have t2 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_neg Y K a)
    exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm (Language.deriv_iff_neg t2))

theorem bigD_mono {K K' : ℕ} (h : K ≤ K') {F : L.Sent → Prop} (hd : L.Deriv F (P.bigD Y K)) :
    L.Deriv F (P.bigD Y K') :=
  Language.deriv_disjList_mono (fun a ha => by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
    rw [mem_Xlist] at hs
    exact List.mem_map.2 ⟨s, (P.mem_Xlist Y).2 ⟨hs.1, Nat.lt_of_lt_of_le hs.2.1 h, hs.2.2⟩, rfl⟩) hd

/-- `θ_K (b)` and `θ_{K+1} (b)` are equivalent for `k(b) ≤ K`. -/
theorem thetaK_succ {K : ℕ} {b : L.Sent} (hb : e M b ≤ K) :
    L.Valid (L.iff (P.thetaK Y K b) (P.thetaK Y (K + 1) b)) := by
  refine P.thetaK_cases Y (K := K + 1) (fun s hs => ?_) ?_
  · by_cases hsK : s ∈ P.Xlist Y K
    · have t1 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_pos Y hsK b)
      have t2 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_pos Y hs b)
      exact Language.deriv_iff_trans t1 (Language.deriv_iff_symm t2)
    · -- then `s` has level `K`
      have hs' := (P.mem_Xlist Y).1 hs
      have hlv : e M b ≤ P.lvl s := by
        have h1 : ¬ P.lvl s < K := fun h => hsK ((P.mem_Xlist Y).2 ⟨hs'.1, h, hs'.2.2⟩)
        omega
      have t1 : L.Deriv (L.single (P.E s)) (L.iff (P.thetaK Y K b) b) :=
        Language.deriv_of_single (P.E_deriv_neg_bigD Y hs'.1 hsK) (P.thetaK_neg Y K b)
      have t2 : L.Deriv (L.single (P.E s)) (L.iff b (P.act s b)) := P.act_ev s b hs'.1 hlv
      have t3 := P.thetaK_pos Y hs b
      exact Language.deriv_ext_of_single (F := L.empty)
        (Language.deriv_iff_trans t1 (Language.deriv_iff_trans t2 (Language.deriv_iff_symm t3)))
  · have hK : L.Deriv (L.single (L.neg (P.bigD Y (K + 1)))) (L.neg (P.bigD Y K)) :=
      Language.deriv_neg_of (P.bigD_mono Y (Nat.le_succ K) (Language.deriv_ext_self _ _))
        (Language.deriv_ext_of _ (Language.deriv_single_self _))
    have t1 : L.Deriv (L.single (L.neg (P.bigD Y (K + 1)))) (L.iff (P.thetaK Y K b) b) :=
      Language.deriv_of_single hK (P.thetaK_neg Y K b)
    have t2 := P.thetaK_neg Y (K + 1) b
    exact Language.deriv_ext_of_single (F := L.empty)
      (Language.deriv_iff_trans t1 (Language.deriv_iff_symm t2))

theorem theta_iff_thetaK (b : L.Sent) :
    ∀ d : ℕ, L.Valid (L.iff (P.theta Y b) (P.thetaK Y (e M b + 1 + d) b))
  | 0 => Language.deriv_iff_refl _ _
  | d + 1 => Language.deriv_iff_trans (theta_iff_thetaK b d)
      (P.thetaK_succ Y (K := e M b + 1 + d) (by omega))

theorem theta_equiv_thetaK {b : L.Sent} {K : ℕ} (hK : e M b + 1 ≤ K) :
    L.Equiv (P.theta Y b) (P.thetaK Y K b) := by
  obtain ⟨d, rfl⟩ : ∃ d, K = e M b + 1 + d := ⟨K - (e M b + 1), by omega⟩
  exact Language.Equiv.of_valid_iff (P.theta_iff_thetaK Y b d)

/-- `θ` commutes with `∧` up to logical equivalence. -/
theorem theta_and (a b : L.Sent) :
    L.Equiv (P.theta Y (L.and a b)) (L.and (P.theta Y a) (P.theta Y b)) := by
  let K := e M a + e M b + e M (L.and a b) + 1
  have h1 := P.theta_equiv_thetaK Y (b := L.and a b) (K := K) (by omega)
  have h2 := P.theta_equiv_thetaK Y (b := a) (K := K) (by omega)
  have h3 := P.theta_equiv_thetaK Y (b := b) (K := K) (by omega)
  exact h1.trans ((Language.Equiv.of_valid_iff (P.thetaK_and Y K a b)).trans
    (Language.Equiv.and h2.symm h3.symm))

/-- `θ` commutes with `¬` up to logical equivalence. -/
theorem theta_neg (a : L.Sent) : L.Equiv (P.theta Y (L.neg a)) (L.neg (P.theta Y a)) := by
  let K := e M a + e M (L.neg a) + 1
  have h1 := P.theta_equiv_thetaK Y (b := L.neg a) (K := K) (by omega)
  have h2 := P.theta_equiv_thetaK Y (b := a) (K := K) (by omega)
  exact h1.trans ((Language.Equiv.of_valid_iff (P.thetaK_negc Y K a)).trans h2.symm.neg)

/-- `θ` preserves logical validity. -/
theorem theta_valid {b : L.Sent} (h : L.Valid b) : L.Valid (P.theta Y b) := by
  refine P.thetaK_cases Y (K := e M b + 1) (fun s hs => ?_) ?_
  · have t1 := Language.deriv_ext_of_single (F := L.empty) (P.thetaK_pos Y hs b)
    exact Language.deriv_iff_mpr t1
      (Language.deriv_ext_of_single (P.act_valid s b ((P.mem_Xlist Y).1 hs).1 h))
  · exact Language.deriv_iff_mpr (Language.deriv_ext_of_single (F := L.empty) (P.thetaK_neg Y _ b))
      (Language.deriv_ext_of _ h)

/-- On the models of `E s`, for a live `s ∈ Y`: `θ (b)` is `act s b`. -/
theorem theta_pos {s : P.I} (hl : P.live s) (hY : Y s) (b : L.Sent) :
    L.Deriv (L.single (P.E s)) (L.iff (P.theta Y b) (P.act s b)) := by
  by_cases hs : s ∈ P.Xlist Y (e M b + 1)
  · exact P.thetaK_pos Y hs b
  · have hlv : e M b ≤ P.lvl s := by
      have h1 : ¬ P.lvl s < e M b + 1 := fun h => hs ((P.mem_Xlist Y).2 ⟨hl, h, hY⟩)
      omega
    exact Language.deriv_iff_trans
      (Language.deriv_of_single (P.E_deriv_neg_bigD Y hl hs) (P.thetaK_neg Y _ b))
      (P.act_ev s b hl hlv)

/-- Where every `E s`, `s ∈ Y`, fails: `θ (b)` is `b`. -/
theorem theta_off {F : L.Sent → Prop} (h : ∀ s, P.live s → Y s → L.Deriv F (L.neg (P.E s)))
    (b : L.Sent) : L.Deriv F (L.iff (P.theta Y b) b) := by
  have h1 : L.Deriv F (L.neg (P.bigD Y (e M b + 1))) := by
    refine Language.deriv_neg_disjList (fun a ha => ?_) (Language.deriv_neg_botOf _ _)
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
    exact h s ((P.mem_Xlist Y).1 hs).1 ((P.mem_Xlist Y).1 hs).2.2
  exact Language.deriv_of_single h1 (P.thetaK_neg Y _ b)

/-- A sentence fixed by every `act s` is fixed by `θ`, up to logical equivalence. -/
theorem theta_fix {b : L.Sent}
    (h : ∀ s, P.live s → L.Deriv (L.single (P.E s)) (L.iff b (P.act s b))) :
    L.Equiv (P.theta Y b) b := by
  refine Language.Equiv.of_valid_iff (P.thetaK_cases Y (K := e M b + 1) (fun s hs => ?_) ?_)
  · exact Language.deriv_ext_of_single (F := L.empty)
      (Language.deriv_iff_trans (P.thetaK_pos Y hs b)
        (Language.deriv_iff_symm (h s ((P.mem_Xlist Y).1 hs).1)))
  · exact Language.deriv_ext_of_single (F := L.empty) (P.thetaK_neg Y _ b)

theorem exists_lvl_bound (l : List P.I) : ∃ N, ∀ s, s ∈ l → P.lvl s < N := by
  induction l with
  | nil => exact ⟨0, fun s hs => by cases hs⟩
  | cons a l ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + P.lvl a + 1, fun s hs => ?_⟩
    rw [List.mem_cons] at hs
    rcases hs with rfl | hs
    · omega
    · have := hN s hs; omega

/-- To prove `F ⊢ θ (c)`: prove `act s c` on the models of `E s`, `s ∈ Y`, and prove `c` where finitely
many `E s`, `s ∈ Y`, fail. -/
theorem theta_intro {F : L.Sent → Prop} {c : L.Sent}
    (h1 : ∀ s, P.live s → Y s → L.Deriv (L.ext F (P.E s)) (P.act s c))
    (l : List P.I) (hl : ∀ s, s ∈ l → P.live s ∧ Y s)
    (h2 : L.Deriv (L.extList F (l.map (fun s => L.neg (P.E s)))) c) : L.Deriv F (P.theta Y c) := by
  obtain ⟨N, hN⟩ := P.exists_lvl_bound l
  rw [(P.theta_equiv_thetaK Y (b := c) (K := e M c + 1 + N) (by omega)).deriv_iff F]
  refine P.thetaK_cases Y (K := e M c + 1 + N) (fun s hs => ?_) ?_
  · have hs' := (P.mem_Xlist Y).1 hs
    exact Language.deriv_iff_mpr (Language.deriv_ext_of_single (P.thetaK_pos Y hs c))
      (h1 s hs'.1 hs'.2.2)
  · refine Language.deriv_iff_mpr (Language.deriv_ext_of_single (P.thetaK_neg Y _ c)) ?_
    refine L.deriv_cut (fun β hβ => ?_) h2
    rcases hβ with hβ | hβ
    · exact L.deriv_of_mem (Or.inl hβ)
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hβ
      have hsX : s ∈ P.Xlist Y (e M c + 1 + N) :=
        (P.mem_Xlist Y).2 ⟨(hl s hs).1, by have := hN s hs; omega, (hl s hs).2⟩
      exact Language.deriv_neg_of (b := P.bigD Y (e M c + 1 + N))
        (Language.deriv_ext_of_single (P.E_deriv_bigD Y hsX))
        (Language.deriv_ext_of _ (Language.deriv_ext_self _ _))

/-! ### The translation -/

section Trans

variable (S : SentSyntax L) (P0 : L.Sent → Prop)

set_option linter.unusedVariables false in -- `h` is used in `decreasing_by`
/-- The translation on sentences: `wrap p` on the prime sentences `p` of `P0`, `wrap (θ p)` on the other
prime sentences, extended over `¬` and `∧`. -/
noncomputable def imap : L.Sent → L.Sent
  | s =>
    match h : S.destruct s with
    | none => if P0 s then S.wrap s else S.wrap (P.theta Y s)
    | some (Sum.inl a) => L.neg (imap a)
    | some (Sum.inr (a, b)) => L.and (imap a) (imap b)
termination_by s => S.size s
decreasing_by
  all_goals simp_wf
  · show S.size a < S.size s
    rw [S.destruct_inl s a h]; exact S.size_neg a
  · show S.size a < S.size s
    rw [S.destruct_inr s a b h]; exact S.size_and_left a b
  · show S.size b < S.size s
    rw [S.destruct_inr s a b h]; exact S.size_and_right a b

theorem imap_neg (a : L.Sent) : P.imap Y S P0 (L.neg a) = L.neg (P.imap Y S P0 a) := by
  rw [imap]
  split
  · rename_i h; rw [S.destruct_neg] at h; cases h
  · rename_i a' h; rw [S.destruct_neg] at h; cases h; rfl
  · rename_i a' b' h; rw [S.destruct_neg] at h; cases h

theorem imap_and (a b : L.Sent) :
    P.imap Y S P0 (L.and a b) = L.and (P.imap Y S P0 a) (P.imap Y S P0 b) := by
  rw [imap]
  split
  · rename_i h; rw [S.destruct_and] at h; cases h
  · rename_i a' h; rw [S.destruct_and] at h; cases h
  · rename_i a' b' h; rw [S.destruct_and] at h; cases h; rfl

theorem imap_prime {p : L.Sent} (hp : S.Prime p) :
    P.imap Y S P0 p = if P0 p then S.wrap p else S.wrap (P.theta Y p) := by
  rw [imap]
  split
  · rfl
  · rename_i a' h; rw [show S.destruct p = none from hp] at h; cases h
  · rename_i a' b' h; rw [show S.destruct p = none from hp] at h; cases h

theorem imap_prime_of {p : L.Sent} (hp : S.Prime p) (h : P0 p) : P.imap Y S P0 p = S.wrap p := by
  rw [P.imap_prime Y S P0 hp, ite_eq_left h]

theorem imap_prime_of_not {p : L.Sent} (hp : S.Prime p) (h : ¬ P0 p) :
    P.imap Y S P0 p = S.wrap (P.theta Y p) := by
  rw [P.imap_prime Y S P0 hp, ite_eq_right h]

/-- The translation of `b` is logically equivalent to `θ (b)`, when every `act s` fixes `P0`. -/
theorem imap_equiv_theta
    (hfix : ∀ p, P0 p → ∀ s, P.live s → L.Deriv (L.single (P.E s)) (L.iff p (P.act s p))) :
    ∀ s, L.Equiv (P.imap Y S P0 s) (P.theta Y s) := by
  refine S.size_induction fun s ih => ?_
  rcases S.cases s with hp | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · by_cases h : P0 s
    · rw [P.imap_prime_of Y S P0 hp h]
      exact (S.wrap_equiv s).trans (P.theta_fix Y (hfix s h)).symm
    · rw [P.imap_prime_of_not Y S P0 hp h]
      exact S.wrap_equiv _
  · rw [imap_neg]
    exact (ih a (S.size_neg a)).neg.trans (P.theta_neg Y a).symm
  · rw [imap_and]
    exact (Language.Equiv.and (ih a (S.size_and_left a b)) (ih b (S.size_and_right a b))).trans
      (P.theta_and Y a b).symm

include S in
/-- `θ_K (s) = θ_{K'} (t)` forces `s = t` (the first conjunct of the first disjunct). -/
theorem eq_of_thetaK_eq {K K' : ℕ} {s t : L.Sent} (h : P.thetaK Y K s = P.thetaK Y K' t) : s = t := by
  unfold thetaK Language.or at h
  have h1 := S.neg_inj h
  have h2 := (S.and_inj h1).1
  have h3 := S.neg_inj h2
  exact (S.and_inj h3).1

/-- A prime sentence is not of the form `θ (t)`. -/
theorem prime_ne_theta {p : L.Sent} (hp : S.Prime p) (t : L.Sent) : p ≠ P.theta Y t := by
  have h : P.theta Y t = L.neg (L.and (L.neg (L.and t (L.neg (P.bigD Y (e M t + 1)))))
      (L.neg (L.disjList (L.botOf P.z0)
        ((P.Xlist Y (e M t + 1)).map (fun s => L.and (P.act s t) (P.E s)))))) := rfl
  rw [h]
  exact SentSyntax.prime_ne_neg hp _

/-- The image of a prime sentence is prime. -/
theorem imap_prime_prime {p : L.Sent} (hp : S.Prime p) : S.Prime (P.imap Y S P0 p) := by
  by_cases h : P0 p
  · rw [P.imap_prime_of Y S P0 hp h]; exact S.wrap_prime _
  · rw [P.imap_prime_of_not Y S P0 hp h]; exact S.wrap_prime _

/-- The translation is injective. -/
theorem imap_inj : ∀ s t, P.imap Y S P0 s = P.imap Y S P0 t → s = t := by
  refine S.size_induction fun s ih t hst => ?_
  rcases S.cases s with hps | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;>
    rcases S.cases t with hpt | ⟨a', rfl⟩ | ⟨a', b', rfl⟩
  · -- prime, prime
    by_cases hs : P0 s <;> by_cases ht : P0 t
    · rw [P.imap_prime_of Y S P0 hps hs, P.imap_prime_of Y S P0 hpt ht] at hst
      exact S.wrap_inj _ _ hst
    · rw [P.imap_prime_of Y S P0 hps hs, P.imap_prime_of_not Y S P0 hpt ht] at hst
      exact absurd (S.wrap_inj _ _ hst) (P.prime_ne_theta Y S hps t)
    · rw [P.imap_prime_of_not Y S P0 hps hs, P.imap_prime_of Y S P0 hpt ht] at hst
      exact absurd (S.wrap_inj _ _ hst).symm (P.prime_ne_theta Y S hpt s)
    · rw [P.imap_prime_of_not Y S P0 hps hs, P.imap_prime_of_not Y S P0 hpt ht] at hst
      exact P.eq_of_thetaK_eq Y S (S.wrap_inj _ _ hst)
  · -- prime, neg
    rw [imap_neg] at hst
    exact absurd hst (SentSyntax.prime_ne_neg (P.imap_prime_prime Y S P0 hps) _)
  · -- prime, and
    rw [imap_and] at hst
    exact absurd hst (SentSyntax.prime_ne_and (P.imap_prime_prime Y S P0 hps) _ _)
  · -- neg, prime
    rw [imap_neg] at hst
    exact absurd hst.symm (SentSyntax.prime_ne_neg (P.imap_prime_prime Y S P0 hpt) _)
  · -- neg, neg
    rw [imap_neg, imap_neg] at hst
    rw [ih a (S.size_neg a) a' (S.neg_inj hst)]
  · -- neg, and
    rw [imap_neg, imap_and] at hst
    exact absurd hst (S.neg_ne_and _ _ _)
  · -- and, prime
    rw [imap_and] at hst
    exact absurd hst.symm (SentSyntax.prime_ne_and (P.imap_prime_prime Y S P0 hpt) _ _)
  · -- and, neg
    rw [imap_and, imap_neg] at hst
    exact absurd hst.symm (S.neg_ne_and _ _ _)
  · -- and, and
    rw [imap_and, imap_and] at hst
    obtain ⟨h1, h2⟩ := S.and_inj hst
    rw [ih a (S.size_and_left a b) a' h1, ih b (S.size_and_right a b) b' h2]

theorem imap_imp (a b : L.Sent) :
    P.imap Y S P0 (L.imp a b) = L.imp (P.imap Y S P0 a) (P.imap Y S P0 b) := by
  unfold Language.imp; rw [imap_neg, imap_and, imap_neg]

theorem imap_conjList (z : L.Sent) (l : List L.Sent) :
    P.imap Y S P0 (L.conjList z l) = L.conjList (P.imap Y S P0 z) (l.map (P.imap Y S P0)) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [Language.conjList, List.map_cons]; rw [imap_and, ih]

/-- On Boolean combinations of prime sentences of `P0` the translation replaces each prime constituent
`p` by `wrap p`. -/
theorem imap_eq_of_boolOver {W : L.Sent → L.Sent} (hWp : ∀ p, S.Prime p → W p = S.wrap p)
    (hWn : ∀ a, W (L.neg a) = L.neg (W a)) (hWa : ∀ a b, W (L.and a b) = L.and (W a) (W b))
    (hP0 : ∀ p, P0 p → S.Prime p) {s : L.Sent} (hs : BoolOver L P0 s) : P.imap Y S P0 s = W s := by
  induction hs with
  | prime h => rw [P.imap_prime_of Y S P0 (hP0 _ h) h, hWp _ (hP0 _ h)]
  | neg _ ih => rw [imap_neg, ih, hWn]
  | and _ _ ih₁ ih₂ => rw [imap_and, ih₁, ih₂, hWa]

/-- The translation `𝓛 → 𝓛` (Definition 2.6) determined by the stages of `Y`. -/
noncomputable def trans
    (hfix : ∀ p, P0 p → ∀ s, P.live s → L.Deriv (L.single (P.E s)) (L.iff p (P.act s p))) :
    Translation L L where
  i := P.imap Y S P0
  inj := fun h => P.imap_inj Y S P0 _ _ h
  map_neg := P.imap_neg Y S P0
  map_and := P.imap_and Y S P0
  map_deriv := fun T α h => by
    obtain ⟨l, hl, hd⟩ := L.deriv_compact h
    -- `⊢ ⋀ l → α`
    have h1 : L.Valid (L.imp (L.conjList (L.topOf P.z0) l) α) :=
      Language.deriv_imp_conjList (L.deriv_mono (fun β hβ => Or.inr hβ) hd)
    have h2 := P.theta_valid Y h1
    have h3 : L.Valid (P.imap Y S P0 (L.imp (L.conjList (L.topOf P.z0) l) α)) :=
      ((P.imap_equiv_theta Y S P0 hfix _).valid_iff).2 h2
    rw [imap_imp, imap_conjList] at h3
    have h4 : L.Deriv (L.extList L.empty (l.map (P.imap Y S P0))) (P.imap Y S P0 α) :=
      Language.deriv_extList_of_imp_conjList (z := P.imap Y S P0 (L.topOf P.z0)) (by
        unfold Language.topOf Language.botOf; rw [imap_neg, imap_and, imap_neg]
        exact Language.deriv_topOf _ _)
        (Language.deriv_of_valid h3)
    refine L.deriv_mono (fun β hβ => ?_) h4
    rcases hβ with hβ | hβ
    · exact hβ.elim
    · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
      exact ⟨γ, hl γ hγ, rfl⟩

theorem trans_i
    (hfix : ∀ p, P0 p → ∀ s, P.live s → L.Deriv (L.single (P.E s)) (L.iff p (P.act s p)))
    (s : L.Sent) : (P.trans Y S P0 hfix).i s = P.imap Y S P0 s := rfl

end Trans

end Perturb

end Stable
