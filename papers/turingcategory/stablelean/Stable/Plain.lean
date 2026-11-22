import Stable.Second
import Stable.SoundCons
import Stable.Sigma2

/-!
# Theories of arithmetic: the identity translation (Sections 1.1, 5 and 5.1 of the restructured paper)

In the restructured manuscript (11 November 2026) the theorems are stated for stably c.e.
theories of arithmetic, with no translation.  They are the case `𝓛 = 𝓐`, `i = id` of the results of
`Stable.Incompleteness` and `Stable.Second`.  This file makes that precise.

* `Translation.id`: the identity translation of a language.
* `Arith.OneConsistent`, `Arith.TwoConsistent`, `Arith.SigmaSound`: Definition 2.9 and
  Definition 6.5 for a theory of arithmetic.  For a translation `i : 𝓐 → 𝓛` the notions
  "relative to `i`" (Definition B.6) are *by definition* these notions for the induced theory
  `F_{i,𝓐}` (`Translation.oneConsistent_iff_induced` etc. are `Iff.rfl`).
* `Arith.BoolComb n`: the Boolean combinations of `Σ⁰ₙ` sentences and of axioms of `Q`; `𝓑₂` of the
  paper is `A.BoolComb 2` (`∨` is omitted, as everywhere in this development).
* `G₀ A : 𝒯 → 𝓐`: the Gödel map `𝒢` of Theorem 1.5, and Proposition 5.5 for it
  (`Arith.not_deriv_G₀`, `Arith.not_deriv_neg_G₀`, `Arith.trueN_G₀`); Theorem 1.5 is
  `first_incompleteness_arith`.
* Theorem 5.11 in its present form (`second_incompleteness_H`): `H` is any deductively closed
  `𝓩`-theory containing `ZFC` such that `F ⊢ b` whenever `b ∈ 𝓑₂` and `b* ∈ H`; then `con ∉ H`.
  As in `Stable.Second`, equation (5.12) is the hypothesis `hcon`, stated for an arbitrary
  sentence `con ∈ 𝓩` (in the paper `con = Con₁ (T)*`).  Corollary 5.13 is
  `second_incompleteness_H_corollary`.
* The simplest case (`second_incompleteness_simple`): if `F ⊢ a` whenever `ZFC ⊢ a*`, then
  `F ⊬ Con₁ (T)`.  The proof is direct: by (5.12), `ZFC ⊢ (¬(Con₁ (T) ∧ ¬𝒢 (T)))*`.
* Theorem 1.1 (`second_incompleteness_sigma`): the second incompleteness theorem for a
  `Σ⁰₂`-definable theory `F` of arithmetic, with `H` as in Theorem 5.11.  Some machine presents `F`
  (`exists_machine_of_isSigma2Set`), and the conclusion holds for every machine presenting `F`.
  Corollary 5.17 is `second_incompleteness_sigma_simple`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-- The identity translation of a language. -/
def Translation.id (L : Language M) : Translation L L where
  i := fun α => α
  inj := fun h => h
  map_neg := fun _ => rfl
  map_and := fun _ _ => rfl
  map_deriv := fun _ _ h => L.deriv_mono (fun β hβ => ⟨β, hβ, rfl⟩) h

theorem Translation.id_derivI_iff (L : Language M) (F : L.Sent → Prop) (α : L.Sent) :
    (Translation.id L).DerivI F α ↔ L.Deriv F α := (Translation.id L).derivI_iff F α

namespace Arith

variable (A : Arith M)

/-- `F` is `1`-consistent (Definition 2.9): `F ⊢ Q`, and for every `Σ⁰₁` sentence `∃x̄ φ` with
`F ⊢ ∃x̄ φ` there is an instance with `F ⊬ ¬φ(n̄)`. -/
def OneConsistent (F : A.Sent → Prop) : Prop :=
  (∀ q, A.Q q → A.Deriv F q) ∧
    ∀ σ, A.IsSigma 1 σ → A.Deriv F σ → ∃ v, ¬ A.Deriv F (A.neg (A.instS σ v))

/-- `F` is `2`-consistent (Definition 2.9). -/
def TwoConsistent (F : A.Sent → Prop) : Prop :=
  A.OneConsistent F ∧
    ∀ σ, A.IsSigma 2 σ → A.Deriv F σ → ∃ v, ¬ A.Deriv F (A.neg (A.instS σ v))

/-- `F` is `Σₙ`-sound (Definition 6.5). -/
def SigmaSound (n : ℕ) (F : A.Sent → Prop) : Prop :=
  ∀ σ, A.IsSigma n σ → A.Deriv F σ → A.TrueN σ

/-- The Boolean combinations of `Σ⁰ₙ` sentences and of axioms of `Q`: the set `𝓑ₙ` of the paper
(`𝓑₂` in Section 1.1, `𝓑ₙ₊₁` in Section 6.3). -/
inductive BoolComb (n : ℕ) : A.Sent → Prop
  | sigma {α : A.Sent} : A.IsSigma n α → BoolComb n α
  | axQ {α : A.Sent} : A.Q α → BoolComb n α
  | neg {α : A.Sent} : BoolComb n α → BoolComb n (A.neg α)
  | and {α β : A.Sent} : BoolComb n α → BoolComb n β → BoolComb n (A.and α β)

end Arith

namespace Translation

variable {A : Arith M} {L : Language M} (i : Translation A.toLanguage L)

/-- Definition B.6: `F` is `1`-consistent relative to `i` iff the induced theory `F_{i,𝓐}` is
`1`-consistent.  This holds by definition. -/
theorem oneConsistent_iff_induced (F : L.Sent → Prop) :
    i.OneConsistent F ↔ A.OneConsistent (i.induced F) := Iff.rfl

theorem twoConsistent_iff_induced (F : L.Sent → Prop) :
    i.TwoConsistent F ↔ A.TwoConsistent (i.induced F) := Iff.rfl

theorem sigmaSound_iff_induced (n : ℕ) (F : L.Sent → Prop) :
    i.SigmaSound n F ↔ A.SigmaSound n (i.induced F) := Iff.rfl

end Translation

namespace Arith

variable (A : Arith M)

/-- For the identity translation the induced theory proves what `F` proves. -/
theorem deriv_induced_id_iff (F : A.Sent → Prop) (α : A.Sent) :
    A.Deriv ((Translation.id A.toLanguage).induced F) α ↔ A.Deriv F α :=
  Translation.id_derivI_iff A.toLanguage F α

theorem id_oneConsistent_iff (F : A.Sent → Prop) :
    (Translation.id A.toLanguage).OneConsistent F ↔ A.OneConsistent F := by
  constructor
  · rintro ⟨hQ, h1⟩
    refine ⟨fun q hq => (A.deriv_induced_id_iff F q).1 (hQ q hq), fun σ hσ hd => ?_⟩
    obtain ⟨v, hv⟩ := h1 σ hσ ((A.deriv_induced_id_iff F σ).2 hd)
    exact ⟨v, fun h => hv ((A.deriv_induced_id_iff F _).2 h)⟩
  · rintro ⟨hQ, h1⟩
    refine ⟨fun q hq => (A.deriv_induced_id_iff F q).2 (hQ q hq), fun σ hσ hd => ?_⟩
    obtain ⟨v, hv⟩ := h1 σ hσ ((A.deriv_induced_id_iff F σ).1 hd)
    exact ⟨v, fun h => hv ((A.deriv_induced_id_iff F _).1 h)⟩

theorem id_twoConsistent_iff (F : A.Sent → Prop) :
    (Translation.id A.toLanguage).TwoConsistent F ↔ A.TwoConsistent F := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(A.id_oneConsistent_iff F).1 h1, fun σ hσ hd => ?_⟩
    obtain ⟨v, hv⟩ := h2 σ hσ ((A.deriv_induced_id_iff F σ).2 hd)
    exact ⟨v, fun h => hv ((A.deriv_induced_id_iff F _).2 h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(A.id_oneConsistent_iff F).2 h1, fun σ hσ hd => ?_⟩
    obtain ⟨v, hv⟩ := h2 σ hσ ((A.deriv_induced_id_iff F σ).1 hd)
    exact ⟨v, fun h => hv ((A.deriv_induced_id_iff F _).1 h)⟩

theorem id_sigmaSound_iff (n : ℕ) (F : A.Sent → Prop) :
    (Translation.id A.toLanguage).SigmaSound n F ↔ A.SigmaSound n F :=
  ⟨fun h σ hσ hd => h σ hσ ((A.deriv_induced_id_iff F σ).2 hd),
    fun h σ hσ hd => h σ hσ ((A.deriv_induced_id_iff F σ).1 hd)⟩

/-- The identity is an `n`-translation for every `n`. -/
theorem id_isNTranslation (n : ℕ) : (Translation.id A.toLanguage).IsNTranslation n := by
  obtain ⟨T, hT⟩ := compT_id (M := M) (A := A.Sent)
  exact ⟨T, fun σ => hT σ.1⟩

end Arith

/-- The Gödel map `𝒢 : 𝒯 → 𝓐` of Theorem 1.5 (equation (5.4)), for theories of arithmetic. -/
noncomputable def G₀ (A : Arith M) : M.Code → A.Sent :=
  G (Translation.id A.toLanguage) (A.id_isNTranslation 2)

namespace Arith

variable (A : Arith M)

theorem G₀_compT : CompT M (G₀ A) := G_compT (Translation.id A.toLanguage) (A.id_isNTranslation 2)

/-- `𝒢 (T)` is the negation of a `Σ⁰₂` sentence, so it lies in `𝓑₂`. -/
theorem G₀_boolComb (T : M.Code) : A.BoolComb 2 (G₀ A T) :=
  BoolComb.neg (BoolComb.sigma (A.sigmaT_sigma2 _))

/-- Proposition 5.5 (3). -/
theorem trueN_G₀ (T : M.Code) (h : A.OneConsistent (Ts (M := M) A.Sent T)) : A.TrueN (G₀ A T) :=
  trueN_G (Translation.id A.toLanguage) (A.id_isNTranslation 2) T ((A.id_oneConsistent_iff _).2 h)

/-- Proposition 5.5 (1). -/
theorem not_deriv_G₀ (T : M.Code) (h : A.OneConsistent (Ts (M := M) A.Sent T)) :
    ¬ A.Deriv (Ts (M := M) A.Sent T) (G₀ A T) := fun hd =>
  not_derivI_G (Translation.id A.toLanguage) (A.id_isNTranslation 2) T
    ((A.id_oneConsistent_iff _).2 h) ((A.deriv_induced_id_iff _ _).2 hd)

/-- Proposition 5.5 (2). -/
theorem not_deriv_neg_G₀ (T : M.Code) (h : A.TwoConsistent (Ts (M := M) A.Sent T)) :
    ¬ A.Deriv (Ts (M := M) A.Sent T) (A.neg (G₀ A T)) := fun hd =>
  not_derivI_neg_G (Translation.id A.toLanguage) (A.id_isNTranslation 2) T
    ((A.id_twoConsistent_iff _).2 h) ((A.deriv_induced_id_iff _ _).2 hd)

end Arith

/-! ### Theorem 1.5 for theories of arithmetic -/

/-- Theorem 1.5 (`theorem_firstincompleteness`) in its present form: there is a total computable
`𝒢 : 𝒯 → 𝓐` such that whenever `T` stably computes `N : ℕ → 𝓐 × {±}` and `F = N^s`:
(1) `F ⊬ 𝒢 (T)` if `F` is `1`-consistent; (2) `F ⊬ ¬𝒢 (T)` if `F` is `2`-consistent;
(3) `ℕ ⊨ 𝒢 (T)` if `F` is `1`-consistent. -/
theorem first_incompleteness_arith (A : Arith M) : ∃ G : M.Code → A.Sent, CompT M G ∧
    ∀ (T : M.Code) (N : ℕ → Option (A.Sent × Bool)), StablyComputes (M := M) T N →
      (A.OneConsistent (Stab N) → ¬ A.Deriv (Stab N) (G T)) ∧
      (A.TwoConsistent (Stab N) → ¬ A.Deriv (Stab N) (A.neg (G T))) ∧
      (A.OneConsistent (Stab N) → A.TrueN (G T)) := by
  refine ⟨G₀ A, A.G₀_compT, fun T N hTN => ?_⟩
  have hFeq : Stab N = Ts (M := M) A.Sent T := funext fun x => propext (hTN.2 x).symm
  rw [hFeq]
  exact ⟨A.not_deriv_G₀ T, A.not_deriv_neg_G₀ T, A.trueN_G₀ T⟩

/-! ### Lemma 6.6 for theories of arithmetic -/

namespace Arith

variable (A : Arith M)

/-- Lemma 6.6 (2). -/
theorem SigmaSound.mono {n : ℕ} {F : A.Sent → Prop} (h : A.SigmaSound (n + 1) F) :
    A.SigmaSound n F := fun σ hσ hd => h σ (A.sigma_succ n σ hσ) hd

/-- Lemma 6.6 (1), first half: given `F ⊢ Q`, `1`-consistency is `Σ₁`-soundness. -/
theorem oneConsistent_iff_sigmaSound {F : A.Sent → Prop} (hQ : ∀ q, A.Q q → A.Deriv F q) :
    A.OneConsistent F ↔ A.SigmaSound 1 F := by
  rw [← A.id_oneConsistent_iff, ← A.id_sigmaSound_iff]
  exact _root_.Stable.oneConsistent_iff_sigmaSound (Translation.id A.toLanguage)
    (fun q hq => (A.deriv_induced_id_iff F q).2 (hQ q hq))

/-- Lemma 6.6 (1), second half: given `F ⊢ Q`, `2`-consistency is `Σ₂`-soundness. -/
theorem twoConsistent_iff_sigmaSound {F : A.Sent → Prop} (hQ : ∀ q, A.Q q → A.Deriv F q) :
    A.TwoConsistent F ↔ A.SigmaSound 2 F := by
  rw [← A.id_twoConsistent_iff, ← A.id_sigmaSound_iff]
  exact _root_.Stable.twoConsistent_iff_sigmaSound (Translation.id A.toLanguage)
    (fun q hq => (A.deriv_induced_id_iff F q).2 (hQ q hq))

end Arith

/-! ### Theorem 5.11 and Corollary 5.13 in their present form -/

variable {A : Arith M} {Z : Language M}

/-- Theorem 5.11 (`theorem_secondincompleteness`), abstract form.  `T` presents the theory of
arithmetic `F = T^s`, which is `1`-consistent.  `H` is a deductively closed `𝓩`-theory containing
`ZFC`, with `F ⊢ b` for every `b ∈ 𝓑₂` with `b* ∈ H` (here `b* = iAZ b`).  `con ∈ 𝓩` is a sentence
with `ZFC ∪ {con} ⊢ 𝒢 (T)*`: equation (5.12) of the paper, for `con = Con₁ (T)*`.
Then `con ∉ H`. -/
theorem second_incompleteness_H (iAZ : Translation A.toLanguage Z) (ZFC H : Z.Sent → Prop)
    (hH : Z.Closed H) (hZFC : ∀ β, ZFC β → H β) (T : M.Code)
    (h1 : A.OneConsistent (Ts (M := M) A.Sent T))
    (hB : ∀ b, A.BoolComb 2 b → H (iAZ.i b) → A.Deriv (Ts (M := M) A.Sent T) b)
    (con : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A T))) : ¬ H con := by
  intro hc
  -- `𝒢 (T)* ∈ H`, as `H` is deductively closed and contains `ZFC` and `con`
  have h2 : Z.Deriv H (iAZ.i (G₀ A T)) := by
    refine Z.deriv_cut (fun β hβ => ?_) hcon
    rcases hβ with hβ | rfl
    · exact Z.deriv_of_mem (hZFC β hβ)
    · exact Z.deriv_of_mem hc
  -- so `F ⊢ 𝒢 (T)`, as `𝒢 (T) ∈ 𝓑₂`; this contradicts Proposition 5.5 (1)
  exact A.not_deriv_G₀ T h1 (hB _ (A.G₀_boolComb T) (hH _ h2))

/-- Corollary 5.13 (`corollary_secondincompleteness`), abstract form.  With `con` as in
Theorem 5.11, let `enum`, `conδ ∈ 𝓩` be the sentences `Enum (T, δ)` and `Con₁ (δ)`: they say, in
terms of `δ`, that `T` stably enumerates `F` and that `F` is `1`-consistent.  Suppose
`ZFC ∪ {enum, conδ} ⊢ con` (as `ZFC` proves `Enum (T, δ) → (Con₁ (δ) ↔ Con₁ (T)*)`).
Then `H` does not contain both `enum` and `conδ`. -/
theorem second_incompleteness_H_corollary (iAZ : Translation A.toLanguage Z)
    (ZFC H : Z.Sent → Prop) (hH : Z.Closed H) (hZFC : ∀ β, ZFC β → H β) (T : M.Code)
    (h1 : A.OneConsistent (Ts (M := M) A.Sent T))
    (hB : ∀ b, A.BoolComb 2 b → H (iAZ.i b) → A.Deriv (Ts (M := M) A.Sent T) b)
    (con enum conδ : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A T)))
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = conδ) con) : ¬ (H enum ∧ H conδ) := by
  rintro ⟨he, hc⟩
  refine second_incompleteness_H iAZ ZFC H hH hZFC T h1 hB con hcon (hH _ ?_)
  refine Z.deriv_cut (fun β hβ => ?_) hδ
  rcases hβ with hβ | rfl | rfl
  · exact Z.deriv_of_mem (hZFC β hβ)
  · exact Z.deriv_of_mem he
  · exact Z.deriv_of_mem hc

/-- The simplest case of Theorem 5.11.  Suppose `F = T^s` is `1`-consistent and `F ⊢ a` for every
sentence `a` of arithmetic with `ZFC ⊢ a*`.  Let `con₀ ∈ 𝓐` satisfy (5.12):
`ZFC ∪ {con₀*} ⊢ 𝒢 (T)*` (in the paper `con₀ = Con₁ (T)`).  Then `F ⊬ con₀`.

The hypothesis on `F` is used for the single sentence `¬(con₀ ∧ ¬𝒢 (T))`, whose translation `ZFC`
proves by (5.12). -/
theorem second_incompleteness_simple (iAZ : Translation A.toLanguage Z) (ZFC : Z.Sent → Prop)
    (T : M.Code) (h1 : A.OneConsistent (Ts (M := M) A.Sent T))
    (hF : ∀ a : A.Sent, Z.Deriv ZFC (iAZ.i a) → A.Deriv (Ts (M := M) A.Sent T) a)
    (con₀ : A.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = iAZ.i con₀) (iAZ.i (G₀ A T))) :
    ¬ A.Deriv (Ts (M := M) A.Sent T) con₀ := by
  intro hc
  -- `ZFC ⊢ (¬(con₀ ∧ ¬𝒢 (T)))*`
  have hZ : Z.Deriv ZFC (iAZ.i (A.neg (A.and con₀ (A.neg (G₀ A T))))) := by
    rw [iAZ.map_neg, iAZ.map_and, iAZ.map_neg]
    refine Z.deriv_neg_intro fun γ => ?_
    have hand : Z.Deriv (fun β => ZFC β ∨ β = Z.and (iAZ.i con₀) (Z.neg (iAZ.i (G₀ A T))))
        (Z.and (iAZ.i con₀) (Z.neg (iAZ.i (G₀ A T)))) := Z.deriv_of_mem (Or.inr rfl)
    have hg : Z.Deriv (fun β => ZFC β ∨ β = Z.and (iAZ.i con₀) (Z.neg (iAZ.i (G₀ A T))))
        (iAZ.i (G₀ A T)) := by
      refine Z.deriv_cut (fun β hβ => ?_) hcon
      rcases hβ with hβ | rfl
      · exact Z.deriv_of_mem (Or.inl hβ)
      · exact Z.deriv_and_left hand
    exact Z.deriv_explosion hg (Z.deriv_and_right hand)
  -- so `F ⊢ ¬(con₀ ∧ ¬𝒢 (T))`, and with `F ⊢ con₀` this gives `F ⊢ 𝒢 (T)`
  have hFc := hF _ hZ
  have hg : A.Deriv (Ts (M := M) A.Sent T) (G₀ A T) := by
    refine A.deriv_dne (A.deriv_neg_intro fun γ => ?_)
    have h1' : A.Deriv (fun β => Ts (M := M) A.Sent T β ∨ β = A.neg (G₀ A T))
        (A.and con₀ (A.neg (G₀ A T))) :=
      A.deriv_and_intro (A.deriv_mono (fun β hβ => Or.inl hβ) hc) (A.deriv_of_mem (Or.inr rfl))
    exact A.deriv_explosion h1' (A.deriv_mono (fun β hβ => Or.inl hβ) hFc)
  exact A.not_deriv_G₀ T h1 hg

/-! ### Theorem 1.1 and Corollary 5.17: `Σ⁰₂`-definable theories -/

/-- A `Σ⁰₂`-definable theory of arithmetic is presented by a machine (Corollary 3.7).  In the paper
the machine `T_σ` of Lemma 5.16 is such a machine, for a `Σ⁰₂` formula `σ` defining the theory. -/
theorem exists_machine_of_isSigma2Set {F : A.Sent → Prop} (hF : IsSigma2Set (M := M) F) :
    ∃ T : M.Code, Ts (M := M) A.Sent T = F := by
  obtain ⟨Mp, ⟨T, hT⟩, hS⟩ := (stablyCE_iff_isSigma2Set A.infinite F).2 hF
  obtain ⟨-, h2⟩ := inTB_of_computes (B := A.Sent) hT
  exact ⟨T, funext fun a => propext
    ⟨fun h => (hS a).2 (IsStable.of_eq h2 h),
      fun h => IsStable.of_eq (fun n => (h2 n).symm) ((hS a).1 h)⟩⟩

/-- Theorem 1.1 (`theorem_secondsigma`), abstract form.  `H` is a deductively closed `𝓩`-theory
containing `ZFC`.  `F` is a `Σ⁰₂`-definable, `1`-consistent theory of arithmetic with `F ⊢ b` for
every `b ∈ 𝓑₂` with `b* ∈ H`: that is, `H` admits a `2`-`F`-reading.  Then some machine presents
`F`.  And for every machine `T` presenting `F`, `conσ ∉ H` for all sentences `con`, `conσ ∈ 𝓩` with
`ZFC ∪ {con} ⊢ 𝒢 (T)*` and `ZFC ∪ {conσ} ⊢ con`.  In the paper `T` is the machine `T_σ` of
Lemma 5.16, built from a `Σ⁰₂` formula `σ` defining `F`.  For `T = T_σ`, `con = Con₁ (T_σ)*` and
`conσ = Con₁ (σ)*` the two hypotheses are equation (5.12) and Lemma 5.16. -/
theorem second_incompleteness_sigma (iAZ : Translation A.toLanguage Z) (ZFC H : Z.Sent → Prop)
    (hH : Z.Closed H) (hZFC : ∀ β, ZFC β → H β) (F : A.Sent → Prop)
    (hF : IsSigma2Set (M := M) F) (h1 : A.OneConsistent F)
    (hB : ∀ b, A.BoolComb 2 b → H (iAZ.i b) → A.Deriv F b) :
    (∃ T : M.Code, Ts (M := M) A.Sent T = F) ∧
    ∀ T : M.Code, Ts (M := M) A.Sent T = F → ∀ con conσ : Z.Sent,
      Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G₀ A T)) →
      Z.Deriv (fun β => ZFC β ∨ β = conσ) con → ¬ H conσ := by
  refine ⟨exists_machine_of_isSigma2Set (A := A) hF, ?_⟩
  intro T hT con conσ hcon hσ hc
  subst hT
  refine second_incompleteness_H iAZ ZFC H hH hZFC T h1 hB con hcon (hH _ ?_)
  -- `con ∈ H`, as `H` is deductively closed and contains `ZFC` and `conσ`
  refine Z.deriv_cut (fun β hβ => ?_) hσ
  rcases hβ with hβ | rfl
  · exact Z.deriv_of_mem (hZFC β hβ)
  · exact Z.deriv_of_mem hc

/-- Corollary 5.17 (`corollary_secondsigma`), abstract form: the simplest case of Theorem 1.1.
`F` is a `Σ⁰₂`-definable, `1`-consistent theory of arithmetic with `F ⊢ a` for every sentence `a`
with `ZFC ⊢ a*`.  Then some machine presents `F`.  And for every machine `T` presenting `F`,
`F ⊬ conσ₀` for all `con₀`, `conσ₀ ∈ 𝓐` with `ZFC ∪ {con₀*} ⊢ 𝒢 (T)*` and
`ZFC ∪ {conσ₀*} ⊢ con₀*`.  In the paper `T = T_σ`, `con₀ = Con₁ (T_σ)` and `conσ₀ = Con₁ (σ)`. -/
theorem second_incompleteness_sigma_simple (iAZ : Translation A.toLanguage Z)
    (ZFC : Z.Sent → Prop) (F : A.Sent → Prop) (hF : IsSigma2Set (M := M) F)
    (h1 : A.OneConsistent F) (hFZ : ∀ a : A.Sent, Z.Deriv ZFC (iAZ.i a) → A.Deriv F a) :
    (∃ T : M.Code, Ts (M := M) A.Sent T = F) ∧
    ∀ T : M.Code, Ts (M := M) A.Sent T = F → ∀ con₀ conσ₀ : A.Sent,
      Z.Deriv (fun β => ZFC β ∨ β = iAZ.i con₀) (iAZ.i (G₀ A T)) →
      Z.Deriv (fun β => ZFC β ∨ β = iAZ.i conσ₀) (iAZ.i con₀) → ¬ A.Deriv F conσ₀ := by
  refine ⟨exists_machine_of_isSigma2Set (A := A) hF, ?_⟩
  intro T hT con₀ conσ₀ hcon hσ
  subst hT
  refine second_incompleteness_simple iAZ ZFC T h1 hFZ conσ₀ ?_
  -- `ZFC ∪ {conσ₀*} ⊢ 𝒢 (T)*`, by cut
  refine Z.deriv_cut (fun β hβ => ?_) hcon
  rcases hβ with hβ | rfl
  · exact Z.deriv_of_mem (Or.inl hβ)
  · exact hσ

end Stable
