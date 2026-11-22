import Stable.Logic
import Stable.NStab

/-!
# The language of arithmetic (Section 2.2) as an interface

`Arith M` is a first order language `𝓐` with the following additional data and classical facts,
used as axioms (the paper cites Tarski–Mostowski–Robinson and Hájek–Pudlák for them):

* truth in the standard model `ℕ ⊨ α` (`TrueN`), sound for the deductive system;
* the classes `Σ⁰ₙ`, `Π⁰ₙ` of sentences (`IsSigma n`, `IsPi n`), with `Σ⁰₀ = Π⁰₀` the `Δ₀`
  sentences, `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Σ⁰ₙ₊₁ ∩ Π⁰ₙ₊₁`, and computable as subsets of `𝓐`;
* instance maps: for `σ = ∃x̄ φ ∈ Σ⁰ₙ₊₁`, `instS σ v = φ(β_r (v)) ∈ Π⁰ₙ`, and for
  `π = ∀x̄ φ ∈ Π⁰ₙ₊₁`, `instP π v = φ(β_r (v)) ∈ Σ⁰ₙ`, where `β_r : ℕ → ℕ^r` are the fixed
  computable surjections of Section 2.2, bijective for `r ≥ 1` (so tuples of witnesses `n̄ ∈ ℕ^r` are contracted to
  single numbers `v`, exactly as in the paper's description of `Tr_{Π₁}`); truth commutes with
  these (`ℕ ⊨ ∃x̄ φ` iff some instance is true, `ℕ ⊨ ∀x̄ φ` iff all instances are true),
  existential introduction and universal elimination hold for them, and they are computable;
* the truth of `Δ₀` sentences is decidable, and Robinson's `Q` decides them
  (`Q ⊢ φ(n̄)` if `ℕ ⊨ φ(n̄)`, `Q ⊢ ¬φ(n̄)` otherwise);
* `¬∀x̄ φ` is logically equivalent to the `Σ⁰ₙ₊₁` sentence `∃x̄ ¬φ` (`negPi`), whose instances
  are the negated instances, and a conjunction of two `Π⁰ₙ` sentences is logically equivalent to a
  `Π⁰ₙ` sentence (`andPi`: rename the variables apart and move the quantifiers out);
* representability (Lemma 4.2 of the paper, via [HP93, Chapter I]): for every computable
  `W ⊂ 𝒯 × ℕ × ℕ` there is a total computable `σ_W : 𝒯 → 𝓐` with `σ_W (T) ∈ Σ⁰₂` and
  `ℕ ⊨ σ_W (T)` iff `∃ u ∀ v, (T, u, v) ∈ W`.

Everything in Sections 3–5 of the paper is proved from this interface and `TuringModel`.
-/

namespace Stable

open Classical

/-- The language of arithmetic with the classical facts used in the paper; see the module
docstring. -/
structure Arith (M : TuringModel) extends Language M where
  /-- Truth in the standard model, `ℕ ⊨ α`. -/
  TrueN : Sent → Prop
  /-- The class of `Σ⁰ₙ` sentences. -/
  IsSigma : ℕ → Sent → Prop
  /-- The class of `Π⁰ₙ` sentences. -/
  IsPi : ℕ → Sent → Prop
  sigma_zero_iff_pi_zero : ∀ α, IsSigma 0 α ↔ IsPi 0 α
  pi_sigma_succ : ∀ n α, IsPi n α → IsSigma (n + 1) α
  sigma_pi_succ : ∀ n α, IsSigma n α → IsPi (n + 1) α
  sigma_succ : ∀ n α, IsSigma n α → IsSigma (n + 1) α
  pi_succ : ∀ n α, IsPi n α → IsPi (n + 1) α
  /-- `Δ₀` sentences are closed under negation. -/
  neg_delta0 : ∀ α, IsSigma 0 α → IsSigma 0 (neg α)
  sigma_comp : ∀ n, @CompSet M Sent enc (IsSigma n)
  pi_comp : ∀ n, @CompSet M Sent enc (IsPi n)
  /-- `instS σ v = φ(β_r v)` for `σ = ∃x̄ φ`. -/
  instS : Sent → ℕ → Sent
  /-- `instP π v = φ(β_r v)` for `π = ∀x̄ φ`. -/
  instP : Sent → ℕ → Sent
  instS_pi : ∀ n σ v, IsSigma (n + 1) σ → IsPi n (instS σ v)
  instP_sigma : ∀ n π v, IsPi (n + 1) π → IsSigma n (instP π v)
  instS_comp : @CompT M (Sent × ℕ) Sent (@encProd M Sent ℕ enc encNat) enc (fun p => instS p.1 p.2)
  instP_comp : @CompT M (Sent × ℕ) Sent (@encProd M Sent ℕ enc encNat) enc (fun p => instP p.1 p.2)
  trueN_sigma : ∀ n σ, IsSigma (n + 1) σ → (TrueN σ ↔ ∃ v, TrueN (instS σ v))
  trueN_pi : ∀ n π, IsPi (n + 1) π → (TrueN π ↔ ∀ v, TrueN (instP π v))
  trueN_neg : ∀ α, TrueN (neg α) ↔ ¬ TrueN α
  trueN_and : ∀ α β, TrueN (and α β) ↔ TrueN α ∧ TrueN β
  /-- Soundness of the deductive system for `ℕ`. -/
  sound : ∀ (F : Sent → Prop) α, (∀ β, F β → TrueN β) → Deriv F α → TrueN α
  /-- The truth of `Δ₀` sentences is decidable. -/
  delta0_dec : @CompSet M Sent enc (fun α => IsSigma 0 α ∧ TrueN α)
  /-- Existential introduction: `φ(n̄) ⊢ ∃x̄ φ`. -/
  exists_intro : ∀ n σ v, IsSigma (n + 1) σ → Deriv (fun β => β = instS σ v) σ
  /-- Universal elimination: `∀x̄ φ ⊢ φ(n̄)`. -/
  forall_elim : ∀ n π v, IsPi (n + 1) π → Deriv (fun β => β = π) (instP π v)
  /-- `∃x̄ ¬φ`, for `π = ∀x̄ φ`. -/
  negPi : Sent → Sent
  negPi_sigma : ∀ n π, IsPi (n + 1) π → IsSigma (n + 1) (negPi π)
  negPi_deriv : ∀ n π, IsPi (n + 1) π → Deriv (fun β => β = neg π) (negPi π)
  negPi_inst : ∀ n π v, IsPi (n + 1) π → instS (negPi π) v = neg (instP π v)
  negPi_comp : @CompT M Sent Sent enc enc negPi
  /-- A `Π⁰ₙ` sentence logically equivalent to `π₁ ∧ π₂`. -/
  andPi : Sent → Sent → Sent
  andPi_pi : ∀ n π₁ π₂, IsPi n π₁ → IsPi n π₂ → IsPi n (andPi π₁ π₂)
  andPi_deriv₁ : ∀ π₁ π₂, Deriv (fun β => β = and π₁ π₂) (andPi π₁ π₂)
  andPi_deriv₂ : ∀ π₁ π₂, Deriv (fun β => β = andPi π₁ π₂) (and π₁ π₂)
  /-- There is a true `Δ₀` sentence (`0 = 0`). -/
  exists_true_delta0 : ∃ α, IsSigma 0 α ∧ TrueN α
  /-- Robinson's arithmetic `Q`, as a set of sentences. -/
  Q : Sent → Prop
  Q_delta0 : ∀ α, IsSigma 0 α → TrueN α → Deriv Q α
  Q_delta0_neg : ∀ α, IsSigma 0 α → ¬ TrueN α → Deriv Q (neg α)
  /-- Representability of `Σ⁰_{m+2}` conditions on machines by `Σ⁰_{m+2}` sentences, uniformly
  (Lemma 4.2 and its level-`n` version in Section 6.3): for a computable `R ⊂ 𝒯 × ℕ^{m+2}` there is a
  total computable `σ_R : 𝒯 → 𝓐` with `σ_R (T) ∈ Σ⁰_{m+2}` and `ℕ ⊨ σ_R (T)` iff
  `∃ u₁ ∀ u₂ ⋯ u_{m+2}, R (T, u₁, …, u_{m+2})` (`NSR m R T ()`). -/
  reprN : ∀ (m : ℕ) (R : NRel M.Code Unit m),
    @NRelComp M M.Code Unit encCode encUnit m R →
    ∃ σ : M.Code → Sent, @CompT M M.Code Sent encCode enc σ ∧
      ∀ T, IsSigma (m + 2) (σ T) ∧ (TrueN (σ T) ↔ NSR m R T ())

namespace Arith

variable {M : TuringModel} (A : Arith M)

/-- Representability of computable relations by `Σ⁰₂` sentences (Lemma 4.2): the case `m = 0`
of `reprN`. -/
theorem repr (W : M.Code → ℕ → ℕ → Prop)
    (hW : CompSet M (fun q : M.Code × ℕ × ℕ => W q.1 q.2.1 q.2.2)) :
    ∃ σ : M.Code → A.Sent, CompT M σ ∧ ∀ T, A.IsSigma 2 (σ T) ∧ (A.TrueN (σ T) ↔ ∃ u, ∀ v, W T u v) := by
  have hR : NRelComp (M := M) 0 (fun (T : M.Code) (_ : NB Unit 0) u v => W T u v) :=
    hW.comp (CompT.pair compT_fst (CompT.pair (compT_fst.comp (compT_snd.comp compT_snd))
      (compT_snd.comp (compT_snd.comp compT_snd))))
  obtain ⟨σ, hσ, hσ'⟩ := A.reprN 0 _ hR
  exact ⟨σ, hσ, fun T => ⟨(hσ' T).1, (hσ' T).2⟩⟩

/-- `Tr_{Πₙ}`: the true `Π⁰ₙ` sentences. -/
def TrPi (n : ℕ) : A.Sent → Prop := fun π => A.IsPi n π ∧ A.TrueN π

/-- `Σ₁`-completeness of `Q` (a consequence of the interface). -/
theorem Q_sigma1 {σ : A.Sent} (hσ : A.IsSigma 1 σ) (ht : A.TrueN σ) : A.Deriv A.Q σ := by
  obtain ⟨v, hv⟩ := (A.trueN_sigma 0 σ hσ).1 ht
  have h0 : A.IsSigma 0 (A.instS σ v) := (A.sigma_zero_iff_pi_zero _).2 (A.instS_pi 0 σ v hσ)
  have h1 := A.Q_delta0 _ h0 hv
  exact A.deriv_cut (fun β hβ => by rw [hβ]; exact h1) (A.exists_intro 0 σ v hσ)

/-- `Δ₀ ⊆ Σₙ` and `Δ₀ ⊆ Πₙ` for every `n`. -/
theorem sigma_of_delta0 {α : A.Sent} (h : A.IsSigma 0 α) : ∀ n, A.IsSigma n α
  | 0 => h
  | n + 1 => A.sigma_succ n α (sigma_of_delta0 h n)

theorem pi_of_delta0 {α : A.Sent} (h : A.IsSigma 0 α) : ∀ n, A.IsPi n α
  | 0 => (A.sigma_zero_iff_pi_zero α).1 h
  | n + 1 => A.pi_succ n α (pi_of_delta0 h n)

/-- A true `Σ⁰ₙ₊₁` sentence `∃x̄ ¬φ` (`negPi π`) refutes `π`. -/
theorem not_trueN_of_trueN_negPi {n : ℕ} {π : A.Sent} (hπ : A.IsPi (n + 1) π)
    (h : A.TrueN (A.negPi π)) : ¬ A.TrueN π := by
  intro hπt
  obtain ⟨v, hv⟩ := (A.trueN_sigma n _ (A.negPi_sigma n π hπ)).1 h
  rw [A.negPi_inst n π v hπ, A.trueN_neg] at hv
  exact hv ((A.trueN_pi n π hπ).1 hπt v)

/-- Universal elimination in the form `F ⊢ ¬φ(n̄)` implies `F ⊢ ¬∀x̄ φ`. -/
theorem deriv_neg_pi_of_neg_inst {F : A.Sent → Prop} {π : A.Sent} {n v : ℕ} (hπ : A.IsPi (n + 1) π)
    (h : A.Deriv F (A.neg (A.instP π v))) : A.Deriv F (A.neg π) := by
  refine A.deriv_neg_intro fun γ => ?_
  have h1 : A.Deriv (fun β => F β ∨ β = π) (A.instP π v) :=
    A.deriv_cut (fun β hβ => by rw [hβ]; exact A.deriv_of_mem (Or.inr rfl)) (A.forall_elim n π v hπ)
  have h2 : A.Deriv (fun β => F β ∨ β = π) (A.neg (A.instP π v)) :=
    A.deriv_mono (fun β hβ => Or.inl hβ) h
  exact A.deriv_explosion h1 h2

/-- A false `Π⁰ₙ₊₁` sentence has a false instance, and then `Q` refutes a `Δ₀` instance of that. -/
theorem trueN_pi_of_forall {π : A.Sent} {n : ℕ} (hπ : A.IsPi (n + 1) π)
    (h : ∀ v, A.TrueN (A.instP π v)) : A.TrueN π := (A.trueN_pi n π hπ).2 h

end Arith

/-! ### Consistency notions relative to a translation (Definition B.6; the forms for theories of
arithmetic, Definitions 2.9 and 6.5, are in `Stable.Plain`) -/

namespace Translation

variable {M : TuringModel} {A : Arith M} {L : Language M} (i : Translation A.toLanguage L)

/-- `F` is `1`-consistent relative to `i` (Definition B.6): `F ⊢ⁱ Q`, and for every
`Σ⁰₁` sentence `∃x̄ φ` with `F ⊢ⁱ ∃x̄ φ` there is an instance with `F ⊬ⁱ ¬φ(n̄)`. -/
def OneConsistent (F : L.Sent → Prop) : Prop :=
  i.DerivISet F A.Q ∧
    ∀ σ, A.IsSigma 1 σ → i.DerivI F σ → ∃ v, ¬ i.DerivI F (A.neg (A.instS σ v))

/-- `F` is `2`-consistent relative to `i`: `1`-consistent, and the same for `Σ⁰₂` sentences
`∃x̄ φ`, `φ ∈ Π⁰₁`. -/
def TwoConsistent (F : L.Sent → Prop) : Prop :=
  i.OneConsistent F ∧
    ∀ σ, A.IsSigma 2 σ → i.DerivI F σ → ∃ v, ¬ i.DerivI F (A.neg (A.instS σ v))

/-- `F` is `Σₙ`-sound relative to `i` (Definition B.6). -/
def SigmaSound (n : ℕ) (F : L.Sent → Prop) : Prop :=
  ∀ σ, A.IsSigma n σ → i.DerivI F σ → A.TrueN σ

/-- `M : ℕ → 𝓛 × {±}` is speculative with respect to `i` (Definition 3.24): `M^s ⊢ⁱ π` for every
true `Π⁰₁` sentence `π`. -/
def Speculative (Mp : ℕ → Option (L.Sent × Bool)) : Prop :=
  ∀ π, A.TrPi 1 π → i.DerivI (Stab Mp) π

/-- `i` is an `n`-translation (Definition B.1): computable on the `Σ⁰ₙ` sentences. -/
def IsNTranslation (n : ℕ) : Prop :=
  @CompT M {α // A.IsSigma n α} L.Sent (Enc.restrict (A.IsSigma n) (A.sigma_comp n)) L.enc
    (fun σ => i.i σ.1)

/-- An `n`-translation is computable on `Π⁰ₙ₋₁` sentences, as these are `Σ⁰ₙ`; here for `n = 2`
and `Π⁰₁`, in the form used for `Spec`. -/
theorem compT_on_pi_of_two {P : A.Sent → Prop} (hP : CompSet M P) (hPsub : ∀ α, P α → A.IsSigma 2 α)
    (h : i.IsNTranslation 2) :
    @CompT M {α // P α} L.Sent (Enc.restrict P hP) L.enc (fun σ => i.i σ.1) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun σ => hT ⟨σ.1, hPsub σ.1 σ.2⟩⟩

end Translation

end Stable
