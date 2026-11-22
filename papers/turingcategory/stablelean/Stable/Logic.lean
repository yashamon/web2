import Stable.Machines

/-!
# First order languages, theories and translations (Section 2.2)

A first order language `𝓛` is identified with its set of sentences.  We package exactly what the
paper uses about it:

* its distinguished encoding (Proposition 2.4 (5)), with the decidable derivation relation
  `Prf ⊂ ℕ × L(𝓛) × 𝓛` such that `image l ⊢ γ` iff `(p, l, γ) ∈ Prf` for some `p`;
* the derivability relation `F ⊢ α` of a fixed sound and complete deductive system, of which
  only the following is used: it is monotone and reflexive, closed under cut, finitary
  (compactness), and satisfies the usual rules for `¬` and `∧`;
* `𝓛` is infinite as an encoded set (used in Section 3.3).

Theories are subsets `F : 𝓛.Sent → Prop`; `𝓛.closure F = {α | F ⊢ α}` is the deductive closure
`F̄`, and `F` is consistent iff `F̄ ≠ 𝓛`.  Translations (Definition 2.6) preserve `¬`, `∧` and
derivability (`∨` is omitted: here it is a defined connective, see `Stable/PropCalc.lean`).
`F ⊢ⁱ α` (Definition B.4) is derivability from the induced theory `F_{i,𝓛'} = i⁻¹ (F̄)`, and
Lemma B.5 (`lemma_vdashi`) identifies it with `F ⊢ i (α)`.
-/

namespace Stable

open Classical

/-- A first order language, identified with its set of sentences, together with the data of
Proposition 2.4 (5) and the properties of derivability used in the paper. -/
structure Language (M : TuringModel) where
  /-- The set of sentences. -/
  Sent : Type
  /-- The distinguished encoding of `𝓛`. -/
  enc : Enc M Sent
  /-- Derivability `F ⊢ α` in the fixed deductive system. -/
  Deriv : (Sent → Prop) → Sent → Prop
  neg : Sent → Sent
  and : Sent → Sent → Sent
  /-- `(p, l, γ) ∈ Prf` iff `p` codes a derivation of `γ` from the list `l`. -/
  Prf : ℕ → List Sent → Sent → Prop
  prf_comp : @CompSet M (ℕ × List Sent × Sent) (@encProd M ℕ (List Sent × Sent) encNat
    (@encProd M (List Sent) Sent (@encList M Sent enc) enc)) (fun q => Prf q.1 q.2.1 q.2.2)
  prf_iff : ∀ (l : List Sent) (γ : Sent), (∃ p, Prf p l γ) ↔ Deriv (fun α => α ∈ l) γ
  /-- `𝓛` is infinite. -/
  infinite : @Enc.Infinite M Sent enc
  /-- Negation is a computable syntactic operation. -/
  neg_comp : @CompT M Sent Sent enc enc neg
  -- structural properties of derivability
  deriv_of_mem : ∀ {F : Sent → Prop} {α}, F α → Deriv F α
  deriv_mono : ∀ {F G : Sent → Prop} {α}, (∀ β, F β → G β) → Deriv F α → Deriv G α
  deriv_cut : ∀ {F G : Sent → Prop} {α}, (∀ β, G β → Deriv F β) → Deriv G α → Deriv F α
  deriv_compact : ∀ {F : Sent → Prop} {α}, Deriv F α →
    ∃ l : List Sent, (∀ β, β ∈ l → F β) ∧ Deriv (fun β => β ∈ l) α
  -- propositional rules
  /-- If `F ∪ {α}` is inconsistent then `F ⊢ ¬α`. -/
  deriv_neg_intro : ∀ {F : Sent → Prop} {α}, (∀ γ, Deriv (fun β => F β ∨ β = α) γ) → Deriv F (neg α)
  deriv_explosion : ∀ {F : Sent → Prop} {α β}, Deriv F α → Deriv F (neg α) → Deriv F β
  deriv_dne : ∀ {F : Sent → Prop} {α}, Deriv F (neg (neg α)) → Deriv F α
  deriv_dni : ∀ {F : Sent → Prop} {α}, Deriv F α → Deriv F (neg (neg α))
  deriv_and_intro : ∀ {F : Sent → Prop} {α β}, Deriv F α → Deriv F β → Deriv F (and α β)
  deriv_and_left : ∀ {F : Sent → Prop} {α β}, Deriv F (and α β) → Deriv F α
  deriv_and_right : ∀ {F : Sent → Prop} {α β}, Deriv F (and α β) → Deriv F β

attribute [instance] Language.enc

namespace Language

variable {M : TuringModel} (L : Language M)

/-- The deductive closure `F̄` of a theory. -/
def closure (F : L.Sent → Prop) : L.Sent → Prop := fun α => L.Deriv F α

/-- `F` is deductively closed. -/
def Closed (F : L.Sent → Prop) : Prop := ∀ α, L.Deriv F α → F α

/-- `F` is consistent: `F̄ ≠ 𝓛`. -/
def Consistent (F : L.Sent → Prop) : Prop := ∃ α, ¬ L.Deriv F α

/-- `F ⊢ G` for a set of sentences `G`. -/
def DerivSet (F G : L.Sent → Prop) : Prop := ∀ α, G α → L.Deriv F α

theorem closed_closure (F : L.Sent → Prop) : L.Closed (L.closure F) := fun _ h =>
  L.deriv_cut (fun _ hβ => hβ) h

theorem deriv_closure_iff (F : L.Sent → Prop) (α : L.Sent) :
    L.Deriv (L.closure F) α ↔ L.Deriv F α :=
  ⟨fun h => L.deriv_cut (fun _ hβ => hβ) h, fun h => L.deriv_mono (fun _ hβ => L.deriv_of_mem hβ) h⟩

/-- An inconsistent theory proves everything. -/
theorem not_consistent_iff (F : L.Sent → Prop) : ¬ L.Consistent F ↔ ∀ α, L.Deriv F α := by
  unfold Consistent
  constructor
  · intro h α; exact Classical.byContradiction fun hc => h ⟨α, hc⟩
  · rintro h ⟨α, hα⟩; exact hα (h α)

theorem consistent_of_not_deriv {F : L.Sent → Prop} {α : L.Sent} (h : ¬ L.Deriv F α) :
    L.Consistent F := ⟨α, h⟩

/-- A theory proving `α` and `¬α` is inconsistent. -/
theorem not_consistent_of_deriv_neg {F : L.Sent → Prop} {α : L.Sent} (h₁ : L.Deriv F α)
    (h₂ : L.Deriv F (L.neg α)) : ¬ L.Consistent F :=
  (L.not_consistent_iff F).2 fun _ => L.deriv_explosion h₁ h₂

/-- Derivability from a finite list, via `Prf`. -/
theorem deriv_list_iff (l : List L.Sent) (γ : L.Sent) :
    L.Deriv (fun α => α ∈ l) γ ↔ ∃ p, L.Prf p l γ := (L.prf_iff l γ).symm

end Language

/-- A translation `i : 𝓛' → 𝓛` (Definition 2.6): a total set embedding preserving `¬`, `∧` and
derivability. -/
structure Translation {M : TuringModel} (L' L : Language M) where
  i : L'.Sent → L.Sent
  inj : ∀ {α β}, i α = i β → α = β
  map_neg : ∀ α, i (L'.neg α) = L.neg (i α)
  map_and : ∀ α β, i (L'.and α β) = L.and (i α) (i β)
  map_deriv : ∀ (S : L'.Sent → Prop) (α : L'.Sent), L'.Deriv S α →
    L.Deriv (fun β => ∃ γ, S γ ∧ i γ = β) (i α)

namespace Translation

variable {M : TuringModel} {L' L : Language M} (i : Translation L' L)

/-- The induced theory `F_{i,𝓛'} = i⁻¹ (F̄)` (Definition B.2). -/
def induced (F : L.Sent → Prop) : L'.Sent → Prop := fun α => L.Deriv F (i.i α)

/-- `F ⊢ⁱ α` (Definition B.4): `F_{i,𝓛'} ⊢ α`. -/
def DerivI (F : L.Sent → Prop) (α : L'.Sent) : Prop := L'.Deriv (i.induced F) α

/-- `F ⊢ⁱ F'` for a set `F'` of sentences of `𝓛'`. -/
def DerivISet (F : L.Sent → Prop) (F' : L'.Sent → Prop) : Prop := ∀ α, F' α → i.DerivI F α

/-- Lemma B.5 (`lemma_vdashi`): `F ⊢ⁱ α` iff `F ⊢ i (α)`. -/
theorem derivI_iff (F : L.Sent → Prop) (α : L'.Sent) : i.DerivI F α ↔ L.Deriv F (i.i α) := by
  constructor
  · intro h
    have h1 := i.map_deriv _ _ h
    refine L.deriv_cut (fun β hβ => ?_) h1
    obtain ⟨γ, hγ, rfl⟩ := hβ
    exact hγ
  · intro h
    exact L'.deriv_of_mem h

/-- Lemma B.3 (`lemma_inducedclosed`): the induced theory is deductively closed. -/
theorem induced_closed (F : L.Sent → Prop) : L'.Closed (i.induced F) := fun α h =>
  (i.derivI_iff F α).1 h

theorem derivI_of_mem {F : L.Sent → Prop} {α : L'.Sent} (h : i.induced F α) : i.DerivI F α :=
  L'.deriv_of_mem h

/-- Monotonicity of `⊢ⁱ` in the theory. -/
theorem derivI_mono {F G : L.Sent → Prop} (h : ∀ β, F β → G β) {α : L'.Sent}
    (hα : i.DerivI F α) : i.DerivI G α := by
  rw [derivI_iff] at *
  exact L.deriv_mono h hα

/-- `⊢ⁱ` is closed under derivability in `𝓛'`. -/
theorem derivI_cut {F : L.Sent → Prop} {G : L'.Sent → Prop} {α : L'.Sent}
    (hG : ∀ β, G β → i.DerivI F β) (h : L'.Deriv G α) : i.DerivI F α :=
  L'.deriv_cut hG h

/-- If `F ⊢ⁱ α` and `F ⊢ⁱ ¬α` then `F̄ = 𝓛`. -/
theorem not_consistent_of_derivI_neg {F : L.Sent → Prop} {α : L'.Sent} (h₁ : i.DerivI F α)
    (h₂ : i.DerivI F (L'.neg α)) : ¬ L.Consistent F := by
  rw [derivI_iff] at h₁ h₂
  rw [i.map_neg] at h₂
  exact L.not_consistent_of_deriv_neg h₁ h₂

/-- `F ⊢ⁱ α` is monotone under passing to the deductive closure. -/
theorem derivI_closure_iff (F : L.Sent → Prop) (α : L'.Sent) :
    i.DerivI (L.closure F) α ↔ i.DerivI F α := by
  rw [derivI_iff, derivI_iff, L.deriv_closure_iff]

end Translation

/-! ### Computable translations and `n`-translations -/

/-- A computable translation map. -/
def Translation.Computable {M : TuringModel} {L' L : Language M} (i : Translation L' L) : Prop :=
  CompT M i.i

end Stable
