import Stable.Incompleteness

/-!
# The second incompleteness theorem (Section 5.1), abstract form

Let `𝓩` be the language of set theory, `i_{𝓐,𝓩} : 𝓐 → 𝓩` the standard interpretation of arithmetic
in set theory (Example 2.8), `ZFC ⊂ 𝓩`, `i : 𝓩 → 𝓛` a `2`-translation and
`j := i ∘ i_{𝓐,𝓩} : 𝓐 → 𝓛`.  Theorem 5.11 says: if `F = T^s` satisfies `F ⊢ⁱ ZFC` and is
`1`-consistent relative to `j`, then `F ⊬ⁱ Con₁ (T, i)`, where `Con₁ (T, i) ∈ 𝓩` is the sentence
"`T^s` is `1`-consistent relative to `j`" of Definition 5.10.

The proof in the paper has exactly one ingredient that is not a theorem about the abstract
objects formalized here: equation (5.12),
```
  ZFC ⊢ Con₁ (T, i) → i_{𝓐,𝓩} (𝒢 (T)),
```
the formalization *inside* `ZFC` of Proposition 5.5 (3), uniformly in `T`.  Verifying (5.12)
would require a formalization of `ZFC`-provability and a `ZFC`-internal replay of the whole
development; it is therefore taken as a hypothesis (`hcon` below), stated for an arbitrary
sentence `con ∈ 𝓩`.  Given (5.12), Theorem 5.11 is the short derivation `second_incompleteness`
below, and Corollary 5.13 is `second_incompleteness_corollary`, with the sentence
"`Enum (T, δ) → (Con₁ (δ, i) ↔ Con₁ (T, i))` is a theorem of `ZFC`" likewise a hypothesis.

In the restructured manuscript (11 November 2026) the theorems are stated for theories of
arithmetic, the case `𝓛 = 𝓐`, `i = id` of this file: see `Stable.Plain` (level `n`: `Stable.NPlain`).
The statements for a translation `i`, as here, are Example 5.23 and its level-`n` form, with the
notation of Appendix B; they are also recovered from readings in `Stable.ReadingsTranslations`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-- Composition of translations. -/
def Translation.comp {L₀ L₁ L₂ : Language M} (i : Translation L₁ L₂) (j : Translation L₀ L₁) :
    Translation L₀ L₂ where
  i := fun α => i.i (j.i α)
  inj := fun h => j.inj (i.inj h)
  map_neg := fun α => by rw [j.map_neg, i.map_neg]
  map_and := fun α β => by rw [j.map_and, i.map_and]
  map_deriv := fun S α h => by
    have h1 := i.map_deriv _ _ (j.map_deriv S α h)
    refine L₂.deriv_mono (fun β hβ => ?_) h1
    obtain ⟨γ, ⟨γ', hγ', rfl⟩, rfl⟩ := hβ
    exact ⟨γ', hγ', rfl⟩

theorem Translation.comp_i {L₀ L₁ L₂ : Language M} (i : Translation L₁ L₂) (j : Translation L₀ L₁)
    (α : L₀.Sent) : (i.comp j).i α = i.i (j.i α) := rfl

variable {A : Arith M} {Z L : Language M}

/-- Theorem 5.11 (`theorem_secondincompleteness`), abstract form.  Hypotheses: `iAZ : 𝓐 → 𝓩`,
`i : 𝓩 → 𝓛` with `j = i ∘ iAZ` a `2`-translation, `F = T^s` with `F ⊢ⁱ ZFC` and `1`-consistent
relative to `j`, and a sentence `con ∈ 𝓩` with `ZFC ∪ {con} ⊢ iAZ (𝒢 (T))` (equation (5.12) of
the paper, for `con = Con₁ (T, i)`).  Then `F ⊬ⁱ con`. -/
theorem second_incompleteness (iAZ : Translation A.toLanguage Z) (i : Translation Z L)
    (hj : (i.comp iAZ).IsNTranslation 2) (ZFC : Z.Sent → Prop) (T : M.Code)
    (hZFC : i.DerivISet (Ts (M := M) L.Sent T) ZFC)
    (h1 : (i.comp iAZ).OneConsistent (Ts (M := M) L.Sent T)) (con : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G (i.comp iAZ) hj T))) :
    ¬ i.DerivI (Ts (M := M) L.Sent T) con := by
  intro hc
  -- `F ⊢ⁱ iAZ (𝒢 T)`, as `F_{i,𝓩}` is deductively closed and contains `ZFC` and `con`
  have h2 : i.DerivI (Ts (M := M) L.Sent T) (iAZ.i (G (i.comp iAZ) hj T)) := by
    refine i.derivI_cut (fun β hβ => ?_) hcon
    rcases hβ with hβ | rfl
    · exact hZFC β hβ
    · exact hc
  -- that is `F ⊢ʲ 𝒢 (T)`, contradicting Proposition 5.5 (1)
  have h3 : (i.comp iAZ).DerivI (Ts (M := M) L.Sent T) (G (i.comp iAZ) hj T) := by
    rw [Translation.derivI_iff] at h2 ⊢
    exact h2
  exact not_derivI_G (i.comp iAZ) hj T h1 h3

/-- Corollary 5.13 (`corollary_secondincompleteness`), abstract form.  With `con = Con₁ (T, i)` as
in Theorem 5.11, let `enum`, `conδ ∈ 𝓩` be the sentences `Enum (T, δ)` and `Con₁ (δ)`: they say, in
terms of `δ`, that `T` stably enumerates `F` and that `F` is `1`-consistent.  Suppose
`ZFC ∪ {enum, conδ} ⊢ con` (as `ZFC` proves
`Enum (T, δ) → (Con₁ (δ, i) ↔ Con₁ (T, i))`).  If `F ⊢ⁱ enum` then `F ⊬ⁱ conδ`. -/
theorem second_incompleteness_corollary (iAZ : Translation A.toLanguage Z) (i : Translation Z L)
    (hj : (i.comp iAZ).IsNTranslation 2) (ZFC : Z.Sent → Prop) (T : M.Code)
    (hZFC : i.DerivISet (Ts (M := M) L.Sent T) ZFC)
    (h1 : (i.comp iAZ).OneConsistent (Ts (M := M) L.Sent T)) (con enum conδ : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G (i.comp iAZ) hj T)))
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = conδ) con)
    (henum : i.DerivI (Ts (M := M) L.Sent T) enum) :
    ¬ i.DerivI (Ts (M := M) L.Sent T) conδ := by
  intro hc
  refine second_incompleteness iAZ i hj ZFC T hZFC h1 con hcon ?_
  refine i.derivI_cut (fun β hβ => ?_) hδ
  rcases hβ with hβ | rfl | rfl
  · exact hZFC β hβ
  · exact henum
  · exact hc

/-- Theorem A.2 in the form of the manuscript before 11 November 2026, abstract form (for the present
form see `Stable.Penrose`).  For `𝓗 = T^s` with `𝓗 ⊢ⁱ ZFC`, a definition `δ`
and the Penrose property `𝓗 ⊢ⁱ Con₁ (δ, i)`, one of: (1) `T` does not stably enumerate `𝓗` — here
`𝓗 = T^s` by definition, so this alternative is vacuous and the theorem is stated for the
enumerating machine `T`; (2) `𝓗` is not `1`-consistent; (3) `𝓗 ⊬ⁱ Enum (T, δ)`.  The `ZFC`-provability
hypotheses are as in `second_incompleteness_corollary`. -/
theorem penrose (iAZ : Translation A.toLanguage Z) (i : Translation Z L)
    (hj : (i.comp iAZ).IsNTranslation 2) (ZFC : Z.Sent → Prop) (T : M.Code)
    (hZFC : i.DerivISet (Ts (M := M) L.Sent T) ZFC) (con enum conδ : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i (G (i.comp iAZ) hj T)))
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = conδ) con)
    (hpenrose : i.DerivI (Ts (M := M) L.Sent T) conδ) :
    ¬ (i.comp iAZ).OneConsistent (Ts (M := M) L.Sent T) ∨ ¬ i.DerivI (Ts (M := M) L.Sent T) enum := by
  by_cases h1 : (i.comp iAZ).OneConsistent (Ts (M := M) L.Sent T)
  · right
    intro henum
    exact second_incompleteness_corollary iAZ i hj ZFC T hZFC h1 con enum conδ hcon hδ henum hpenrose
  · exact Or.inl h1

end Stable
