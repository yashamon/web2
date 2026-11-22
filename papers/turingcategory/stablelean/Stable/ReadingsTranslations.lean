import Stable.Readings

/-!
# Translations as readings (Example 5.23 of the restructured paper)

Let `𝓛` be a first order language and `i : 𝓐 → 𝓛` a translation whose restriction to a computable
`P ⊇ 𝓑₂` is computable.  Then `R := {(a, i (a))}` is a reading with `IsReadingOn P R`
(`isReadingOn_translation`), and for `F₀ = F̄₁`, presented by `C_𝓛 (T₁)`, the set `F₀^R` is the
induced theory `i⁻¹ (F̄₁)` (`asserted_graph_eq_induced`).  So Corollaries 5.20 and 5.21 give the
theorems for translations of the earlier version of the paper, with the Gödel sentence
`𝒢 (Sh_R (C_𝓛 (T₁)))`:

* `first_incompleteness_via_readings`: the three statements of Theorem 1.5 relative to `i`;
* `second_incompleteness_via_readings`: `F₁ ⊬ⁱ con`, for `i : 𝓩 → 𝓛` with `F₁ ⊢ⁱ ZFC`, where
  `j = i ∘ i_{𝓐,𝓩}` is computable on `P` and `F₁` is `1`-consistent relative to `j`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-- A computable set is `Σ⁰₂`. -/
theorem IsSigma2Set.of_compSet {B : Type} [Enc M B] {S : B → Prop} (h : CompSet M S) :
    IsSigma2Set (M := M) S := by
  have h0 : CompSet M (fun n : ℕ => ∃ b : B, e M b = n ∧ S b) := by
    refine TuringModel.IsCompSet.congr h fun n => ?_
    constructor
    · intro hn; exact ⟨n, rfl, hn⟩
    · rintro ⟨a, rfl, hn⟩; exact hn
  exact ⟨fun x _ _ => ∃ b : B, e M b = x ∧ S b, h0.comp compT_fst,
    fun x => ⟨fun hx => ⟨0, fun _ => hx⟩, fun ⟨_, hu⟩ => hu 0⟩⟩

variable {A : Arith M} {L : Language M}

/-- Example 5.23: the graph of a translation computable on `P` is a reading whose part on `P` is
computable, hence `Σ⁰₂`. -/
theorem isReadingOn_translation (i : Translation A.toLanguage L) {P : A.Sent → Prop}
    (hP : CompSet M P)
    (hi : @CompT M {α // P α} L.Sent (Enc.restrict P hP) L.enc (fun σ => i.i σ.1)) :
    IsReadingOn (M := M) P (fun (a : A.Sent) (α : L.Sent) => i.i a = α) := by
  -- `b ↦ i b` on `P`, as a total `Option`-valued computable map
  have hg : CompT M (fun b : A.Sent => if P b then some (i.i b) else none) := by
    refine CompT.ofComp (Comp.ofRestrict hP (f := i.i) hi) ?_
    exact hP.congr fun b => by by_cases h : P b <;> simp [h]
  have hEq : CompSet M (fun p : A.Sent × L.Sent =>
      (if P p.1 then some (i.i p.1) else none) = some p.2) :=
    compSet_eq (hg.comp compT_fst) (compT_some.comp compT_snd)
  refine IsSigma2Set.of_compSet (hEq.congr fun p => ?_)
  by_cases h : P p.1 <;> simp [h]

/-- For `F₀ = F̄₁`, presented by `C_𝓛 (T₁)`, and the graph of a translation `i`:
`F₀^R = i⁻¹ (F̄₁)`, the induced theory. -/
theorem asserted_graph_eq_induced {L' : Language M} (i : Translation L' L) (T₁ : M.Code) :
    Asserted (fun (a : L'.Sent) (α : L.Sent) => i.i a = α) (Ts (M := M) L.Sent (CL L T₁)) =
      i.induced (Ts (M := M) L.Sent T₁) := by
  funext a
  refine propext ⟨?_, fun h => ⟨i.i a, (CL_spec L T₁ _).2 h, rfl⟩⟩
  rintro ⟨α, hα, h⟩
  rw [← h] at hα
  exact (CL_spec L T₁ _).1 hα

section Example

variable (i : Translation A.toLanguage L) {P : A.Sent → Prop} (hP : CompSet M P)
  (hi : @CompT M {α // P α} L.Sent (Enc.restrict P hP) L.enc (fun σ => i.i σ.1))

/-- The machine `Sh_R (C_𝓛 (T₁))` of Example 5.23. -/
noncomputable def ShadowT : M.Code → M.Code :=
  fun T₁ => Shadow hP (isReadingOn_translation i hP hi) (CL L T₁)

theorem ShadowT_compT : CompT M (ShadowT i hP hi) :=
  (Shadow_compT hP (isReadingOn_translation i hP hi)).comp (choose_spec (exists_C L)).1

/-- `(Sh_R (C_𝓛 T₁))^s = i⁻¹ (F̄₁) ∩ P`. -/
theorem ShadowT_Ts (T₁ : M.Code) (b : A.Sent) :
    Ts (M := M) A.Sent (ShadowT i hP hi T₁) b ↔
      P b ∧ Asserted (fun (a : A.Sent) (α : L.Sent) => i.i a = α)
        (Ts (M := M) L.Sent (CL L T₁)) b :=
  Shadow_Ts hP (isReadingOn_translation i hP hi) (CL L T₁) b

include hP hi in
/-- Example 5.23, first part: the statements of Theorem 1.5 relative to a translation `i`
computable on `P ⊇ 𝓑₂`, for the total computable map `𝒢 ∘ Sh_R ∘ C_𝓛`. -/
theorem first_incompleteness_via_readings (hPB : ∀ b, A.BoolComb 2 b → P b) :
    ∃ G : M.Code → A.Sent, CompT M G ∧ ∀ T₁ : M.Code,
      (i.OneConsistent (Ts (M := M) L.Sent T₁) → ¬ i.DerivI (Ts (M := M) L.Sent T₁) (G T₁)) ∧
      (i.TwoConsistent (Ts (M := M) L.Sent T₁) →
        ¬ i.DerivI (Ts (M := M) L.Sent T₁) (A.neg (G T₁))) ∧
      (i.OneConsistent (Ts (M := M) L.Sent T₁) → A.TrueN (G T₁)) := by
  refine ⟨fun T₁ => G₀ A (ShadowT i hP hi T₁), A.G₀_compT.comp (ShadowT_compT i hP hi),
    fun T₁ => ?_⟩
  have hE := asserted_graph_eq_induced i T₁
  have hcl : A.toLanguage.Closed (Asserted (fun (a : A.Sent) (α : L.Sent) => i.i a = α)
      (Ts (M := M) L.Sent (CL L T₁))) := by
    rw [hE]; exact i.induced_closed _
  have h := reading_first hPB (ShadowT_Ts i hP hi T₁) hcl
  rw [hE] at h
  exact ⟨fun hc hd => h.1 hc (i.induced_closed _ _ hd),
    fun hc hd => h.2.1 hc (i.induced_closed _ _ hd), fun hc => h.2.2 hc⟩

end Example

/-- Example 5.23, last part: for `i : 𝓩 → 𝓛` with `F₁ ⊢ⁱ ZFC`, `j = i ∘ i_{𝓐,𝓩}` computable on
`P ⊇ 𝓑₂`, and `F₁` `1`-consistent relative to `j`: `F₁ ⊬ⁱ con`, where `con ∈ 𝓩` satisfies (5.12) for
the machine `T = Sh_R (C_𝓛 (T₁))`. -/
theorem second_incompleteness_via_readings {Z : Language M} (iAZ : Translation A.toLanguage Z)
    (i : Translation Z L) {P : A.Sent → Prop} (hP : CompSet M P)
    (hPB : ∀ b, A.BoolComb 2 b → P b)
    (hj : @CompT M {α // P α} L.Sent (Enc.restrict P hP) L.enc (fun σ => (i.comp iAZ).i σ.1))
    (ZFC : Z.Sent → Prop) (T₁ : M.Code)
    (hZFC : i.DerivISet (Ts (M := M) L.Sent T₁) ZFC)
    (h1 : (i.comp iAZ).OneConsistent (Ts (M := M) L.Sent T₁)) (con : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con)
      (iAZ.i (G₀ A (ShadowT (i.comp iAZ) hP hj T₁)))) :
    ¬ i.DerivI (Ts (M := M) L.Sent T₁) con := by
  intro hc
  have hE := asserted_graph_eq_induced i T₁
  have hEj := asserted_graph_eq_induced (i.comp iAZ) T₁
  -- `H = F₀^{R'}` is the induced theory `i⁻¹ (F̄₁)`
  have hH : Z.Closed (Asserted (fun (z : Z.Sent) (α : L.Sent) => i.i z = α)
      (Ts (M := M) L.Sent (CL L T₁))) := by
    rw [hE]; exact i.induced_closed _
  have hZ : ∀ β, ZFC β → Asserted (fun (z : Z.Sent) (α : L.Sent) => i.i z = α)
      (Ts (M := M) L.Sent (CL L T₁)) β := by
    intro β hβ; rw [hE]; exact i.induced_closed _ _ (hZFC β hβ)
  -- the shadow machine presents `j⁻¹ (F̄₁) ∩ P`, which is `1`-consistent
  have hT := ShadowT_Ts (i.comp iAZ) hP hj T₁
  have hclj : A.toLanguage.Closed (Asserted (fun (a : A.Sent) (α : L.Sent) => (i.comp iAZ).i a = α)
      (Ts (M := M) L.Sent (CL L T₁))) := by
    rw [hEj]; exact (i.comp iAZ).induced_closed _
  have h1' : A.OneConsistent (Ts (M := M) A.Sent (ShadowT (i.comp iAZ) hP hj T₁)) := by
    refine oneConsistent_shadow hPB hT hclj ?_
    rw [hEj]; exact h1
  have h := reading_second iAZ ZFC hPB hT hH hZ h1' con hcon
  rw [hE] at h
  exact h (i.induced_closed _ _ hc)

end Stable
