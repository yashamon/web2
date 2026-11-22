import Stable.SpecRel

/-!
# The speculative closure (Theorem 3.25, `theorem_speculative`)

For a `2`-translation `i : 𝓐 → 𝓛` there is a total computable `Spec_i : 𝒯 → 𝒯` such that for every
`T`, writing `T_spec = Spec_i T`:
1. `T_spec ∈ 𝒯_𝓛` and `T_spec'` is total;
2. `T_spec'` is speculative with respect to `i`;
3. `T_spec^s = T^s ∪ i (Tr_{Π₁})`;
4. if `T^s` is `1`-consistent relative to `i` then `T_spec^s` is consistent.

Parts 1–3 are the stabilizer-machine construction for the relation `R_S` (`Stable.SpecRel`);
part 4 is Lemma 3.26 (`lemma_Sconsistent`): if `F ∪ i (Tr_{Π₁})` is inconsistent then `F ⊢ⁱ ¬π`
for some true `Π⁰₁` sentence `π`, which contradicts `1`-consistency.
-/

namespace Stable

open Classical

variable {M : TuringModel} {A : Arith M} {L : Language M} (i : Translation A.toLanguage L)

/-- The conjunction `π₁ ∧ … ∧ πₙ ∧ δ` of a list of `Π⁰₁` sentences, as a `Π⁰₁` sentence
(`andPi` iterated, with base `δ`). -/
def conjPi (A : Arith M) (δ : A.Sent) : List A.Sent → A.Sent
  | [] => δ
  | π :: πs => A.andPi π (conjPi A δ πs)

theorem conjPi_pi {δ : A.Sent} {n : ℕ} (hδ : A.IsPi n δ) :
    ∀ πs : List A.Sent, (∀ π, π ∈ πs → A.IsPi n π) → A.IsPi n (conjPi A δ πs)
  | [], _ => hδ
  | π :: πs, h => A.andPi_pi n _ _ (h π (List.mem_cons_self ..))
      (conjPi_pi hδ πs fun π' hπ' => h π' (List.mem_cons_of_mem _ hπ'))

/-- `π₁ ∧ π₂` true implies `andPi π₁ π₂` true, by soundness. -/
theorem trueN_andPi {π₁ π₂ : A.Sent} (h₁ : A.TrueN π₁) (h₂ : A.TrueN π₂) :
    A.TrueN (A.andPi π₁ π₂) := by
  refine A.sound (fun β => β = A.and π₁ π₂) _ (fun β hβ => ?_) (A.andPi_deriv₁ π₁ π₂)
  rw [hβ, A.trueN_and]; exact ⟨h₁, h₂⟩

theorem conjPi_true {δ : A.Sent} (hδ : A.TrueN δ) :
    ∀ πs : List A.Sent, (∀ π, π ∈ πs → A.TrueN π) → A.TrueN (conjPi A δ πs)
  | [], _ => hδ
  | π :: πs, h => trueN_andPi (h π (List.mem_cons_self ..))
      (conjPi_true hδ πs fun π' hπ' => h π' (List.mem_cons_of_mem _ hπ'))

/-- Each member of the list follows from the conjunction. -/
theorem conjPi_deriv_mem {δ : A.Sent} :
    ∀ (πs : List A.Sent) (π : A.Sent), π ∈ πs → A.Deriv (fun β => β = conjPi A δ πs) π
  | [], π, h => absurd h (List.not_mem_nil)
  | π' :: πs, π, h => by
    have hand : A.Deriv (fun β => β = conjPi A δ (π' :: πs)) (A.and π' (conjPi A δ πs)) :=
      A.andPi_deriv₂ _ _
    rcases List.mem_cons.1 h with rfl | h
    · exact A.deriv_and_left hand
    · exact A.deriv_cut (fun β hβ => by rw [hβ]; exact A.deriv_and_right hand)
        (conjPi_deriv_mem πs π h)

/-- The extension `F ∪ i (Tr_{Πₙ})` of a theory by the true `Π⁰ₙ` sentences. -/
def specExtN (n : ℕ) (F : L.Sent → Prop) : L.Sent → Prop :=
  fun x => F x ∨ ∃ π, A.TrPi n π ∧ x = i.i π

/-- The speculative extension `F ∪ i (Tr_{Π₁})` of a theory. -/
def specExt (F : L.Sent → Prop) : L.Sent → Prop := specExtN i 1 F

/-- Lemma 3.26 (`lemma_Sconsistent`), at level `n`: if `F ∪ i (Tr_{Πₙ})` is inconsistent then
`F ⊢ⁱ ¬π` for some `π ∈ Tr_{Πₙ}` (the paper's Lemma 6.6 (3) uses the case of general `n`). -/
theorem exists_trPiN_derivI_neg_of_not_consistent {n : ℕ} {F : L.Sent → Prop}
    (h : ¬ L.Consistent (specExtN i n F)) : ∃ π, A.TrPi n π ∧ i.DerivI F (A.neg π) := by
  obtain ⟨δ, hδ0, hδt⟩ := A.exists_true_delta0
  have hδ1 : A.IsPi n δ := A.pi_of_delta0 hδ0 n
  have hall := (L.not_consistent_iff _).1 h
  -- two finite derivations of `i δ` and `¬ i δ` from the speculative extension
  obtain ⟨l₁, hl₁, hd₁⟩ := L.deriv_compact (hall (i.i δ))
  obtain ⟨l₂, hl₂, hd₂⟩ := L.deriv_compact (hall (L.neg (i.i δ)))
  let l := l₁ ++ l₂
  have hl : ∀ x, x ∈ l → specExtN i n F x := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact hl₁ x hx
    · exact hl₂ x hx
  -- the `Π⁰₁` sentences used, and their conjunction `cp`
  let πs : List A.Sent := l.filterMap fun x =>
    if h : ∃ π, A.TrPi n π ∧ x = i.i π then some (choose h) else none
  have hπs : ∀ π, π ∈ πs → A.TrPi n π := by
    intro π hπ
    obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hπ
    split at hx
    · rename_i hex
      cases hx
      exact (choose_spec hex).1
    · cases hx
  let cp := conjPi A δ πs
  have hcp_pi : A.IsPi n cp := conjPi_pi hδ1 πs fun π hπ => (hπs π hπ).1
  have hcp_true : A.TrueN cp := conjPi_true hδt πs fun π hπ => (hπs π hπ).2
  -- every member of `l` follows from `F ∪ {i cp}`
  have hmem : ∀ x, x ∈ l → L.Deriv (fun β => F β ∨ β = i.i cp) x := by
    intro x hx
    rcases hl x hx with hF | hex
    · exact L.deriv_of_mem (Or.inl hF)
    · have hx' : x = i.i (choose hex) := (choose_spec hex).2
      have hin : choose hex ∈ πs := by
        refine List.mem_filterMap.2 ⟨x, hx, ?_⟩
        rw [dite_eq_left hex]
      have h1 : A.Deriv (fun β => β = cp) (choose hex) := conjPi_deriv_mem πs _ hin
      have h2 := i.map_deriv _ _ h1
      rw [hx']
      refine L.deriv_cut (fun β hβ => ?_) h2
      obtain ⟨γ, rfl, rfl⟩ := hβ
      exact L.deriv_of_mem (Or.inr rfl)
  have hd₁' : L.Deriv (fun β => F β ∨ β = i.i cp) (i.i δ) :=
    L.deriv_cut (fun β hβ => hmem β (List.mem_append_left _ hβ)) hd₁
  have hd₂' : L.Deriv (fun β => F β ∨ β = i.i cp) (L.neg (i.i δ)) :=
    L.deriv_cut (fun β hβ => hmem β (List.mem_append_right _ hβ)) hd₂
  have hneg : L.Deriv F (L.neg (i.i cp)) :=
    L.deriv_neg_intro fun γ => L.deriv_explosion hd₁' hd₂'
  refine ⟨cp, ⟨hcp_pi, hcp_true⟩, ?_⟩
  rw [i.derivI_iff, i.map_neg]
  exact hneg

/-- Lemma 3.26 (`lemma_Sconsistent`). -/
theorem exists_trPi_derivI_neg_of_not_consistent {F : L.Sent → Prop}
    (h : ¬ L.Consistent (specExt i F)) : ∃ π, A.TrPi 1 π ∧ i.DerivI F (A.neg π) :=
  exists_trPiN_derivI_neg_of_not_consistent i h

/-- Part 4 of Theorem 3.25: a `1`-consistent theory has a consistent speculative extension. -/
theorem consistent_specExt {F : L.Sent → Prop} (h1 : i.OneConsistent F) :
    L.Consistent (specExt i F) := by
  refine Classical.byContradiction fun hc => ?_
  obtain ⟨π, ⟨hπ, hπt⟩, hneg⟩ := exists_trPi_derivI_neg_of_not_consistent i hc
  -- `F ⊢ⁱ ∃x̄ ¬φ`
  have hsig : i.DerivI F (A.negPi π) :=
    i.derivI_cut (fun β hβ => by rw [hβ]; exact hneg) (A.negPi_deriv 0 π hπ)
  obtain ⟨v, hv⟩ := h1.2 _ (A.negPi_sigma 0 π hπ) hsig
  rw [A.negPi_inst 0 π v hπ] at hv
  -- but `φ(n̄)` is a true `Δ₀` sentence, provable in `Q`, hence in `F` under `i`
  have htrue : A.TrueN (A.instP π v) := (A.trueN_pi 0 π hπ).1 hπt v
  have hQ : A.Deriv A.Q (A.instP π v) := A.Q_delta0 _ (A.instP_sigma 0 π v hπ) htrue
  have hF : i.DerivI F (A.instP π v) := i.derivI_cut (fun q hq => h1.1 q hq) hQ
  exact hv (A.deriv_dni hF)

/-- Theorem 3.25 (`theorem_speculative`). -/
theorem exists_Spec (hi : i.IsNTranslation 2) : ∃ Spec : M.Code → M.Code, CompT M Spec ∧ ∀ T,
    InTB (M := M) L.Sent (Spec T) ∧ (∀ n, seqOf (M := M) L.Sent (Spec T) n ≠ none) ∧
    i.Speculative (seqOf (M := M) L.Sent (Spec T)) ∧
    (∀ x, Ts (M := M) L.Sent (Spec T) x ↔ specExt i (Ts (M := M) L.Sent T) x) ∧
    (i.OneConsistent (Ts (M := M) L.Sent T) → L.Consistent (Ts (M := M) L.Sent (Spec T))) := by
  obtain ⟨Spec, hSpec, hSpec'⟩ :=
    exists_stabMachine (M := M) (B := L.Sent) L.infinite (compSet_RS i hi)
  refine ⟨Spec, hSpec, fun T => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hSpec' T
  have hset : ∀ x, Ts (M := M) L.Sent (Spec T) x ↔ specExt i (Ts (M := M) L.Sent T) x := by
    intro x; rw [Ts_def, h3, SR_RS_iff]; rfl
  refine ⟨h1, h2, ?_, hset, ?_⟩
  · intro π hπ
    rw [i.derivI_iff]
    exact L.deriv_of_mem ((hset (i.i π)).2 (Or.inr ⟨π, hπ, rfl⟩))
  · intro hcons
    obtain ⟨α, hα⟩ := consistent_specExt i hcons
    refine ⟨α, fun hd => hα ?_⟩
    exact L.deriv_mono (fun β hβ => (hset β).1 hβ) hd

end Stable
