import Stable.Arith

/-!
# The relation `R_S` of the speculative closure (proof of Theorem 3.25, `theorem_speculative`)

Let `i : 𝓐 → 𝓛` be a `2`-translation.  `(T, x, u, v) ∈ R_S`, with `u = ⟨c, w⟩`, iff either
* `c = 0` and `(T, x, w, v) ∈ R_𝓛` (the relation `R_B` of Definition 3.14 for `B = 𝓛`), or
* `c = 1`, `w = e_𝓐 (π)` for a `Π⁰₁` sentence `π = ∀x̄ φ`, `x = i (π)`, and `ℕ ⊨ φ(β_r (v))`
  (here `φ(β_r (v)) = instP π v`).

`R_S` is computable: `R_𝓛` is, the set of codes of `Π⁰₁` sentences is, `i` is computable on
`Π⁰₁` sentences (as `i` is a `2`-translation and `Π⁰₁ ⊂ Σ⁰₂`), and the truth of a `Δ₀` sentence
is decidable.  Moreover `S_{R_S} (T) = T^s ∪ i (Tr_{Π₁})`.
-/

namespace Stable

open Classical

variable {M : TuringModel} {A : Arith M} {L : Language M} (i : Translation A.toLanguage L)

/-- The relation `R_S ⊂ 𝒯 × 𝓛 × ℕ × ℕ`. -/
def RS (T : M.Code) (x : L.Sent) (u v : ℕ) : Prop :=
  ((M.unpair u).1 = 0 ∧ RB (M := M) L.Sent T x (M.unpair u).2 v) ∨
    ((M.unpair u).1 = 1 ∧ ∃ π : A.Sent, e M π = (M.unpair u).2 ∧ A.IsPi 1 π ∧ x = i.i π ∧
      A.TrueN (A.instP π v))

/-- `R_S` is computable when `i` is a `2`-translation. -/
theorem compSet_RS (hi : i.IsNTranslation 2) :
    CompSet M (fun q : M.Code × L.Sent × ℕ × ℕ => RS i q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  -- the coordinates `c = (unpair u).1` and `w = (unpair u).2` of `u = q.2.2.1`
  have hu : CompT M (fun q : M.Code × L.Sent × ℕ × ℕ => q.2.2.1) :=
    compT_fst.comp (compT_snd.comp compT_snd)
  have hc : CompT M (fun q : M.Code × L.Sent × ℕ × ℕ => (M.unpair q.2.2.1).1) :=
    compT_unpair_fst.comp hu
  have hw : CompT M (fun q : M.Code × L.Sent × ℕ × ℕ => (M.unpair q.2.2.1).2) :=
    compT_unpair_snd.comp hu
  -- first disjunct: `c = 0` and `(T, x, w, v) ∈ R_𝓛`
  have h0 : CompSet M (fun q : M.Code × L.Sent × ℕ × ℕ => (M.unpair q.2.2.1).1 = 0) :=
    compSet_eq hc (compT_const 0)
  have hRB : CompSet M (fun q : M.Code × L.Sent × ℕ × ℕ =>
      RB (M := M) L.Sent q.1 q.2.1 (M.unpair q.2.2.1).2 q.2.2.2) :=
    (compSet_RB (B := L.Sent)).comp (CompT.pair compT_fst (CompT.pair (compT_fst.comp compT_snd)
      (CompT.pair hw (compT_snd.comp (compT_snd.comp compT_snd)))))
  -- second disjunct: `c = 1` and the decoded `π = e⁻¹ (w)` qualifies
  have h1 : CompSet M (fun q : M.Code × L.Sent × ℕ × ℕ => (M.unpair q.2.2.1).1 = 1) :=
    compSet_eq hc (compT_const 1)
  -- `π ↦ i π` on `Π⁰₁` sentences, as a total `Option`-valued computable map
  have hg : CompT M (fun π : A.Sent => if A.IsPi 1 π then some (i.i π) else none) := by
    refine CompT.ofComp (Comp.ofRestrict (A.pi_comp 1) (f := i.i)
      (i.compT_on_pi_of_two (A.pi_comp 1) (A.pi_sigma_succ 1) hi)) ?_
    exact (A.pi_comp 1).congr fun π => by by_cases h : A.IsPi 1 π <;> simp [h]
  -- the condition on `((x, v), π)`
  have hΦ : CompSet M (fun p : (L.Sent × ℕ) × A.Sent =>
      A.IsPi 1 p.2 ∧ p.1.1 = i.i p.2 ∧ A.TrueN (A.instP p.2 p.1.2)) := by
    have hEq : CompSet M (fun p : (L.Sent × ℕ) × A.Sent =>
        some p.1.1 = if A.IsPi 1 p.2 then some (i.i p.2) else none) :=
      compSet_eq (compT_some.comp (compT_fst.comp compT_fst)) (hg.comp compT_snd)
    have hTr : CompSet M (fun p : (L.Sent × ℕ) × A.Sent =>
        A.IsSigma 0 (A.instP p.2 p.1.2) ∧ A.TrueN (A.instP p.2 p.1.2)) :=
      A.delta0_dec.comp (A.instP_comp.comp (CompT.pair compT_snd (compT_snd.comp compT_fst)))
    refine (hEq.and hTr).congr fun p => ?_
    by_cases h : A.IsPi 1 p.2
    · rw [ite_eq_left h]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h, Option.some.inj h1, h3⟩
      · rintro ⟨_, h1, h3⟩; exact ⟨congrArg some h1, A.instP_sigma 0 _ _ h, h3⟩
    · rw [ite_eq_right h]
      constructor
      · rintro ⟨h1, _⟩; exact absurd h1 (Option.some_ne_none _)
      · rintro ⟨h1, _⟩; exact absurd h1 h
  have hEx : CompSet M (fun q : M.Code × L.Sent × ℕ × ℕ =>
      ∃ π : A.Sent, e M π = (M.unpair q.2.2.1).2 ∧ A.IsPi 1 π ∧ q.2.1 = i.i π ∧
        A.TrueN (A.instP π q.2.2.2)) :=
    (CompSet.exists_decode (Φ := fun (a : L.Sent × ℕ) (π : A.Sent) =>
      A.IsPi 1 π ∧ a.1 = i.i π ∧ A.TrueN (A.instP π a.2)) hΦ).comp
      (CompT.pair (CompT.pair (compT_fst.comp compT_snd)
        (compT_snd.comp (compT_snd.comp compT_snd))) hw)
  exact ((h0.and hRB).or (h1.and hEx)).congr fun q => Iff.rfl

/-- `S_{R_S} (T) = T^s ∪ i (Tr_{Π₁})`. -/
theorem SR_RS_iff (T : M.Code) (x : L.Sent) :
    SR (RS i) T x ↔ Ts (M := M) L.Sent T x ∨ ∃ π : A.Sent, A.TrPi 1 π ∧ x = i.i π := by
  rw [Ts_def, tStable_iff_SR_RB]
  unfold SR RS
  constructor
  · rintro ⟨u, hu⟩
    by_cases hc0 : (M.unpair u).1 = 0
    · -- `c = 0`: the first disjunct holds for every `v`
      left
      refine ⟨(M.unpair u).2, fun v => ?_⟩
      rcases hu v with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [hc0] at h; cases h
    · by_cases hc1 : (M.unpair u).1 = 1
      · -- `c = 1`: the second disjunct holds for every `v`, with the same `π = e⁻¹ (w)`
        right
        obtain ⟨π, hπe, hπ, hx, _⟩ : ∃ π : A.Sent, e M π = (M.unpair u).2 ∧ A.IsPi 1 π ∧
            x = i.i π ∧ A.TrueN (A.instP π 0) := by
          rcases hu 0 with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd h hc0
          · exact h
        refine ⟨π, ⟨hπ, (A.trueN_pi 0 π hπ).2 fun v => ?_⟩, hx⟩
        rcases hu v with ⟨h, _⟩ | ⟨_, π', hπ'e, _, _, ht⟩
        · exact absurd h hc0
        · rw [← Enc.inj (hπ'e.trans hπe.symm)]; exact ht
      · -- `c ≥ 2`: `R_S (T, x, u, v)` fails
        exfalso
        rcases hu 0 with ⟨h, _⟩ | ⟨h, _⟩
        · exact hc0 h
        · exact hc1 h
  · rintro (⟨w, hw⟩ | ⟨π, ⟨hπ, ht⟩, hx⟩)
    · refine ⟨M.pair 0 w, fun v => Or.inl ?_⟩
      rw [M.unpair_pair]
      exact ⟨rfl, hw v⟩
    · refine ⟨M.pair 1 (e M π), fun v => Or.inr ?_⟩
      rw [M.unpair_pair]
      exact ⟨rfl, π, rfl, hπ, hx, (A.trueN_pi 0 π hπ).1 ht v⟩

end Stable
