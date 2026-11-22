import Stable.Machines

/-!
# Stably c.e. sets are the `Σ⁰₂` sets (Corollary 3.7, `corollary_sigma2`)

For an infinite encoded set `B` and `S ⊂ B` the following are equivalent:
1. `S` is stably c.e. (`S = M^s` for a computable `M : ℕ → B × {±}`);
2. `S = D^d` for a total computable decision map `D` on `B`;
3. `e_B (S) ⊂ ℕ` is `Σ⁰₂`, i.e. `e_B (S) = {x | ∃ u ∀ v, R₀ (x, u, v)}` for a computable
   `R₀ ⊂ ℕ³`.
In particular the stabilization of a computable map is also the stabilization of a total
computable map.
-/

namespace Stable

open Classical

variable {M : TuringModel} {B : Type} [Enc M B]

/-- `S` is stably c.e. (Definition 1.4 / 3.1). -/
def StablyCE (S : B → Prop) : Prop :=
  ∃ Mp : ℕ → Option (B × Bool), Comp M Mp ∧ ∀ b, S b ↔ IsStable Mp b

/-- `S = D^d` for a total computable decision map `D`. -/
def DecidedByTotal (S : B → Prop) : Prop :=
  ∃ D : B → ℕ → Bool, CompT M (fun p : B × ℕ => D p.1 p.2) ∧
    ∀ b, S b ↔ IsDecided (fun b n => some (D b n)) b

/-- `e_B (S)` is a `Σ⁰₂` subset of `ℕ`. -/
def IsSigma2Set (S : B → Prop) : Prop :=
  ∃ R₀ : ℕ → ℕ → ℕ → Prop, CompSet M (fun q : ℕ × ℕ × ℕ => R₀ q.1 q.2.1 q.2.2) ∧
    ∀ x, (∃ b, e M b = x ∧ S b) ↔ ∃ u, ∀ v, R₀ x u v

/-- (1) ⇒ (3). -/
theorem IsSigma2Set.of_stablyCE {S : B → Prop} (h : StablyCE (M := M) S) : IsSigma2Set (M := M) S := by
  obtain ⟨Mp, ⟨T, hT⟩, hS⟩ := h
  have hseq := inTB_of_computes (M := M) (B := B) hT
  -- `S = T^s`, which is `∃ u ∀ v, R_B (T, b, u, v)`
  have hS' : ∀ b, S b ↔ SR (RB (M := M) B) T b := fun b => by
    rw [hS b, ← tStable_iff_SR_RB]
    exact ⟨IsStable.of_eq fun n => (hseq.2 n).symm, IsStable.of_eq hseq.2⟩
  refine ⟨fun x u v => ∃ b, e M b = x ∧ RB (M := M) B T b u v, ?_, fun x => ?_⟩
  · have h0 : CompSet M (fun p : (ℕ × ℕ) × B => RB (M := M) B T p.2 p.1.1 p.1.2) :=
      (compSet_RB (B := B)).comp (CompT.pair (compT_const T)
        (CompT.pair compT_snd (CompT.pair (compT_fst.comp compT_fst) (compT_snd.comp compT_fst))))
    have h1 := CompSet.exists_decode (M := M) (X := B)
      (Φ := fun (p : ℕ × ℕ) b => RB (M := M) B T b p.1 p.2) h0
    exact (h1.comp (CompT.pair (CompT.pair (compT_fst.comp compT_snd) (compT_snd.comp compT_snd))
      compT_fst)).congr fun q => Iff.rfl
  · constructor
    · rintro ⟨b, rfl, hb⟩
      obtain ⟨u, hu⟩ := (hS' b).1 hb
      exact ⟨u, fun v => ⟨b, rfl, hu v⟩⟩
    · rintro ⟨u, hu⟩
      obtain ⟨b, rfl, _⟩ := hu 0
      refine ⟨b, rfl, (hS' b).2 ⟨u, fun v => ?_⟩⟩
      obtain ⟨b', hb', h⟩ := hu v
      rw [Enc.inj hb'] at h; exact h

/-- (3) ⇒ (2), by the stabilizer lemma with a one-point parameter set. -/
theorem DecidedByTotal.of_isSigma2Set {S : B → Prop} (h : IsSigma2Set (M := M) S) :
    DecidedByTotal (M := M) S := by
  obtain ⟨R₀, hR₀, hS⟩ := h
  let R : ℕ → B → ℕ → ℕ → Prop := fun _ b u v => R₀ (e M b) u v
  have hR : CompSet M (fun q : ℕ × B × ℕ × ℕ => R q.1 q.2.1 q.2.2.1 q.2.2.2) :=
    hR₀.comp (CompT.pair (compT_e.comp (compT_fst.comp compT_snd))
      (CompT.pair (compT_fst.comp (compT_snd.comp compT_snd)) (compT_snd.comp (compT_snd.comp compT_snd))))
  refine ⟨fun b t => DR R 0 b t, ?_, fun b => ?_⟩
  · exact (compT_DR hR).comp (CompT.pair (compT_const 0) compT_id)
  · rw [isDecided_DR_iff]
    constructor
    · intro hb; exact (hS (e M b)).1 ⟨b, rfl, hb⟩
    · intro hb
      obtain ⟨b', hb', hS'⟩ := (hS (e M b)).2 hb
      rw [Enc.inj hb'] at hS'; exact hS'

/-- (2) ⇒ (1), for infinite `B`: `S = M_D^s` with `M_D` total and computable. -/
theorem StablyCE.of_decidedByTotal (hB : Enc.Infinite M B) {S : B → Prop}
    (h : DecidedByTotal (M := M) S) :
    ∃ Mp : ℕ → Option (B × Bool), Comp M Mp ∧ (∀ n, Mp n ≠ none) ∧ ∀ b, S b ↔ IsStable Mp b := by
  obtain ⟨D, hD, hS⟩ := h
  refine ⟨seqOfDec (M := M) (fun b n => some (D b n)), comp_seqOfDec hD, ?_, fun b => ?_⟩
  · exact seqOfDec_total hB (fun _ _ => Option.some_ne_none _)
  · rw [hS b, isStable_seqOfDec_iff]

/-- Corollary 3.7: for infinite `B`, (1) ⇔ (2) ⇔ (3). -/
theorem stablyCE_iff_decidedByTotal (hB : Enc.Infinite M B) (S : B → Prop) :
    StablyCE (M := M) S ↔ DecidedByTotal (M := M) S :=
  ⟨fun h => DecidedByTotal.of_isSigma2Set (IsSigma2Set.of_stablyCE h), fun h => by
    obtain ⟨Mp, h1, _, h3⟩ := StablyCE.of_decidedByTotal hB h
    exact ⟨Mp, h1, h3⟩⟩

theorem stablyCE_iff_isSigma2Set (hB : Enc.Infinite M B) (S : B → Prop) :
    StablyCE (M := M) S ↔ IsSigma2Set (M := M) S :=
  ⟨IsSigma2Set.of_stablyCE, fun h => (stablyCE_iff_decidedByTotal hB S).2 (DecidedByTotal.of_isSigma2Set h)⟩

/-- The stabilization of a computable map is the stabilization of a total computable map. -/
theorem exists_total_of_stablyCE (hB : Enc.Infinite M B) {S : B → Prop} (h : StablyCE (M := M) S) :
    ∃ Mp : ℕ → Option (B × Bool), Comp M Mp ∧ (∀ n, Mp n ≠ none) ∧ ∀ b, S b ↔ IsStable Mp b :=
  StablyCE.of_decidedByTotal hB ((stablyCE_iff_decidedByTotal hB S).1 h)

end Stable
