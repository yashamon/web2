import Stable.NMachines

/-!
# `n`-stably c.e. sets are the `Σ⁰_{n+1}` sets (Corollary 6.3, `corollary_sigman`)

For an infinite encoded set `B`, `S ⊂ B` and `n = m+1`, the following are equivalent:
1. `S` is `(m+1)`-stably c.e. (`S = M^{s_{m+1}}` for a computable `M : ℕ^{m+1} → B × {±}`);
2. `S = D^{d_{m+1}}` for a total computable `(m+1)`-decision map `D` on `B`;
3. `S` is `Σ⁰_{m+2}`: `S = {b | ∃ u₁ ∀ u₂ ⋯ u_{m+2}, R (b, u₁, …, u_{m+2})}` for a computable `R`.
-/

namespace Stable

open Classical

variable {M : TuringModel} {B : Type} [Enc M B]

/-- `S` is `(m+1)`-stably c.e. -/
def NStablyCE (m : ℕ) (S : B → Prop) : Prop :=
  ∃ Mp : NB ℕ m → Option (B × Bool), Comp M Mp ∧ ∀ b, S b ↔ NStable m Mp b

/-- `S = D^{d_{m+1}}` for a total computable `(m+1)`-decision map `D`. -/
def NDecidedByTotal (m : ℕ) (S : B → Prop) : Prop :=
  ∃ D : NB B m → ℕ → Bool, CompT M (fun p : NB B m × ℕ => D p.1 p.2) ∧
    ∀ b, S b ↔ NDec m (fun x w => some (D x w)) b

/-- `S` is a `Σ⁰_{m+2}` subset of `B`. -/
def IsSigmaNSet (m : ℕ) (S : B → Prop) : Prop :=
  ∃ R : NRel Unit B m, NRelComp (M := M) m R ∧ ∀ b, S b ↔ NSR m R () b

/-- (1) ⇒ (3). -/
theorem IsSigmaNSet.of_nStablyCE {m : ℕ} {S : B → Prop} (h : NStablyCE (M := M) m S) :
    IsSigmaNSet (M := M) m S := by
  obtain ⟨Mp, ⟨T, hT⟩, hS⟩ := h
  obtain ⟨_, hseq⟩ := nseqOf_of_computes (M := M) (m := m) (B := B) hT
  refine ⟨fun _ x u v => complPow m (RBase (M := M) m B) T x u v,
    ((nRelComp_RBase (M := M) (B := B) m).complPow m).comp
      (CompT.pair (compT_const T) compT_snd), fun b => ?_⟩
  rw [hS b, ← NStable.of_eq m hseq b]
  have := NTs_iff_NSR (M := M) m T b
  unfold NTs at this
  rw [this]
  refine (NSR_congr_at m T (R' := fun _ x u v => complPow m (RBase (M := M) m B) T x u v)
    (fun _ _ _ => Iff.rfl) b).trans ?_
  exact NSR_param_const m (fun _ x u v => complPow m (RBase (M := M) m B) T x u v) T b

/-- (3) ⇒ (2), by the `n`-stabilizer lemma with a one-point parameter set. -/
theorem NDecidedByTotal.of_isSigmaNSet {m : ℕ} {S : B → Prop} (h : IsSigmaNSet (M := M) m S) :
    NDecidedByTotal (M := M) m S := by
  obtain ⟨R, hR, hS⟩ := h
  obtain ⟨D, hD, hD'⟩ := n_stabilizer (M := M) m R hR
  refine ⟨D (), hD.comp (CompT.pair (compT_const ()) compT_id), fun b => ?_⟩
  rw [hS b, hD' () b]

/-- (2) ⇒ (1), for infinite `B`: `S = M_D^{s_{m+1}}` with `M_D` total and computable. -/
theorem NStablyCE.of_nDecidedByTotal (hB : Enc.Infinite M B) {m : ℕ} {S : B → Prop}
    (h : NDecidedByTotal (M := M) m S) :
    ∃ Mp : NB ℕ m → Option (B × Bool), Comp M Mp ∧ (∀ y, Mp y ≠ none) ∧ ∀ b, S b ↔ NStable m Mp b := by
  obtain ⟨D, hD, hS⟩ := h
  refine ⟨MD (M := M) m (fun x w => some (D x w)), comp_MD m hD, ?_, fun b => ?_⟩
  · exact MD_total m hB (fun _ _ => Option.some_ne_none _)
  · rw [hS b, NStable_MD_iff]

/-- Corollary 6.3. -/
theorem nStablyCE_iff_isSigmaNSet (hB : Enc.Infinite M B) (m : ℕ) (S : B → Prop) :
    NStablyCE (M := M) m S ↔ IsSigmaNSet (M := M) m S :=
  ⟨IsSigmaNSet.of_nStablyCE, fun h => by
    obtain ⟨Mp, h1, _, h3⟩ := NStablyCE.of_nDecidedByTotal hB (NDecidedByTotal.of_isSigmaNSet h)
    exact ⟨Mp, h1, h3⟩⟩

theorem nStablyCE_iff_nDecidedByTotal (hB : Enc.Infinite M B) (m : ℕ) (S : B → Prop) :
    NStablyCE (M := M) m S ↔ NDecidedByTotal (M := M) m S :=
  ⟨fun h => NDecidedByTotal.of_isSigmaNSet (IsSigmaNSet.of_nStablyCE h), fun h => by
    obtain ⟨Mp, h1, _, h3⟩ := NStablyCE.of_nDecidedByTotal hB h
    exact ⟨Mp, h1, h3⟩⟩

end Stable
