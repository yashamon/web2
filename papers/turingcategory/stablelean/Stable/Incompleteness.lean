import Stable.Halting
import Stable.Closure

/-!
# The incompleteness theorems (Section 5)

Fix a `2`-translation `i : 𝓐 → 𝓛`.  With `Dec = Dec_𝓛` (Definition 3.14), `C` (Lemma 3.22),
`Spec = Spec_i` (Theorem 3.25) and `s` (Definition 4.3), define
`H (P, T, n) := (Dec (C (Spec P)))' (i (s T), n)`, the s-m-n machine `Tur` with `Tur P` computing
`D^P (T, n) = H (P, T, n)`, and the Gödel sentence `𝒢 (T) := s (Tur T)`.  In the manuscript the map
`H` of (5.1) is now called `Λ`; there `H` is the theory of Theorem 5.11.

Proposition 5.5 (`proposition_syntactic`), for `F = T^s` and any `T`:
1. if `F` is `1`-consistent (relative to `i`) then `F ⊬ⁱ 𝒢 (T)`;
2. if `F` is `2`-consistent then `F ⊬ⁱ ¬𝒢 (T)`;
3. if `F` is `1`-consistent then `ℕ ⊨ 𝒢 (T)`.

Theorem 1.5 (`theorem_firstincompleteness`) follows: `𝒢` is total computable, and the three
statements hold for `F = N^s` whenever `T` stably computes `N`.

In the restructured manuscript (11 November 2026) the theorems are stated for theories of
arithmetic, the case `𝓛 = 𝓐`, `i = id` of this file: see `Stable.Plain` (level `n`: `Stable.NPlain`).
The statements for a translation `i`, as here, are Example 5.23 and its level-`n` form, with the
notation of Appendix B; they are also recovered from readings in `Stable.ReadingsTranslations`.
-/

namespace Stable

open Classical

variable {M : TuringModel} {A : Arith M} {L : Language M}

/-! ### The machines `Dec_𝓛`, `C`, `Spec_i`, `Tur` -/

/-- `Dec_𝓛` of Definition 3.14. -/
noncomputable def DecL (L : Language M) : M.Code → M.Code := choose (exists_Dec (M := M) (B := L.Sent))

theorem DecL_spec (L : Language M) (T : M.Code) (γ : L.Sent) :
    TStable (M := M) T γ ↔ TDecided (M := M) (DecL L T) γ :=
  ((choose_spec (exists_Dec (M := M) (B := L.Sent))).2 T).2.2 γ

/-- `C` of Lemma 3.22. -/
noncomputable def CL (L : Language M) : M.Code → M.Code := choose (exists_C L)

theorem CL_spec (L : Language M) (T : M.Code) (γ : L.Sent) :
    Ts (M := M) L.Sent (CL L T) γ ↔ L.Deriv (Ts (M := M) L.Sent T) γ :=
  ((choose_spec (exists_C L)).2 T).2.2 γ

variable (i : Translation A.toLanguage L) (hi : i.IsNTranslation 2)
include hi

/-- `Spec_i` of Theorem 3.25. -/
noncomputable def SpecI : M.Code → M.Code := choose (exists_Spec i hi)

theorem SpecI_speculative (T : M.Code) : i.Speculative (seqOf (M := M) L.Sent (SpecI i hi T)) :=
  ((choose_spec (exists_Spec i hi)).2 T).2.2.1

theorem SpecI_Ts (T : M.Code) (x : L.Sent) :
    Ts (M := M) L.Sent (SpecI i hi T) x ↔ specExt i (Ts (M := M) L.Sent T) x :=
  ((choose_spec (exists_Spec i hi)).2 T).2.2.2.1 x

theorem SpecI_consistent (T : M.Code) (h : i.OneConsistent (Ts (M := M) L.Sent T)) :
    L.Consistent (Ts (M := M) L.Sent (SpecI i hi T)) :=
  ((choose_spec (exists_Spec i hi)).2 T).2.2.2.2 h

/-- `i ∘ s : 𝒯 → 𝓛` is computable, as `s (T)` is the negation of a `Σ⁰₂` sentence and `i` is a
`2`-translation. -/
theorem compT_i_sT : CompT M (fun T => i.i (A.sT T)) := by
  have h1 : Comp M (fun α : A.Sent => if A.IsSigma 2 α then some (i.i α) else none) :=
    Comp.ofRestrict (A.sigma_comp 2) (f := i.i) hi
  have h2 : CompT M (fun T => i.i (A.sigmaT T)) := by
    have := h1.compT A.sigmaT_compT
    exact this.congr fun T => by rw [ite_eq_left (A.sigmaT_sigma2 T)]
  have h3 : CompT M (fun T => L.neg (i.i (A.sigmaT T))) := L.neg_comp.comp h2
  exact h3.congr fun T => by unfold Arith.sT; rw [i.map_neg]

/-- The map of (5.1), `H : 𝒯 × 𝒯 × ℕ → {±}`, `H (P, T, n) = (Dec_𝓛 (C (Spec_i P)))' (i (s T), n)`.
It is `Λ` in the manuscript. -/
noncomputable def H (P T : M.Code) (n : ℕ) : Option Bool :=
  decOf (M := M) L.Sent (DecL L (CL L (SpecI i hi P))) (i.i (A.sT T)) n

/-- `H` is computable (the composition (5.1) of the paper). -/
theorem comp_H : Comp M (fun q : M.Code × (M.Code × ℕ) => H i hi q.1 q.2.1 q.2.2) := by
  have hDec : CompT M (DecL L) := (choose_spec (exists_Dec (M := M) (B := L.Sent))).1
  have hC : CompT M (CL L) := (choose_spec (exists_C L)).1
  have hS : CompT M (SpecI i hi) := (choose_spec (exists_Spec i hi)).1
  have h1 : CompT M (fun q : M.Code × (M.Code × ℕ) => DecL L (CL L (SpecI i hi q.1))) :=
    hDec.comp (hC.comp (hS.comp compT_fst))
  have h2 : CompT M (fun q : M.Code × (M.Code × ℕ) => i.i (A.sT q.2.1)) :=
    (compT_i_sT i hi).comp (compT_fst.comp compT_snd)
  have := (comp_VD (M := M) (B := L.Sent)).compT (CompT.pair h1 (CompT.pair h2 (compT_snd.comp compT_snd)))
  exact this.congr fun q => rfl

/-- The s-m-n machine `Tur : 𝒯 → 𝒯` (5.2): `Tur P` computes `D^P (T, n) = H (P, T, n)`. -/
noncomputable def Tur : M.Code → M.Code := choose (smn (comp_H i hi))

theorem Tur_compT : CompT M (Tur i hi) := (choose_spec (smn (comp_H i hi))).1

theorem Tur_computes (P : M.Code) :
    Computes M (Tur i hi P) (fun q : M.Code × ℕ => H i hi P q.1 q.2) :=
  (choose_spec (smn (comp_H i hi))).2 P

theorem decOf_Tur (P T : M.Code) (n : ℕ) :
    decOf (M := M) M.Code (Tur i hi P) T n = H i hi P T n :=
  (inDB_of_computes (D := fun T n => H i hi P T n) (Tur_computes i hi P)).2 T n

/-- The Gödel sentence `𝒢 (T) := s (Tur T)` (5.4). -/
noncomputable def G (T : M.Code) : A.Sent := A.sT (Tur i hi T)

theorem G_compT : CompT M (G i hi) := A.sT_compT.comp (Tur_compT i hi)

/-- `𝒢 (T) = ¬ σ (Tur T)`, so `ℕ ⊨ ¬𝒢 (T)` iff `ℕ ⊨ σ (Tur T)`. -/
theorem not_trueN_G_iff (T : M.Code) : ¬ A.TrueN (G i hi T) ↔ A.TrueN (A.sigmaT (Tur i hi T)) := by
  unfold G Arith.sT
  rw [A.trueN_neg, Classical.not_not]

/-! ### Proposition 5.5 -/

section Syntactic

variable (T : M.Code)

/-- `M̃ := (C (Spec_i T))'`. -/
noncomputable def Mt : ℕ → Option (L.Sent × Bool) := seqOf (M := M) L.Sent (CL L (SpecI i hi T))

/-- `M̃^s` is the deductive closure of `T^s ∪ i (Tr_{Π₁})`. -/
theorem stab_Mt_iff (x : L.Sent) :
    Stab (Mt i hi T) x ↔ L.Deriv (specExt i (Ts (M := M) L.Sent T)) x := by
  show Ts (M := M) L.Sent (CL L (SpecI i hi T)) x ↔ _
  rw [CL_spec]
  constructor
  · exact L.deriv_mono fun β hβ => (SpecI_Ts i hi T β).1 hβ
  · exact L.deriv_mono fun β hβ => (SpecI_Ts i hi T β).2 hβ

/-- `M̃` is speculative. -/
theorem Mt_speculative : i.Speculative (Mt i hi T) := by
  intro π hπ
  rw [i.derivI_iff]
  exact L.deriv_of_mem ((stab_Mt_iff i hi T _).2 (L.deriv_of_mem (Or.inr ⟨π, hπ, rfl⟩)))

/-- `M̃^s ⊇ closure (T^s)`. -/
theorem derivI_Mt_of_derivI {α : A.Sent} (h : i.DerivI (Ts (M := M) L.Sent T) α) :
    i.DerivI (Stab (Mt i hi T)) α := by
  rw [i.derivI_iff] at *
  refine L.deriv_of_mem ((stab_Mt_iff i hi T _).2 ?_)
  exact L.deriv_mono (fun β hβ => Or.inl hβ) h

/-- If `T^s` is `1`-consistent then `M̃^s` is consistent (Theorem 3.25 (4) and Lemma 3.22). -/
theorem consistent_Mt (h : i.OneConsistent (Ts (M := M) L.Sent T)) : L.Consistent (Stab (Mt i hi T)) := by
  obtain ⟨α, hα⟩ := SpecI_consistent i hi T h
  refine ⟨α, fun hd => hα ?_⟩
  have hd' : L.Deriv (specExt i (Ts (M := M) L.Sent T)) α :=
    L.deriv_cut (fun β hβ => (stab_Mt_iff i hi T β).1 hβ) hd
  exact L.deriv_mono (fun β hβ => (SpecI_Ts i hi T β).2 hβ) hd'

/-- (5.6) and (5.7): `i (𝒢 (T))` is `M̃`-stable iff `Tur T` is `D^T`-decided iff `Tur T` is
`Ω (Tur T)`-decided iff `ℕ ⊨ ¬𝒢 (T)`. -/
theorem isStable_Mt_G_iff : IsStable (Mt i hi T) (i.i (G i hi T)) ↔ ¬ A.TrueN (G i hi T) := by
  -- `i (𝒢 T)` is `M̃`-stable iff it is `Dec (C (Spec T))`-decided (Lemma 3.16)
  have h1 : IsStable (Mt i hi T) (i.i (G i hi T)) ↔
      TDecided (M := M) (DecL L (CL L (SpecI i hi T))) (i.i (G i hi T)) :=
    DecL_spec L _ _
  -- which is, by definition of `H`, `Tur T` being `D^T`-decided
  have h2 : TDecided (M := M) (DecL L (CL L (SpecI i hi T))) (i.i (G i hi T)) ↔
      IsDecided (fun T' n => H i hi T T' n) (Tur i hi T) := Iff.rfl
  -- which is `Tur T` being `Ω (Tur T)`-decided, as `Tur T` computes `D^T`
  have h3 : IsDecided (fun T' n => H i hi T T' n) (Tur i hi T) ↔
      TDecided (M := M) (Omega M (Tur i hi T)) (Tur i hi T) := by
    unfold TDecided
    constructor
    · exact IsDecided.of_eq fun b n => by rw [decOf_Omega, decOf_Tur]
    · exact IsDecided.of_eq fun b n => by rw [decOf_Omega, decOf_Tur]
  rw [h1, h2, h3, ← A.trueN_sigmaT_iff, not_trueN_G_iff]

/-- If `ℕ ⊨ ¬𝒢 (T)` then `M̃ ⊢ⁱ ¬𝒢 (T)`, as `M̃` is speculative. -/
theorem derivI_Mt_sigma_of_not_trueN (h : ¬ A.TrueN (G i hi T)) :
    i.DerivI (Stab (Mt i hi T)) (A.sigmaT (Tur i hi T)) := by
  rw [not_trueN_G_iff] at h
  have hσ := A.sigmaT_sigma2 (Tur i hi T)
  obtain ⟨u, hu⟩ := (A.trueN_sigma 1 _ hσ).1 h
  have hπ : A.TrPi 1 (A.instS (A.sigmaT (Tur i hi T)) u) := ⟨A.instS_pi 1 _ u hσ, hu⟩
  have h1 := Mt_speculative i hi T _ hπ
  exact i.derivI_cut (fun β hβ => by rw [hβ]; exact h1) (A.exists_intro 1 _ u hσ)

/-- Proposition 5.5 (3): if `T^s` is `1`-consistent then `ℕ ⊨ 𝒢 (T)`. -/
theorem trueN_G (h : i.OneConsistent (Ts (M := M) L.Sent T)) : A.TrueN (G i hi T) := by
  refine Classical.byContradiction fun hc => ?_
  have h1 : i.DerivI (Stab (Mt i hi T)) (A.sigmaT (Tur i hi T)) := derivI_Mt_sigma_of_not_trueN i hi T hc
  have h2 : i.DerivI (Stab (Mt i hi T)) (A.neg (A.sigmaT (Tur i hi T))) := by
    rw [i.derivI_iff]
    exact L.deriv_of_mem ((isStable_Mt_G_iff i hi T).2 hc)
  exact i.not_consistent_of_derivI_neg h1 h2 (consistent_Mt i hi T h)

/-- Proposition 5.5 (1): if `T^s` is `1`-consistent then `T^s ⊬ⁱ 𝒢 (T)`. -/
theorem not_derivI_G (h : i.OneConsistent (Ts (M := M) L.Sent T)) :
    ¬ i.DerivI (Ts (M := M) L.Sent T) (G i hi T) := by
  intro hd
  have h1 : IsStable (Mt i hi T) (i.i (G i hi T)) := by
    have := derivI_Mt_of_derivI i hi T hd
    rw [i.derivI_iff] at this
    exact (stab_Mt_iff i hi T _).2 (L.deriv_cut (fun β hβ => (stab_Mt_iff i hi T β).1 hβ) this)
  exact (isStable_Mt_G_iff i hi T).1 h1 (trueN_G i hi T h)

/-- Proposition 5.5 (2): if `T^s` is `2`-consistent then `T^s ⊬ⁱ ¬𝒢 (T)`. -/
theorem not_derivI_neg_G (h : i.TwoConsistent (Ts (M := M) L.Sent T)) :
    ¬ i.DerivI (Ts (M := M) L.Sent T) (A.neg (G i hi T)) := by
  intro hd
  have hσ := A.sigmaT_sigma2 (Tur i hi T)
  -- `F ⊢ⁱ σ (Tur T)`, by double negation elimination
  have h1 : i.DerivI (Ts (M := M) L.Sent T) (A.sigmaT (Tur i hi T)) := by
    unfold G Arith.sT at hd
    exact A.deriv_dne hd
  -- `2`-consistency gives an instance `φ(u)` with `F ⊬ⁱ ¬φ(u)`
  obtain ⟨u, hu⟩ := h.2 _ hσ h1
  -- `φ(u)` is a true `Π⁰₁` sentence: a false instance would be refuted by `Q`
  have hπ : A.IsPi 1 (A.instS (A.sigmaT (Tur i hi T)) u) := A.instS_pi 1 _ u hσ
  have htrue : A.TrueN (A.instS (A.sigmaT (Tur i hi T)) u) := by
    refine (A.trueN_pi 0 _ hπ).2 fun v => Classical.byContradiction fun hv => ?_
    have hQ : A.Deriv A.Q (A.neg (A.instP (A.instS (A.sigmaT (Tur i hi T)) u) v)) :=
      A.Q_delta0_neg _ (A.instP_sigma 0 _ v hπ) hv
    have hQ' : A.Deriv A.Q (A.neg (A.instS (A.sigmaT (Tur i hi T)) u)) :=
      A.deriv_neg_pi_of_neg_inst hπ hQ
    exact hu (i.derivI_cut (fun q hq => h.1.1 q hq) hQ')
  -- hence `ℕ ⊨ σ (Tur T)`, i.e. `ℕ ⊨ ¬𝒢 (T)`, contradicting (3)
  have h2 : A.TrueN (A.sigmaT (Tur i hi T)) := (A.trueN_sigma 1 _ hσ).2 ⟨u, htrue⟩
  exact (not_trueN_G_iff i hi T).2 h2 (trueN_G i hi T h.1)

end Syntactic

/-! ### Theorem 1.5 -/

/-- Theorem 1.5 (`theorem_firstincompleteness`) in the form for a translation `i`.  In the present
manuscript this form is Example 5.23; the printed Theorem 1.5, for theories of arithmetic, is
`first_incompleteness_arith` in `Stable/Plain.lean`.  There is a total computable `𝒢 : 𝒯 → 𝓐`,
depending only on `i` (here `G` is obtained by choice from `hi`), such that whenever `T` stably
computes `N : ℕ → 𝓛 × {±}` and `F = N^s`:
(1) `F ⊬ⁱ 𝒢 (T)` if `F` is `1`-consistent; (2) `F ⊬ⁱ ¬𝒢 (T)` if `F` is `2`-consistent;
(3) `ℕ ⊨ 𝒢 (T)` if `F` is `1`-consistent (all relative to `i`). -/
theorem first_incompleteness : ∃ G : M.Code → A.Sent, CompT M G ∧
    ∀ (T : M.Code) (N : ℕ → Option (L.Sent × Bool)), StablyComputes (M := M) T N →
      (i.OneConsistent (Stab N) → ¬ i.DerivI (Stab N) (G T)) ∧
      (i.TwoConsistent (Stab N) → ¬ i.DerivI (Stab N) (A.neg (G T))) ∧
      (i.OneConsistent (Stab N) → A.TrueN (G T)) := by
  refine ⟨G i hi, G_compT i hi, fun T N hTN => ?_⟩
  -- `N^s = T^s` as sets
  have hF : ∀ x, Stab N x ↔ Ts (M := M) L.Sent T x := fun x => (hTN.2 x).symm
  have hFeq : Stab N = Ts (M := M) L.Sent T := funext fun x => propext (hF x)
  rw [hFeq]
  exact ⟨not_derivI_G i hi T, not_derivI_neg_G i hi T, trueN_G i hi T⟩

end Stable
