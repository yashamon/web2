import Stable.NHalting
import Stable.Second

/-!
# The incompleteness theorems at level `n = m+1` (Section 6.3, Theorems 6.8 and 6.9)

Fix an `(m+2)`-translation `i : 𝓐 → 𝓛`.  With `Dec^{m+1}`, `C^{m+1}`, `Spec^{m+1}_i`, `s_{m+1}` in place
of `Dec`, `C`, `Spec_i`, `s`, define `Tur_{m+1}` and `𝒢_{m+1} (T) := s_{m+1} (Tur_{m+1} T)` exactly as
in Section 5.  Theorem 6.8 (`theorem_nfirstincompleteness`): for `T ∈ 𝒯^{m+1}_𝓛` and
`F = T^{s_{m+1}}`,
1. if `F` is `Σ_{m+1}`-sound relative to `i` then `F ⊬ⁱ 𝒢_{m+1} (T)` and `ℕ ⊨ 𝒢_{m+1} (T)`;
2. if `F` is `Σ_{m+2}`-sound relative to `i` then `F ⊬ⁱ ¬𝒢_{m+1} (T)`.
Theorem 6.9 (`theorem_nsecondincompleteness`) is the abstract second incompleteness theorem at
level `m+1`, with the `ZFC`-provability of part (1) as an explicit hypothesis, as in `Stable.Second`.
For `m = 0` these are Theorem 1.5 (with `F ⊢ⁱ Q` dropped, by Lemma 6.6 (1)) and Theorem 5.11.

In the restructured manuscript (11 November 2026) the theorems are stated for theories of
arithmetic, the case `𝓛 = 𝓐`, `i = id` of this file: see `Stable.Plain` (level `n`: `Stable.NPlain`).
The statements for a translation `i`, as here, are Example 5.23 and its level-`n` form, with the
notation of Appendix B; they are also recovered from readings in `Stable.ReadingsTranslations`.
-/

namespace Stable

open Classical

variable {M : TuringModel} {A : Arith M} {L : Language M}

/-- `Dec^{m+1}_𝓛`. -/
noncomputable def NDecL (L : Language M) (m : ℕ) : M.Code → M.Code :=
  choose (exists_nDec (M := M) (B := L.Sent) m)

theorem NDecL_spec (L : Language M) (m : ℕ) (T : M.Code) (γ : L.Sent) :
    NTs (M := M) m L.Sent T γ ↔ NDec m (decOf (M := M) (NB L.Sent m) (NDecL L m T)) γ :=
  ((choose_spec (exists_nDec (M := M) (B := L.Sent) m)).2 T).2.2 γ

/-- `C^{m+1}`. -/
noncomputable def NCL (L : Language M) (m : ℕ) : M.Code → M.Code := choose (exists_nC L m)

theorem NCL_spec (L : Language M) (m : ℕ) (T : M.Code) (γ : L.Sent) :
    NTs (M := M) m L.Sent (NCL L m T) γ ↔ L.Deriv (NTs (M := M) m L.Sent T) γ :=
  ((choose_spec (exists_nC L m)).2 T).2.2 γ

variable (i : Translation A.toLanguage L) (m : ℕ) (hi : i.IsNTranslation (m + 2))
include hi

/-- `Spec^{m+1}_i`. -/
noncomputable def NSpecI : M.Code → M.Code := choose (exists_nSpec i m hi)

theorem NSpecI_speculative (T : M.Code) : NSpeculative i m (nseqOf (M := M) m L.Sent (NSpecI i m hi T)) :=
  ((choose_spec (exists_nSpec i m hi)).2 T).2.2.1

theorem NSpecI_NTs (T : M.Code) (x : L.Sent) :
    NTs (M := M) m L.Sent (NSpecI i m hi T) x ↔ specExtN i (m + 1) (NTs (M := M) m L.Sent T) x :=
  ((choose_spec (exists_nSpec i m hi)).2 T).2.2.2.1 x

theorem NSpecI_consistent (T : M.Code) (h : i.SigmaSound (m + 1) (NTs (M := M) m L.Sent T)) :
    L.Consistent (NTs (M := M) m L.Sent (NSpecI i m hi T)) :=
  ((choose_spec (exists_nSpec i m hi)).2 T).2.2.2.2 h

/-- `i ∘ s_{m+1}` is computable. -/
theorem compT_i_nsT : CompT M (fun T => i.i (A.nsT m T)) := by
  have h1 : Comp M (fun α : A.Sent => if A.IsSigma (m + 2) α then some (i.i α) else none) :=
    Comp.ofRestrict (A.sigma_comp (m + 2)) (f := i.i) hi
  have h2 : CompT M (fun T => i.i (A.nsigmaT m T)) := by
    have := h1.compT (A.nsigmaT_compT m)
    exact this.congr fun T => by rw [ite_eq_left (A.nsigmaT_sigma m T)]
  have h3 : CompT M (fun T => L.neg (i.i (A.nsigmaT m T))) := L.neg_comp.comp h2
  exact h3.congr fun T => by unfold Arith.nsT; rw [i.map_neg]

/-- The `(m+1)`-decision map `D^P` on `𝒯`: `D^P ((T, ū), w) = (Dec (C (Spec P)))' ((i (s T), ū), w)`. -/
noncomputable def NH (P : M.Code) : NB M.Code m → ℕ → Option Bool :=
  fun x w => decOf (M := M) (NB L.Sent m) (NDecL L m (NCL L m (NSpecI i m hi P)))
    (nbMapBase m (fun T => i.i (A.nsT m T)) x) w

theorem comp_NH : Comp M (fun q : M.Code × (NB M.Code m × ℕ) => NH i m hi q.1 q.2.1 q.2.2) := by
  have hDec : CompT M (NDecL L m) := (choose_spec (exists_nDec (M := M) (B := L.Sent) m)).1
  have hC : CompT M (NCL L m) := (choose_spec (exists_nC L m)).1
  have hS : CompT M (NSpecI i m hi) := (choose_spec (exists_nSpec i m hi)).1
  have h1 : CompT M (fun q : M.Code × (NB M.Code m × ℕ) => NDecL L m (NCL L m (NSpecI i m hi q.1))) :=
    hDec.comp (hC.comp (hS.comp compT_fst))
  have h2 : CompT M (fun q : M.Code × (NB M.Code m × ℕ) =>
      nbMapBase m (fun T => i.i (A.nsT m T)) q.2.1) :=
    (compT_nbMapBase m (compT_i_nsT i m hi)).comp (compT_fst.comp compT_snd)
  have := (comp_VD (M := M) (B := NB L.Sent m)).compT
    (CompT.pair h1 (CompT.pair h2 (compT_snd.comp compT_snd)))
  exact this.congr fun q => rfl

/-- `Tur_{m+1} : 𝒯 → 𝒯`: `Tur P` computes `D^P`. -/
noncomputable def NTur : M.Code → M.Code := choose (smn (comp_NH i m hi))

theorem NTur_compT : CompT M (NTur i m hi) := (choose_spec (smn (comp_NH i m hi))).1

theorem decOf_NTur (P : M.Code) (x : NB M.Code m) (w : ℕ) :
    decOf (M := M) (NB M.Code m) (NTur i m hi P) x w = NH i m hi P x w :=
  (inDB_of_computes (D := fun x w => NH i m hi P x w) ((choose_spec (smn (comp_NH i m hi))).2 P)).2 x w

/-- The Gödel sentence `𝒢_{m+1} (T) := s_{m+1} (Tur_{m+1} T)`. -/
noncomputable def NG (T : M.Code) : A.Sent := A.nsT m (NTur i m hi T)

theorem NG_compT : CompT M (NG i m hi) := (A.nsT_compT m).comp (NTur_compT i m hi)

theorem not_trueN_NG_iff (T : M.Code) : ¬ A.TrueN (NG i m hi T) ↔ A.TrueN (A.nsigmaT m (NTur i m hi T)) := by
  unfold NG Arith.nsT
  rw [A.trueN_neg, Classical.not_not]

/-! ### Theorem 6.8 -/

section Main

variable (T : M.Code)

/-- `M̃ := (C (Spec T))'`, with `M̃^{s_{m+1}} = closure (T^{s_{m+1}} ∪ i (Tr_{Π_{m+1}}))`. -/
theorem NTs_C_Spec_iff (x : L.Sent) :
    NTs (M := M) m L.Sent (NCL L m (NSpecI i m hi T)) x ↔
      L.Deriv (specExtN i (m + 1) (NTs (M := M) m L.Sent T)) x := by
  rw [NCL_spec]
  constructor
  · exact L.deriv_mono fun β hβ => (NSpecI_NTs i m hi T β).1 hβ
  · exact L.deriv_mono fun β hβ => (NSpecI_NTs i m hi T β).2 hβ

theorem speculative_C_Spec : NSpeculative i m (nseqOf (M := M) m L.Sent (NCL L m (NSpecI i m hi T))) := by
  intro π hπ
  rw [i.derivI_iff]
  exact L.deriv_of_mem ((NTs_C_Spec_iff i m hi T _).2 (L.deriv_of_mem (Or.inr ⟨π, hπ, rfl⟩)))

theorem consistent_C_Spec (h : i.SigmaSound (m + 1) (NTs (M := M) m L.Sent T)) :
    L.Consistent (NTs (M := M) m L.Sent (NCL L m (NSpecI i m hi T))) := by
  obtain ⟨α, hα⟩ := NSpecI_consistent i m hi T h
  refine ⟨α, fun hd => hα ?_⟩
  have hd' : L.Deriv (specExtN i (m + 1) (NTs (M := M) m L.Sent T)) α :=
    L.deriv_cut (fun β hβ => (NTs_C_Spec_iff i m hi T β).1 hβ) hd
  exact L.deriv_mono (fun β hβ => (NSpecI_NTs i m hi T β).2 hβ) hd'

/-- (5.6)–(5.7) at level `m+1`: `i (𝒢 T)` is `M̃`-`(m+1)`-stable iff `ℕ ⊨ ¬𝒢 (T)`. -/
theorem NTs_NG_iff : NTs (M := M) m L.Sent (NCL L m (NSpecI i m hi T)) (i.i (NG i m hi T)) ↔
    ¬ A.TrueN (NG i m hi T) := by
  rw [NDecL_spec]
  -- `Tur T` is `D^T`-decided
  have h1 : NDec m (decOf (M := M) (NB L.Sent m) (NDecL L m (NCL L m (NSpecI i m hi T)))) (i.i (NG i m hi T)) ↔
      NDec m (NH i m hi T) (NTur i m hi T) := by
    unfold NG
    exact (NDec_nbMapBase m _ (fun T' => i.i (A.nsT m T')) (NTur i m hi T)).symm
  have h2 : NDec m (NH i m hi T) (NTur i m hi T) ↔
      NDec m (decOf (M := M) (NB M.Code m) (NOmega M m (NTur i m hi T))) (NTur i m hi T) :=
    NDec.of_eq m (fun x w => by rw [decOf_NOmega, decOf_NTur]) _
  rw [h1, h2, ← A.trueN_nsigmaT_iff, not_trueN_NG_iff]

theorem derivI_sigma_of_not_trueN (h : ¬ A.TrueN (NG i m hi T)) :
    i.DerivI (NTs (M := M) m L.Sent (NCL L m (NSpecI i m hi T))) (A.nsigmaT m (NTur i m hi T)) := by
  rw [not_trueN_NG_iff] at h
  have hσ := A.nsigmaT_sigma m (NTur i m hi T)
  obtain ⟨u, hu⟩ := (A.trueN_sigma (m + 1) _ hσ).1 h
  have hπ : A.TrPi (m + 1) (A.instS (A.nsigmaT m (NTur i m hi T)) u) := ⟨A.instS_pi (m + 1) _ u hσ, hu⟩
  have h1 := speculative_C_Spec i m hi T _ hπ
  exact i.derivI_cut (fun β hβ => by rw [hβ]; exact h1) (A.exists_intro (m + 1) _ u hσ)

/-- Theorem 6.8 (1), second half: `ℕ ⊨ 𝒢_{m+1} (T)` for `Σ_{m+1}`-sound `T^{s_{m+1}}`. -/
theorem trueN_NG (h : i.SigmaSound (m + 1) (NTs (M := M) m L.Sent T)) : A.TrueN (NG i m hi T) := by
  refine Classical.byContradiction fun hc => ?_
  have h1 := derivI_sigma_of_not_trueN i m hi T hc
  have h2 : i.DerivI (NTs (M := M) m L.Sent (NCL L m (NSpecI i m hi T))) (A.neg (A.nsigmaT m (NTur i m hi T))) := by
    rw [i.derivI_iff]
    exact L.deriv_of_mem ((NTs_NG_iff i m hi T).2 hc)
  exact i.not_consistent_of_derivI_neg h1 h2 (consistent_C_Spec i m hi T h)

/-- Theorem 6.8 (1), first half: `T^{s_{m+1}} ⊬ⁱ 𝒢_{m+1} (T)` for `Σ_{m+1}`-sound `T^{s_{m+1}}`. -/
theorem not_derivI_NG (h : i.SigmaSound (m + 1) (NTs (M := M) m L.Sent T)) :
    ¬ i.DerivI (NTs (M := M) m L.Sent T) (NG i m hi T) := by
  intro hd
  rw [i.derivI_iff] at hd
  have h1 : NTs (M := M) m L.Sent (NCL L m (NSpecI i m hi T)) (i.i (NG i m hi T)) :=
    (NTs_C_Spec_iff i m hi T _).2 (L.deriv_mono (fun β hβ => Or.inl hβ) hd)
  exact (NTs_NG_iff i m hi T).1 h1 (trueN_NG i m hi T h)

/-- Theorem 6.8 (2): `T^{s_{m+1}} ⊬ⁱ ¬𝒢_{m+1} (T)` for `Σ_{m+2}`-sound `T^{s_{m+1}}`. -/
theorem not_derivI_neg_NG (h : i.SigmaSound (m + 2) (NTs (M := M) m L.Sent T)) :
    ¬ i.DerivI (NTs (M := M) m L.Sent T) (A.neg (NG i m hi T)) := by
  intro hd
  have h1 : i.DerivI (NTs (M := M) m L.Sent T) (A.nsigmaT m (NTur i m hi T)) := by
    unfold NG Arith.nsT at hd
    exact A.deriv_dne hd
  have h2 : A.TrueN (A.nsigmaT m (NTur i m hi T)) := h _ (A.nsigmaT_sigma m _) h1
  exact (not_trueN_NG_iff i m hi T).2 h2 (trueN_NG i m hi T (SigmaSound.mono i h))

end Main

/-- Theorem 6.8 (`theorem_nfirstincompleteness`), packaged: a total computable `𝒢_{m+1} : 𝒯 → 𝓐` with,
for every `T` and `F = T^{s_{m+1}}`: (1) if `F` is `Σ_{m+1}`-sound then `F ⊬ⁱ 𝒢 (T)` and
`ℕ ⊨ 𝒢 (T)`; (2) if `F` is `Σ_{m+2}`-sound then `F ⊬ⁱ ¬𝒢 (T)`. -/
theorem n_first_incompleteness : ∃ G : M.Code → A.Sent, CompT M G ∧ ∀ T : M.Code,
    (i.SigmaSound (m + 1) (NTs (M := M) m L.Sent T) →
      ¬ i.DerivI (NTs (M := M) m L.Sent T) (G T) ∧ A.TrueN (G T)) ∧
    (i.SigmaSound (m + 2) (NTs (M := M) m L.Sent T) → ¬ i.DerivI (NTs (M := M) m L.Sent T) (A.neg (G T))) :=
  ⟨NG i m hi, NG_compT i m hi, fun T =>
    ⟨fun h => ⟨not_derivI_NG i m hi T h, trueN_NG i m hi T h⟩, not_derivI_neg_NG i m hi T⟩⟩

end Stable

namespace Stable

open Classical

variable {M : TuringModel} {A : Arith M} {Z L : Language M}

/-- Theorem 6.9 (`theorem_nsecondincompleteness`), abstract form, as in `Stable.Second`: with
`j = i ∘ iAZ` an `(m+2)`-translation, `F = T^{s_{m+1}}`, `F ⊢ⁱ ZFC`, `F` `Σ_{m+1}`-sound relative to `j`,
and `snd ∈ 𝓩` with `ZFC ∪ {snd} ⊢ iAZ (𝒢_{m+1} (T))` (the `ZFC`-formalization of Theorem 6.8 (1), for
`snd = Snd_{m+1} (T, i)`), we have `F ⊬ⁱ snd`. -/
theorem n_second_incompleteness (iAZ : Translation A.toLanguage Z) (i : Translation Z L) (m : ℕ)
    (hj : (i.comp iAZ).IsNTranslation (m + 2)) (ZFC : Z.Sent → Prop) (T : M.Code)
    (hZFC : i.DerivISet (NTs (M := M) m L.Sent T) ZFC)
    (h1 : (i.comp iAZ).SigmaSound (m + 1) (NTs (M := M) m L.Sent T)) (snd : Z.Sent)
    (hsnd : Z.Deriv (fun β => ZFC β ∨ β = snd) (iAZ.i (NG (i.comp iAZ) m hj T))) :
    ¬ i.DerivI (NTs (M := M) m L.Sent T) snd := by
  intro hc
  have h2 : i.DerivI (NTs (M := M) m L.Sent T) (iAZ.i (NG (i.comp iAZ) m hj T)) := by
    refine i.derivI_cut (fun β hβ => ?_) hsnd
    rcases hβ with hβ | rfl
    · exact hZFC β hβ
    · exact hc
  have h3 : (i.comp iAZ).DerivI (NTs (M := M) m L.Sent T) (NG (i.comp iAZ) m hj T) := by
    rw [Translation.derivI_iff] at h2 ⊢
    exact h2
  exact not_derivI_NG (i.comp iAZ) m hj T h1 h3

/-- Theorem 6.9, second part (Corollary 5.13 at level `m+1`). -/
theorem n_second_incompleteness_corollary (iAZ : Translation A.toLanguage Z) (i : Translation Z L)
    (m : ℕ) (hj : (i.comp iAZ).IsNTranslation (m + 2)) (ZFC : Z.Sent → Prop) (T : M.Code)
    (hZFC : i.DerivISet (NTs (M := M) m L.Sent T) ZFC)
    (h1 : (i.comp iAZ).SigmaSound (m + 1) (NTs (M := M) m L.Sent T)) (snd enum sndδ : Z.Sent)
    (hsnd : Z.Deriv (fun β => ZFC β ∨ β = snd) (iAZ.i (NG (i.comp iAZ) m hj T)))
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = sndδ) snd)
    (henum : i.DerivI (NTs (M := M) m L.Sent T) enum) :
    ¬ i.DerivI (NTs (M := M) m L.Sent T) sndδ := by
  intro hc
  refine n_second_incompleteness iAZ i m hj ZFC T hZFC h1 snd hsnd ?_
  refine i.derivI_cut (fun β hβ => ?_) hδ
  rcases hβ with hβ | rfl | rfl
  · exact hZFC β hβ
  · exact henum
  · exact hc

end Stable
