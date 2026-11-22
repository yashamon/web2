import Stable.Readings
import Stable.NIncompleteness
import Stable.NSigma

/-!
# Level `n`: theories of arithmetic (Section 6.3 of the restructured paper)

Paper level `n = m + 1`.  As in `Stable.Plain`, the results of `Stable.NIncompleteness` are
specialized to the identity translation, and Theorem 6.9 is put in the form of Theorem 5.11.

* `NG₀ A m : 𝒯 → 𝓐`: the map `𝒢ₙ`; Theorem 6.8 is `Arith.not_deriv_NG₀`, `Arith.trueN_NG₀`,
  `Arith.not_deriv_neg_NG₀`, packaged as `n_first_incompleteness_arith`.
* Theorem 6.9 (`n_second_incompleteness_H`, `n_second_incompleteness_H_corollary`): `H` is a
  deductively closed `𝓩`-theory containing `ZFC` with `F ⊢ b` whenever `b ∈ 𝓑ₙ₊₁` and `b* ∈ H`;
  then `snd ∉ H`.  The `ZFC`-formalization of Theorem 6.8 (1) is the hypothesis `hsnd`.
* The simplest case (`n_second_incompleteness_simple`).
* Theorem 1.1 and Corollary 5.17 at level `n` (`n_second_incompleteness_sigma`,
  `n_second_incompleteness_sigma_simple`), for a `Σ⁰ₙ₊₁`-definable theory `F`.  Some machine
  presents `F` (`exists_nmachine_of_isSigmaNSet`, by Corollary 6.3), and the conclusion holds for
  every machine presenting `F`.
* Corollaries 5.20 and 5.21 at level `n` (`n_reading_first`, `n_reading_second`), for a machine
  `T` with `T^{sₙ} = F₀^R ∩ P`, `P ⊇ 𝓑ₙ₊₁`.  Such a machine is given, computably in a
  presentation of `F₀`, by the map `Shⁿ_R` of Section 6.3: `exists_nShadow` in
  `Stable/NReadings.lean`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-- The Gödel map `𝒢_{m+1} : 𝒯 → 𝓐` of Section 6.3, for theories of arithmetic. -/
noncomputable def NG₀ (A : Arith M) (m : ℕ) : M.Code → A.Sent :=
  NG (Translation.id A.toLanguage) m (A.id_isNTranslation (m + 2))

namespace Arith

variable (A : Arith M) (m : ℕ)

theorem NG₀_compT : CompT M (NG₀ A m) :=
  NG_compT (Translation.id A.toLanguage) m (A.id_isNTranslation (m + 2))

/-- `𝒢_{m+1} (T)` is the negation of a `Σ⁰_{m+2}` sentence, so it lies in `𝓑_{m+2}`. -/
theorem NG₀_boolComb (T : M.Code) : A.BoolComb (m + 2) (NG₀ A m T) :=
  BoolComb.neg (BoolComb.sigma (A.nsigmaT_sigma m _))

/-- Theorem 6.8 (1), second half. -/
theorem trueN_NG₀ (T : M.Code) (h : A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T)) :
    A.TrueN (NG₀ A m T) :=
  trueN_NG (Translation.id A.toLanguage) m (A.id_isNTranslation (m + 2)) T
    ((A.id_sigmaSound_iff _ _).2 h)

/-- Theorem 6.8 (1), first half. -/
theorem not_deriv_NG₀ (T : M.Code) (h : A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T)) :
    ¬ A.Deriv (NTs (M := M) m A.Sent T) (NG₀ A m T) := fun hd =>
  not_derivI_NG (Translation.id A.toLanguage) m (A.id_isNTranslation (m + 2)) T
    ((A.id_sigmaSound_iff _ _).2 h) ((A.deriv_induced_id_iff _ _).2 hd)

/-- Theorem 6.8 (2). -/
theorem not_deriv_neg_NG₀ (T : M.Code) (h : A.SigmaSound (m + 2) (NTs (M := M) m A.Sent T)) :
    ¬ A.Deriv (NTs (M := M) m A.Sent T) (A.neg (NG₀ A m T)) := fun hd =>
  not_derivI_neg_NG (Translation.id A.toLanguage) m (A.id_isNTranslation (m + 2)) T
    ((A.id_sigmaSound_iff _ _).2 h) ((A.deriv_induced_id_iff _ _).2 hd)

end Arith

/-- Theorem 6.8 (`theorem_nfirstincompleteness`) in its present form. -/
theorem n_first_incompleteness_arith (A : Arith M) (m : ℕ) :
    ∃ G : M.Code → A.Sent, CompT M G ∧ ∀ T : M.Code,
      (A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T) →
        ¬ A.Deriv (NTs (M := M) m A.Sent T) (G T) ∧ A.TrueN (G T)) ∧
      (A.SigmaSound (m + 2) (NTs (M := M) m A.Sent T) →
        ¬ A.Deriv (NTs (M := M) m A.Sent T) (A.neg (G T))) :=
  ⟨NG₀ A m, A.NG₀_compT m, fun T =>
    ⟨fun h => ⟨A.not_deriv_NG₀ m T h, A.trueN_NG₀ m T h⟩, A.not_deriv_neg_NG₀ m T⟩⟩

/-! ### The deductions of Theorems 5.11 and 6.9, for an arbitrary sentence `g` -/

variable {A : Arith M} {Z : Language M}

/-- The last step of the proofs of Theorems 5.11 and 6.9.  `g` is a sentence of arithmetic with
`F ⊬ g`; `H` is deductively closed, contains `ZFC`, and `g* ∈ H` implies `F ⊢ g`; `con ∈ 𝓩`
satisfies `ZFC ∪ {con} ⊢ g*`.  Then `con ∉ H`. -/
theorem not_mem_of_deriv_godel (iAZ : Translation A.toLanguage Z) (ZFC H : Z.Sent → Prop)
    (hH : Z.Closed H) (hZFC : ∀ β, ZFC β → H β) {F : A.Sent → Prop} {g : A.Sent}
    (hg : ¬ A.Deriv F g) (hB : H (iAZ.i g) → A.Deriv F g) (con : Z.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = con) (iAZ.i g)) : ¬ H con := by
  intro hc
  refine hg (hB (hH _ (Z.deriv_cut (fun β hβ => ?_) hcon)))
  rcases hβ with hβ | rfl
  · exact Z.deriv_of_mem (hZFC β hβ)
  · exact Z.deriv_of_mem hc

/-- The simplest case, for an arbitrary sentence `g` with `F ⊬ g`: if `F ⊢ a` whenever
`ZFC ⊢ a*`, and `ZFC ∪ {con₀*} ⊢ g*`, then `F ⊬ con₀`. -/
theorem not_deriv_of_deriv_godel (iAZ : Translation A.toLanguage Z) (ZFC : Z.Sent → Prop)
    {F : A.Sent → Prop} {g : A.Sent} (hg : ¬ A.Deriv F g)
    (hF : ∀ a : A.Sent, Z.Deriv ZFC (iAZ.i a) → A.Deriv F a) (con₀ : A.Sent)
    (hcon : Z.Deriv (fun β => ZFC β ∨ β = iAZ.i con₀) (iAZ.i g)) : ¬ A.Deriv F con₀ := by
  intro hc
  have hZ : Z.Deriv ZFC (iAZ.i (A.neg (A.and con₀ (A.neg g)))) := by
    rw [iAZ.map_neg, iAZ.map_and, iAZ.map_neg]
    refine Z.deriv_neg_intro fun γ => ?_
    have hand : Z.Deriv (fun β => ZFC β ∨ β = Z.and (iAZ.i con₀) (Z.neg (iAZ.i g)))
        (Z.and (iAZ.i con₀) (Z.neg (iAZ.i g))) := Z.deriv_of_mem (Or.inr rfl)
    have hg' : Z.Deriv (fun β => ZFC β ∨ β = Z.and (iAZ.i con₀) (Z.neg (iAZ.i g))) (iAZ.i g) := by
      refine Z.deriv_cut (fun β hβ => ?_) hcon
      rcases hβ with hβ | rfl
      · exact Z.deriv_of_mem (Or.inl hβ)
      · exact Z.deriv_and_left hand
    exact Z.deriv_explosion hg' (Z.deriv_and_right hand)
  have hFc := hF _ hZ
  refine hg (A.deriv_dne (A.deriv_neg_intro fun γ => ?_))
  have h1' : A.Deriv (fun β => F β ∨ β = A.neg g) (A.and con₀ (A.neg g)) :=
    A.deriv_and_intro (A.deriv_mono (fun β hβ => Or.inl hβ) hc) (A.deriv_of_mem (Or.inr rfl))
  exact A.deriv_explosion h1' (A.deriv_mono (fun β hβ => Or.inl hβ) hFc)

/-! ### Theorem 6.9 in its present form -/

/-- Theorem 6.9 (`theorem_nsecondincompleteness`), first assertion, abstract form. -/
theorem n_second_incompleteness_H (iAZ : Translation A.toLanguage Z) (ZFC H : Z.Sent → Prop)
    (hH : Z.Closed H) (hZFC : ∀ β, ZFC β → H β) (m : ℕ) (T : M.Code)
    (h1 : A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T))
    (hB : ∀ b, A.BoolComb (m + 2) b → H (iAZ.i b) → A.Deriv (NTs (M := M) m A.Sent T) b)
    (snd : Z.Sent)
    (hsnd : Z.Deriv (fun β => ZFC β ∨ β = snd) (iAZ.i (NG₀ A m T))) : ¬ H snd :=
  not_mem_of_deriv_godel iAZ ZFC H hH hZFC (A.not_deriv_NG₀ m T h1)
    (hB _ (A.NG₀_boolComb m T)) snd hsnd

/-- Theorem 6.9, second assertion: `H` does not contain both `Enumₙ (T, δ)` and `Sndₙ (δ)`. -/
theorem n_second_incompleteness_H_corollary (iAZ : Translation A.toLanguage Z)
    (ZFC H : Z.Sent → Prop) (hH : Z.Closed H) (hZFC : ∀ β, ZFC β → H β) (m : ℕ) (T : M.Code)
    (h1 : A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T))
    (hB : ∀ b, A.BoolComb (m + 2) b → H (iAZ.i b) → A.Deriv (NTs (M := M) m A.Sent T) b)
    (snd enum sndδ : Z.Sent)
    (hsnd : Z.Deriv (fun β => ZFC β ∨ β = snd) (iAZ.i (NG₀ A m T)))
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = sndδ) snd) : ¬ (H enum ∧ H sndδ) := by
  rintro ⟨he, hc⟩
  refine n_second_incompleteness_H iAZ ZFC H hH hZFC m T h1 hB snd hsnd (hH _ ?_)
  refine Z.deriv_cut (fun β hβ => ?_) hδ
  rcases hβ with hβ | rfl | rfl
  · exact Z.deriv_of_mem (hZFC β hβ)
  · exact Z.deriv_of_mem he
  · exact Z.deriv_of_mem hc

/-- The simplest case of Theorem 6.9: if `F = T^{sₙ}` is `Σₙ`-sound and `F ⊢ a` whenever
`ZFC ⊢ a*`, then `F ⊬ snd₀`, for `snd₀ ∈ 𝓐` with `ZFC ∪ {snd₀*} ⊢ 𝒢ₙ (T)*`. -/
theorem n_second_incompleteness_simple (iAZ : Translation A.toLanguage Z) (ZFC : Z.Sent → Prop)
    (m : ℕ) (T : M.Code) (h1 : A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T))
    (hF : ∀ a : A.Sent, Z.Deriv ZFC (iAZ.i a) → A.Deriv (NTs (M := M) m A.Sent T) a)
    (snd₀ : A.Sent)
    (hsnd : Z.Deriv (fun β => ZFC β ∨ β = iAZ.i snd₀) (iAZ.i (NG₀ A m T))) :
    ¬ A.Deriv (NTs (M := M) m A.Sent T) snd₀ :=
  not_deriv_of_deriv_godel iAZ ZFC (A.not_deriv_NG₀ m T h1) hF snd₀ hsnd

/-! ### Corollaries 5.20 and 5.21 at level `n` -/

/-- For `b ∈ 𝓑ₙ`: `F ⊢ b` iff `b ∈ E`, when `F = E ∩ P`, `P ⊇ 𝓑ₙ`, and `E` is deductively closed. -/
theorem deriv_fragment_iff {n : ℕ} {P E F : A.Sent → Prop} (hPB : ∀ b, A.BoolComb n b → P b)
    (hF : ∀ b, F b ↔ P b ∧ E b) (hcl : A.toLanguage.Closed E) {b : A.Sent}
    (hb : A.BoolComb n b) : A.Deriv F b ↔ E b :=
  ⟨fun h => hcl b (A.deriv_mono (fun β hβ => ((hF β).1 hβ).2) h),
    fun h => A.deriv_of_mem ((hF b).2 ⟨hPB b hb, h⟩)⟩

/-- Corollary 5.20 at level `n = m + 1`, for a machine `T` with `T^{sₙ} = F₀^R ∩ P`, `P ⊇ 𝓑ₙ₊₁`,
and `F₀^R` deductively closed: (1) if `F₀^R` is `Σₙ`-sound then `𝒢ₙ (T) ∉ F₀^R` and
`ℕ ⊨ 𝒢ₙ (T)`; (2) if `F₀^R` is `Σₙ₊₁`-sound then `¬𝒢ₙ (T) ∉ F₀^R`. -/
theorem n_reading_first {Y : Type} (m : ℕ) {P : A.Sent → Prop}
    (hPB : ∀ b, A.BoolComb (m + 2) b → P b) {R : A.Sent → Y → Prop} {F₀ : Y → Prop} {T : M.Code}
    (hT : ∀ b, NTs (M := M) m A.Sent T b ↔ P b ∧ Asserted R F₀ b)
    (hcl : A.toLanguage.Closed (Asserted R F₀)) :
    (A.SigmaSound (m + 1) (Asserted R F₀) →
      ¬ Asserted R F₀ (NG₀ A m T) ∧ A.TrueN (NG₀ A m T)) ∧
    (A.SigmaSound (m + 2) (Asserted R F₀) → ¬ Asserted R F₀ (A.neg (NG₀ A m T))) := by
  have s1 : A.SigmaSound (m + 1) (Asserted R F₀) →
      A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T) := fun h σ hσ hd =>
    h σ hσ (A.deriv_of_mem ((deriv_fragment_iff hPB hT hcl
      (Arith.BoolComb.sigma (A.sigma_succ (m + 1) σ hσ))).1 hd))
  have s2 : A.SigmaSound (m + 2) (Asserted R F₀) →
      A.SigmaSound (m + 2) (NTs (M := M) m A.Sent T) := fun h σ hσ hd =>
    h σ hσ (A.deriv_of_mem ((deriv_fragment_iff hPB hT hcl (Arith.BoolComb.sigma hσ)).1 hd))
  refine ⟨fun h => ⟨fun hg => ?_, A.trueN_NG₀ m T (s1 h)⟩, fun h hg => ?_⟩
  · exact A.not_deriv_NG₀ m T (s1 h)
      ((deriv_fragment_iff hPB hT hcl (A.NG₀_boolComb m T)).2 hg)
  · exact A.not_deriv_neg_NG₀ m T (s2 h)
      ((deriv_fragment_iff hPB hT hcl (Arith.BoolComb.neg (A.NG₀_boolComb m T))).2 hg)

/-- Corollary 5.21 at level `n = m + 1`, first assertion, abstract form. -/
theorem n_reading_second {Y : Type} (iAZ : Translation A.toLanguage Z) (ZFC : Z.Sent → Prop)
    (m : ℕ) {P : A.Sent → Prop} (hPB : ∀ b, A.BoolComb (m + 2) b → P b)
    {R' : Z.Sent → Y → Prop} {F₀ : Y → Prop} {T : M.Code}
    (hT : ∀ b, NTs (M := M) m A.Sent T b ↔ P b ∧ Asserted (fun a α => R' (iAZ.i a) α) F₀ b)
    (hH : Z.Closed (Asserted R' F₀)) (hZFC : ∀ β, ZFC β → Asserted R' F₀ β)
    (h1 : A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T)) (snd : Z.Sent)
    (hsnd : Z.Deriv (fun β => ZFC β ∨ β = snd) (iAZ.i (NG₀ A m T))) : ¬ Asserted R' F₀ snd :=
  n_second_incompleteness_H iAZ ZFC (Asserted R' F₀) hH hZFC m T h1
    (fun b hb hHb => A.deriv_of_mem ((hT b).2 ⟨hPB b hb, hHb⟩)) snd hsnd

/-- Corollary 5.21 at level `n = m + 1`, second assertion. -/
theorem n_reading_second_corollary {Y : Type} (iAZ : Translation A.toLanguage Z)
    (ZFC : Z.Sent → Prop) (m : ℕ) {P : A.Sent → Prop} (hPB : ∀ b, A.BoolComb (m + 2) b → P b)
    {R' : Z.Sent → Y → Prop} {F₀ : Y → Prop} {T : M.Code}
    (hT : ∀ b, NTs (M := M) m A.Sent T b ↔ P b ∧ Asserted (fun a α => R' (iAZ.i a) α) F₀ b)
    (hH : Z.Closed (Asserted R' F₀)) (hZFC : ∀ β, ZFC β → Asserted R' F₀ β)
    (h1 : A.SigmaSound (m + 1) (NTs (M := M) m A.Sent T)) (snd enum sndδ : Z.Sent)
    (hsnd : Z.Deriv (fun β => ZFC β ∨ β = snd) (iAZ.i (NG₀ A m T)))
    (hδ : Z.Deriv (fun β => ZFC β ∨ β = enum ∨ β = sndδ) snd) :
    ¬ (Asserted R' F₀ enum ∧ Asserted R' F₀ sndδ) :=
  n_second_incompleteness_H_corollary iAZ ZFC (Asserted R' F₀) hH hZFC m T h1
    (fun b hb hHb => A.deriv_of_mem ((hT b).2 ⟨hPB b hb, hHb⟩)) snd enum sndδ hsnd hδ

/-! ### Theorem 1.1 and Corollary 5.17 at level `n` -/

/-- A `Σ⁰_{m+2}`-definable theory of arithmetic is presented by a machine at level `n = m + 1`
(Corollary 6.3).  In the paper the machine `T_σ` of Lemma 5.16 at level `n` is such a machine, for
a `Σ⁰ₙ₊₁` formula `σ` defining the theory. -/
theorem exists_nmachine_of_isSigmaNSet (m : ℕ) {F : A.Sent → Prop}
    (hF : IsSigmaNSet (M := M) m F) : ∃ T : M.Code, NTs (M := M) m A.Sent T = F := by
  obtain ⟨Mp, ⟨T, hT⟩, hS⟩ := (nStablyCE_iff_isSigmaNSet A.infinite m F).2 hF
  obtain ⟨-, h2⟩ := nseqOf_of_computes (M := M) (m := m) (B := A.Sent) hT
  refine ⟨T, funext fun a => propext ?_⟩
  show NStable m (nseqOf (M := M) m A.Sent T) a ↔ F a
  exact (NStable.of_eq m h2 a).trans (hS a).symm

/-- Theorem 1.1 at level `n = m + 1` (Section 6.3), abstract form.  `H` is a deductively closed
`𝓩`-theory containing `ZFC`.  `F` is a `Σ⁰ₙ₊₁`-definable, `Σₙ`-sound theory of arithmetic with
`F ⊢ b` for every `b ∈ 𝓑ₙ₊₁` with `b* ∈ H`.  Then some machine presents `F` at level `n`.  And for
every machine `T` presenting `F` at level `n`, `sndσ ∉ H` for all sentences `snd`, `sndσ ∈ 𝓩` with
`ZFC ∪ {snd} ⊢ 𝒢ₙ (T)*` and `ZFC ∪ {sndσ} ⊢ snd`.  For `T = T_σ`, `snd = Sndₙ (T_σ)*` and
`sndσ = Sndₙ (σ)*` these two hypotheses are equation (5.12) and Lemma 5.16 at level `n`. -/
theorem n_second_incompleteness_sigma (iAZ : Translation A.toLanguage Z) (ZFC H : Z.Sent → Prop)
    (hH : Z.Closed H) (hZFC : ∀ β, ZFC β → H β) (m : ℕ) (F : A.Sent → Prop)
    (hF : IsSigmaNSet (M := M) m F) (h1 : A.SigmaSound (m + 1) F)
    (hB : ∀ b, A.BoolComb (m + 2) b → H (iAZ.i b) → A.Deriv F b) :
    (∃ T : M.Code, NTs (M := M) m A.Sent T = F) ∧
    ∀ T : M.Code, NTs (M := M) m A.Sent T = F → ∀ snd sndσ : Z.Sent,
      Z.Deriv (fun β => ZFC β ∨ β = snd) (iAZ.i (NG₀ A m T)) →
      Z.Deriv (fun β => ZFC β ∨ β = sndσ) snd → ¬ H sndσ := by
  refine ⟨exists_nmachine_of_isSigmaNSet (A := A) m hF, ?_⟩
  intro T hT snd sndσ hsnd hσ hc
  subst hT
  refine n_second_incompleteness_H iAZ ZFC H hH hZFC m T h1 hB snd hsnd (hH _ ?_)
  -- `snd ∈ H`, as `H` is deductively closed and contains `ZFC` and `sndσ`
  refine Z.deriv_cut (fun β hβ => ?_) hσ
  rcases hβ with hβ | rfl
  · exact Z.deriv_of_mem (hZFC β hβ)
  · exact Z.deriv_of_mem hc

/-- Corollary 5.17 at level `n = m + 1`, abstract form: the simplest case of Theorem 1.1 at level
`n`.  `F` is a `Σ⁰ₙ₊₁`-definable, `Σₙ`-sound theory of arithmetic with `F ⊢ a` for every sentence
`a` with `ZFC ⊢ a*`.  Then some machine presents `F` at level `n`.  And for every machine `T`
presenting `F` at level `n`, `F ⊬ sndσ₀` for all `snd₀`, `sndσ₀ ∈ 𝓐` with
`ZFC ∪ {snd₀*} ⊢ 𝒢ₙ (T)*` and `ZFC ∪ {sndσ₀*} ⊢ snd₀*`.  In the paper `T = T_σ`,
`snd₀ = Sndₙ (T_σ)` and `sndσ₀ = Sndₙ (σ)`. -/
theorem n_second_incompleteness_sigma_simple (iAZ : Translation A.toLanguage Z)
    (ZFC : Z.Sent → Prop) (m : ℕ) (F : A.Sent → Prop) (hF : IsSigmaNSet (M := M) m F)
    (h1 : A.SigmaSound (m + 1) F) (hFZ : ∀ a : A.Sent, Z.Deriv ZFC (iAZ.i a) → A.Deriv F a) :
    (∃ T : M.Code, NTs (M := M) m A.Sent T = F) ∧
    ∀ T : M.Code, NTs (M := M) m A.Sent T = F → ∀ snd₀ sndσ₀ : A.Sent,
      Z.Deriv (fun β => ZFC β ∨ β = iAZ.i snd₀) (iAZ.i (NG₀ A m T)) →
      Z.Deriv (fun β => ZFC β ∨ β = iAZ.i sndσ₀) (iAZ.i snd₀) → ¬ A.Deriv F sndσ₀ := by
  refine ⟨exists_nmachine_of_isSigmaNSet (A := A) m hF, ?_⟩
  intro T hT snd₀ sndσ₀ hsnd hσ
  subst hT
  refine n_second_incompleteness_simple iAZ ZFC m T h1 hFZ sndσ₀ ?_
  -- `ZFC ∪ {sndσ₀*} ⊢ 𝒢ₙ (T)*`, by cut
  refine Z.deriv_cut (fun β hβ => ?_) hsnd
  rcases hβ with hβ | rfl
  · exact Z.deriv_of_mem (Or.inl hβ)
  · exact hσ

end Stable
