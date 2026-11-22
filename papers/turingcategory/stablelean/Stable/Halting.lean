import Stable.Spec

/-!
# The stable halting problem (Section 4)

* `Omega : 𝒯 → 𝒯` (Lemma 4.1): `Ω T ∈ 𝒟_𝒯` and `(Ω T)' = T'` for every `T`.
* `W ⊂ 𝒯 × ℕ × ℕ` (proof of Lemma 4.2): `T` is `Ω T`-decided iff `∃ u ∀ v, (T, u, v) ∈ W`.
* `sigmaT : 𝒯 → 𝓐` (Lemma 4.2): a total computable map with `σ (T) ∈ Σ⁰₂` and
  `ℕ ⊨ σ (T)` iff `T` is `Ω T`-decided; obtained from the representability axiom of `Arith`.
* `s T := ¬ σ (T)` (Definition 4.3); `ℕ ⊨ s T` iff `T` is not `Ω T`-decided.
* Stable soundness and completeness (Definition 4.4), `Θ_{D,T}`, Lemma 4.5 and Theorem 4.6
  (`theorem_stablehalting`): no stably computable `D` is stably sound and complete.
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-- The map `Ω` of Lemma 4.1 (for `B = 𝒯`). -/
noncomputable def Omega (M : TuringModel) : M.Code → M.Code :=
  choose (exists_Omega (M := M) (B := M.Code))

theorem Omega_compT : CompT M (Omega M) := (choose_spec (exists_Omega (M := M) (B := M.Code))).1

theorem Omega_inDB (T : M.Code) : InDB (M := M) M.Code (Omega M T) :=
  ((choose_spec (exists_Omega (M := M) (B := M.Code))).2 T).1

theorem decOf_Omega (T b : M.Code) (n : ℕ) :
    decOf (M := M) M.Code (Omega M T) b n = decOf (M := M) M.Code T b n :=
  ((choose_spec (exists_Omega (M := M) (B := M.Code))).2 T).2 b n

/-- Lemma 4.1 (2): if `T ∈ 𝒟_𝒯` stably computes `D` then so does `Ω T`; in fact `(Ω T)' = T'`
always, so `T` is `D`-decided iff `T` is `Ω T`-decided whenever `T'` is stably equivalent to `D`. -/
theorem tDecided_Omega_iff_of_stablyEquiv {T : M.Code} {D : M.Code → ℕ → Option Bool}
    (h : StablyEquiv (decOf (M := M) M.Code T) D) (b : M.Code) :
    TDecided (M := M) (Omega M T) b ↔ IsDecided D b := by
  unfold TDecided
  rw [← h b]
  exact ⟨IsDecided.of_eq (decOf_Omega T), IsDecided.of_eq fun b n => (decOf_Omega T b n).symm⟩

/-- The relation `W` of the proof of Lemma 4.2: `(T, ⟨m, k⟩, ⟨n, k'⟩) ∈ W` iff
`(Ω T, e (T, m), k, 1) ∈ Halt'` and (`n ≤ m` or `(Ω T, e (T, n), k', 0) ∉ Halt'`). -/
def W (T : M.Code) (u v : ℕ) : Prop :=
  M.run (Omega M T) (e M (T, (M.unpair u).1)) (M.unpair u).2 = some 1 ∧
    ((M.unpair v).1 ≤ (M.unpair u).1 ∨
      M.run (Omega M T) (e M (T, (M.unpair v).1)) (M.unpair v).2 ≠ some 0)

theorem compSet_W : CompSet M (fun q : M.Code × ℕ × ℕ => W q.1 q.2.1 q.2.2) := by
  have hT : CompT M (fun q : M.Code × ℕ × ℕ => Omega M q.1) := Omega_compT.comp compT_fst
  have hu1 : CompT M (fun q : M.Code × ℕ × ℕ => (M.unpair q.2.1).1) :=
    compT_unpair_fst.comp (compT_fst.comp compT_snd)
  have hu2 : CompT M (fun q : M.Code × ℕ × ℕ => (M.unpair q.2.1).2) :=
    compT_unpair_snd.comp (compT_fst.comp compT_snd)
  have hv1 : CompT M (fun q : M.Code × ℕ × ℕ => (M.unpair q.2.2).1) :=
    compT_unpair_fst.comp (compT_snd.comp compT_snd)
  have hv2 : CompT M (fun q : M.Code × ℕ × ℕ => (M.unpair q.2.2).2) :=
    compT_unpair_snd.comp (compT_snd.comp compT_snd)
  have h1 : CompSet M (fun q : M.Code × ℕ × ℕ =>
      M.run (Omega M q.1) (e M (q.1, (M.unpair q.2.1).1)) (M.unpair q.2.1).2 = some 1) :=
    compSet_halt'.comp (CompT.pair hT (CompT.pair (compT_e.comp (CompT.pair compT_fst hu1))
      (CompT.pair hu2 (compT_const 1))))
  have h2 : CompSet M (fun q : M.Code × ℕ × ℕ =>
      M.run (Omega M q.1) (e M (q.1, (M.unpair q.2.2).1)) (M.unpair q.2.2).2 = some 0) :=
    compSet_halt'.comp (CompT.pair hT (CompT.pair (compT_e.comp (CompT.pair compT_fst hv1))
      (CompT.pair hv2 (compT_const 0))))
  exact h1.and ((compSet_le hv1 hu1).or h2.not)

theorem e_true : e M (true : Bool) = 1 := rfl
theorem e_false : e M (false : Bool) = 0 := rfl

/-- `T` is `Ω T`-decided iff `∃ u ∀ v, (T, u, v) ∈ W`. -/
theorem tDecided_Omega_iff (T : M.Code) : TDecided (M := M) (Omega M T) T ↔ ∃ u, ∀ v, W T u v := by
  unfold TDecided IsDecided W
  constructor
  · rintro ⟨m, hm, hm'⟩
    obtain ⟨k, hk⟩ := (M.eval_iff _ _ _).1 (decOf_eq_some_iff.1 hm)
    refine ⟨M.pair m k, fun v => ?_⟩
    rw [M.unpair_pair]
    refine ⟨hk, ?_⟩
    by_cases hle : (M.unpair v).1 ≤ m
    · exact Or.inl hle
    · right
      intro hrun
      have hd : decOf (M := M) M.Code (Omega M T) T (M.unpair v).1 = some false :=
        decOf_eq_some_iff.2 (TuringModel.eval_eq_some_of_run hrun)
      rcases hm' (M.unpair v).1 (Nat.le_of_lt (Nat.lt_of_not_le hle)) with h | h
      · rw [h] at hd; cases hd
      · rw [h] at hd; cases hd
  · rintro ⟨u, hu⟩
    have hk : M.run (Omega M T) (e M (T, (M.unpair u).1)) (M.unpair u).2 = some 1 := (hu 0).1
    refine ⟨(M.unpair u).1, decOf_eq_some_iff.2 (TuringModel.eval_eq_some_of_run hk), fun n hn => ?_⟩
    cases hd : decOf (M := M) M.Code (Omega M T) T n with
    | none => exact Or.inr rfl
    | some s =>
      cases s with
      | true => exact Or.inl rfl
      | false =>
        exfalso
        obtain ⟨k', hk'⟩ := (M.eval_iff _ _ _).1 (decOf_eq_some_iff.1 hd)
        have := (hu (M.pair n k')).2
        rw [M.unpair_pair] at this
        rcases this with h | h
        · have hnm : n = (M.unpair u).1 := Nat.le_antisymm h hn
          rw [hnm] at hk'
          have := TuringModel.run_unique hk hk'
          cases this
        · exact h hk'

variable (A : Arith M)

/-- The map `σ : 𝒯 → 𝓐` of Lemma 4.2, from the representability axiom applied to `W`. -/
noncomputable def Arith.sigmaT : M.Code → A.Sent := choose (A.repr W compSet_W)

theorem Arith.sigmaT_compT : CompT M A.sigmaT := (choose_spec (A.repr W compSet_W)).1

theorem Arith.sigmaT_sigma2 (T : M.Code) : A.IsSigma 2 (A.sigmaT T) :=
  ((choose_spec (A.repr W compSet_W)).2 T).1

/-- Lemma 4.2: `ℕ ⊨ σ (T)` iff `T` is `Ω T`-decided. -/
theorem Arith.trueN_sigmaT_iff (T : M.Code) :
    A.TrueN (A.sigmaT T) ↔ TDecided (M := M) (Omega M T) T := by
  unfold Arith.sigmaT
  rw [((choose_spec (A.repr W compSet_W)).2 T).2, tDecided_Omega_iff]

/-- Definition 4.3: `s (T) := ¬ σ (T)`. -/
noncomputable def Arith.sT (T : M.Code) : A.Sent := A.neg (A.sigmaT T)

theorem Arith.sT_compT : CompT M A.sT := A.neg_comp.comp A.sigmaT_compT

/-- `ℕ ⊨ s (T)` iff `T` is not `Ω T`-decided. -/
theorem Arith.trueN_sT_iff (T : M.Code) : A.TrueN (A.sT T) ↔ ¬ TDecided (M := M) (Omega M T) T := by
  unfold Arith.sT
  rw [A.trueN_neg, A.trueN_sigmaT_iff]

/-! ### Stable soundness and completeness (Definition 4.4) -/

/-- `D : 𝒯 × ℕ → {±}` is stably sound: `T` `D`-decided implies `s (T)`. -/
def StablySound (D : M.Code → ℕ → Option Bool) : Prop :=
  ∀ T, IsDecided D T → A.TrueN (A.sT T)

/-- `D` stably decides `T`: `s (T)` implies `T` is `D`-decided. -/
def StablyDecides (D : M.Code → ℕ → Option Bool) (T : M.Code) : Prop :=
  A.TrueN (A.sT T) → IsDecided D T

/-- `D` is stably sound and complete. -/
def StablySoundComplete (D : M.Code → ℕ → Option Bool) : Prop :=
  StablySound A D ∧ ∀ T, StablyDecides A D T

/-- Lemma 4.5 (`lemma_Dstablysound`): if `D` is stably sound then for all `T`, `¬Θ_{D,T}` or
`T` is not `D`-decided. -/
theorem not_theta_or_not_decided {D : M.Code → ℕ → Option Bool} (hD : StablySound A D) (T : M.Code) :
    ¬ Theta (M := M) D T ∨ ¬ IsDecided D T := by
  by_cases hdec : IsDecided D T
  · left
    rintro ⟨_, hequiv⟩
    have h1 : ¬ TDecided (M := M) (Omega M T) T := (A.trueN_sT_iff T).1 (hD T hdec)
    exact h1 ((tDecided_Omega_iff_of_stablyEquiv hequiv T).2 hdec)
  · exact Or.inr hdec

/-- Theorem 4.6 (`theorem_stablehalting`): there is no stably computable `D : 𝒯 × ℕ → {±}`
which is stably sound and complete, i.e. for such `D` no `T ∈ 𝒟_𝒯` stably computes `D`. -/
theorem stable_halting {D : M.Code → ℕ → Option Bool} (hD : StablySoundComplete A D) (T : M.Code) :
    ¬ Theta (M := M) D T := by
  intro hΘ
  -- (4.7): `Θ_{D,T} → ¬ (T is D-decided)`
  have h1 : ¬ IsDecided D T := by
    rcases not_theta_or_not_decided A hD.1 T with h | h
    · exact absurd hΘ h
    · exact h
  -- (4.8): `Θ_{D,T} → (¬ D-decided → ¬ Ω T-decided)`, hence `s (T)`
  have h2 : ¬ TDecided (M := M) (Omega M T) T := fun hd =>
    h1 ((tDecided_Omega_iff_of_stablyEquiv hΘ.2 T).1 hd)
  -- completeness: `s (T) → T is D-decided`
  exact h1 (hD.2 T ((A.trueN_sT_iff T).2 h2))

end Stable
