import Stable.NSpec

/-!
# The stable halting problem at level `n = m+1` (Section 6.3, Theorem 6.7)

* `NOmega m : 𝒯 → 𝒯` is `Ω^{m+1}` (Lemma 4.1 for `𝒯 × ℕ^{m+1}`): `Ω T ∈ 𝒟^{m+1}_𝒯` and `(Ω T)' = T'`.
* `RW m` and `nsigmaT m : 𝒯 → 𝓐`: "`T` is `Ω^{m+1} (T)`-`(m+1)`-decided" is a `Σ⁰_{m+2}` condition
  (Lemma 4.2 at level `m+1`), and `nsT m T := ¬ nsigmaT m T` (`s_{m+1}`).
* `(m+1)`-stable soundness and completeness, and Theorem 6.7 (`n_stable_halting`).
-/

namespace Stable

open Classical

variable {M : TuringModel}

/-- `Ω^{m+1}`: the map `Ω` of Lemma 4.1 for `(m+1)`-decision maps on `𝒯`. -/
noncomputable def NOmega (M : TuringModel) (m : ℕ) : M.Code → M.Code :=
  choose (exists_Omega (M := M) (B := NB M.Code m))

theorem NOmega_compT (m : ℕ) : CompT M (NOmega M m) :=
  (choose_spec (exists_Omega (M := M) (B := NB M.Code m))).1

theorem NOmega_inDB (m : ℕ) (T : M.Code) : InDB (M := M) (NB M.Code m) (NOmega M m T) :=
  ((choose_spec (exists_Omega (M := M) (B := NB M.Code m))).2 T).1

theorem decOf_NOmega (m : ℕ) (T : M.Code) (x : NB M.Code m) (n : ℕ) :
    decOf (M := M) (NB M.Code m) (NOmega M m T) x n = decOf (M := M) (NB M.Code m) T x n :=
  ((choose_spec (exists_Omega (M := M) (B := NB M.Code m))).2 T).2 x n

/-- `(m+1)`-stable equivalence of `(m+1)`-decision maps on `𝒯`, and `Θ_{D,T}` at level `m+1`:
`T ∈ 𝒟^{m+1}_𝒯` and `T'` is `(m+1)`-stably equivalent to `D`. -/
def NTheta (m : ℕ) (D : NB M.Code m → ℕ → Option Bool) (T : M.Code) : Prop :=
  InDB (M := M) (NB M.Code m) T ∧ ∀ b, NDec m (decOf (M := M) (NB M.Code m) T) b ↔ NDec m D b

/-- If `T'` is `(m+1)`-stably equivalent to `D` then so is `(Ω T)'`. -/
theorem nDec_NOmega_iff_of_equiv {m : ℕ} {T : M.Code} {D : NB M.Code m → ℕ → Option Bool}
    (h : ∀ b, NDec m (decOf (M := M) (NB M.Code m) T) b ↔ NDec m D b) (b : M.Code) :
    NDec m (decOf (M := M) (NB M.Code m) (NOmega M m T)) b ↔ NDec m D b := by
  rw [← h b]
  exact NDec.of_eq m (decOf_NOmega m T) b

/-- The matrix for "`x` is `Ω T`-decided": `(Ω T, e (x, m'), k, 1) ∈ Halt'` and
(`n ≤ m'` or `(Ω T, e (x, n), k', 0) ∉ Halt'`). -/
def RW (m : ℕ) : NRel M.Code M.Code m := fun T x u v =>
  M.run (NOmega M m T) (e M (x, (M.unpair u).1)) (M.unpair u).2 = some 1 ∧
    ((M.unpair v).1 ≤ (M.unpair u).1 ∨
      M.run (NOmega M m T) (e M (x, (M.unpair v).1)) (M.unpair v).2 ≠ some 0)

theorem nRelComp_RW (m : ℕ) : NRelComp (M := M) m (RW (M := M) m) := by
  unfold NRelComp RW
  have hT : CompT M (fun q : M.Code × NB M.Code m × ℕ × ℕ => NOmega M m q.1) :=
    (NOmega_compT m).comp compT_fst
  have hx : CompT M (fun q : M.Code × NB M.Code m × ℕ × ℕ => q.2.1) := compT_fst.comp compT_snd
  have hu1 : CompT M (fun q : M.Code × NB M.Code m × ℕ × ℕ => (M.unpair q.2.2.1).1) :=
    compT_unpair_fst.comp (compT_fst.comp (compT_snd.comp compT_snd))
  have hu2 : CompT M (fun q : M.Code × NB M.Code m × ℕ × ℕ => (M.unpair q.2.2.1).2) :=
    compT_unpair_snd.comp (compT_fst.comp (compT_snd.comp compT_snd))
  have hv1 : CompT M (fun q : M.Code × NB M.Code m × ℕ × ℕ => (M.unpair q.2.2.2).1) :=
    compT_unpair_fst.comp (compT_snd.comp (compT_snd.comp compT_snd))
  have hv2 : CompT M (fun q : M.Code × NB M.Code m × ℕ × ℕ => (M.unpair q.2.2.2).2) :=
    compT_unpair_snd.comp (compT_snd.comp (compT_snd.comp compT_snd))
  have h1 := compSet_halt'.comp (CompT.pair hT (CompT.pair (compT_e.comp (CompT.pair hx hu1))
    (CompT.pair hu2 (compT_const 1))))
  have h2 := compSet_halt'.comp (CompT.pair hT (CompT.pair (compT_e.comp (CompT.pair hx hv1))
    (CompT.pair hv2 (compT_const 0))))
  exact h1.and ((compSet_le hv1 hu1).or h2.not)

/-- `x` is `Ω T`-decided (as a `1`-decision map on `NB 𝒯 m`) iff `∃ u ∀ v, RW (T, x, u, v)`. -/
theorem isDecided_NOmega_iff (m : ℕ) (T : M.Code) (x : NB M.Code m) :
    IsDecided (decOf (M := M) (NB M.Code m) (NOmega M m T)) x ↔ ∃ u, ∀ v, RW (M := M) m T x u v := by
  unfold IsDecided RW
  constructor
  · rintro ⟨m₀, hm, hm'⟩
    obtain ⟨k, hk⟩ := (M.eval_iff _ _ _).1 (decOf_eq_some_iff.1 hm)
    refine ⟨M.pair m₀ k, fun v => ?_⟩
    rw [M.unpair_pair]
    refine ⟨hk, ?_⟩
    by_cases hle : (M.unpair v).1 ≤ m₀
    · exact Or.inl hle
    · right
      intro hrun
      have hd : decOf (M := M) (NB M.Code m) (NOmega M m T) x (M.unpair v).1 = some false :=
        decOf_eq_some_iff.2 (TuringModel.eval_eq_some_of_run hrun)
      rcases hm' (M.unpair v).1 (Nat.le_of_lt (Nat.lt_of_not_le hle)) with h | h
      · rw [h] at hd; cases hd
      · rw [h] at hd; cases hd
  · rintro ⟨u, hu⟩
    have hk : M.run (NOmega M m T) (e M (x, (M.unpair u).1)) (M.unpair u).2 = some 1 := (hu 0).1
    refine ⟨(M.unpair u).1, decOf_eq_some_iff.2 (TuringModel.eval_eq_some_of_run hk), fun n hn => ?_⟩
    cases hd : decOf (M := M) (NB M.Code m) (NOmega M m T) x n with
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
          cases TuringModel.run_unique hk hk'
        · exact h hk'

/-- "`T` is `Ω^{m+1} (T)`-`(m+1)`-decided" as a `Σ⁰_{m+2}` condition on `T` alone. -/
def RWdiag (m : ℕ) : NRel M.Code Unit m := fun T y u v =>
  complPow m (RW (M := M) m) T (nbMapBase m (fun _ : Unit => T) y) u v

theorem nRelComp_RWdiag (m : ℕ) : NRelComp (M := M) m (RWdiag (M := M) m) := by
  have h := (nRelComp_RW (M := M) m).complPow m
  exact h.comp (CompT.pair compT_fst (CompT.pair
    ((compT_nbMapBase_param m (f := fun (T : M.Code) (_ : Unit) => T) (compT_fst)).comp
      (CompT.pair (compT_fst.comp compT_snd) compT_fst))
    (compT_snd.comp compT_snd)))

theorem NSR_RWdiag_iff (m : ℕ) (T : M.Code) :
    NSR m (RWdiag (M := M) m) T () ↔ NDec m (decOf (M := M) (NB M.Code m) (NOmega M m T)) T := by
  unfold RWdiag
  rw [NSR_nbMapBase_param m (complPow m (RW (M := M) m)) (fun T (_ : Unit) => T) T ()]
  exact (NDec_iff_NSR m _ _ T (isDecided_NOmega_iff m T) T).symm

variable (A : Arith M)

/-- `σ_{m+1} : 𝒯 → 𝓐`: the `Σ⁰_{m+2}` sentence expressing "`T` is `Ω^{m+1} (T)`-`(m+1)`-decided". -/
noncomputable def Arith.nsigmaT (m : ℕ) : M.Code → A.Sent := choose (A.reprN m _ (nRelComp_RWdiag m))

theorem Arith.nsigmaT_compT (m : ℕ) : CompT M (A.nsigmaT m) :=
  (choose_spec (A.reprN m _ (nRelComp_RWdiag m))).1

theorem Arith.nsigmaT_sigma (m : ℕ) (T : M.Code) : A.IsSigma (m + 2) (A.nsigmaT m T) :=
  ((choose_spec (A.reprN m _ (nRelComp_RWdiag m))).2 T).1

theorem Arith.trueN_nsigmaT_iff (m : ℕ) (T : M.Code) :
    A.TrueN (A.nsigmaT m T) ↔ NDec m (decOf (M := M) (NB M.Code m) (NOmega M m T)) T := by
  unfold Arith.nsigmaT
  rw [((choose_spec (A.reprN m _ (nRelComp_RWdiag m))).2 T).2, NSR_RWdiag_iff]

/-- `s_{m+1} (T) := ¬ σ_{m+1} (T)`. -/
noncomputable def Arith.nsT (m : ℕ) (T : M.Code) : A.Sent := A.neg (A.nsigmaT m T)

theorem Arith.nsT_compT (m : ℕ) : CompT M (A.nsT m) := A.neg_comp.comp (A.nsigmaT_compT m)

theorem Arith.trueN_nsT_iff (m : ℕ) (T : M.Code) :
    A.TrueN (A.nsT m T) ↔ ¬ NDec m (decOf (M := M) (NB M.Code m) (NOmega M m T)) T := by
  unfold Arith.nsT
  rw [A.trueN_neg, A.trueN_nsigmaT_iff]

/-- `D` is `(m+1)`-stably sound: `T` `D`-`(m+1)`-decided implies `s_{m+1} (T)`. -/
def NStablySound (m : ℕ) (D : NB M.Code m → ℕ → Option Bool) : Prop :=
  ∀ T, NDec m D T → A.TrueN (A.nsT m T)

/-- `D` is `(m+1)`-stably complete: `s_{m+1} (T)` implies `T` is `D`-`(m+1)`-decided. -/
def NStablyComplete (m : ℕ) (D : NB M.Code m → ℕ → Option Bool) : Prop :=
  ∀ T, A.TrueN (A.nsT m T) → NDec m D T

/-- Theorem 6.7 (`theorem_nstablehalting`): no `(m+1)`-decision map `D : 𝒯 × ℕ^{m+1} → {±}`
which is `(m+1)`-stably computed by some `T ∈ 𝒟^{m+1}_𝒯` is `(m+1)`-stably sound and complete;
that is, for such `D` no `T` satisfies `Θ_{D,T}`. (In particular no computable such `D`, as a `T`
computing `D` satisfies `Θ_{D,T}`.) -/
theorem n_stable_halting (m : ℕ) {D : NB M.Code m → ℕ → Option Bool} (hs : NStablySound A m D)
    (hc : NStablyComplete A m D) (T : M.Code) : ¬ NTheta (M := M) m D T := by
  intro hΘ
  have h1 : ¬ NDec m D T := fun hd =>
    ((A.trueN_nsT_iff m T).1 (hs T hd)) ((nDec_NOmega_iff_of_equiv hΘ.2 T).2 hd)
  have h2 : ¬ NDec m (decOf (M := M) (NB M.Code m) (NOmega M m T)) T := fun hd =>
    h1 ((nDec_NOmega_iff_of_equiv hΘ.2 T).1 hd)
  exact h1 (hc T ((A.trueN_nsT_iff m T).2 h2))

end Stable
