import Stable.Enc

/-!
# Stable computability and decision maps (Section 3 of the paper)

* `IsStable M b` — `b` is `M`-stable (Definition 1.2 / 3.1) for a partial map
  `M : ℕ → B × {±}`, modelled as `M : ℕ → Option (B × Bool)` with `true = +`;
  `Stab M` is the stabilization `M^s`.
* `IsDecided D b` — `b` is `D`-decided (Definition 3.4) for a decision map
  `D : B × ℕ → {±}`, modelled as `D : B → ℕ → Option Bool`; `Decided D` is `D^d`.
* Remark 3.5 (`remark_dectoseq`): the passage `D ↦ M_D` (for infinite `B`) and `M ↦ D_M`,
  with `M_D^s = D^d` and `D_M^d = M^s`.
* Lemma 3.6, the stabilizer lemma: for a computable `R ⊂ A × B × ℕ × ℕ` the total computable
  decision map `D_R` with `D_R (a,·,·)^d = S_R (a) = {b | ∃ u ∀ v, R a b u v}`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

section Defs

variable {B : Type}

/-- `b` is `M`-stable: there is `m` with `M m = (b, +)` such that for every `n > m` with
`M n = (b, s)` we have `s = +` (Definition 1.2). -/
def IsStable (Mp : ℕ → Option (B × Bool)) (b : B) : Prop :=
  ∃ m, Mp m = some (b, true) ∧ ∀ n, m < n → ∀ s, Mp n = some (b, s) → s = true

/-- The stabilization `M^s ⊂ B` of `M`. -/
def Stab (Mp : ℕ → Option (B × Bool)) : B → Prop := fun b => IsStable Mp b

/-- `b` is `D`-decided: there is `m` with `D (b, m) = +` such that for all `n ≥ m`,
`D (b, n) = +` or `D (b, n)` is undefined (Definition 3.4). -/
def IsDecided (D : B → ℕ → Option Bool) (b : B) : Prop :=
  ∃ m, D b m = some true ∧ ∀ n, m ≤ n → D b n = some true ∨ D b n = none

/-- The set `D^d ⊂ B` of `D`-decided elements. -/
def Decided (D : B → ℕ → Option Bool) : B → Prop := fun b => IsDecided D b

/-- Two decision maps are stably equivalent (Definition 3.20) if they decide the same elements. -/
def StablyEquiv (D₀ D₁ : B → ℕ → Option Bool) : Prop := ∀ b, IsDecided D₀ b ↔ IsDecided D₁ b

theorem IsStable.of_eq {Mp Np : ℕ → Option (B × Bool)} (h : ∀ n, Mp n = Np n) {b : B}
    (hb : IsStable Mp b) : IsStable Np b := by
  obtain ⟨m, hm, hm'⟩ := hb
  exact ⟨m, (h m).symm.trans hm, fun n hn s hs => hm' n hn s ((h n).trans hs)⟩

theorem IsDecided.of_eq {D D' : B → ℕ → Option Bool} (h : ∀ b n, D b n = D' b n) {b : B}
    (hb : IsDecided D b) : IsDecided D' b := by
  obtain ⟨m, hm, hm'⟩ := hb
  refine ⟨m, (h b m).symm.trans hm, fun n hn => ?_⟩
  rw [← h b n]; exact hm' n hn

/-- For a total decision map, being decided means the verdict is eventually constantly `+`. -/
theorem isDecided_total {D : B → ℕ → Bool} {b : B} :
    IsDecided (fun b n => some (D b n)) b ↔ ∃ m, ∀ n, m ≤ n → D b n = true := by
  constructor
  · rintro ⟨m, _, hm'⟩
    refine ⟨m, fun n hn => ?_⟩
    rcases hm' n hn with h | h
    · exact Option.some.inj h
    · cases h
  · rintro ⟨m, hm⟩
    exact ⟨m, by simp [hm m (Nat.le_refl m)], fun n hn => Or.inl (by simp [hm n hn])⟩

end Defs

/-! ## Decision maps versus sequences (Remark 3.5) -/

section DecToSeq

variable {B : Type} [Enc M B]

/-- The decision map `D_M` associated with `M : ℕ → B × {±}`: `D_M (b, n) = ±` if `M n = (b, ±)`,
undefined otherwise. -/
noncomputable def decOfSeq (Mp : ℕ → Option (B × Bool)) (b : B) (n : ℕ) : Option Bool :=
  match Mp n with
  | some (b', s) => if b' = b then some s else none
  | none => none

theorem decOfSeq_eq_some_iff {Mp : ℕ → Option (B × Bool)} {b : B} {n : ℕ} {s : Bool} :
    decOfSeq Mp b n = some s ↔ Mp n = some (b, s) := by
  unfold decOfSeq
  cases h : Mp n with
  | none => simp
  | some p =>
    obtain ⟨b', s'⟩ := p
    by_cases hb : b' = b
    · subst hb; simp
    · simp [hb]

/-- `D_M^d = M^s`. -/
theorem isDecided_decOfSeq_iff (Mp : ℕ → Option (B × Bool)) (b : B) :
    IsDecided (decOfSeq Mp) b ↔ IsStable Mp b := by
  constructor
  · rintro ⟨m, hm, hm'⟩
    refine ⟨m, decOfSeq_eq_some_iff.1 hm, fun n hn s hs => ?_⟩
    have := decOfSeq_eq_some_iff.2 hs
    rcases hm' n (Nat.le_of_lt hn) with h | h
    · rw [h] at this; exact (Option.some.inj this).symm
    · rw [h] at this; cases this
  · rintro ⟨m, hm, hm'⟩
    refine ⟨m, decOfSeq_eq_some_iff.2 hm, fun n hn => ?_⟩
    cases h : decOfSeq Mp b n with
    | none => exact Or.inr rfl
    | some s =>
      left
      rcases Nat.eq_or_lt_of_le hn with rfl | hlt
      · rw [decOfSeq_eq_some_iff] at h; rw [hm] at h
        cases h; rfl
      · rw [hm' n hlt s (decOfSeq_eq_some_iff.1 h)]

/-- `D_M` is computable when `M` is. -/
theorem comp_decOfSeq {Mp : ℕ → Option (B × Bool)} (hM : Comp M Mp) :
    Comp M (fun p : B × ℕ => decOfSeq Mp p.1 p.2) := by
  -- `(b, n) ↦ M n`, then keep the sign iff the first component is `b`
  have h1 : Comp M (fun p : B × ℕ => (Mp p.2).map (fun q => (p.1, q))) :=
    (compT_fst.toComp.pair (hM.compT compT_snd)).congr fun p => by
      cases Mp p.2 <;> simp [Option.bind, Option.map]
  have h2 : Comp M (fun q : B × (B × Bool) => if q.2.1 = q.1 then some q.2.2 else none) :=
    Comp.cases (compSet_eq (compT_fst.comp compT_snd) compT_fst) (compT_snd.comp compT_snd) comp_none
  refine (h2.comp h1).congr fun p => ?_
  unfold decOfSeq
  cases h : Mp p.2 with
  | none => simp [Option.bind]
  | some q => obtain ⟨b', s⟩ := q; simp [Option.bind, Option.map]

/-- The map `M_D` associated with a decision map `D` on an infinite `B`:
`M_D (ι (b, t)) = (b, D (b, t))`, where `ι (b, t) = ⟨ε_B b, t⟩` (Remark 3.5). -/
noncomputable def seqOfDec (D : B → ℕ → Option Bool) (n : ℕ) : Option (B × Bool) :=
  (epsilonInv (M := M) B (M.unpair n).1).bind fun b => (D b (M.unpair n).2).map fun s => (b, s)

/-- `ι (b, t) = ⟨ε_B b, t⟩`. -/
noncomputable def iota (b : B) (t : ℕ) : ℕ := M.pair (epsilon (M := M) b) t

theorem seqOfDec_iota (D : B → ℕ → Option Bool) (b : B) (t : ℕ) :
    seqOfDec (M := M) D (iota (M := M) b t) = (D b t).map fun s => (b, s) := by
  unfold seqOfDec iota
  rw [M.unpair_pair]
  simp only [epsilonInv_epsilon, Option.bind_some]

theorem seqOfDec_eq_some_iff {D : B → ℕ → Option Bool} {n : ℕ} {b : B} {s : Bool} :
    seqOfDec (M := M) D n = some (b, s) ↔
      n = iota (M := M) b (M.unpair n).2 ∧ D b (M.unpair n).2 = some s := by
  unfold seqOfDec iota
  constructor
  · intro h
    cases he : epsilonInv (M := M) B (M.unpair n).1 with
    | none => rw [he] at h; cases h
    | some b' =>
      rw [he] at h
      simp only [Option.bind_some] at h
      cases hd : D b' (M.unpair n).2 with
      | none => rw [hd] at h; cases h
      | some s' =>
        rw [hd] at h
        simp only [Option.map_some] at h
        have h' := Option.some.inj h
        cases h'
        have hk := epsilonInv_eq_some_iff.1 he
        refine ⟨?_, hd⟩
        rw [hk, M.pair_unpair]
  · rintro ⟨hn, hd⟩
    have hk : (M.unpair n).1 = epsilon (M := M) b := by
      have := congrArg (fun x => (M.unpair x).1) hn
      rw [M.unpair_pair] at this; exact this
    rw [hk, epsilonInv_epsilon, Option.bind_some, hd]; rfl

/-- `M_D^s = D^d` (Remark 3.5). -/
theorem isStable_seqOfDec_iff (D : B → ℕ → Option Bool) (b : B) :
    IsStable (seqOfDec (M := M) D) b ↔ IsDecided D b := by
  constructor
  · rintro ⟨m, hm, hm'⟩
    obtain ⟨hmi, hDm⟩ := seqOfDec_eq_some_iff.1 hm
    refine ⟨(M.unpair m).2, hDm, fun t ht => ?_⟩
    rcases Nat.eq_or_lt_of_le ht with rfl | hlt
    · exact Or.inl hDm
    · cases hd : D b t with
      | none => exact Or.inr rfl
      | some s =>
        left
        have hn : iota (M := M) b t > m := by
          rw [hmi]; exact M.pair_lt_right _ hlt
        have := hm' _ hn s (by rw [seqOfDec_iota, hd]; rfl)
        rw [this]
  · rintro ⟨t₀, ht₀, ht₀'⟩
    refine ⟨iota (M := M) b t₀, by rw [seqOfDec_iota, ht₀]; rfl, fun n hn s hs => ?_⟩
    obtain ⟨hni, hDn⟩ := seqOfDec_eq_some_iff.1 hs
    -- `n = ι (b, t)` with `t > t₀`, by monotonicity of `ι (b, ·)`
    have ht : t₀ < (M.unpair n).2 := by
      refine Classical.byContradiction fun hc => ?_
      have hle : (M.unpair n).2 ≤ t₀ := Nat.le_of_not_lt hc
      have : n ≤ iota (M := M) b t₀ := by
        rw [hni]
        rcases Nat.eq_or_lt_of_le hle with h | h
        · rw [h]; exact Nat.le_refl _
        · exact Nat.le_of_lt (M.pair_lt_right _ h)
      exact Nat.not_lt.2 this hn
    rcases ht₀' _ (Nat.le_of_lt ht) with h | h
    · rw [h] at hDn; exact (Option.some.inj hDn).symm
    · rw [h] at hDn; cases hDn

theorem compT_unpair_fst : CompT M (fun n : ℕ => (M.unpair n).1) := TuringModel.isCompT_fst
theorem compT_unpair_snd : CompT M (fun n : ℕ => (M.unpair n).2) := TuringModel.isCompT_snd

/-- `M_D` is computable when `D` is. -/
theorem comp_seqOfDec {D : B → ℕ → Option Bool} (hD : Comp M (fun p : B × ℕ => D p.1 p.2)) :
    Comp M (seqOfDec (M := M) D) := by
  -- `n ↦ (ε⁻¹ (unpair n).1, (unpair n).2)`, then `(b, t) ↦ (b, D b t)`
  have h1 : Comp M (fun n : ℕ => (epsilonInv (M := M) B (M.unpair n).1).map
      fun b => (b, (M.unpair n).2)) := by
    have := Comp.pair (M := M) ((comp_epsilonInv (A := B)).compT compT_unpair_fst)
      compT_unpair_snd.toComp
    exact this.congr fun n => by
      cases epsilonInv (M := M) B (M.unpair n).1 <;> simp [Option.bind, Option.map]
  have h2 : Comp M (fun p : B × ℕ => (D p.1 p.2).map fun s => (p.1, s)) :=
    (compT_fst.toComp.pair hD).congr fun p => by
      cases D p.1 p.2 <;> simp [Option.bind, Option.map]
  refine (h2.comp h1).congr fun n => ?_
  unfold seqOfDec
  cases epsilonInv (M := M) B (M.unpair n).1 <;> simp [Option.bind, Option.map]

/-- For infinite `B`, `M_D` is total when `D` is. -/
theorem seqOfDec_total (hB : Enc.Infinite M B) {D : B → ℕ → Option Bool}
    (hD : ∀ b n, D b n ≠ none) (n : ℕ) : seqOfDec (M := M) D n ≠ none := by
  unfold seqOfDec
  cases he : epsilonInv (M := M) B (M.unpair n).1 with
  | none => exact absurd he (epsilonInv_isSome hB _)
  | some b =>
    simp only [Option.bind_some]
    cases hd : D b (M.unpair n).2 with
    | none => exact absurd hd (hD b _)
    | some s => simp

end DecToSeq

/-! ## The stabilizer lemma (Lemma 3.6) -/

section Stabilizer

variable {A B : Type} [Enc M A] [Enc M B]

theorem compT_pred : CompT M (fun n : ℕ => n - 1) := TuringModel.isCompT_pred

/-- `S_R (a) = {b | ∃ u ∀ v, R a b u v}`. -/
def SR (R : A → B → ℕ → ℕ → Prop) (a : A) (b : B) : Prop := ∃ u, ∀ v, R a b u v

/-- `c_t (a, b)`: the least `u ≤ t` such that `R a b u v` for all `v ≤ t`, if it exists. -/
noncomputable def cT (R : A → B → ℕ → ℕ → Prop) (a : A) (b : B) (t : ℕ) : Option ℕ :=
  bmin (fun (q : A × B × ℕ) u => ∀ v, v ≤ q.2.2 → R q.1 q.2.1 u v) (a, b, t) t

theorem cT_eq_some_iff {R : A → B → ℕ → ℕ → Prop} {a : A} {b : B} {t u : ℕ} :
    cT R a b t = some u ↔
      u ≤ t ∧ (∀ v, v ≤ t → R a b u v) ∧ ∀ u' < u, ∃ v, v ≤ t ∧ ¬ R a b u' v := by
  unfold cT
  rw [bmin_eq_some_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun u' hu' => ?_⟩
    have := h3 u' hu'
    refine Classical.byContradiction fun hc => this fun v hv => ?_
    exact Classical.byContradiction fun hr => hc ⟨v, hv, hr⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun u' hu' hall => ?_⟩
    obtain ⟨v, hv, hr⟩ := h3 u' hu'
    exact hr (hall v hv)

theorem cT_eq_none_iff {R : A → B → ℕ → ℕ → Prop} {a : A} {b : B} {t : ℕ} :
    cT R a b t = none ↔ ∀ u, u ≤ t → ∃ v, v ≤ t ∧ ¬ R a b u v := by
  unfold cT
  rw [bmin_eq_none_iff]
  constructor
  · intro h u hu
    have := h u hu
    refine Classical.byContradiction fun hc => this fun v hv => ?_
    exact Classical.byContradiction fun hr => hc ⟨v, hv, hr⟩
  · intro h u hu hall
    obtain ⟨v, hv, hr⟩ := h u hu
    exact hr (hall v hv)

/-- The decision map `D_R` of the stabilizer lemma: `D_R (a, b, 0) = -`, and
`D_R (a, b, t+1) = +` iff `c_{t+1} (a,b)` and `c_t (a,b)` are both defined and equal. -/
noncomputable def DR (R : A → B → ℕ → ℕ → Prop) (a : A) (b : B) : ℕ → Bool
  | 0 => false
  | t + 1 => (cT R a b (t + 1)).isSome && decide (cT R a b (t + 1) = cT R a b t)

theorem DR_zero {R : A → B → ℕ → ℕ → Prop} {a : A} {b : B} : DR R a b 0 = false := rfl

theorem DR_succ_eq_true_iff {R : A → B → ℕ → ℕ → Prop} {a : A} {b : B} {t : ℕ} :
    DR R a b (t + 1) = true ↔ ∃ u, cT R a b (t + 1) = some u ∧ cT R a b t = some u := by
  show ((cT R a b (t + 1)).isSome && decide (cT R a b (t + 1) = cT R a b t)) = true ↔ _
  cases h1 : cT R a b (t + 1) with
  | none => simp
  | some u =>
    cases h2 : cT R a b t with
    | none => simp
    | some u' =>
      simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨u, rfl, rfl⟩
      · rintro ⟨w, hw, hw'⟩; cases hw; cases hw'; rfl

/-- Lemma 3.6, correctness: `b` is `D_R (a, ·, ·)`-decided iff `b ∈ S_R (a)`. -/
theorem isDecided_DR_iff (R : A → B → ℕ → ℕ → Prop) (a : A) (b : B) :
    IsDecided (fun b t => some (DR R a b t)) b ↔ SR R a b := by
  rw [isDecided_total]
  constructor
  · rintro ⟨m, hm⟩
    -- from `m` on, `c_t` is constant, say `= u`; then `∀ v, R a b u v`
    have hm1 : m ≤ m + 1 := Nat.le_succ m
    obtain ⟨u, hu, hu'⟩ := DR_succ_eq_true_iff.1 (hm (m + 1) hm1)
    -- `c_t = some u` for all `t ≥ m`, by induction
    have hconst : ∀ k, cT R a b (m + k) = some u := by
      intro k
      induction k with
      | zero => exact hu'
      | succ k ih =>
        obtain ⟨w, hw, hw'⟩ := DR_succ_eq_true_iff.1 (hm (m + k + 1) (by omega))
        rw [ih] at hw'
        cases hw'; exact hw
    have hconst' : ∀ t, m ≤ t → cT R a b t = some u := fun t ht => by
      obtain ⟨k, rfl⟩ : ∃ k, t = m + k := ⟨t - m, by omega⟩
      exact hconst k
    refine ⟨u, fun v => ?_⟩
    have ht : m ≤ max m v := Nat.le_max_left m v
    obtain ⟨_, h2, _⟩ := cT_eq_some_iff.1 (hconst' (max m v) ht)
    exact h2 v (Nat.le_max_right m v)
  · rintro ⟨u, hu⟩
    -- let `u₀` be the least `u` with `∀ v, R a b u v`
    obtain ⟨u₀, hu₀, hu₀'⟩ := exists_least (P := fun u => ∀ v, R a b u v) ⟨u, hu⟩
    -- each `u' < u₀` fails at some `v`; let `t₁` bound all these `v`
    have hfail : ∀ u' < u₀, ∃ v, ¬ R a b u' v := fun u' hu' =>
      Classical.byContradiction fun hc => hu₀' u' hu' fun v =>
        Classical.byContradiction fun hr => hc ⟨v, hr⟩
    obtain ⟨t₁, ht₁⟩ : ∃ t₁, ∀ u' < u₀, ∃ v, v ≤ t₁ ∧ ¬ R a b u' v := by
      -- bound the witnesses below `u₀` by a finite maximum, by induction on `u₀`
      have key : ∀ k, k ≤ u₀ → ∃ t₁, ∀ u' < k, ∃ v, v ≤ t₁ ∧ ¬ R a b u' v := by
        intro k
        induction k with
        | zero => intro _; exact ⟨0, fun u' h => absurd h (Nat.not_lt_zero u')⟩
        | succ k ih =>
          intro hk
          obtain ⟨t, ht⟩ := ih (Nat.le_of_succ_le hk)
          obtain ⟨v, hv⟩ := hfail k hk
          refine ⟨max t v, fun u' hu' => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hu' with h | rfl
          · obtain ⟨w, hw, hw'⟩ := ht u' h
            exact ⟨w, Nat.le_trans hw (Nat.le_max_left t v), hw'⟩
          · exact ⟨v, Nat.le_max_right t v, hv⟩
      exact key u₀ (Nat.le_refl u₀)
    -- for `t ≥ max u₀ t₁`, `c_t = some u₀`
    have hconst : ∀ t, max u₀ t₁ ≤ t → cT R a b t = some u₀ := by
      intro t ht
      rw [cT_eq_some_iff]
      refine ⟨Nat.le_trans (Nat.le_max_left u₀ t₁) ht, fun v _ => hu₀ v, fun u' hu' => ?_⟩
      obtain ⟨v, hv, hr⟩ := ht₁ u' hu'
      exact ⟨v, Nat.le_trans hv (Nat.le_trans (Nat.le_max_right u₀ t₁) ht), hr⟩
    refine ⟨max u₀ t₁ + 1, fun n hn => ?_⟩
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    rw [DR_succ_eq_true_iff]
    exact ⟨u₀, hconst (t + 1) (by omega), hconst t (by omega)⟩

/-- Lemma 3.6, computability: `D_R : A × B × ℕ → {±}` is total computable when `R` is a
computable subset of `A × B × ℕ × ℕ`. -/
theorem compT_DR {R : A → B → ℕ → ℕ → Prop}
    (hR : CompSet M (fun q : A × B × ℕ × ℕ => R q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    CompT M (fun q : A × B × ℕ => DR R q.1 q.2.1 q.2.2) := by
  -- `c : A × B × ℕ → Option ℕ` is total computable
  have hP : CompSet M (fun p : (A × B × ℕ) × ℕ => ∀ v, v ≤ p.1.2.2 → R p.1.1 p.1.2.1 p.2 v) := by
    have h0 : CompSet M (fun p : ((A × B × ℕ) × ℕ) × ℕ => R p.1.1.1 p.1.1.2.1 p.1.2 p.2) :=
      hR.comp (CompT.pair (compT_fst.comp (compT_fst.comp compT_fst))
        (CompT.pair (compT_fst.comp (compT_snd.comp (compT_fst.comp compT_fst)))
          (CompT.pair (compT_snd.comp compT_fst) compT_snd)))
    have h1 := CompSet.ballLe (P := fun (p : (A × B × ℕ) × ℕ) v => R p.1.1 p.1.2.1 p.2 v) h0
    exact h1.comp (CompT.pair compT_id (compT_snd.comp (compT_snd.comp compT_fst)))
  have hc : CompT M (fun q : A × B × ℕ => cT R q.1 q.2.1 q.2.2) := by
    have := (compT_bmin (P := fun (q : A × B × ℕ) u => ∀ v, v ≤ q.2.2 → R q.1 q.2.1 u v) hP).comp
      (CompT.pair (compT_id (A := A × B × ℕ)) (compT_snd.comp compT_snd))
    exact this.congr fun q => rfl
  have hc1 : CompT M (fun q : A × B × ℕ => cT R q.1 q.2.1 (q.2.2 + 1)) :=
    hc.comp (CompT.pair compT_fst (CompT.pair (compT_fst.comp compT_snd)
      (compT_succ.comp (compT_snd.comp compT_snd))))
  have hcm : CompT M (fun q : A × B × ℕ => cT R q.1 q.2.1 (q.2.2 - 1)) :=
    hc.comp (CompT.pair compT_fst (CompT.pair (compT_fst.comp compT_snd)
      (compT_pred.comp (compT_snd.comp compT_snd))))
  -- `D_R q = [q.2.2 ≠ 0 ∧ c (t) ≠ none ∧ c (t) = c (t-1)]` where `t = q.2.2`
  have hset : CompSet M (fun q : A × B × ℕ =>
      q.2.2 ≠ 0 ∧ cT R q.1 q.2.1 q.2.2 ≠ none ∧ cT R q.1 q.2.1 q.2.2 = cT R q.1 q.2.1 (q.2.2 - 1)) :=
    ((compSet_eq (compT_snd.comp compT_snd) (compT_const 0)).not).and
      (((compSet_eq hc (compT_const none)).not).and (compSet_eq hc hcm))
  refine hset.toCompT.congr fun q => ?_
  obtain ⟨a, b, t⟩ := q
  cases t with
  | zero => simp [DR]
  | succ t =>
    simp only [Nat.succ_ne_zero, ne_eq, not_false_eq_true, true_and, Nat.add_sub_cancel]
    cases h1 : cT R a b (t + 1) with
    | none => simp [DR, h1]
    | some u =>
      cases h2 : cT R a b t with
      | none => simp [DR, h1, h2]
      | some u' =>
        simp only [DR, h1, h2, Option.some.injEq, reduceCtorEq, not_false_eq_true, true_and]
        by_cases h : u = u'
        · subst h; simp
        · simp [h]

end Stabilizer

end Stable
