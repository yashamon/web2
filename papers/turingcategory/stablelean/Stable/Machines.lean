import Stable.Stab

/-!
# Machines computing sequences and decision maps (Sections 3.2, 4)

* `seqOf T : ℕ → Option (B × Bool)` — the map `T'` of Definition 3.9 (`𝒯_B`), defined for every
  `T` as `e⁻¹ ∘ T`; `InTB T` says `T ∈ 𝒯_B`, i.e. `T` lands in the image of `e_{B × {±}}`, and then
  `T` computes `seqOf T`.
* `decOf T : B → ℕ → Option Bool` — the map `T'` of Definition 3.8 (`𝒟_B`); `InDB T` says `T ∈ 𝒟_B`.
* `Ts T = (T')^s` (Notation 3.21), `TStable`, `TDecided` (Definition 3.10).
* Lemma 3.13 (`κ`, written `K` in earlier versions of the manuscript; `exists_K` here), Lemma 4.1 (`Ω`).
* The uniform stabilizer machines: for a computable `R ⊂ 𝒯 × B × ℕ × ℕ` total computable
  `stabMachine R : 𝒯 → 𝒯_B` and `decMachine R : 𝒯 → 𝒟_B` whose stabilization / decided set at `T`
  is `S_R (T)`.  `Dec_B` (Definition 3.14) and Lemma 3.16 (`lemma_convert`) are the instance
  `R = R_B`; Lemma 3.22 (`C`) and Theorem 3.25 (`Spec`) are further instances (later files).
* Remark 3.18, the uniform form of the last statement of Corollary 3.7: `exists_total_uniform`,
  the instance `R = R_B` of `stabMachine`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

section TB

variable {B : Type} [Enc M B]

/-- The map `T' : ℕ → B × {±}` computed by `T` (Definition 3.9), as `e⁻¹ ∘ T`. -/
noncomputable def seqOf (B : Type) [Enc M B] (T : M.Code) (n : ℕ) : Option (B × Bool) :=
  (M.eval T n).bind (Enc.decode (M := M) (B × Bool))

/-- `T ∈ 𝒯_B`: every output of `T` is a code of an element of `B × {±}`. -/
def InTB (B : Type) [Enc M B] (T : M.Code) : Prop :=
  ∀ n y, M.eval T n = some y → ∃ x : B × Bool, e M x = y

theorem seqOf_eq_some_iff {T : M.Code} {n : ℕ} {x : B × Bool} :
    seqOf (M := M) B T n = some x ↔ M.eval T n = some (e M x) := by
  unfold seqOf
  cases h : M.eval T n with
  | none => simp
  | some y =>
    simp only [Option.bind_some]
    rw [Enc.decode_eq_some_iff]
    constructor
    · rintro rfl; rfl
    · intro h; cases h; rfl

/-- `T ∈ 𝒯_B` iff `T` computes `T'`, i.e. the diagram of Definition 3.9 commutes. -/
theorem inTB_iff_computes {T : M.Code} :
    InTB (M := M) B T ↔ Computes M T (seqOf (M := M) B T) := by
  constructor
  · intro h n
    show M.eval T n = (seqOf (M := M) B T n).map (e M)
    cases he : M.eval T n with
    | none => unfold seqOf; rw [he]; rfl
    | some y =>
      obtain ⟨x, rfl⟩ := h n y he
      rw [seqOf_eq_some_iff.2 he]; rfl
  · intro h n y he
    have this : M.eval T n = (seqOf (M := M) B T n).map (e M) := h n
    rw [he] at this
    cases hs : seqOf (M := M) B T n with
    | none => rw [hs] at this; cases this
    | some x => rw [hs] at this; exact ⟨x, (Option.some.inj this).symm⟩

theorem InTB.computes {T : M.Code} (h : InTB (M := M) B T) : Computes M T (seqOf (M := M) B T) :=
  inTB_iff_computes.1 h

/-- If `T` computes some `N : ℕ → B × {±}` then `T ∈ 𝒯_B` and `T' = N`. -/
theorem inTB_of_computes {T : M.Code} {N : ℕ → Option (B × Bool)} (h : Computes M T N) :
    InTB (M := M) B T ∧ ∀ n, seqOf (M := M) B T n = N n := by
  have hN : ∀ n, seqOf (M := M) B T n = N n := by
    intro n
    have hn : M.eval T n = (N n).map (e M) := h n
    unfold seqOf
    rw [hn]
    cases N n with
    | none => rfl
    | some x => simp [Enc.decode_e]
  refine ⟨inTB_iff_computes.2 fun n => ?_, hN⟩
  show M.eval T n = (seqOf (M := M) B T n).map (e M)
  rw [hN n]; exact h n

/-- The stabilization `T^s = (T')^s ⊂ B` (Notation 3.21). -/
noncomputable def Ts (B : Type) [Enc M B] (T : M.Code) : B → Prop := Stab (seqOf (M := M) B T)

/-- `b` is `T`-stable (Definition 3.10). -/
noncomputable def TStable (T : M.Code) (b : B) : Prop := IsStable (seqOf (M := M) B T) b

theorem Ts_def (T : M.Code) (b : B) : Ts (M := M) B T b ↔ TStable (M := M) T b := Iff.rfl

/-- `T` stably computes `N : ℕ → B × {±}` (Definition 1.4 / 3.1): `T ∈ 𝒯_B` and `(T')^s = N^s`. -/
noncomputable def StablyComputes (T : M.Code) (N : ℕ → Option (B × Bool)) : Prop :=
  InTB (M := M) B T ∧ ∀ b, IsStable (seqOf (M := M) B T) b ↔ IsStable N b

/-- `T` computing `N` stably computes it. -/
theorem stablyComputes_of_computes {T : M.Code} {N : ℕ → Option (B × Bool)}
    (h : Computes M T N) : StablyComputes (M := M) T N := by
  obtain ⟨h1, h2⟩ := inTB_of_computes h
  exact ⟨h1, fun b => ⟨IsStable.of_eq h2, IsStable.of_eq fun n => (h2 n).symm⟩⟩

/-- The decision map `T' : B × ℕ → {±}` computed by `T` (Definition 3.8), as `e⁻¹ ∘ T ∘ e`. -/
noncomputable def decOf (B : Type) [Enc M B] (T : M.Code) (b : B) (n : ℕ) : Option Bool :=
  (M.eval T (e M (b, n))).bind (Enc.decode (M := M) Bool)

/-- `T ∈ 𝒟_B`: on codes of `B × ℕ`, `T` outputs codes of `{±}` or diverges. -/
def InDB (B : Type) [Enc M B] (T : M.Code) : Prop :=
  ∀ (b : B) (n : ℕ) y, M.eval T (e M (b, n)) = some y → ∃ s : Bool, e M s = y

theorem decOf_eq_some_iff {T : M.Code} {b : B} {n : ℕ} {s : Bool} :
    decOf (M := M) B T b n = some s ↔ M.eval T (e M (b, n)) = some (e M s) := by
  unfold decOf
  cases h : M.eval T (e M (b, n)) with
  | none => simp
  | some y =>
    simp only [Option.bind_some]
    rw [Enc.decode_eq_some_iff]
    constructor
    · rintro rfl; rfl
    · intro h; cases h; rfl

theorem inDB_iff_computes {T : M.Code} :
    InDB (M := M) B T ↔ Computes M T (fun p : B × ℕ => decOf (M := M) B T p.1 p.2) := by
  constructor
  · intro h p
    obtain ⟨b, n⟩ := p
    show M.eval T (e M (b, n)) = (decOf (M := M) B T b n).map (e M)
    cases he : M.eval T (e M (b, n)) with
    | none => unfold decOf; rw [he]; rfl
    | some y =>
      obtain ⟨s, rfl⟩ := h b n y he
      rw [decOf_eq_some_iff.2 he]; rfl
  · intro h b n y he
    have this : M.eval T (e M (b, n)) = (decOf (M := M) B T b n).map (e M) := h (b, n)
    rw [he] at this
    cases hs : decOf (M := M) B T b n with
    | none => rw [hs] at this; cases this
    | some s => rw [hs] at this; exact ⟨s, (Option.some.inj this).symm⟩

theorem inDB_of_computes {T : M.Code} {D : B → ℕ → Option Bool}
    (h : Computes M T (fun p : B × ℕ => D p.1 p.2)) :
    InDB (M := M) B T ∧ ∀ b n, decOf (M := M) B T b n = D b n := by
  have hD : ∀ b n, decOf (M := M) B T b n = D b n := by
    intro b n
    have hn : M.eval T (e M (b, n)) = (D b n).map (e M) := h (b, n)
    unfold decOf
    rw [hn]
    cases D b n with
    | none => rfl
    | some s => simp [Enc.decode_e]
  refine ⟨inDB_iff_computes.2 fun p => ?_, hD⟩
  show M.eval T (e M p) = (decOf (M := M) B T p.1 p.2).map (e M)
  rw [hD p.1 p.2]; exact h p

/-- `b` is `T`-decided (Definition 3.10). -/
noncomputable def TDecided (T : M.Code) (b : B) : Prop := IsDecided (decOf (M := M) B T) b

/-- `T ∈ 𝒟_B` stably computes the decision map `D₀` (Definition 3.20): `T'` is stably
equivalent to `D₀`. -/
noncomputable def StablyComputesDec (T : M.Code) (D₀ : B → ℕ → Option Bool) : Prop :=
  InDB (M := M) B T ∧ StablyEquiv (decOf (M := M) B T) D₀

/-- The sentence `Θ_{D,T}` of Section 4: `T ∈ 𝒟_𝒯` and `T` stably computes `D`. -/
noncomputable def Theta (D : B → ℕ → Option Bool) (T : M.Code) : Prop :=
  StablyComputesDec (M := M) T D

/-! ### Lemma 3.13 (`κ`; `exists_K` below) and Lemma 4.1 (`Ω`) -/

/-- The map `V_B (T, n) = e⁻¹ (U (T, n)) : 𝒯 × ℕ → B × {±}` is computable. -/
theorem comp_V : Comp M (fun p : M.Code × ℕ => seqOf (M := M) B p.1 p.2) := by
  have := (comp_decode (M := M) (A := B × Bool)).comp (comp_univ (M := M))
  exact this.congr fun p => rfl

/-- Lemma 3.13 (the map `κ` of the manuscript): a total computable `K : 𝒯 → 𝒯` with `K T ∈ 𝒯_B` and `(K T)' = T'` for every `T`
(in particular `K T` and `T` compute the same map when `T ∈ 𝒯_B`). -/
theorem exists_K : ∃ K : M.Code → M.Code, CompT M K ∧ ∀ T,
    InTB (M := M) B (K T) ∧ ∀ n, seqOf (M := M) B (K T) n = seqOf (M := M) B T n := by
  obtain ⟨K, hK, hK'⟩ := smn (comp_V (M := M) (B := B))
  exact ⟨K, hK, fun T => inTB_of_computes (hK' T)⟩

/-- The map `𝒯 × (B × ℕ) → {±}`, `(T, (b, n)) ↦ e⁻¹ (U (T, e (b, n)))`, is computable. -/
theorem comp_VD : Comp M (fun p : M.Code × (B × ℕ) => decOf (M := M) B p.1 p.2.1 p.2.2) := by
  have h1 : Comp M (fun p : M.Code × (B × ℕ) => M.eval p.1 (e M p.2)) :=
    comp_univ.compT (CompT.pair compT_fst (compT_e.comp compT_snd))
  have := (comp_decode (A := Bool)).comp h1
  exact this.congr fun p => rfl

/-- Lemma 4.1: a total computable `Ω : 𝒯 → 𝒯` with `Ω T ∈ 𝒟_B` and `(Ω T)' = T'` for every `T`. -/
theorem exists_Omega : ∃ Ω : M.Code → M.Code, CompT M Ω ∧ ∀ T,
    InDB (M := M) B (Ω T) ∧ ∀ b n, decOf (M := M) B (Ω T) b n = decOf (M := M) B T b n := by
  obtain ⟨Ω, hΩ, hΩ'⟩ := smn (comp_VD (M := M) (B := B))
  exact ⟨Ω, hΩ, fun T => inDB_of_computes (hΩ' T)⟩

/-! ### Uniform stabilizer machines -/

variable {R : M.Code → B → ℕ → ℕ → Prop}

/-- Given a computable `R ⊂ 𝒯 × B × ℕ × ℕ`, a total computable `𝒯 → 𝒟_B` whose value at `T`
computes the total decision map `D_R (T, ·, ·)` of the stabilizer lemma. -/
theorem exists_decMachine
    (hR : CompSet M (fun q : M.Code × B × ℕ × ℕ => R q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    ∃ Dec : M.Code → M.Code, CompT M Dec ∧ ∀ T,
      InDB (M := M) B (Dec T) ∧ (∀ b n, decOf (M := M) B (Dec T) b n = some (DR R T b n)) ∧
      ∀ b, TDecided (M := M) (Dec T) b ↔ SR R T b := by
  have hD := compT_DR (M := M) hR
  obtain ⟨Dec, hDec, hDec'⟩ := smn (f := fun q : M.Code × (B × ℕ) => some (DR R q.1 q.2.1 q.2.2)) hD
  refine ⟨Dec, hDec, fun T => ?_⟩
  obtain ⟨h1, h2⟩ := inDB_of_computes (D := fun b n => some (DR R T b n)) (hDec' T)
  refine ⟨h1, h2, fun b => ?_⟩
  unfold TDecided
  rw [← isDecided_DR_iff R T b]
  exact ⟨IsDecided.of_eq h2, IsDecided.of_eq fun b n => (h2 b n).symm⟩

/-- Given a computable `R ⊂ 𝒯 × B × ℕ × ℕ` and infinite `B`, a total computable `𝒯 → 𝒯_B` whose
value at `T` computes the total map `M_{D_R (T,·,·)}`, so that its stabilization is `S_R (T)`. -/
theorem exists_stabMachine (hB : Enc.Infinite M B)
    (hR : CompSet M (fun q : M.Code × B × ℕ × ℕ => R q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    ∃ St : M.Code → M.Code, CompT M St ∧ ∀ T,
      InTB (M := M) B (St T) ∧ (∀ n, seqOf (M := M) B (St T) n ≠ none) ∧
      ∀ b, TStable (M := M) (St T) b ↔ SR R T b := by
  have hD := compT_DR (M := M) hR
  -- `(T, n) ↦ M_{D_R (T,·,·)} (n)`
  have hM : Comp M (fun p : M.Code × ℕ =>
      seqOfDec (M := M) (fun b t => some (DR R p.1 b t)) p.2) := by
    -- as in `comp_seqOfDec`, with the parameter `T` carried along
    have h1 : Comp M (fun p : M.Code × ℕ => (epsilonInv (M := M) B (M.unpair p.2).1).map
        fun b => (p.1, (b, (M.unpair p.2).2))) := by
      have := Comp.pair (M := M) (compT_fst (A := M.Code) (B := ℕ)).toComp
        (Comp.pair ((comp_epsilonInv (M := M) (A := B)).compT (compT_unpair_fst.comp compT_snd))
          (compT_unpair_snd.comp compT_snd).toComp)
      exact this.congr fun p => by
        cases epsilonInv (M := M) B (M.unpair p.2).1 <;> simp [Option.bind, Option.map]
    have h2 : CompT M (fun q : M.Code × (B × ℕ) => (q.2.1, DR R q.1 q.2.1 q.2.2)) :=
      CompT.pair (compT_fst.comp compT_snd) hD
    refine (h2.toComp.comp h1).congr fun p => ?_
    unfold seqOfDec
    cases epsilonInv (M := M) B (M.unpair p.2).1 <;> simp [Option.bind, Option.map]
  obtain ⟨St, hSt, hSt'⟩ := smn hM
  refine ⟨St, hSt, fun T => ?_⟩
  obtain ⟨h1, h2⟩ := inTB_of_computes (hSt' T)
  refine ⟨h1, fun n => ?_, fun b => ?_⟩
  · rw [h2 n]
    exact seqOfDec_total hB (fun _ _ => Option.some_ne_none _) n
  · unfold TStable
    have e1 : IsStable (seqOf (M := M) B (St T)) b ↔
        IsStable (seqOfDec (M := M) (fun b t => some (DR R T b t))) b :=
      ⟨IsStable.of_eq h2, IsStable.of_eq fun n => (h2 n).symm⟩
    rw [e1, isStable_seqOfDec_iff, isDecided_DR_iff]

/-! ### `Dec_B` and Lemma 3.16 -/

/-- The relation `R_B` of Definition 3.14: `(T, b, u, v) ∈ R_B`, `u = ⟨m, k⟩`, `v = ⟨n, k'⟩`, iff
`(T, m, k, e (b, +)) ∈ Halt'` and (`n ≤ m` or `(T, n, k', e (b, -)) ∉ Halt'`). -/
def RB (B : Type) [Enc M B] (T : M.Code) (b : B) (u v : ℕ) : Prop :=
  M.run T (M.unpair u).1 (M.unpair u).2 = some (e M (b, true)) ∧
    ((M.unpair v).1 ≤ (M.unpair u).1 ∨
      M.run T (M.unpair v).1 (M.unpair v).2 ≠ some (e M (b, false)))

theorem compSet_RB : CompSet M (fun q : M.Code × B × ℕ × ℕ => RB (M := M) B q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  -- the two `Halt'` conditions, with the arguments rearranged by total computable maps
  have hu1 : CompT M (fun q : M.Code × B × ℕ × ℕ => (M.unpair q.2.2.1).1) :=
    compT_unpair_fst.comp (compT_fst.comp (compT_snd.comp compT_snd))
  have hu2 : CompT M (fun q : M.Code × B × ℕ × ℕ => (M.unpair q.2.2.1).2) :=
    compT_unpair_snd.comp (compT_fst.comp (compT_snd.comp compT_snd))
  have hv1 : CompT M (fun q : M.Code × B × ℕ × ℕ => (M.unpair q.2.2.2).1) :=
    compT_unpair_fst.comp (compT_snd.comp (compT_snd.comp compT_snd))
  have hv2 : CompT M (fun q : M.Code × B × ℕ × ℕ => (M.unpair q.2.2.2).2) :=
    compT_unpair_snd.comp (compT_snd.comp (compT_snd.comp compT_snd))
  have hplus : CompT M (fun q : M.Code × B × ℕ × ℕ => e M (q.2.1, true)) :=
    compT_e.comp (CompT.pair (compT_fst.comp compT_snd) (compT_const true))
  have hminus : CompT M (fun q : M.Code × B × ℕ × ℕ => e M (q.2.1, false)) :=
    compT_e.comp (CompT.pair (compT_fst.comp compT_snd) (compT_const false))
  have h1 : CompSet M (fun q : M.Code × B × ℕ × ℕ =>
      M.run q.1 (M.unpair q.2.2.1).1 (M.unpair q.2.2.1).2 = some (e M (q.2.1, true))) :=
    compSet_halt'.comp (CompT.pair compT_fst (CompT.pair hu1 (CompT.pair hu2 hplus)))
  have h2 : CompSet M (fun q : M.Code × B × ℕ × ℕ =>
      M.run q.1 (M.unpair q.2.2.2).1 (M.unpair q.2.2.2).2 = some (e M (q.2.1, false))) :=
    compSet_halt'.comp (CompT.pair compT_fst (CompT.pair hv1 (CompT.pair hv2 hminus)))
  exact h1.and ((compSet_le hv1 hu1).or h2.not)

/-- `b` is `T`-stable iff `∃ u ∀ v, R_B (T, b, u, v)` (the computation in the proof of
Lemma 3.16, valid for every `T`). -/
theorem tStable_iff_SR_RB (T : M.Code) (b : B) : TStable (M := M) T b ↔ SR (RB (M := M) B) T b := by
  unfold TStable IsStable SR RB
  constructor
  · rintro ⟨m, hm, hm'⟩
    obtain ⟨k, hk⟩ := (M.eval_iff _ _ _).1 (seqOf_eq_some_iff.1 hm)
    refine ⟨M.pair m k, fun v => ?_⟩
    rw [M.unpair_pair]
    refine ⟨hk, ?_⟩
    by_cases hle : (M.unpair v).1 ≤ m
    · exact Or.inl hle
    · right
      intro hrun
      have := hm' (M.unpair v).1 (Nat.lt_of_not_le hle) false
        (seqOf_eq_some_iff.2 (TuringModel.eval_eq_some_of_run hrun))
      cases this
  · rintro ⟨u, hu⟩
    refine ⟨(M.unpair u).1, seqOf_eq_some_iff.2 (TuringModel.eval_eq_some_of_run (hu 0).1),
      fun n hn s hs => ?_⟩
    cases s with
    | true => rfl
    | false =>
      exfalso
      obtain ⟨k', hk'⟩ := (M.eval_iff _ _ _).1 (seqOf_eq_some_iff.1 hs)
      have := (hu (M.pair n k')).2
      rw [M.unpair_pair] at this
      rcases this with h | h
      · exact Nat.not_lt.2 h hn
      · exact h hk'

/-- Definition 3.14 and Lemmas 3.15, 3.16: a total computable `Dec_B : 𝒯 → 𝒯` with
`Dec_B T ∈ 𝒟_B`, `(Dec_B T)'` total, and `b` `T`-stable iff `b` `Dec_B T`-decided. -/
theorem exists_Dec : ∃ Dec : M.Code → M.Code, CompT M Dec ∧ ∀ T,
    InDB (M := M) B (Dec T) ∧ (∀ b n, decOf (M := M) B (Dec T) b n ≠ none) ∧
    ∀ b : B, TStable (M := M) T b ↔ TDecided (M := M) (Dec T) b := by
  obtain ⟨Dec, hDec, hDec'⟩ := exists_decMachine (M := M) (R := RB (M := M) B) (compSet_RB (B := B))
  refine ⟨Dec, hDec, fun T => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hDec' T
  refine ⟨h1, fun b n => by rw [h2]; exact Option.some_ne_none _, fun b => ?_⟩
  rw [h3, tStable_iff_SR_RB]

/-- Remark 3.18 (`remark_silent`), first half: for infinite `B`, a total computable `St : 𝒯 → 𝒯`
with `St T ∈ 𝒯_B`, `(St T)'` total, and `(St T)^s = T^s`, for every `T`.  So the last statement
of Corollary 3.7 holds uniformly in `T`.  The machine `St T` computes `M_{D_{R_B} (T,·,·)}`.  This
is the map `M_{(Dec_B (T))'}` of the remark, as `(Dec_B (T))' = D_{R_B} (T,·,·)`. -/
theorem exists_total_uniform (hB : Enc.Infinite M B) : ∃ St : M.Code → M.Code, CompT M St ∧ ∀ T,
    InTB (M := M) B (St T) ∧ (∀ n, seqOf (M := M) B (St T) n ≠ none) ∧
    ∀ b : B, TStable (M := M) (St T) b ↔ TStable (M := M) T b := by
  obtain ⟨St, hSt, hSt'⟩ :=
    exists_stabMachine (M := M) (R := RB (M := M) B) hB (compSet_RB (B := B))
  refine ⟨St, hSt, fun T => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hSt' T
  refine ⟨h1, h2, fun b => ?_⟩
  rw [h3, tStable_iff_SR_RB]

end TB

end Stable
