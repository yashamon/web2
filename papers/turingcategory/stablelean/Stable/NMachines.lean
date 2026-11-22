import Stable.NList
import Stable.Logic

/-!
# Machines at level `n = m+1` (Section 6.2, "the constructions")

* `nseqOf m B T : ℕ^{m+1} → B × {±}` is the map `T'` of `𝒯^{m+1}_B` (defined for every `T`, as
  `e⁻¹ ∘ T ∘ e`; `T ∈ 𝒯^{m+1}_B` is `InTB B T`, every output of `T` being a code of `B × {±}`, since
  every number codes a tuple), and `NTs m B T = (T')^{s_{m+1}}` is its `(m+1)`-stabilization.
* `RBase m B : NRel 𝒯 B m` is the computable relation with `b` being `T`-`(m+1)`-stable iff
  `NSR m (complPow m (RBase m B)) T b` (the unwinding of Section 6.2: `m+2` alternating quantifiers
  over a matrix built from `Halt'`).
* `exists_nDecMachine`, `exists_nStabMachine`: the uniform `(m+1)`-decision and `(m+1)`-sequence
  machines for a computable `R`, from Lemma 6.2 and s-m-n (`Dec^n`, `C^n`, `Spec^n` are instances).
* `exists_nDec`: `Dec^{m+1}_B` (Lemmas 3.15, 3.16 at level `m+1`).
* `exists_nC`: `C^{m+1}` (Lemma 3.22 at level `m+1`): `(C^{m+1} T)^{s_{m+1}} = closure (T^{s_{m+1}})`.
-/

namespace Stable

open Classical

variable {M : TuringModel}

section Seq

variable {B : Type} [Enc M B]

/-- A base map preserving codes preserves the code of the tuple. -/
theorem e_nbMapBase_of : ∀ (m : ℕ) {B C : Type} [Enc M B] [Enc M C] (f : B → C),
    (∀ b, e M (f b) = e M b) → ∀ x : NB B m, e M (nbMapBase m f x) = e M x
  | 0, _, _, _, _, _, hf, x => hf x
  | m + 1, B, C, _, _, f, hf, x => by
    show e M (nbMapBase m (fun p : B × ℕ => (f p.1, p.2)) x) = e M x
    refine e_nbMapBase_of m _ (fun p => ?_) x
    show M.pair (e M (f p.1)) (e M p.2) = M.pair (e M p.1) (e M p.2)
    rw [hf]

/-- Every natural number codes a tuple in `ℕ^{m+1}`. -/
theorem nb_nat_surj : ∀ (m : ℕ) (n : ℕ), ∃ y : NB ℕ m, e M y = n
  | 0, n => ⟨n, rfl⟩
  | m + 1, n => by
    obtain ⟨y, hy⟩ := nb_nat_surj m n
    refine ⟨nbMapBase m (fun w => ((M.unpair w).1, (M.unpair w).2)) y, ?_⟩
    rw [← hy]
    exact e_nbMapBase_of m _ (fun w => by
      show M.pair (M.unpair w).1 (M.unpair w).2 = w
      exact M.pair_unpair w) y

/-- The map `T' : ℕ^{m+1} → B × {±}` computed by `T` (Section 6.2), as `e⁻¹ ∘ T ∘ e`. -/
noncomputable def nseqOf (m : ℕ) (B : Type) [Enc M B] (T : M.Code) (y : NB ℕ m) : Option (B × Bool) :=
  (M.eval T (e M y)).bind (Enc.decode (M := M) (B × Bool))

/-- `T^{s_{m+1}} = (T')^{s_{m+1}}`. -/
noncomputable def NTs (m : ℕ) (B : Type) [Enc M B] (T : M.Code) : B → Prop :=
  fun b => NStable m (nseqOf (M := M) m B T) b

theorem nseqOf_eq_some_iff {m : ℕ} {T : M.Code} {y : NB ℕ m} {x : B × Bool} :
    nseqOf (M := M) m B T y = some x ↔ M.eval T (e M y) = some (e M x) := by
  unfold nseqOf
  cases h : M.eval T (e M y) with
  | none => simp
  | some z =>
    simp only [Option.bind_some]
    rw [Enc.decode_eq_some_iff]
    constructor
    · rintro rfl; rfl
    · intro h; cases h; rfl

/-- If `T` computes `N : ℕ^{m+1} → B × {±}` then `T ∈ 𝒯^{m+1}_B` and `T' = N`. -/
theorem nseqOf_of_computes {m : ℕ} {T : M.Code} {N : NB ℕ m → Option (B × Bool)}
    (h : Computes M T N) : InTB (M := M) B T ∧ ∀ y, nseqOf (M := M) m B T y = N y := by
  have hN : ∀ y, nseqOf (M := M) m B T y = N y := by
    intro y
    have hy : M.eval T (e M y) = (N y).map (e M) := h y
    unfold nseqOf
    rw [hy]
    cases N y with
    | none => rfl
    | some x => simp [Enc.decode_e]
  refine ⟨fun n z hz => ?_, hN⟩
  obtain ⟨y, rfl⟩ := nb_nat_surj (M := M) m n
  have hy : M.eval T (e M y) = (N y).map (e M) := h y
  rw [hy] at hz
  cases hN' : N y with
  | none => rw [hN'] at hz; cases hz
  | some x => rw [hN'] at hz; exact ⟨x, Option.some.inj hz⟩

/-! ### `(m+1)`-stability of `T'` as a `Σ⁰_{m+2}` condition -/

/-- The matrix: `1`-stability of the slice of `T'` at `x = ((b, u₁), …, u_m)`, as in `R_B`. -/
def RBase (m : ℕ) (B : Type) [Enc M B] : NRel M.Code B m := fun T x u v =>
  M.run T (e M (nbMapBase m (fun _ : B => (M.unpair u).1) x)) (M.unpair u).2 =
      some (e M (nbBase m x, true)) ∧
    ((M.unpair v).1 ≤ (M.unpair u).1 ∨
      M.run T (e M (nbMapBase m (fun _ : B => (M.unpair v).1) x)) (M.unpair v).2 ≠
        some (e M (nbBase m x, false)))

theorem nRelComp_RBase (m : ℕ) : NRelComp (M := M) m (RBase (M := M) m B) := by
  unfold NRelComp RBase
  have hx : CompT M (fun q : M.Code × NB B m × ℕ × ℕ => q.2.1) := compT_fst.comp compT_snd
  have hu1 : CompT M (fun q : M.Code × NB B m × ℕ × ℕ => (M.unpair q.2.2.1).1) :=
    compT_unpair_fst.comp (compT_fst.comp (compT_snd.comp compT_snd))
  have hu2 : CompT M (fun q : M.Code × NB B m × ℕ × ℕ => (M.unpair q.2.2.1).2) :=
    compT_unpair_snd.comp (compT_fst.comp (compT_snd.comp compT_snd))
  have hv1 : CompT M (fun q : M.Code × NB B m × ℕ × ℕ => (M.unpair q.2.2.2).1) :=
    compT_unpair_fst.comp (compT_snd.comp (compT_snd.comp compT_snd))
  have hv2 : CompT M (fun q : M.Code × NB B m × ℕ × ℕ => (M.unpair q.2.2.2).2) :=
    compT_unpair_snd.comp (compT_snd.comp (compT_snd.comp compT_snd))
  have hbase : CompT M (fun q : M.Code × NB B m × ℕ × ℕ => nbBase m q.2.1) :=
    (compT_nbBase m).comp hx
  have hplus : CompT M (fun q : M.Code × NB B m × ℕ × ℕ => e M (nbBase m q.2.1, true)) :=
    compT_e.comp (CompT.pair hbase (compT_const true))
  have hminus : CompT M (fun q : M.Code × NB B m × ℕ × ℕ => e M (nbBase m q.2.1, false)) :=
    compT_e.comp (CompT.pair hbase (compT_const false))
  have hargu : CompT M (fun q : M.Code × NB B m × ℕ × ℕ =>
      e M (nbMapBase m (fun _ : B => (M.unpair q.2.2.1).1) q.2.1)) :=
    compT_e.comp ((compT_nbMapBase_const m (B := B) (C := ℕ)).comp (CompT.pair hx hu1))
  have hargv : CompT M (fun q : M.Code × NB B m × ℕ × ℕ =>
      e M (nbMapBase m (fun _ : B => (M.unpair q.2.2.2).1) q.2.1)) :=
    compT_e.comp ((compT_nbMapBase_const m (B := B) (C := ℕ)).comp (CompT.pair hx hv1))
  have h1 := compSet_halt'.comp (CompT.pair compT_fst (CompT.pair hargu (CompT.pair hu2 hplus)))
  have h2 := compSet_halt'.comp (CompT.pair compT_fst (CompT.pair hargv (CompT.pair hv2 hminus)))
  exact h1.and ((compSet_le hv1 hu1).or h2.not)

/-- `x` is decided by the decision map of `T'` iff `∃ u ∀ v, RBase (T, x, u, v)`. -/
theorem isDecided_DM_nseqOf_iff (m : ℕ) (T : M.Code) (x : NB B m) :
    IsDecided (DM m (nseqOf (M := M) m B T)) x ↔ ∃ u, ∀ v, RBase (M := M) m B T x u v := by
  -- `DM m (nseqOf T) x w = some s ↔ eval T (e (x with base w)) = some (e (base x, s))`
  have key : ∀ w s, DM m (nseqOf (M := M) m B T) x w = some s ↔
      M.eval T (e M (nbMapBase m (fun _ : B => w) x)) = some (e M (nbBase m x, s)) := by
    intro w s
    unfold DM
    rw [← nseqOf_eq_some_iff]
    cases h : nseqOf (M := M) m B T (nbMapBase m (fun _ : B => w) x) with
    | none => simp
    | some p =>
      obtain ⟨b', s'⟩ := p
      by_cases hb : b' = nbBase m x
      · subst hb; simp
      · simp [hb]
  unfold IsDecided RBase
  constructor
  · rintro ⟨m₀, hm, hm'⟩
    obtain ⟨k, hk⟩ := (M.eval_iff _ _ _).1 ((key m₀ true).1 hm)
    refine ⟨M.pair m₀ k, fun v => ?_⟩
    rw [M.unpair_pair]
    refine ⟨hk, ?_⟩
    by_cases hle : (M.unpair v).1 ≤ m₀
    · exact Or.inl hle
    · right
      intro hrun
      have hd := (key (M.unpair v).1 false).2 (TuringModel.eval_eq_some_of_run hrun)
      rcases hm' (M.unpair v).1 (Nat.le_of_lt (Nat.lt_of_not_le hle)) with h | h
      · rw [h] at hd; cases hd
      · rw [h] at hd; cases hd
  · rintro ⟨u, hu⟩
    have hk := (hu 0).1
    refine ⟨(M.unpair u).1, (key _ true).2 (TuringModel.eval_eq_some_of_run hk), fun n hn => ?_⟩
    cases hd : DM m (nseqOf (M := M) m B T) x n with
    | none => exact Or.inr rfl
    | some s =>
      cases s with
      | true => exact Or.inl rfl
      | false =>
        exfalso
        obtain ⟨k', hk'⟩ := (M.eval_iff _ _ _).1 ((key n false).1 hd)
        have := (hu (M.pair n k')).2
        rw [M.unpair_pair] at this
        rcases this with h | h
        · have hnm : n = (M.unpair u).1 := Nat.le_antisymm h hn
          rw [hnm] at hk'
          have := TuringModel.run_unique hk hk'
          have h2 : e M (nbBase m x, true) = e M (nbBase m x, false) := this
          cases Enc.inj h2
        · exact h hk'

/-- `complPow` preserves computability. -/
theorem NRelComp.complPow {A B : Type} [Enc M A] [Enc M B] {m : ℕ} {R : NRel A B m}
    (h : NRelComp (M := M) m R) : ∀ k, NRelComp (M := M) m (complPow k R)
  | 0 => h
  | k + 1 => (NRelComp.complPow h k).compl

/-- `b` is `T`-`(m+1)`-stable iff `NSR m (complPow m (RBase m B)) T b`: the `Σ⁰_{m+2}` form of
`(m+1)`-stability, uniformly in `T`. -/
theorem NTs_iff_NSR (m : ℕ) (T : M.Code) (b : B) :
    NTs (M := M) m B T b ↔ NSR m (complPow m (RBase (M := M) m B)) T b := by
  unfold NTs
  rw [← NDec_DM_iff]
  exact NDec_iff_NSR m _ _ T (isDecided_DM_nseqOf_iff m T) b

/-- A relation not depending on the parameter: `NSR` with parameter `a` equals `NSR` with
parameter `()`. -/
theorem NSR_param_const : ∀ (m : ℕ) {A' B : Type} (R : NRel Unit B m) (a : A') (b : B),
    NSR m (fun (_ : A') x u v => R () x u v) a b ↔ NSR m R () b
  | 0, _, _, _, _, _ => Iff.rfl
  | m + 1, _, _, R, a, b => by
    show (∃ u, ¬ NSR m (compl fun (_ : _) x u v => R () x u v) a (b, u)) ↔
      ∃ u, ¬ NSR m (compl R) () (b, u)
    refine exists_congr fun u => not_congr ?_
    exact NSR_param_const m (compl R) a (b, u)

/-- `NSR m R a b` depends only on `R a`. -/
theorem NSR_congr_at : ∀ (m : ℕ) {A B : Type} {R R' : NRel A B m} (a : A),
    (∀ x u v, R a x u v ↔ R' a x u v) → ∀ b, NSR m R a b ↔ NSR m R' a b
  | 0, _, _, _, _, a, h, b => by
    show (∃ u, ∀ v, _) ↔ ∃ u, ∀ v, _
    exact exists_congr fun u => forall_congr' fun v => h b u v
  | m + 1, _, _, R, R', a, h, b => by
    show (∃ u, ¬ NSR m (compl R) a (b, u)) ↔ ∃ u, ¬ NSR m (compl R') a (b, u)
    exact exists_congr fun u => not_congr
      (NSR_congr_at m a (fun x u v => not_congr (h x u v)) (b, u))

/-- Transport along a base map depending on the parameter. -/
theorem NSR_nbMapBase_param (m : ℕ) {A B C : Type} (R : NRel A C m) (f : A → B → C) (a : A) (b : B) :
    NSR m (fun a x u v => R a (nbMapBase m (f a) x) u v) a b ↔ NSR m R a (f a b) :=
  (NSR_congr_at m a (R' := fun a' x u v => R a' (nbMapBase m (f a) x) u v)
    (fun _ _ _ => Iff.rfl) b).trans (NSR_nbMapBase m R (f a) a b)

/-! ### Uniform `(m+1)`-decision and `(m+1)`-sequence machines -/

variable {R : NRel M.Code B m}

/-- From a computable `R ⊂ 𝒯 × B × ℕ^{m+2}`: a total computable `𝒯 → 𝒟^{m+1}_B` whose value at `T`
computes the total `(m+1)`-decision map `D_R (T, ·)` of Lemma 6.2. -/
theorem exists_nDecMachine (m : ℕ) {R : NRel M.Code B m} (hR : NRelComp (M := M) m R) :
    ∃ Dec : M.Code → M.Code, CompT M Dec ∧ ∀ T,
      InDB (M := M) (NB B m) (Dec T) ∧ (∀ x w, decOf (M := M) (NB B m) (Dec T) x w ≠ none) ∧
      ∀ b, NDec m (decOf (M := M) (NB B m) (Dec T)) b ↔ NSR m R T b := by
  obtain ⟨D, hD, hD'⟩ := n_stabilizer (M := M) m R hR
  obtain ⟨Dec, hDec, hDec'⟩ := smn (f := fun q : M.Code × (NB B m × ℕ) => some (D q.1 q.2.1 q.2.2)) hD
  refine ⟨Dec, hDec, fun T => ?_⟩
  obtain ⟨h1, h2⟩ := inDB_of_computes (D := fun x w => some (D T x w)) (hDec' T)
  refine ⟨h1, fun x w => by rw [h2]; exact Option.some_ne_none _, fun b => ?_⟩
  rw [← hD' T b]
  exact NDec.of_eq m h2 b

/-- `(T, y) ↦ M_{D (T,·)} (y)` is computable when `D` is. -/
theorem comp_MD_param (m : ℕ) {D : M.Code → NB B m → ℕ → Bool}
    (hD : CompT M (fun q : M.Code × NB B m × ℕ => D q.1 q.2.1 q.2.2)) :
    Comp M (fun p : M.Code × NB ℕ m => MD (M := M) m (fun x w => some (D p.1 x w)) p.2) := by
  -- `(T, y) ↦ (T, y, ε⁻¹ (unpair (base y)).1)`, then `(T, y, b) ↦ (b, D T (y with base b) (unpair (base y)).2)`
  have hbase : CompT M (fun p : M.Code × NB ℕ m => nbBase m p.2) := (compT_nbBase m).comp compT_snd
  have h1 : Comp M (fun p : M.Code × NB ℕ m =>
      (epsilonInv (M := M) B (M.unpair (nbBase m p.2)).1).map fun b => (p, b)) := by
    have := Comp.pair (M := M) (compT_id (A := M.Code × NB ℕ m)).toComp
      ((comp_epsilonInv (M := M) (A := B)).compT (compT_unpair_fst.comp hbase))
    exact this.congr fun p => by
      cases epsilonInv (M := M) B (M.unpair (nbBase m p.2)).1 <;> simp [Option.bind, Option.map]
  have h2 : CompT M (fun q : (M.Code × NB ℕ m) × B =>
      (q.2, D q.1.1 (nbMapBase m (fun _ : ℕ => q.2) q.1.2) (M.unpair (nbBase m q.1.2)).2)) := by
    refine CompT.pair compT_snd (hD.comp (CompT.pair (compT_fst.comp compT_fst) (CompT.pair ?_ ?_)))
    · exact (compT_nbMapBase_const m (B := ℕ) (C := B)).comp (CompT.pair (compT_snd.comp compT_fst) compT_snd)
    · exact compT_unpair_snd.comp ((compT_nbBase m).comp (compT_snd.comp compT_fst))
  refine (h2.toComp.comp h1).congr fun p => ?_
  unfold MD
  cases epsilonInv (M := M) B (M.unpair (nbBase m p.2)).1 <;> simp [Option.bind, Option.map]

/-- From a computable `R ⊂ 𝒯 × B × ℕ^{m+2}` and infinite `B`: a total computable `𝒯 → 𝒯^{m+1}_B`
whose value at `T` computes a total map `ℕ^{m+1} → B × {±}` with `(m+1)`-stabilization `S_R (T)`. -/
theorem exists_nStabMachine (m : ℕ) (hB : Enc.Infinite M B) {R : NRel M.Code B m}
    (hR : NRelComp (M := M) m R) :
    ∃ St : M.Code → M.Code, CompT M St ∧ ∀ T,
      InTB (M := M) B (St T) ∧ (∀ y, nseqOf (M := M) m B (St T) y ≠ none) ∧
      ∀ b, NTs (M := M) m B (St T) b ↔ NSR m R T b := by
  obtain ⟨D, hD, hD'⟩ := n_stabilizer (M := M) m R hR
  obtain ⟨St, hSt, hSt'⟩ := smn (comp_MD_param m hD)
  refine ⟨St, hSt, fun T => ?_⟩
  obtain ⟨h1, h2⟩ := nseqOf_of_computes (hSt' T)
  refine ⟨h1, fun y => ?_, fun b => ?_⟩
  · rw [h2 y]
    exact MD_total m hB (fun _ _ => Option.some_ne_none _) y
  · unfold NTs
    refine (NStable.of_eq m (Mp' := MD (M := M) m (fun x w => some (D T x w))) (fun y => h2 y) b).trans ?_
    rw [NStable_MD_iff, hD' T b]

/-- `Dec^{m+1}_B` (Section 6.2, Lemmas 3.15 and 3.16 at level `m+1`): a total computable
`Dec : 𝒯 → 𝒯` with `Dec T ∈ 𝒟^{m+1}_B`, `(Dec T)'` total, and `b` `T`-`(m+1)`-stable iff `b`
`Dec T`-`(m+1)`-decided. -/
theorem exists_nDec (m : ℕ) : ∃ Dec : M.Code → M.Code, CompT M Dec ∧ ∀ T,
    InDB (M := M) (NB B m) (Dec T) ∧ (∀ x w, decOf (M := M) (NB B m) (Dec T) x w ≠ none) ∧
    ∀ b : B, NTs (M := M) m B T b ↔ NDec m (decOf (M := M) (NB B m) (Dec T)) b := by
  obtain ⟨Dec, hDec, hDec'⟩ :=
    exists_nDecMachine (M := M) m ((nRelComp_RBase (M := M) (B := B) m).complPow m)
  refine ⟨Dec, hDec, fun T => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hDec' T
  refine ⟨h1, h2, fun b => ?_⟩
  rw [h3, NTs_iff_NSR]

end Seq

/-! ### `C^{m+1}`: the deductive closure (Lemma 3.22 at level `m+1`) -/

section Closure

variable (L : Language M)

/-- Derivability from `S` through a finite list and a derivation code. -/
theorem deriv_iff_exists_prf (S : L.Sent → Prop) (γ : L.Sent) :
    L.Deriv S γ ↔ ∃ q : ℕ × List L.Sent, L.Prf q.1 q.2 γ ∧
      ∀ j, j < q.2.length → ∃ γ', q.2[j]? = some γ' ∧ S γ' := by
  constructor
  · intro h
    obtain ⟨l, hl, hd⟩ := L.deriv_compact h
    obtain ⟨p, hp⟩ := (L.prf_iff l γ).2 hd
    refine ⟨(p, l), hp, fun j hj => ?_⟩
    exact ⟨l[j]'hj, List.getElem?_eq_some_iff.2 ⟨hj, rfl⟩, hl _ (List.getElem_mem hj)⟩
  · rintro ⟨⟨p, l⟩, hp, hl⟩
    have hd : L.Deriv (fun α => α ∈ l) γ := (L.prf_iff l γ).1 ⟨p, hp⟩
    refine L.deriv_cut (fun β hβ => ?_) hd
    obtain ⟨j, hj, hjβ⟩ := List.getElem_of_mem hβ
    obtain ⟨γ', hγ', hS⟩ := hl j hj
    have hγ'' : l[j]? = some γ' := hγ'
    have : l[j]? = some β := List.getElem?_eq_some_iff.2 ⟨hj, hjβ⟩
    rw [this] at hγ''
    cases hγ''
    exact L.deriv_of_mem hS

/-- `C^{m+1}` (Lemma 3.22 at level `m+1`): a total computable `C : 𝒯 → 𝒯` with `C T ∈ 𝒯^{m+1}_𝓛`,
`(C T)'` total, and `(C T)^{s_{m+1}} = closure (T^{s_{m+1}})`. -/
theorem exists_nC (m : ℕ) : ∃ C : M.Code → M.Code, CompT M C ∧ ∀ T,
    InTB (M := M) L.Sent (C T) ∧ (∀ y, nseqOf (M := M) m L.Sent (C T) y ≠ none) ∧
    ∀ γ : L.Sent, NTs (M := M) m L.Sent (C T) γ ↔ L.Deriv (NTs (M := M) m L.Sent T) γ := by
  -- the `Σ⁰_{m+2}` condition `∀ j < length l, l[j] ∈ T^{s_{m+1}}` on `(γ, (p, l))`, with `Prf p l γ`
  have hR : NRelComp (M := M) m (complPow m (RBase (M := M) m L.Sent)) :=
    (nRelComp_RBase (M := M) (B := L.Sent) m).complPow m
  obtain ⟨R₁, hR₁, h₁⟩ := NSR_forall_nth_absorb (M := M) m _ hR
  obtain ⟨R₂, hR₂, h₂⟩ := NSR_comp_base (M := M) (B := L.Sent × (ℕ × List L.Sent)) m R₁ hR₁
    (f := fun z => z.2.2) (compT_snd.comp compT_snd)
  obtain ⟨R₃, hR₃, h₃⟩ := NSR_and_dec (M := M) m R₂ hR₂
    (P := fun z : L.Sent × (ℕ × List L.Sent) => L.Prf z.2.1 z.2.2 z.1)
    (L.prf_comp.comp (CompT.pair (compT_fst.comp compT_snd) (CompT.pair (compT_snd.comp compT_snd) compT_fst)))
  obtain ⟨R₄, hR₄, h₄⟩ := NSR_exists_absorb (M := M) m R₃ hR₃
  obtain ⟨C, hC, hC'⟩ := exists_nStabMachine (M := M) m L.infinite hR₄
  refine ⟨C, hC, fun T => ?_⟩
  obtain ⟨hc1, hc2, hc3⟩ := hC' T
  refine ⟨hc1, hc2, fun γ => ?_⟩
  rw [hc3, h₄, deriv_iff_exists_prf]
  refine exists_congr fun q => ?_
  rw [h₃, h₂, h₁]
  refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun _ => exists_congr fun γ' =>
    and_congr Iff.rfl ?_)
  exact (NTs_iff_NSR m T γ').symm

end Closure

end Stable
