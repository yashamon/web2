/- Infra3.lean — component theory: componentD is sound and complete for
   same-kind connectivity (ConnK). The BFS fuel argument runs on a
   filter-complement measure (no cardinality lemmas needed). -/
import SgoLemma
open SgoDisplay

variable {n : Nat}

/-! ### BEq lawfulness for DKind (derived BEq is structural). -/

instance : LawfulBEq DKind where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> rfl

/-! ### Adjacency is symmetric. -/

theorem adjI_symm {a b : Nat} (h : adjI n a b = true) : adjI n b a = true := by
  simp only [adjI, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
  omega

/-! ### Filter-complement measure lemmas. -/

/-- Filter length is monotone in the predicate. -/
theorem filter_length_mono (l : List Nat) (p q : Nat → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    simp only [List.filter]
    cases hp : p a
    · cases hq : q a
      · exact ih
      · exact Nat.le_succ_of_le ih
    · rw [h a hp]
      exact Nat.succ_le_succ ih

/-- Strictly monotone when a witness flips. -/
theorem filter_length_strict (l : List Nat) (p q : Nat → Bool)
    (h : ∀ x, p x = true → q x = true)
    (y : Nat) (hy : y ∈ l) (hpy : p y = false) (hqy : q y = true) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => cases hy
  | cons a t ih =>
    simp only [List.filter]
    rcases List.mem_cons.mp hy with rfl | hyt
    · rw [hpy, hqy]
      exact Nat.lt_succ_of_le (filter_length_mono t p q h)
    · cases hp : p a
      · cases hq : q a
        · exact ih hyt
        · exact Nat.lt_succ_of_lt (ih hyt)
      · rw [h a hp]
        exact Nat.succ_lt_succ (ih hyt)

/-! ### The BFS measure: board indices not yet collected. -/

def compMeasure (m : Nat) (comp : List Nat) : Nat :=
  ((List.range m).filter (fun x => !comp.contains x)).length

theorem compMeasure_le (m : Nat) (comp : List Nat) : compMeasure m comp ≤ m := by
  unfold compMeasure
  calc ((List.range m).filter _).length ≤ (List.range m).length :=
        List.length_filter_le _ _
    _ = m := List.length_range m

theorem compMeasure_zero_full (m : Nat) (comp : List Nat)
    (h : compMeasure m comp = 0) : ∀ x, x < m → x ∈ comp := by
  intro x hx
  unfold compMeasure at h
  have hnil := List.length_eq_zero.mp h
  have hall := List.filter_eq_nil_iff.mp hnil x (List.mem_range.mpr hx)
  cases hc : comp.contains x
  · rw [hc] at hall
    exact absurd rfl hall
  · exact List.contains_iff_mem.mp hc

theorem compMeasure_decrease (m : Nat) (comp comp' : List Nat)
    (hsub : ∀ x, x ∈ comp → x ∈ comp')
    (y : Nat) (hym : y < m) (hy' : y ∈ comp') (hy : y ∉ comp) :
    compMeasure m comp' < compMeasure m comp := by
  unfold compMeasure
  apply filter_length_strict _ _ _ ?_ y (List.mem_range.mpr hym) ?_ ?_
  · intro x hx
    rw [Bool.not_eq_true'] at hx ⊢
    cases hc : comp.contains x
    · rfl
    · have hx' : x ∈ comp' := hsub x (List.contains_iff_mem.mp hc)
      rw [List.contains_iff_mem.mpr hx'] at hx
      exact Bool.noConfusion hx
  · rw [List.contains_iff_mem.mpr hy']
    rfl
  · rw [Bool.not_eq_true']
    cases hc : comp.contains y
    · rfl
    · exact absurd (List.contains_iff_mem.mp hc) hy

/-! ### Closure of the BFS result. -/

/-- Adjacency-closed for kind k (scoped to the board). -/
def ClosedK (D : Display n) (k : DKind) (R : List Nat) : Prop :=
  ∀ q, q ∈ allIdx n → kindAt D q = some k →
    (∃ r, r ∈ R ∧ adjI n q r = true) → q ∈ R

/-- The BFS invariant: an uncollected kind-k neighbor of comp is a
    neighbor of the frontier. -/
def FrontInv (D : Display n) (k : DKind) (comp frontier : List Nat) : Prop :=
  ∀ q, q ∈ allIdx n → kindAt D q = some k → q ∉ comp →
    (∃ r, r ∈ comp ∧ adjI n q r = true) →
    ∃ r', r' ∈ frontier ∧ adjI n q r' = true

/-- Membership in one round's filter. -/
theorem mem_round_filter (D : Display n) (k : DKind)
    (comp frontier : List Nat) (q : Nat)
    (hq : q ∈ allIdx n) (hk : kindAt D q = some k) (hnc : q ∉ comp)
    (r' : Nat) (hr' : r' ∈ frontier) (hadj : adjI n q r' = true) :
    q ∈ (allIdx n).filter (fun q =>
      kindAt D q == some k && !comp.contains q &&
      frontier.any fun r => adjI n q r) := by
  refine List.mem_filter.mpr ⟨hq, ?_⟩
  simp only [Bool.and_eq_true]
  refine ⟨⟨beq_iff_eq.mpr hk, ?_⟩, List.any_eq_true.mpr ⟨r', hr', hadj⟩⟩
  rw [Bool.not_eq_true']
  cases hc : comp.contains q
  · rfl
  · exact absurd (List.contains_iff_mem.mp hc) hnc

/-- The BFS result is adjacency-closed, given fuel above the measure. -/
theorem compAux_closed (D : Display n) (k : DKind) :
    ∀ (fuel : Nat) (comp frontier : List Nat),
      compMeasure (n*n) comp ≤ fuel →
      FrontInv D k comp frontier →
      ClosedK D k (componentKAux n D k fuel comp frontier)
  | 0, comp, _, hfuel, _ => by
    intro q hq _ _
    simp only [componentKAux]
    exact compMeasure_zero_full (n*n) comp (Nat.le_zero.mp hfuel) q
      (List.mem_range.mp hq)
  | fuel+1, comp, frontier, hfuel, hinv => by
    simp only [componentKAux]
    split
    · next hnil =>
      intro q hq hk hadj
      by_cases hqc : q ∈ comp
      · exact hqc
      · rcases hinv q hq hk hqc hadj with ⟨r', hr', hadjr⟩
        have hmem := mem_round_filter D k comp frontier q hq hk hqc r' hr' hadjr
        rw [hnil] at hmem
        exact absurd hmem (List.not_mem_nil q)
    · next _ hne =>
      have hex : ∃ x, x ∈ (allIdx n).filter (fun q =>
          kindAt D q == some k && !comp.contains q &&
          frontier.any fun r => adjI n q r) := by
        cases hfe : (allIdx n).filter (fun q =>
            kindAt D q == some k && !comp.contains q &&
            frontier.any fun r => adjI n q r) with
        | nil => exact absurd hfe hne
        | cons a t => exact ⟨a, List.mem_cons.mpr (Or.inl rfl)⟩
      rcases hex with ⟨head, hhead⟩
      have hprops := List.mem_filter.mp hhead
      have hheadm : head < n*n := List.mem_range.mp hprops.1
      have hheadnc : head ∉ comp := by
        have hb := hprops.2
        simp only [Bool.and_eq_true] at hb
        have := hb.1.2
        rw [Bool.not_eq_true'] at this
        intro hmem
        rw [List.contains_iff_mem.mpr hmem] at this
        exact Bool.noConfusion this
      have hdec := compMeasure_decrease (n*n) comp
        (comp ++ (allIdx n).filter (fun q =>
          kindAt D q == some k && !comp.contains q &&
          frontier.any fun r => adjI n q r))
        (fun x hx => List.mem_append.mpr (Or.inl hx))
        head hheadm (List.mem_append.mpr (Or.inr hhead)) hheadnc
      have hfuel' : compMeasure (n*n) (comp ++ (allIdx n).filter (fun q =>
          kindAt D q == some k && !comp.contains q &&
          frontier.any fun r => adjI n q r)) ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdec hfuel)
      have hinv' : FrontInv D k
          (comp ++ (allIdx n).filter (fun q =>
            kindAt D q == some k && !comp.contains q &&
            frontier.any fun r => adjI n q r))
          ((allIdx n).filter (fun q =>
            kindAt D q == some k && !comp.contains q &&
            frontier.any fun r => adjI n q r)) := by
        intro q hq hk hqc hadjE
        rcases hadjE with ⟨r, hr, hadj⟩
        rcases List.mem_append.mp hr with hrc | hrn
        · have hqcomp : q ∉ comp := fun h => hqc (List.mem_append.mpr (Or.inl h))
          rcases hinv q hq hk hqcomp ⟨r, hrc, hadj⟩ with ⟨r', hr', hadjr⟩
          have hmem := mem_round_filter D k comp frontier q hq hk hqcomp r' hr' hadjr
          exact absurd (List.mem_append.mpr (Or.inr hmem)) hqc
        · exact ⟨r, hrn, hadj⟩
      exact compAux_closed D k fuel _ _ hfuel' hinv'

/-! ### Monotonicity and soundness of the BFS. -/

theorem compAux_mono (D : Display n) (k : DKind) :
    ∀ (fuel : Nat) (comp frontier : List Nat) (x : Nat),
      x ∈ comp → x ∈ componentKAux n D k fuel comp frontier
  | 0, _, _, _, hx => by
    simp only [componentKAux]; exact hx
  | fuel+1, comp, frontier, x, hx => by
    simp only [componentKAux]
    split
    · exact hx
    · exact compAux_mono D k fuel _ _ x (List.mem_append.mpr (Or.inl hx))

/-- Same-kind connectivity: a path of kind-k board stones from the seed. -/
inductive ConnK (D : Display n) (k : DKind) (i : Nat) : Nat → Prop where
  | refl : ConnK D k i i
  | step {j q : Nat} : ConnK D k i j → q ∈ allIdx n → kindAt D q = some k →
      adjI n q j = true → ConnK D k i q

theorem compAux_sound (D : Display n) (k : DKind) (i : Nat) :
    ∀ (fuel : Nat) (comp frontier : List Nat),
      (∀ x, x ∈ comp → ConnK D k i x) →
      (∀ x, x ∈ frontier → ConnK D k i x) →
      ∀ x, x ∈ componentKAux n D k fuel comp frontier → ConnK D k i x
  | 0, comp, _, hcomp, _, x, hx => by
    simp only [componentKAux] at hx
    exact hcomp x hx
  | fuel+1, comp, frontier, hcomp, hfront, x, hx => by
    simp only [componentKAux] at hx
    have hnextconn : ∀ y, y ∈ (allIdx n).filter (fun q =>
        kindAt D q == some k && !comp.contains q &&
        frontier.any fun r => adjI n q r) → ConnK D k i y := by
      intro y hy
      have hyi := (List.mem_filter.mp hy).1
      have hb := (List.mem_filter.mp hy).2
      simp only [Bool.and_eq_true] at hb
      rcases List.any_eq_true.mp hb.2 with ⟨r, hr, hadj⟩
      exact ConnK.step (hfront r hr) hyi (beq_iff_eq.mp hb.1.1) hadj
    split at hx
    · exact hcomp x hx
    · refine compAux_sound D k i fuel _ _ ?_ hnextconn x hx
      intro y hy
      rcases List.mem_append.mp hy with hyc | hyn
      · exact hcomp y hyc
      · exact hnextconn y hyn

/-! ### The component membership characterization. -/

theorem componentD_mem_iff (D : Display n) (i : Nat) (k : DKind)
    (hk : kindAt D i = some k) (q : Nat) :
    q ∈ componentD D i ↔ ConnK D k i q := by
  have hunf : componentD D i = componentKAux n D k (n*n) [i] [i] := by
    unfold componentD
    rw [hk]
  rw [hunf]
  constructor
  · intro hq
    refine compAux_sound D k i (n*n) [i] [i] ?_ ?_ q hq <;>
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | h
      · exact ConnK.refl
      · exact absurd h (List.not_mem_nil x)
  · intro hconn
    have hclosed : ClosedK D k (componentKAux n D k (n*n) [i] [i]) :=
      compAux_closed D k (n*n) [i] [i] (compMeasure_le (n*n) [i])
        (fun _ _ _ _ hE => hE)
    have hmem : i ∈ componentKAux n D k (n*n) [i] [i] :=
      compAux_mono D k (n*n) [i] [i] i (List.mem_cons.mpr (Or.inl rfl))
    induction hconn with
    | refl => exact hmem
    | step hc hqi hqk hadj ih => exact hclosed _ hqi hqk ⟨_, ih, hadj⟩

/-- Everything in a component has the root's kind. -/
theorem componentD_kind (D : Display n) (i : Nat) (k : DKind)
    (hk : kindAt D i = some k) (q : Nat) (hq : q ∈ componentD D i) :
    kindAt D q = some k := by
  rcases (componentD_mem_iff D i k hk q).mp hq with _ | ⟨_, _, hqk, _⟩
  · exact hk
  · exact hqk

/-- The root belongs to its component. -/
theorem componentD_mem_self (D : Display n) (i : Nat) (k : DKind)
    (hk : kindAt D i = some k) : i ∈ componentD D i :=
  (componentD_mem_iff D i k hk i).mpr ConnK.refl

/-- Components are adjacency-maximal: a board stone of the root's kind
    adjacent to the component belongs to it. -/
theorem componentD_maximal (D : Display n) (i : Nat) (k : DKind)
    (hk : kindAt D i = some k) (q : Nat) (hqi : q ∈ allIdx n)
    (hqk : kindAt D q = some k) (r : Nat) (hr : r ∈ componentD D i)
    (hadj : adjI n q r = true) : q ∈ componentD D i := by
  rw [componentD_mem_iff D i k hk] at hr ⊢
  exact ConnK.step hr hqi hqk hadj
