/- SgoDInv.lean — the main theorem, milestone 3a: the Δ-layer machinery.

   The DSGo reachability invariant replaces SGo's compatibility by
   occupancy inclusion — exactly the re-cut's own test: every branch
   stone stands on an occupied display intersection. The
   postprocessing recursion is analyzed by a measure (occupied cells
   plus q-stones strictly drop at every changing round), giving: with
   the shipped fuel the recursion reaches its fixpoint; along it the
   re-cut is vacuous (a branch stone's intersection has nonempty ev,
   so the rounds never remove it); and at the fixpoint the display is
   supported — every occupied intersection is occupied in some branch
   (else the round would have removed it). These are the printed
   lem_survival facts for DSGo. -/
import SgoNat
import SgoStage1

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv

namespace SgoDInv

variable {n : Nat}

/-! ### Occupancy inclusion, the re-cut's test -/

/-- The re-cut's branch test: every stone on an occupied display
    intersection. -/
def occIncB (n : Nat) (D b : Display n) : Bool :=
  (allIdx n).all fun i => occD D i || kindAt b i == none

theorem occIncB_of_compat {D b : Display n}
    (hc : compatibleB n D b = true) : occIncB n D b = true := by
  unfold occIncB
  rw [List.all_eq_true]
  intro i hi
  have hci := (List.all_eq_true.mp hc) i hi
  cases hk : kindAt b i with
  | none =>
    apply bool_or_right
    exact beq_iff_eq.mpr rfl
  | some k =>
    apply bool_or_left
    rw [hk] at hci
    cases hD : kindAt D i with
    | none =>
      rw [hD] at hci
      cases hci
    | some k' => exact occD_of_kind hD

/-- A display-empty intersection is empty in an included branch. -/
theorem branch_empty_of_occInc {D b : Display n}
    (hc : occIncB n D b = true) {i : Nat} (hi : i < n*n)
    (hocc : occD D i = false) : occD b i = false := by
  have hci := (List.all_eq_true.mp hc) i (List.mem_range.mpr hi)
  rcases bool_or_elim hci with h | h
  · rw [hocc] at h
    cases h
  · have hk := beq_iff_eq.mp h
    unfold occD
    unfold kindAt at hk
    cases hg : b.get i with
    | none => rfl
    | some c =>
      rw [hg] at hk
      cases hk

theorem serialP_isSome_of_occInc {D b : Display n}
    (hc : occIncB n D b = true) {m0 m1 : Option Nat}
    (h0 : availD n D m0 = true) (h1 : availD n D m1 = true) :
    (serialP n b m0 m1).isSome := by
  have hs : ∀ (c : DKind) (mo : Option Nat), availD n D mo = true →
      (bStep n b c mo).isSome := by
    intro c mo hav
    cases mo with
    | none => simp [bStep]
    | some i =>
      unfold availD at hav
      have hsplit : decide (i < n*n) = true ∧ (!occD D i) = true := by
        simpa using hav
      have hi : i < n*n := of_decide_eq_true hsplit.1
      have hocc : occD D i = false := by
        cases hoc : occD D i
        · rfl
        · exact absurd hsplit.2 (by simp [hoc])
      exact goMoveN_isSome_of_empty b c i
        (branch_empty_of_occInc hc hi hocc)
  rcases Option.isSome_iff_exists.mp (hs .b m0 h0) with ⟨x0, hx0⟩
  rcases Option.isSome_iff_exists.mp (hs .w m1 h1) with ⟨x1, hx1⟩
  cases h01 : bStep2 n b .b .w m0 m1 with
  | some a =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a' => simp [serialP, h01, h10]
    | none => simp [serialP, h01, h10, hx1]
  | none =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a' => simp [serialP, h01, h10, hx0]
    | none => simp [serialP, h01, h10, hx0, hx1]

theorem simEvAux_isSome_of_occInc {bs : List (Display n)} {D : Display n}
    (hc : ∀ b, b ∈ bs → occIncB n D b = true) {m0 m1 : Option Nat}
    (h0 : availD n D m0 = true) (h1 : availD n D m1 = true) :
    (simEvAux n m0 m1 bs).isSome := by
  induction bs with
  | nil => simp [simEvAux]
  | cons b bs ih =>
    rcases Option.isSome_iff_exists.mp
      (serialP_isSome_of_occInc (hc b (List.mem_cons_self b bs)) h0 h1)
      with ⟨l, hl⟩
    rcases Option.isSome_iff_exists.mp
      (ih (fun x hx => hc x (List.mem_cons_of_mem b hx))) with ⟨r, hr⟩
    simp [simEv, simEvAux, hl, hr]

/-! ### Counting: the postprocessing measure -/

theorem countP_le (l : List Nat) (p q : Nat → Bool)
    (h : ∀ x, x ∈ l → p x = true → q x = true) :
    l.countP p ≤ l.countP q := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    have hih := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    by_cases hp : p a = true
    · rw [List.countP_cons_of_pos _ _ hp,
        List.countP_cons_of_pos _ _ (h a (List.mem_cons_self a l) hp)]
      omega
    · rw [List.countP_cons_of_neg _ _ hp]
      by_cases hq : q a = true
      · rw [List.countP_cons_of_pos _ _ hq]
        omega
      · rw [List.countP_cons_of_neg _ _ hq]
        exact hih

theorem countP_lt (l : List Nat) (p q : Nat → Bool)
    (h : ∀ x, x ∈ l → p x = true → q x = true)
    (x0 : Nat) (hx0 : x0 ∈ l) (hpx : p x0 = false) (hqx : q x0 = true) :
    l.countP p < l.countP q := by
  induction l with
  | nil => cases hx0
  | cons a l ih =>
    rcases List.mem_cons.mp hx0 with he | hx0'
    · have hpa : ¬ p a = true := by
        rw [← he, hpx]
        exact Bool.noConfusion
      have hqa : q a = true := by
        rw [← he]
        exact hqx
      rw [List.countP_cons_of_neg _ _ hpa,
        List.countP_cons_of_pos _ _ hqa]
      have := countP_le l p q (fun x hx => h x (List.mem_cons_of_mem a hx))
      omega
    · have hih := ih (fun x hx => h x (List.mem_cons_of_mem a hx)) hx0'
      by_cases hp : p a = true
      · rw [List.countP_cons_of_pos _ _ hp,
          List.countP_cons_of_pos _ _ (h a (List.mem_cons_self a l) hp)]
        omega
      · rw [List.countP_cons_of_neg _ _ hp]
        by_cases hq : q a = true
        · rw [List.countP_cons_of_pos _ _ hq]
          omega
        · rw [List.countP_cons_of_neg _ _ hq]
          exact hih

/-- The measure: occupied cells plus q-stones. -/
def measD (D : Display n) : Nat :=
  (allIdx n).countP (fun i => occD D i)
    + (allIdx n).countP (fun i => kindAt D i == some .r)

theorem measD_le (D : Display n) : measD D ≤ 2 * (n*n) := by
  unfold measD
  have h1 : (allIdx n).countP (fun i => occD D i) ≤ (allIdx n).length :=
    List.countP_le_length _
  have h2 : (allIdx n).countP (fun i => kindAt D i == some .r)
      ≤ (allIdx n).length := List.countP_le_length _
  have hl : (allIdx n).length = n*n := List.length_range (n*n)
  omega

/-! ### Reading a postprocessing round -/

theorem dR_wfd (t : Nat) (M : List (Display n)) (D : Display n) :
    WFD (deltaRound n t M D) := by
  unfold WFD deltaRound
  simp [Array.size_map, Array.size_range]

theorem dR_get_oob (t : Nat) (M : List (Display n)) (D : Display n)
    {i : Nat} (hi : ¬ i < n*n) : (deltaRound n t M D).get i = none := by
  unfold deltaRound
  rw [get_map_range, if_neg hi]

theorem dR_get_in (t : Nat) (M : List (Display n)) (D : Display n)
    {i : Nat} (hi : i < n*n) :
    (deltaRound n t M D).get i
      = (match D.get i with
        | none => none
        | some (k, st) =>
          let (hb, hw) := evSet n M i
          if !hb && !hw then none
          else if k == .r && st == t then
            if hb && !hw then some (.b, st)
            else if hw && !hb then some (.w, st)
            else some (k, st)
          else some (k, st)) := by
  unfold deltaRound
  rw [get_map_range, if_pos hi]
  rfl

theorem dR_get_none (t : Nat) (M : List (Display n)) (D : Display n)
    {i : Nat} (hi : i < n*n) (hg : D.get i = none) :
    (deltaRound n t M D).get i = none := by
  rw [dR_get_in t M D hi, hg]

theorem dR_get_pair (t : Nat) (M : List (Display n)) (D : Display n)
    {i : Nat} (hi : i < n*n) {kk : DKind} {st : Nat}
    (hg : D.get i = some (kk, st)) {hbv hwv : Bool}
    (hev : evSet n M i = (hbv, hwv)) :
    (deltaRound n t M D).get i
      = if (!hbv && !hwv) = true then none
        else if (kk == DKind.r && st == t) = true then
          (if (hbv && !hwv) = true then some (DKind.b, st)
           else if (hwv && !hbv) = true then some (DKind.w, st)
           else some (kk, st))
        else some (kk, st) := by
  rw [dR_get_in t M D hi, hg, hev]

/-- The evSet components witness branch stones. -/
theorem evSet_b {M : List (Display n)} {b : Display n} (hb : b ∈ M)
    {i : Nat} (hk : kindAt b i = some .b) : (evSet n M i).1 = true := by
  show (M.any fun b => kindAt b i == some .b) = true
  exact List.any_eq_true.mpr ⟨b, hb, beq_iff_eq.mpr hk⟩

theorem evSet_w {M : List (Display n)} {b : Display n} (hb : b ∈ M)
    {i : Nat} (hk : kindAt b i = some .w) : (evSet n M i).2 = true := by
  show (M.any fun b => kindAt b i == some .w) = true
  exact List.any_eq_true.mpr ⟨b, hb, beq_iff_eq.mpr hk⟩

theorem evSet_empty_of {M : List (Display n)} {i : Nat}
    (h : ∀ b, b ∈ M → occD b i = false)
    (hcl : ∀ b, b ∈ M → IsClassical b) :
    evSet n M i = (false, false) := by
  show ((M.any fun b => kindAt b i == some .b),
    (M.any fun b => kindAt b i == some .w)) = (false, false)
  have h1 : (M.any fun b => kindAt b i == some .b) = false := by
    cases hany : M.any fun b => kindAt b i == some .b
    · rfl
    · exfalso
      rcases List.any_eq_true.mp hany with ⟨b, hb, hkb⟩
      have := occD_of_kind (beq_iff_eq.mp hkb)
      rw [h b hb] at this
      exact Bool.noConfusion this
  have h2 : (M.any fun b => kindAt b i == some .w) = false := by
    cases hany : M.any fun b => kindAt b i == some .w
    · rfl
    · exfalso
      rcases List.any_eq_true.mp hany with ⟨b, hb, hkb⟩
      have := occD_of_kind (beq_iff_eq.mp hkb)
      rw [h b hb] at this
      exact Bool.noConfusion this
  rw [h1, h2]

theorem evSet_inv {M : List (Display n)} {i : Nat}
    (h : ¬ evSet n M i = (false, false)) :
    ∃ b, b ∈ M ∧ occD b i = true := by
  by_cases h1 : (M.any fun b => kindAt b i == some .b) = true
  · rcases List.any_eq_true.mp h1 with ⟨b, hb, hkb⟩
    exact ⟨b, hb, occD_of_kind (beq_iff_eq.mp hkb)⟩
  · by_cases h2 : (M.any fun b => kindAt b i == some .w) = true
    · rcases List.any_eq_true.mp h2 with ⟨b, hb, hkb⟩
      exact ⟨b, hb, occD_of_kind (beq_iff_eq.mp hkb)⟩
    · exfalso
      apply h
      show ((M.any fun b => kindAt b i == some .b),
        (M.any fun b => kindAt b i == some .w)) = (false, false)
      have e1 : (M.any fun b => kindAt b i == some .b) = false := by
        cases hh : M.any fun b => kindAt b i == some .b
        · rfl
        · exact absurd hh h1
      have e2 : (M.any fun b => kindAt b i == some .w) = false := by
        cases hh : M.any fun b => kindAt b i == some .w
        · rfl
        · exact absurd hh h2
      rw [e1, e2]

/-- A branch stone's intersection survives the round. -/
theorem dR_keeps (t : Nat) (M : List (Display n)) (D : Display n)
    {b : Display n} (hb : b ∈ M) (hclb : IsClassical b)
    {i : Nat} (hi : i < n*n) (hocc : occD b i = true)
    (hDocc : occD D i = true) :
    occD (deltaRound n t M D) i = true := by
  rcases kind_some_of_occ hocc with ⟨k, hk⟩
  have hknr : k ≠ .r := fun h => hclb i (h ▸ hk)
  have hev : ¬ evSet n M i = (false, false) := by
    intro hev
    rcases kind_c_or_opp .b k (by intro h; cases h) hknr with h | h
    · have := evSet_b hb (h ▸ hk)
      rw [hev] at this
      cases this
    · have hkw : k = .w := by
        cases k with
        | b => cases h
        | w => rfl
        | r => exact absurd rfl hknr
      have := evSet_w hb (hkw ▸ hk)
      rw [hev] at this
      cases this
  rcases kind_some_of_occ hDocc with ⟨kD, hkD⟩
  have hgD : ∃ cD, D.get i = some cD := by
    unfold kindAt at hkD
    cases hg : D.get i with
    | none =>
      rw [hg] at hkD
      cases hkD
    | some c => exact ⟨c, rfl⟩
  rcases hgD with ⟨⟨kk, st⟩, hgD⟩
  unfold occD
  rw [dR_get_in t M D hi, hgD]
  -- the match reduces on the pair; the ev-guard is not both-false
  cases hevv : evSet n M i with
  | mk hbv hwv =>
    have hnbf : (!hbv && !hwv) = false := by
      cases hbb : hbv with
      | true => rfl
      | false =>
        cases hww : hwv with
        | true => rfl
        | false =>
          rw [hbb, hww] at hevv
          exact absurd hevv hev
    simp only [hevv, hnbf, Bool.false_eq_true, if_false]
    by_cases hqr : (kk == DKind.r && st == t) = true
    · rw [if_pos hqr]
      cases hbv <;> cases hwv <;> simp
    · rw [if_neg hqr]
      rfl

/-- Occupancy never grows across a round. -/
theorem dR_occ_le (t : Nat) (M : List (Display n)) (D : Display n)
    {i : Nat} (h : occD (deltaRound n t M D) i = true) :
    occD D i = true := by
  by_cases hi : i < n*n
  · unfold occD at h
    rw [dR_get_in t M D hi] at h
    cases hg : D.get i with
    | none =>
      rw [hg] at h
      cases h
    | some c => exact occD_of_kind (by unfold kindAt; rw [hg]; rfl)
  · unfold occD at h
    rw [dR_get_oob t M D hi] at h
    cases h

/-- q-stones never appear across a round. -/
theorem dR_q_le (t : Nat) (M : List (Display n)) (D : Display n)
    {i : Nat} (h : kindAt (deltaRound n t M D) i = some .r) :
    kindAt D i = some .r := by
  by_cases hi : i < n*n
  · unfold kindAt at h
    cases hg : D.get i with
    | none =>
      rw [dR_get_none t M D hi hg] at h
      cases h
    | some c =>
      obtain ⟨kk, st⟩ := c
      cases hevv : evSet n M i with
      | mk hbv hwv =>
        rw [dR_get_pair t M D hi hg hevv] at h
        unfold kindAt
        rw [hg]
        by_cases hnbf : (!hbv && !hwv) = true
        · rw [if_pos hnbf] at h
          cases h
        · rw [if_neg hnbf] at h
          by_cases hqr : (kk == DKind.r && st == t) = true
          · rw [if_pos hqr] at h
            have hkk : kk = .r := by
              rw [Bool.and_eq_true] at hqr
              exact beq_iff_eq.mp hqr.1
            by_cases hb1 : (hbv && !hwv) = true
            · rw [if_pos hb1] at h
              cases h
            · rw [if_neg hb1] at h
              by_cases hw1 : (hwv && !hbv) = true
              · rw [if_pos hw1] at h
                cases h
              · rw [if_neg hw1] at h
                exact h
          · rw [if_neg hqr] at h
            exact h
  · unfold kindAt at h
    rw [dR_get_oob t M D hi] at h
    cases h

/-! ### The measure drops at every changing round -/

theorem dR_meas (t : Nat) (M : List (Display n)) (D : Display n)
    (hwf : WFD D) (hne : ¬ deltaRound n t M D = D) :
    measD (deltaRound n t M D) < measD D := by
  -- a differing cell exists
  have hex : ∃ i, i < n*n ∧ (deltaRound n t M D).get i ≠ D.get i := by
    apply Classical.byContradiction
    intro hall
    apply hne
    have hget : ∀ i, i < n*n → (deltaRound n t M D).get i = D.get i :=
      fun i hi => Classical.byContradiction
        (fun hne' => hall ⟨i, hi, hne'⟩)
    apply display_ext
    apply Array.ext
    · rw [show (deltaRound n t M D).cells.size = n*n from dR_wfd t M D,
        hwf]
    · intro p h1 h2
      have hpb : p < n*n := by
        have := dR_wfd t M D
        unfold WFD at this
        omega
      rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2]
      exact hget p hpb
  rcases hex with ⟨i0, hi0, hdiff⟩
  -- classify the change at i0
  have hocc_le : ∀ x, x ∈ allIdx n →
      (occD (deltaRound n t M D) x) = true → occD D x = true :=
    fun x _ h => dR_occ_le t M D h
  have hq_le : ∀ x, x ∈ allIdx n →
      (kindAt (deltaRound n t M D) x == some DKind.r) = true →
      (kindAt D x == some DKind.r) = true :=
    fun x _ h => beq_iff_eq.mpr (dR_q_le t M D (beq_iff_eq.mp h))
  cases hg : D.get i0 with
  | none =>
    exfalso
    apply hdiff
    rw [dR_get_none t M D hi0 hg, hg]
  | some c =>
    obtain ⟨kk, st⟩ := c
    cases hevv : evSet n M i0 with
    | mk hbv hwv =>
      have hread := dR_get_pair t M D hi0 hg hevv
      by_cases hnbf : (!hbv && !hwv) = true
      · -- the cell is removed: occupancy strictly drops
        rw [if_pos hnbf] at hread
        have hoccD : occD D i0 = true :=
          occD_of_kind (by unfold kindAt; rw [hg]; rfl)
        have hoccD' : occD (deltaRound n t M D) i0 = false := by
          unfold occD
          rw [hread]
          rfl
        unfold measD
        have h1 : (allIdx n).countP (fun i => occD (deltaRound n t M D) i)
            < (allIdx n).countP (fun i => occD D i) :=
          countP_lt _ _ _ hocc_le i0 (List.mem_range.mpr hi0)
            hoccD' hoccD
        have h2 : (allIdx n).countP
            (fun i => kindAt (deltaRound n t M D) i == some DKind.r)
            ≤ (allIdx n).countP (fun i => kindAt D i == some DKind.r) :=
          countP_le _ _ _ hq_le
        omega
      · rw [if_neg hnbf] at hread
        by_cases hqr : (kk == DKind.r && st == t) = true
        · rw [if_pos hqr] at hread
          have hkk : kk = DKind.r := by
            rw [Bool.and_eq_true] at hqr
            exact beq_iff_eq.mp hqr.1
          by_cases hb1 : (hbv && !hwv) = true
          · -- recolored black: the q-stone count strictly drops
            rw [if_pos hb1] at hread
            have hqD : (kindAt D i0 == some DKind.r) = true := by
              apply beq_iff_eq.mpr
              unfold kindAt
              rw [hg, hkk]
              rfl
            have hqD' : (kindAt (deltaRound n t M D) i0
                == some DKind.r) = false := by
              unfold kindAt
              rw [hread]
              rfl
            unfold measD
            have h1 : (allIdx n).countP
                (fun i => occD (deltaRound n t M D) i)
                ≤ (allIdx n).countP (fun i => occD D i) :=
              countP_le _ _ _ hocc_le
            have h2 : (allIdx n).countP
                (fun i => kindAt (deltaRound n t M D) i == some DKind.r)
                < (allIdx n).countP
                  (fun i => kindAt D i == some DKind.r) :=
              countP_lt _ _ _ hq_le i0 (List.mem_range.mpr hi0)
                hqD' hqD
            omega
          · rw [if_neg hb1] at hread
            by_cases hw1 : (hwv && !hbv) = true
            · rw [if_pos hw1] at hread
              have hqD : (kindAt D i0 == some DKind.r) = true := by
                apply beq_iff_eq.mpr
                unfold kindAt
                rw [hg, hkk]
                rfl
              have hqD' : (kindAt (deltaRound n t M D) i0
                  == some DKind.r) = false := by
                unfold kindAt
                rw [hread]
                rfl
              unfold measD
              have h1 : (allIdx n).countP
                  (fun i => occD (deltaRound n t M D) i)
                  ≤ (allIdx n).countP (fun i => occD D i) :=
                countP_le _ _ _ hocc_le
              have h2 : (allIdx n).countP
                  (fun i => kindAt (deltaRound n t M D) i
                    == some DKind.r)
                  < (allIdx n).countP
                    (fun i => kindAt D i == some DKind.r) :=
                countP_lt _ _ _ hq_le i0 (List.mem_range.mpr hi0)
                  hqD' hqD
              omega
            · rw [if_neg hw1] at hread
              exfalso
              apply hdiff
              rw [hread, hg, hkk]
        · rw [if_neg hqr] at hread
          exfalso
          apply hdiff
          rw [hread, hg]

/-! ### The recursion reaches its fixpoint -/

theorem recut_mem (D : Display n) (M : List (Display n)) (b : Display n) :
    b ∈ recut n D M ↔ b ∈ M ∧ occIncB n D b = true := by
  unfold recut
  rw [List.mem_filter]
  rfl

/-- The postprocessing output: the re-cut is vacuous, inclusion is
    preserved, and the display is supported by the branches. -/
theorem deltaAux_out (t : Nat) (fuel : Nat) :
    ∀ (D : Display n) (M : List (Display n)),
    WFD D → measD D < fuel →
    (∀ b, b ∈ M → IsClassical b) →
    (∀ b, b ∈ M → occIncB n D b = true) →
    (∀ b, b ∈ (deltaAux n t fuel D M).2 ↔ b ∈ M)
    ∧ WFD (deltaAux n t fuel D M).1
    ∧ (∀ b, b ∈ M → occIncB n (deltaAux n t fuel D M).1 b = true)
    ∧ (∀ i, i < n*n → occD (deltaAux n t fuel D M).1 i = true →
        ∃ b, b ∈ M ∧ occD b i = true) := by
  induction fuel with
  | zero =>
    intro D M _ hfuel _ _
    omega
  | succ fuel ih =>
    intro D M hwf hfuel hcl hinc
    have hkeep : ∀ b, b ∈ M →
        occIncB n (deltaRound n t M D) b = true := by
      intro b hb
      unfold occIncB
      rw [List.all_eq_true]
      intro i hi
      cases hk : kindAt b i with
      | none =>
        apply bool_or_right
        exact beq_iff_eq.mpr rfl
      | some k =>
        apply bool_or_left
        have hocc : occD b i = true := occD_of_kind hk
        have hDocc : occD D i = true := by
          have hci := (List.all_eq_true.mp (hinc b hb)) i hi
          rcases bool_or_elim hci with h | h
          · exact h
          · exfalso
            have := beq_iff_eq.mp h
            rw [hk] at this
            cases this
        exact dR_keeps t M D hb (hcl b hb) (List.mem_range.mp hi)
          hocc hDocc
    have hrecut : ∀ b, b ∈ recut n (deltaRound n t M D) M ↔ b ∈ M := by
      intro b
      rw [recut_mem]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, hkeep b h⟩
    have hunf : deltaAux n t (fuel+1) D M
        = if (deltaRound n t M D == D) = true
          then (deltaRound n t M D, recut n (deltaRound n t M D) M)
          else deltaAux n t fuel (deltaRound n t M D)
            (recut n (deltaRound n t M D) M) := rfl
    by_cases htest : (deltaRound n t M D == D) = true
    · rw [hunf, if_pos htest]
      have heq : deltaRound n t M D = D := display_eq_of_beq htest
      refine ⟨hrecut, ?_, ?_, ?_⟩
      · show WFD (deltaRound n t M D)
        exact dR_wfd t M D
      · intro b hb
        show occIncB n (deltaRound n t M D) b = true
        exact hkeep b hb
      · intro i hi hocc
        apply Classical.byContradiction
        intro hno
        have hall : ∀ b, b ∈ M → occD b i = false := by
          intro b hb
          cases hoc : occD b i
          · rfl
          · exact absurd ⟨b, hb, hoc⟩ hno
        have hev := evSet_empty_of hall hcl
        have hoccD : occD D i = true := by
          rw [← heq]
          exact hocc
        rcases kind_some_of_occ hoccD with ⟨k, hkD⟩
        have hgD : ∃ c, D.get i = some c := by
          unfold kindAt at hkD
          cases hg : D.get i with
          | none =>
            rw [hg] at hkD
            cases hkD
          | some c => exact ⟨c, rfl⟩
        rcases hgD with ⟨⟨kk, st⟩, hgD⟩
        have hread := dR_get_pair t M D hi hgD hev
        rw [if_pos (show ((!false && !false) = true) from rfl)] at hread
        have : occD (deltaRound n t M D) i = false := by
          unfold occD
          rw [hread]
          rfl
        rw [heq, hoccD] at this
        exact Bool.noConfusion this
    · rw [hunf, if_neg htest]
      have hne : ¬ deltaRound n t M D = D := by
        intro he
        rw [he] at htest
        exact htest (display_beq_self D)
      have hmeas : measD (deltaRound n t M D) < fuel := by
        have := dR_meas t M D hwf hne
        omega
      have hcl' : ∀ b, b ∈ recut n (deltaRound n t M D) M →
          IsClassical b :=
        fun b hb => hcl b ((hrecut b).mp hb)
      have hinc' : ∀ b, b ∈ recut n (deltaRound n t M D) M →
          occIncB n (deltaRound n t M D) b = true :=
        fun b hb => hkeep b ((hrecut b).mp hb)
      rcases ih (deltaRound n t M D) (recut n (deltaRound n t M D) M)
        (dR_wfd t M D) hmeas hcl' hinc' with ⟨hm, hw, hoi, hsup⟩
      refine ⟨?_, hw, ?_, ?_⟩
      · intro b
        rw [hm b]
        exact hrecut b
      · intro b hb
        exact hoi b ((hrecut b).mpr hb)
      · intro i hi hocc
        rcases hsup i hi hocc with ⟨b, hb, hocb⟩
        exact ⟨b, (hrecut b).mp hb, hocb⟩

/-- The shipped fuel reaches the fixpoint. -/
theorem delta_out (t : Nat) (D : Display n) (M : List (Display n))
    (hwf : WFD D)
    (hcl : ∀ b, b ∈ M → IsClassical b)
    (hinc : ∀ b, b ∈ M → occIncB n D b = true) :
    (∀ b, b ∈ (delta n t D M).2 ↔ b ∈ M)
    ∧ WFD (delta n t D M).1
    ∧ (∀ b, b ∈ M → occIncB n (delta n t D M).1 b = true)
    ∧ (∀ i, i < n*n → occD (delta n t D M).1 i = true →
        ∃ b, b ∈ M ∧ occD b i = true) := by
  have hfuel : measD D < 2*(n*n) + 2 := by
    have := measD_le D
    omega
  exact deltaAux_out t (2*(n*n) + 2) D M hwf hfuel hcl hinc

end SgoDInv
