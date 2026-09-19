/- Infra4.lean — liberty characterization, component transport, and
   board-neighbor existence: the toolkit for Step 0 and the classical
   steps. -/
import Infra3
open SgoDisplay

variable {n : Nat}

/-! ### noLibD characterization ("has a liberty"). -/

theorem noLibD_eq_false_iff (D : Display n) (comp : List Nat) :
    noLibD D comp = false ↔
    ∃ q, q ∈ allIdx n ∧ occD D q = false ∧
      ∃ r, r ∈ comp ∧ adjI n q r = true := by
  unfold noLibD
  rw [List.all_eq_false]
  constructor
  · rintro ⟨q, hq, hp⟩
    rw [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    exact ⟨q, hq, hp.1, List.any_eq_true.mp hp.2⟩
  · rintro ⟨q, hq, hocc, r, hr, hadj⟩
    refine ⟨q, hq, ?_⟩
    rw [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true,
      Bool.not_eq_true']
    exact ⟨hocc, List.any_eq_true.mpr ⟨r, hr, hadj⟩⟩

/-! ### Membership congruence. -/

theorem any_congr_mem (l l' : List Nat) (p : Nat → Bool)
    (h : ∀ x, x ∈ l ↔ x ∈ l') : l.any p = l'.any p := by
  cases hb : l.any p
  · cases ha : l'.any p
    · rfl
    · rcases List.any_eq_true.mp ha with ⟨x, hx, hpx⟩
      have hcontra : l.any p = true :=
        List.any_eq_true.mpr ⟨x, (h x).mpr hx, hpx⟩
      rw [hb] at hcontra
      exact Bool.noConfusion hcontra
  · symm
    rcases List.any_eq_true.mp hb with ⟨x, hx, hpx⟩
    exact List.any_eq_true.mpr ⟨x, (h x).mp hx, hpx⟩

/-- noLibD sees only the membership of the component list. -/
theorem noLibD_congr (D : Display n) (l l' : List Nat)
    (h : ∀ x, x ∈ l ↔ x ∈ l') : noLibD D l = noLibD D l' := by
  unfold noLibD
  have hfun : (fun q => !(!occD D q && l.any fun r => adjI n q r))
      = (fun q => !(!occD D q && l'.any fun r => adjI n q r)) :=
    funext fun q => by rw [any_congr_mem l l' _ h]
  rw [hfun]

/-! ### ConnK is an equivalence on kind-k board stones. -/

theorem ConnK_kind {D : Display n} {k : DKind} {i q : Nat}
    (hk : kindAt D i = some k) (h : ConnK D k i q) :
    kindAt D q = some k := by
  cases h with
  | refl => exact hk
  | step _ _ hqk _ => exact hqk

theorem ConnK_board {D : Display n} {k : DKind} {i q : Nat}
    (hi : i ∈ allIdx n) (h : ConnK D k i q) : q ∈ allIdx n := by
  cases h with
  | refl => exact hi
  | step _ hqi _ _ => exact hqi

theorem ConnK_trans {D : Display n} {k : DKind} {i j q : Nat}
    (h1 : ConnK D k i j) (h2 : ConnK D k j q) : ConnK D k i q := by
  induction h2 with
  | refl => exact h1
  | step _ hqi hqk hadj ih => exact ConnK.step ih hqi hqk hadj

theorem ConnK_symm {D : Display n} {k : DKind} {i q : Nat}
    (hi : i ∈ allIdx n) (hik : kindAt D i = some k)
    (h : ConnK D k i q) : ConnK D k q i := by
  induction h with
  | refl => exact ConnK.refl
  | step hc hqi hqk hadj ih =>
    exact ConnK_trans
      (ConnK.step ConnK.refl (ConnK_board hi hc) (ConnK_kind hik hc)
        (adjI_symm hadj)) ih

/-- Two members of one component have membership-equal components. -/
theorem componentD_eq_mem (D : Display n) (i j : Nat) (k : DKind)
    (hib : i ∈ allIdx n) (hik : kindAt D i = some k)
    (hj : j ∈ componentD D i) :
    ∀ q, q ∈ componentD D j ↔ q ∈ componentD D i := by
  have hconn : ConnK D k i j := (componentD_mem_iff D i k hik j).mp hj
  have hjk : kindAt D j = some k := ConnK_kind hik hconn
  intro q
  rw [componentD_mem_iff D i k hik q, componentD_mem_iff D j k hjk q]
  exact ⟨fun h => ConnK_trans hconn h,
    fun h => ConnK_trans (ConnK_symm hib hik hconn) h⟩

/-! ### Transport across displays agreeing on kind-k cells. -/

theorem ConnK_transport (D E : Display n) (k : DKind)
    (hagree : ∀ z, z ∈ allIdx n →
      kindAt D z = some k → kindAt E z = some k)
    {i q : Nat} (h : ConnK D k i q) : ConnK E k i q := by
  induction h with
  | refl => exact ConnK.refl
  | step _ hqi hqk hadj ih => exact ConnK.step ih hqi (hagree _ hqi hqk) hadj

theorem componentD_transport (D E : Display n) (k : DKind)
    (hagree : ∀ z, z ∈ allIdx n →
      (kindAt D z = some k ↔ kindAt E z = some k))
    (i : Nat) (hkD : kindAt D i = some k) (hkE : kindAt E i = some k)
    (q : Nat) : q ∈ componentD D i ↔ q ∈ componentD E i := by
  rw [componentD_mem_iff D i k hkD q, componentD_mem_iff E i k hkE q]
  exact ⟨ConnK_transport D E k (fun z hz => (hagree z hz).mp),
    ConnK_transport E D k (fun z hz => (hagree z hz).mpr)⟩

/-! ### Every board intersection has a neighbor (n ≥ 2). -/

theorem exists_neighbor (hn : 2 ≤ n) (i : Nat) (hi : i < n*n) :
    ∃ j, j < n*n ∧ adjI n j i = true := by
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hyd : n * (i / n) + i % n = i := Nat.div_add_mod i n
  have hylt : i % n < n := Nat.mod_lt i hn0
  have hxlt : i / n < n := (Nat.div_lt_iff_lt_mul hn0).mpr hi
  by_cases hy : i % n + 1 < n
  · refine ⟨i+1, ?_, ?_⟩
    · have hnn : n * (i / n + 1) ≤ n * n := Nat.mul_le_mul_left n hxlt
      have hstep : n * (i / n + 1) = n * (i / n) + n := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    · have heq : i + 1 = n * (i / n) + (i % n + 1) := by omega
      have hd : (i+1) / n = i / n := by
        rw [heq, Nat.mul_add_div hn0, Nat.div_eq_of_lt hy]
        exact Nat.add_zero _
      have hm : (i+1) % n = i % n + 1 := by
        rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
      simp only [adjI]
      rw [hd, hm]
      simp
  · have hy1 : 1 ≤ i % n := by omega
    have hmlt : i % n - 1 < n := by omega
    refine ⟨i-1, ?_, ?_⟩
    · omega
    · have heq : i - 1 = n * (i / n) + (i % n - 1) := by omega
      have hd : (i-1) / n = i / n := by
        rw [heq, Nat.mul_add_div hn0, Nat.div_eq_of_lt hmlt]
        exact Nat.add_zero _
      have hm : (i-1) % n = i % n - 1 := by
        rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hmlt]
      simp only [adjI]
      rw [hd, hm, Nat.sub_add_cancel hy1]
      simp
