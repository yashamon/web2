/- SgoBridge.lean — the main theorem, milestone 2e: the abstract↔executable
   bridge, on the option-C bigraded semantics.

   The uniform # computations on Go's states: a black move lands in
   S_{1,0} and a white move in S_{0,0}, with the SAME core action from
   every live state of the position — the content that makes the
   position normal form faithful to play. Then the chain computations
   for the four slot shapes, and the correspondence: the # chains at a
   position normal form are the concrete bStep chains, tagged by their
   bigrading; both chains' tags share one normal form (repP), so P at
   a normal form is serialP's output, represented. No corner cases:
   normal-form inputs have pass grading 0. -/
import SgoOK

open SgoGo SgoDisplay SgoSerial SgoGames SgoInv

namespace SgoBridge

variable {n : Nat}

/-- Black's and White's slot moves. -/
def mB (o : Option Nat) : goMv.M := o.map fun i => (false, i)
def mW (o : Option Nat) : goMv.M := o.map fun i => (true, i)

/-! ### sE on Go, computed -/

/-- No core of Go is ended by play: the game ends by a double pass
    alone, so the pass is defined at every live state (the printed
    stipulation). -/
theorem go_not_ended (d : Display n) : ¬(goGame n).ended d := fun h => h

theorem sE_pass_j0 (d : Display n) (g : Bool) :
    sE (goGame n) (.live d g false) goMv.pass = some (.live d (!g) true) :=
  prop_pass0 (goGame n) d g (go_not_ended d)

theorem sE_pass_j1 (d : Display n) (g : Bool) :
    sE (goGame n) (.live d g true) goMv.pass = some (.done d (!g)) :=
  prop_pass1 (goGame n) d g (go_not_ended d)

theorem sE_black_at0 (d : Display n) (j : Bool) (i : Nat) :
    sE (goGame n) (.live d false j) (some (false, i))
      = (goMvAct n d (some (false, i))).map
          (fun d' => PState.live d' true false) := by
  rw [sE_nonpass (goGame n) d false j _ (by simp [goMv]) (go_not_ended d),
    if_pos (Or.inl ⟨rfl, Or.inr ⟨i, rfl⟩⟩)]
  rfl

theorem sE_black_at1 (d : Display n) (j : Bool) (i : Nat) :
    sE (goGame n) (.live d true j) (some (false, i)) = none := by
  rw [sE_nonpass (goGame n) d true j _ (by simp [goMv]) (go_not_ended d), if_neg]
  rintro (⟨hg, _⟩ | ⟨_, hd⟩)
  · cases hg
  · rcases hd with h | ⟨i', hi'⟩
    · cases h
    · cases hi'

theorem sE_white_at1 (d : Display n) (j : Bool) (i : Nat) :
    sE (goGame n) (.live d true j) (some (true, i))
      = (goMvAct n d (some (true, i))).map
          (fun d' => PState.live d' false false) := by
  rw [sE_nonpass (goGame n) d true j _ (by simp [goMv]) (go_not_ended d),
    if_pos (Or.inr ⟨rfl, Or.inr ⟨i, rfl⟩⟩)]
  rfl

theorem sE_white_at0 (d : Display n) (j : Bool) (i : Nat) :
    sE (goGame n) (.live d false j) (some (true, i)) = none := by
  rw [sE_nonpass (goGame n) d false j _ (by simp [goMv]) (go_not_ended d), if_neg]
  rintro (⟨_, hd⟩ | ⟨hg, _⟩)
  · rcases hd with h | ⟨i', hi'⟩
    · cases h
    · cases hi'
  · cases hg

/-! ### hashOp on Go: uniform over the position's live states -/

theorem goHash_black (d : Display n) (g j : Bool) (i : Nat) :
    hashOp (goGame n) (.live d g j) (some (false, i))
      = (goMvAct n d (some (false, i))).map
          (fun d' => PState.live d' true false) := by
  cases g with
  | false =>
    unfold hashOp
    rw [sE_black_at0]
    cases hm : goMvAct n d (some (false, i)) with
    | some d' => simp [hm]
    | none =>
      simp only [hm, Option.map_none']
      cases j <;> simp [sBar, sE_black_at1]
  | true =>
    unfold hashOp
    rw [sE_black_at1]
    cases j <;> simp [sBar, sE_black_at0]

theorem goHash_white (d : Display n) (g j : Bool) (i : Nat) :
    hashOp (goGame n) (.live d g j) (some (true, i))
      = (goMvAct n d (some (true, i))).map
          (fun d' => PState.live d' false false) := by
  cases g with
  | true =>
    unfold hashOp
    rw [sE_white_at1]
    cases hm : goMvAct n d (some (true, i)) with
    | some d' => simp [hm]
    | none =>
      simp only [hm, Option.map_none']
      cases j <;> simp [sBar, sE_white_at0]
  | false =>
    unfold hashOp
    rw [sE_white_at0]
    cases j <;> simp [sBar, sE_white_at1]

theorem goHash_pass_j0 (d : Display n) (g : Bool) :
    hashOp (goGame n) (.live d g false) goMv.pass
      = some (.live d (!g) true) := by
  unfold hashOp
  rw [sE_pass_j0]

theorem goHash_pass_j1 (d : Display n) (g : Bool) :
    hashOp (goGame n) (.live d g true) goMv.pass
      = some (.done d (!g)) := by
  unfold hashOp
  rw [sE_pass_j1]

/-! ### Lawfulness of the derived Boolean equalities -/

instance : LawfulBEq DKind where
  eq_of_beq {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
  rfl {x} := by cases x <;> rfl

instance instLawfulBEqArray {α : Type} [BEq α] [LawfulBEq α] :
    LawfulBEq (Array α) where
  eq_of_beq {a b} h := by
    rw [Array.beq_eq_decide] at h
    by_cases hs : a.size = b.size
    · rw [dif_pos hs] at h
      exact Array.ext a b hs fun i h1 _ =>
        eq_of_beq (of_decide_eq_true h i h1)
    · rw [dif_neg hs] at h
      cases h
  rfl {a} := by
    rw [Array.beq_eq_decide, dif_pos rfl]
    exact decide_eq_true fun i h' => LawfulBEq.rfl

instance : LawfulBEq (Display n) where
  eq_of_beq {x y} h := by
    cases x with
    | mk cx =>
      cases y with
      | mk cy =>
        have h' : (cx == cy) = true := h
        exact congrArg Display.mk (eq_of_beq h')
  rfl {x} := by
    cases x with
    | mk cx => show (cx == cx) = true; exact LawfulBEq.rfl

/-- Deduplication is membership-invariant (both directions; the
    forward one is SgoInv's mem_dedupD). -/
theorem mem_dedupD_iff (l : List (Display n)) (x : Display n) :
    x ∈ dedupD n l ↔ x ∈ l := by
  constructor
  · exact mem_dedupD l x
  · induction l with
    | nil => intro hx; cases hx
    | cons y ys ih =>
      intro hx
      simp only [dedupD]
      rcases List.mem_cons.mp hx with h | h
      · rw [h]
        by_cases hc : (dedupD n ys).contains y = true
        · rw [if_pos hc]
          exact List.contains_iff_mem.mp hc
        · rw [if_neg hc]
          exact List.mem_cons_self y (dedupD n ys)
      · have hin := ih h
        by_cases hc : (dedupD n ys).contains y = true
        · rw [if_pos hc]; exact hin
        · rw [if_neg hc]; exact List.mem_cons_of_mem y hin

/-! ### The chains at a position normal form -/

/-- The bigrading tag of the black-first chain. -/
def tag01 (m0 m1 : Option Nat) (e : Display n) : PState (Display n) :=
  match m0, m1 with
  | some _, some _ => .live e false false
  | some _, none   => .live e false true
  | none,   some _ => .live e false false
  | none,   none   => .done e false

/-- The bigrading tag of the white-first chain. -/
def tag10 (m0 m1 : Option Nat) (e : Display n) : PState (Display n) :=
  match m0, m1 with
  | some _, some _ => .live e true false
  | some _, none   => .live e true false
  | none,   some _ => .live e true true
  | none,   none   => .done e false

/-- The common normal form of both tags. -/
def repP (m0 m1 : Option Nat) (e : Display n) : PState (Display n) :=
  match m0, m1 with
  | none, none => .done e false
  | _, _ => .live e false false

theorem sN_tag01 (m0 m1 : Option Nat) (e : Display n) :
    sN (tag01 m0 m1 e) = repP m0 m1 e := by
  cases m0 <;> cases m1 <;> rfl

theorem sN_tag10 (m0 m1 : Option Nat) (e : Display n) :
    sN (tag10 m0 m1 e) = repP m0 m1 e := by
  cases m0 <;> cases m1 <;> rfl

theorem repP_inj (m0 m1 : Option Nat) (e e' : Display n)
    (h : repP m0 m1 e = repP m0 m1 e') : e = e' := by
  cases m0 <;> cases m1 <;>
    simp only [repP] at h <;>
    cases h <;> rfl

/-- goMvAct is goMoveN at in-bounds indices: the black move. The color
    is delivered reduced, so rewriting leaves a bare goMoveN in the
    goal and case analysis on it substitutes. -/
theorem goMvAct_b (d : Display n) {i : Nat} (hi : i < n*n) :
    goMvAct n d (some (false, i)) = goMoveN n d .b i := by
  show (if i < n*n then goMoveN n d .b i else none) = goMoveN n d .b i
  rw [if_pos hi]

/-- goMvAct is goMoveN at in-bounds indices: the white move. -/
theorem goMvAct_w (d : Display n) {i : Nat} (hi : i < n*n) :
    goMvAct n d (some (true, i)) = goMoveN n d .w i := by
  show (if i < n*n then goMoveN n d .w i else none) = goMoveN n d .w i
  rw [if_pos hi]

/-- The black-first chain is the concrete composite, tagged. -/
theorem hash2_01 (d : Display n) (m0 m1 : Option Nat)
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n) :
    hash2 (goGame n) (.live d false false) (mB m0) (mW m1)
      = (bStep2 n d .b .w m0 m1).map (tag01 m0 m1) := by
  cases m0 with
  | none =>
    cases m1 with
    | none =>
      unfold hash2
      rw [show mB none = goMv.pass from rfl, goHash_pass_j0]
      show hashOp (goGame n) (PState.live d (!false) true) (mW none)
        = (bStep2 n d .b .w none none).map (tag01 none none)
      rw [show mW none = goMv.pass from rfl, goHash_pass_j1]
      rfl
    | some i1 =>
      unfold hash2
      rw [show mB none = goMv.pass from rfl, goHash_pass_j0]
      show hashOp (goGame n) (PState.live d (!false) true) (mW (some i1))
        = (bStep2 n d .b .w none (some i1)).map (tag01 none (some i1))
      rw [show mW (some i1) = some (true, i1) from rfl,
        goHash_white d (!false) true i1, goMvAct_w d (h1 i1 rfl)]
      cases hg : goMoveN n d .w i1 <;> simp [bStep2, bStep, hg, tag01]
  | some i0 =>
    unfold hash2
    rw [show mB (some i0) = some (false, i0) from rfl,
      goHash_black d false false i0, goMvAct_b d (h0 i0 rfl)]
    cases m1 with
    | none =>
      cases hg : goMoveN n d .b i0 with
      | none => simp [hg, bStep2, bStep]
      | some d1 =>
        show hashOp (goGame n) (PState.live d1 true false) (mW none)
          = (bStep2 n d .b .w (some i0) none).map (tag01 (some i0) none)
        rw [show mW none = goMv.pass from rfl, goHash_pass_j0]
        simp [bStep2, bStep, hg, tag01]
    | some i1 =>
      cases hg : goMoveN n d .b i0 with
      | none => simp [hg, bStep2, bStep]
      | some d1 =>
        show hashOp (goGame n) (PState.live d1 true false) (mW (some i1))
          = (bStep2 n d .b .w (some i0) (some i1)).map
              (tag01 (some i0) (some i1))
        rw [show mW (some i1) = some (true, i1) from rfl,
          goHash_white d1 true false i1, goMvAct_w d1 (h1 i1 rfl)]
        cases hg1 : goMoveN n d1 .w i1 <;>
          simp [bStep2, bStep, hg, hg1, tag01]

/-- The white-first chain is the concrete composite, tagged. -/
theorem hash2_10 (d : Display n) (m0 m1 : Option Nat)
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n) :
    hash2 (goGame n) (.live d false false) (mW m1) (mB m0)
      = (bStep2 n d .w .b m1 m0).map (tag10 m0 m1) := by
  cases m1 with
  | none =>
    cases m0 with
    | none =>
      unfold hash2
      rw [show mW none = goMv.pass from rfl, goHash_pass_j0]
      show hashOp (goGame n) (PState.live d (!false) true) (mB none)
        = (bStep2 n d .w .b none none).map (tag10 none none)
      rw [show mB none = goMv.pass from rfl, goHash_pass_j1]
      rfl
    | some i0 =>
      unfold hash2
      rw [show mW none = goMv.pass from rfl, goHash_pass_j0]
      show hashOp (goGame n) (PState.live d (!false) true) (mB (some i0))
        = (bStep2 n d .w .b none (some i0)).map (tag10 (some i0) none)
      rw [show mB (some i0) = some (false, i0) from rfl,
        goHash_black d (!false) true i0, goMvAct_b d (h0 i0 rfl)]
      cases hg : goMoveN n d .b i0 <;> simp [bStep2, bStep, hg, tag10]
  | some i1 =>
    unfold hash2
    rw [show mW (some i1) = some (true, i1) from rfl,
      goHash_white d false false i1, goMvAct_w d (h1 i1 rfl)]
    cases m0 with
    | none =>
      cases hg : goMoveN n d .w i1 with
      | none => simp [hg, bStep2, bStep]
      | some d1 =>
        show hashOp (goGame n) (PState.live d1 false false) (mB none)
          = (bStep2 n d .w .b (some i1) none).map (tag10 none (some i1))
        rw [show mB none = goMv.pass from rfl, goHash_pass_j0]
        simp [bStep2, bStep, hg, tag10]
    | some i0 =>
      cases hg : goMoveN n d .w i1 with
      | none => simp [hg, bStep2, bStep]
      | some d1 =>
        show hashOp (goGame n) (PState.live d1 false false) (mB (some i0))
          = (bStep2 n d .w .b (some i1) (some i0)).map
              (tag10 (some i0) (some i1))
        rw [show mB (some i0) = some (false, i0) from rfl,
          goHash_black d1 false false i0, goMvAct_b d1 (h0 i0 rfl)]
        cases hg1 : goMoveN n d1 .b i0 <;>
          simp [bStep2, bStep, hg, hg1, tag10]

/-! ### The single # at a position normal form -/

/-- The bigrading tag of a lone black move: a pass raises the pass
    grading, a real move flips the turn. -/
def tagB (m0 : Option Nat) (e : Display n) : PState (Display n) :=
  match m0 with
  | some _ => .live e true false
  | none   => .live e true true

/-- The bigrading tag of a lone white move from grading (0,0): the
    real move is played at bar (the # fallback), landing back at turn
    grading 0. -/
def tagW (m1 : Option Nat) (e : Display n) : PState (Display n) :=
  match m1 with
  | some _ => .live e false false
  | none   => .live e true true

theorem hash1_B (d : Display n) (m0 : Option Nat)
    (h0 : ∀ i, m0 = some i → i < n*n) :
    hashOp (goGame n) (.live d false false) (mB m0)
      = (bStep n d .b m0).map (tagB m0) := by
  cases m0 with
  | none =>
    rw [show mB none = goMv.pass from rfl, goHash_pass_j0]
    rfl
  | some i =>
    rw [show mB (some i) = some (false, i) from rfl,
      goHash_black d false false i, goMvAct_b d (h0 i rfl)]
    rfl

theorem hash1_W (d : Display n) (m1 : Option Nat)
    (h1 : ∀ i, m1 = some i → i < n*n) :
    hashOp (goGame n) (.live d false false) (mW m1)
      = (bStep n d .w m1).map (tagW m1) := by
  cases m1 with
  | none =>
    rw [show mW none = goMv.pass from rfl, goHash_pass_j0]
    rfl
  | some i =>
    rw [show mW (some i) = some (true, i) from rfl,
      goHash_white d false false i, goMvAct_w d (h1 i rfl)]
    rfl

theorem sN_tagB (m0 : Option Nat) (e : Display n) :
    sN (tagB m0 e) = PState.live e false false := by
  cases m0 <;> rfl

theorem sN_tagW (m1 : Option Nat) (e : Display n) :
    sN (tagW m1 e) = PState.live e false false := by
  cases m1 <;> rfl

/-- Away from the double pass, the common normal form is live. -/
theorem repP_live {m0 m1 : Option Nat}
    (h : ¬(m0 = none ∧ m1 = none)) (e : Display n) :
    repP m0 m1 e = PState.live e false false := by
  cases m0 with
  | some i => rfl
  | none =>
    cases m1 with
    | some j => rfl
    | none => exact absurd ⟨rfl, rfl⟩ h

theorem bStep2_pass_pass (d : Display n) (c0 c1 : DKind) :
    bStep2 n d c0 c1 none none = some d := rfl

/-! ### P at a position normal form is serialP, represented

    Both argument orders (the raw moves of a joint turn arrive in
    either order); serialP is order-normalized by construction. The
    two clauses per order: definedness agrees, and every branch of
    serialP's output is a member of P's output under repP. -/

theorem Pmap_BW_corr (d : Display n) (m0 m1 : Option Nat)
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n) :
    (Pmap (goGame n) (.live d false false) (mB m0) (mW m1)).isSome
        = (serialP n d m0 m1).isSome
    ∧ ∀ l, serialP n d m0 m1 = some l → ∀ e, e ∈ l →
        ∃ P, Pmap (goGame n) (.live d false false) (mB m0) (mW m1) = some P
          ∧ P (repP m0 m1 e) := by
  have e01 := hash2_01 d m0 m1 h0 h1
  have e10 := hash2_10 d m0 m1 h0 h1
  cases hx : bStep2 n d .b .w m0 m1 with
  | some x =>
    rw [hx] at e01
    cases hy : bStep2 n d .w .b m1 m0 with
    | some y =>
      rw [hy] at e10
      have hp : Pmap (goGame n) (.live d false false) (mB m0) (mW m1)
          = some (BSet.pair (sN (tag01 m0 m1 x)) (sN (tag10 m0 m1 y))) := by
        unfold Pmap; rw [e01, e10]; rfl
      have hs : serialP n d m0 m1 = some (dedupD n [x, y]) := by
        unfold serialP; rw [hx, hy]
      refine ⟨by simp [hp, hs], ?_⟩
      intro l hl e he
      rw [hs] at hl
      cases hl
      refine ⟨_, hp, ?_⟩
      rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp he) with h | h
      · rw [h, sN_tag01]; exact Or.inl rfl
      · rw [List.mem_singleton.mp h, sN_tag10]; exact Or.inr rfl
    | none =>
      rw [hy] at e10
      have hnn : ¬(m0 = none ∧ m1 = none) := by
        rintro ⟨rfl, rfl⟩
        rw [bStep2_pass_pass] at hy
        cases hy
      have h1W := hash1_W d m1 h1
      cases hw : bStep n d .w m1 with
      | some yw =>
        rw [hw] at h1W
        have hp : Pmap (goGame n) (.live d false false) (mB m0) (mW m1)
            = some (BSet.pair (sN (tag01 m0 m1 x)) (sN (tagW m1 yw))) := by
          unfold Pmap; rw [e01, e10, h1W]; rfl
        have hs : serialP n d m0 m1 = some (dedupD n [x, yw]) := by
          unfold serialP; rw [hx, hy, hw]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl e he
        rw [hs] at hl
        cases hl
        refine ⟨_, hp, ?_⟩
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp he) with h | h
        · rw [h, sN_tag01]; exact Or.inl rfl
        · rw [List.mem_singleton.mp h, sN_tagW, repP_live hnn]
          exact Or.inr rfl
      | none =>
        rw [hw] at h1W
        have hp : Pmap (goGame n) (.live d false false) (mB m0) (mW m1)
            = none := by
          unfold Pmap; rw [e01, e10, h1W]; rfl
        have hs : serialP n d m0 m1 = none := by
          unfold serialP; rw [hx, hy, hw]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl
        rw [hs] at hl
        cases hl
  | none =>
    rw [hx] at e01
    have hnn : ¬(m0 = none ∧ m1 = none) := by
      rintro ⟨rfl, rfl⟩
      rw [bStep2_pass_pass] at hx
      cases hx
    cases hy : bStep2 n d .w .b m1 m0 with
    | some y =>
      rw [hy] at e10
      have h1B := hash1_B d m0 h0
      cases hb : bStep n d .b m0 with
      | some xb =>
        rw [hb] at h1B
        have hp : Pmap (goGame n) (.live d false false) (mB m0) (mW m1)
            = some (BSet.pair (sN (tagB m0 xb)) (sN (tag10 m0 m1 y))) := by
          unfold Pmap; rw [e01, e10, h1B]; rfl
        have hs : serialP n d m0 m1 = some (dedupD n [xb, y]) := by
          unfold serialP; rw [hx, hy, hb]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl e he
        rw [hs] at hl
        cases hl
        refine ⟨_, hp, ?_⟩
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp he) with h | h
        · rw [h, sN_tagB, repP_live hnn]; exact Or.inl rfl
        · rw [List.mem_singleton.mp h, sN_tag10]; exact Or.inr rfl
      | none =>
        rw [hb] at h1B
        have hp : Pmap (goGame n) (.live d false false) (mB m0) (mW m1)
            = none := by
          unfold Pmap; rw [e01, e10, h1B]; rfl
        have hs : serialP n d m0 m1 = none := by
          unfold serialP; rw [hx, hy, hb]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl
        rw [hs] at hl
        cases hl
    | none =>
      rw [hy] at e10
      have h1B := hash1_B d m0 h0
      have h1W := hash1_W d m1 h1
      cases hb : bStep n d .b m0 with
      | some xb =>
        rw [hb] at h1B
        cases hw : bStep n d .w m1 with
        | some yw =>
          rw [hw] at h1W
          have hp : Pmap (goGame n) (.live d false false) (mB m0) (mW m1)
              = some (BSet.pair (sN (tagB m0 xb)) (sN (tagW m1 yw))) := by
            unfold Pmap; rw [e01, e10, h1B, h1W]; rfl
          have hs : serialP n d m0 m1 = some (dedupD n [xb, yw]) := by
            unfold serialP; rw [hx, hy, hb, hw]
          refine ⟨by simp [hp, hs], ?_⟩
          intro l hl e he
          rw [hs] at hl
          cases hl
          refine ⟨_, hp, ?_⟩
          rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp he) with h | h
          · rw [h, sN_tagB, repP_live hnn]; exact Or.inl rfl
          · rw [List.mem_singleton.mp h, sN_tagW, repP_live hnn]
            exact Or.inr rfl
        | none =>
          rw [hw] at h1W
          have hp : Pmap (goGame n) (.live d false false) (mB m0) (mW m1)
              = none := by
            unfold Pmap; rw [e01, e10, h1B, h1W]; rfl
          have hs : serialP n d m0 m1 = none := by
            unfold serialP; rw [hx, hy, hb, hw]
          refine ⟨by simp [hp, hs], ?_⟩
          intro l hl
          rw [hs] at hl
          cases hl
      | none =>
        rw [hb] at h1B
        have hp : Pmap (goGame n) (.live d false false) (mB m0) (mW m1)
            = none := by
          unfold Pmap; rw [e01, e10, h1B]; rfl
        have hs : serialP n d m0 m1 = none := by
          unfold serialP; rw [hx, hy, hb]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl
        rw [hs] at hl
        cases hl

theorem Pmap_WB_corr (d : Display n) (m0 m1 : Option Nat)
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n) :
    (Pmap (goGame n) (.live d false false) (mW m1) (mB m0)).isSome
        = (serialP n d m0 m1).isSome
    ∧ ∀ l, serialP n d m0 m1 = some l → ∀ e, e ∈ l →
        ∃ P, Pmap (goGame n) (.live d false false) (mW m1) (mB m0) = some P
          ∧ P (repP m0 m1 e) := by
  have e01 := hash2_01 d m0 m1 h0 h1
  have e10 := hash2_10 d m0 m1 h0 h1
  cases hy : bStep2 n d .w .b m1 m0 with
  | some y =>
    rw [hy] at e10
    cases hx : bStep2 n d .b .w m0 m1 with
    | some x =>
      rw [hx] at e01
      have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
          = some (BSet.pair (sN (tag10 m0 m1 y)) (sN (tag01 m0 m1 x))) := by
        unfold Pmap; rw [e01, e10]; rfl
      have hs : serialP n d m0 m1 = some (dedupD n [x, y]) := by
        unfold serialP; rw [hx, hy]
      refine ⟨by simp [hp, hs], ?_⟩
      intro l hl e he
      rw [hs] at hl
      cases hl
      refine ⟨_, hp, ?_⟩
      rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp he) with h | h
      · rw [h, sN_tag01]; exact Or.inr rfl
      · rw [List.mem_singleton.mp h, sN_tag10]; exact Or.inl rfl
    | none =>
      rw [hx] at e01
      have hnn : ¬(m0 = none ∧ m1 = none) := by
        rintro ⟨rfl, rfl⟩
        rw [bStep2_pass_pass] at hx
        cases hx
      have h1B := hash1_B d m0 h0
      cases hb : bStep n d .b m0 with
      | some xb =>
        rw [hb] at h1B
        have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
            = some (BSet.pair (sN (tag10 m0 m1 y)) (sN (tagB m0 xb))) := by
          unfold Pmap; rw [e01, e10, h1B]; rfl
        have hs : serialP n d m0 m1 = some (dedupD n [xb, y]) := by
          unfold serialP; rw [hx, hy, hb]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl e he
        rw [hs] at hl
        cases hl
        refine ⟨_, hp, ?_⟩
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp he) with h | h
        · rw [h, sN_tagB, repP_live hnn]; exact Or.inr rfl
        · rw [List.mem_singleton.mp h, sN_tag10]; exact Or.inl rfl
      | none =>
        rw [hb] at h1B
        have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
            = none := by
          unfold Pmap; rw [e01, e10, h1B]; rfl
        have hs : serialP n d m0 m1 = none := by
          unfold serialP; rw [hx, hy, hb]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl
        rw [hs] at hl
        cases hl
  | none =>
    rw [hy] at e10
    have hnn : ¬(m0 = none ∧ m1 = none) := by
      rintro ⟨rfl, rfl⟩
      rw [bStep2_pass_pass] at hy
      cases hy
    cases hx : bStep2 n d .b .w m0 m1 with
    | some x =>
      rw [hx] at e01
      have h1W := hash1_W d m1 h1
      cases hw : bStep n d .w m1 with
      | some yw =>
        rw [hw] at h1W
        have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
            = some (BSet.pair (sN (tagW m1 yw)) (sN (tag01 m0 m1 x))) := by
          unfold Pmap; rw [e01, e10, h1W]; rfl
        have hs : serialP n d m0 m1 = some (dedupD n [x, yw]) := by
          unfold serialP; rw [hx, hy, hw]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl e he
        rw [hs] at hl
        cases hl
        refine ⟨_, hp, ?_⟩
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp he) with h | h
        · rw [h, sN_tag01]; exact Or.inr rfl
        · rw [List.mem_singleton.mp h, sN_tagW, repP_live hnn]
          exact Or.inl rfl
      | none =>
        rw [hw] at h1W
        have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
            = none := by
          unfold Pmap; rw [e01, e10, h1W]; rfl
        have hs : serialP n d m0 m1 = none := by
          unfold serialP; rw [hx, hy, hw]
        refine ⟨by simp [hp, hs], ?_⟩
        intro l hl
        rw [hs] at hl
        cases hl
    | none =>
      rw [hx] at e01
      have h1B := hash1_B d m0 h0
      have h1W := hash1_W d m1 h1
      cases hw : bStep n d .w m1 with
      | some yw =>
        rw [hw] at h1W
        cases hb : bStep n d .b m0 with
        | some xb =>
          rw [hb] at h1B
          have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
              = some (BSet.pair (sN (tagW m1 yw)) (sN (tagB m0 xb))) := by
            unfold Pmap; rw [e01, e10, h1B, h1W]; rfl
          have hs : serialP n d m0 m1 = some (dedupD n [xb, yw]) := by
            unfold serialP; rw [hx, hy, hb, hw]
          refine ⟨by simp [hp, hs], ?_⟩
          intro l hl e he
          rw [hs] at hl
          cases hl
          refine ⟨_, hp, ?_⟩
          rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp he) with h | h
          · rw [h, sN_tagB, repP_live hnn]; exact Or.inr rfl
          · rw [List.mem_singleton.mp h, sN_tagW, repP_live hnn]
            exact Or.inl rfl
        | none =>
          rw [hb] at h1B
          have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
              = none := by
            unfold Pmap; rw [e01, e10, h1B, h1W]; rfl
          have hs : serialP n d m0 m1 = none := by
            unfold serialP; rw [hx, hy, hb, hw]
          refine ⟨by simp [hp, hs], ?_⟩
          intro l hl
          rw [hs] at hl
          cases hl
      | none =>
        rw [hw] at h1W
        cases hb : bStep n d .b m0 with
        | some xb =>
          rw [hb] at h1B
          have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
              = none := by
            unfold Pmap; rw [e01, e10, h1B, h1W]; rfl
          have hs : serialP n d m0 m1 = none := by
            unfold serialP; rw [hx, hy, hb, hw]
          refine ⟨by simp [hp, hs], ?_⟩
          intro l hl
          rw [hs] at hl
          cases hl
        | none =>
          rw [hb] at h1B
          have hp : Pmap (goGame n) (.live d false false) (mW m1) (mB m0)
              = none := by
            unfold Pmap; rw [e01, e10, h1B, h1W]; rfl
          have hs : serialP n d m0 m1 = none := by
            unfold serialP; rw [hx, hy, hb, hw]
          refine ⟨by simp [hp, hs], ?_⟩
          intro l hl
          rw [hs] at hl
          cases hl

end SgoBridge
