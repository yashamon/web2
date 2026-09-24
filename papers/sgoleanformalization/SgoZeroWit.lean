/- SgoZeroWit.lean — a witness that the conflict hypothesis of
   thm_zero is satisfiable, in the printed chess mechanism's smallest
   form: two moves each of which blocks the other.

   The game: Black's move b and White's move w are available at the
   initial core alone, and after either one the other is undefined. So
   at the initial state — semi-classical, being initial — neither
   composite a # m_0 # m_1 is defined, the serialization map falls to
   its lowest priority case, and P (a, b, w) = {N (a # b), N (a # w)}
   has two elements, neither final: exactly the printed conflict at the
   chess state a^*, where each rook move blocks the other's path.

   Hence 0 lies in the radius spectrum of this game, by thm_zero(2). -/
import SgoZero

namespace SgoZeroWit

open SgoGames

/-! ### The game -/

inductive TM where
  | p | b | w

inductive TC where
  | start | sb | sw

def tMv : Moves where
  M := TM
  deg0 := fun m => m = TM.p ∨ m = TM.b
  deg1 := fun m => m = TM.p ∨ m = TM.w
  pass := TM.p
  pass_deg0 := Or.inl rfl
  pass_deg1 := Or.inl rfl
  pass_unique := by
    intro m h0 h1
    cases m with
    | p => rfl
    | b =>
      rcases h1 with h | h
      · exact h
      · exact absurd h (fun h => TM.noConfusion h)
    | w =>
      rcases h0 with h | h
      · exact h
      · exact absurd h (fun h => TM.noConfusion h)

/-- Black's move and White's move, each available only at the start,
    and each undefined after the other. -/
def tMvAct : TC → TM → Option TC
  | TC.start, TM.b => some TC.sb
  | TC.start, TM.w => some TC.sw
  | _, _ => none

def tGame : SeqGame tMv where
  C := TC
  mv := tMvAct
  q0 := TC.start
  ended := fun _ => False

def tA : TM → TM
  | TM.p => TM.p
  | TM.b => TM.w
  | TM.w => TM.b

def tR : TC → TC
  | TC.start => TC.start
  | TC.sb => TC.sw
  | TC.sw => TC.sb

theorem tGame_seqSym : SeqSym tGame := by
  refine ⟨tA, tR, ?_, rfl, ?_, ?_, rfl, ?_, ?_⟩
  · intro m; cases m <;> rfl
  · intro m
    cases m with
    | p => exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩
    | b => exact ⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl⟩
    | w =>
      constructor
      · rintro (h | h) <;> exact absurd h (fun h => TM.noConfusion h)
      · rintro (h | h) <;> exact absurd h (fun h => TM.noConfusion h)
  · intro c; cases c <;> rfl
  · intro c; exact Iff.rfl
  · intro c m; cases c <;> cases m <;> rfl

theorem tGame_not_ended (c : TC) : ¬tGame.ended c := fun h => h

/-! ### The conflict -/

theorem tb_ne_pass : TM.b ≠ tMv.pass := fun h => TM.noConfusion h
theorem tw_ne_pass : TM.w ≠ tMv.pass := fun h => TM.noConfusion h

theorem hash_b : hashOp tGame (PState.live TC.start false false) TM.b
    = some (PState.live TC.sb true false) :=
  hashOp_move tGame tb_ne_pass (tGame_not_ended _) (Or.inl ⟨rfl, Or.inr rfl⟩) rfl

theorem w_guard_false :
    ¬((false = false ∧ tMv.deg0 TM.w) ∨ (false = true ∧ tMv.deg1 TM.w)) := by
  rintro (⟨-, h | h⟩ | ⟨h, -⟩)
  · exact TM.noConfusion h
  · exact TM.noConfusion h
  · exact Bool.noConfusion h

/-- White's move is not of Black's grading, so # plays it at the bar
    (the printed "the move is played at a if i = k and at bar a
    otherwise"). -/
theorem hash_w : hashOp tGame (PState.live TC.start false false) TM.w
    = some (PState.live TC.sw false false) :=
  hashOp_move_bar tGame tw_ne_pass (tGame_not_ended _) w_guard_false
    (Or.inr ⟨rfl, Or.inr rfl⟩) rfl

theorem hash2_bw : hash2 tGame (PState.live TC.start false false) TM.b TM.w = none := by
  unfold hash2
  rw [hash_b]
  show hashOp tGame (PState.live TC.sb true false) TM.w = none
  exact hashOp_none tGame tw_ne_pass (tGame_not_ended _) rfl

theorem hash2_wb : hash2 tGame (PState.live TC.start false false) TM.w TM.b = none := by
  unfold hash2
  rw [hash_w]
  show hashOp tGame (PState.live TC.sw false false) TM.b = none
  exact hashOp_none tGame tb_ne_pass (tGame_not_ended _) rfl

theorem tval_bw : tval tGame (PState.live TC.start false false) TM.b TM.w
    = some (PState.live TC.sb true false) := by
  unfold tval
  rw [hash2_bw]
  exact hash_b

theorem tval_wb : tval tGame (PState.live TC.start false false) TM.w TM.b
    = some (PState.live TC.sw false false) := by
  unfold tval
  rw [hash2_wb]
  exact hash_w

theorem tPmap : Pmap tGame (PState.live TC.start false false) TM.b TM.w
    = some (BSet.pair (PState.live TC.sb false false) (PState.live TC.sw false false)) := by
  rw [Pmap_eq, tval_bw, tval_wb]
  rfl

/-- The conflict: at the initial (semi-classical) state the joint move
    b/w is available, and P has the two distinct non final elements
    N (a # b) and N (a # w). -/
theorem tGame_hasConflict : HasConflict tGame := by
  refine ⟨(simGame tGame).q0, sInit tGame, TM.b, TM.w,
    BSet.pair (PState.live TC.sb false false) (PState.live TC.sw false false),
    PState.live TC.sb false false, PState.live TC.sw false false,
    SemiC.init, fun h => h, tPmap, Or.inl rfl, Or.inr rfl, ?_, ?_⟩
  · intro h
    injection h with h1 _ _
    exact TC.noConfusion h1
  · rintro z (hz | hz) <;> rw [hz] <;> exact fun h => h

/-- Zero lies in the radius spectrum of the witness game: the
    truncated universal simultaneization has faithfulness radius
    exactly zero. -/
theorem tGame_zero_inSpectrum : InSpectrum tGame (some 0) :=
  (thm_zero_2 tGame tGame_seqSym tGame_hasConflict).2

end SgoZeroWit
