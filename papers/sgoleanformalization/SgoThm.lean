/- SgoThm.lean — the main theorem, the verified assembly.

   Everything here is sorry-free and in the propext/Choice/Quot.sound
   cone (no native_decide). All clauses of the full printed theorem are
   now included: Go's symmetry; SGo (radius 0); DSGo (radius ∞); and
   k-DSGo with faithfulness radius EXACTLY k — the UPPER bound (within
   k) and, at side ≥ 5, the LOWER bound ¬FaithfulWithin (k+1) (the
   delayed-verdict witness, SgoKFin). `thm52` assembles the whole
   statement; `spectrum_full` is the ℕ ⊔ {∞} spectrum corollary. -/
import SgoSym
import SgoWit
import SgoKFin
import SgoDyn
import SgoZero

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoSemi SgoFaith SgoSimple SgoWit SgoDInv SgoDOK SgoDNat SgoDSemi
  SgoDFaith SgoKInv SgoKNat SgoSwap SgoSym SgoKWit

namespace SgoThm

variable {n : Nat}

/-! ### Go is symmetric -/

theorem go_symmetric : GoOK n := goOK

/-! ### SGo: the main theorem's SGo clause, in full -/

/-- SGo is a simple symmetric simultaneization of Go with faithfulness
    radius exactly 0 (within 0; not within 1 at side ≥ 3). -/
theorem thm52_SGo (hn : 2 ≤ n) : Thm52_SGo n :=
  ⟨sgo_simOK, sgo_simSym, sgo_isSimultaneization hn, sgo_isSimple,
   sgo_faithful0 hn, fun h3 => sgo_not_faithful1 h3⟩

/-! ### DSGo: the main theorem's DSGo clause, in full -/

/-- DSGo is a simple symmetric simultaneization of Go, faithful within
    every distance — faithfulness radius ∞. -/
theorem thm52_DSGo (hn : 2 ≤ n) : Thm52_DSGo n :=
  ⟨dsgo_simOK, dsgo_simSym, dsgo_isSimultaneization hn, dsgo_isSimple,
   dsgo_faithful_all⟩

/-! ### k-DSGo: the main theorem's k-DSGo clause, in full -/

/-- k-DSGo is a simple symmetric simultaneization of Go, faithful
    within k (the strictness — not within k+1 — is the held witness). -/
theorem kdsgo (hn : 2 ≤ n) (k : Nat) (hk : 1 ≤ k) :
    SimOK (kGame n k)
    ∧ SimSym (kGame n k) (kEqv n)
    ∧ IsSimultaneization (goGame n) (kGame n k) (rhoK n)
    ∧ IsSimple (goGame n) (kGame n k)
    ∧ FaithfulWithin (goGame n) (kGame n k) (rhoK n) k :=
  ⟨k_simOK k hk, k_simSym k, k_isSimultaneization hn k, k_isSimple,
   k_faithful_k hn⟩

/-- k-DSGo is a simple symmetric simultaneization of Go with
    faithfulness radius EXACTLY k: faithful within k, and — at side
    ≥ 5 — not within k+1 (the delayed-verdict witness, SgoKFin). -/
theorem thm52_kDSGo (hn : 5 ≤ n) (k : Nat) (hk : 1 ≤ k) : Thm52_kDSGo n k :=
  ⟨k_simOK k hk, k_simSym k, k_isSimultaneization (by omega) k, k_isSimple,
   k_faithful_k (by omega), fun h5 => not_faithful_kp1 h5 hk⟩

/-! ### The main theorem, in full -/

/-- The main theorem in its entirety, at board side n ≥ 5: Go is symmetric,
    and SGo, DSGo, and every k-DSGo (k ≥ 1) are simple symmetric
    simultaneizations of Go realizing faithfulness radii 0, ∞, and
    exactly k respectively. -/
theorem thm52 (hn : 5 ≤ n) : Thm52 n :=
  ⟨go_symmetric, thm52_SGo (by omega), thm52_DSGo (by omega),
   fun k hk => thm52_kDSGo hn k hk⟩

/-! ### The spectrum, minus the k-DSGo strictness witnesses -/

theorem sgoEqv_isEquiv : IsEquivB (sgoGame n) (sgoEqv n) := by
  refine ⟨fun a => ⟨rfl, rfl, rfl, fun _ => Iff.rfl⟩, ?_, ?_⟩
  · rintro a b ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h2.symm, h3.symm, fun x => (h4 x).symm⟩
  · rintro a b c ⟨h1, h2, h3, h4⟩ ⟨g1, g2, g3, g4⟩
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, fun x => (h4 x).trans (g4 x)⟩

theorem kEqv_isEquiv {k : Nat} : IsEquivB (kGame n k) (kEqv n) := by
  refine ⟨fun a => ⟨rfl, rfl, rfl, rfl, fun _ => Iff.rfl⟩, ?_, ?_⟩
  · rintro a b ⟨h1, h2, h3, h5, h4⟩
    exact ⟨h1.symm, h2.symm, h3.symm, h5.symm, fun x => (h4 x).symm⟩
  · rintro a b c ⟨h1, h2, h3, h5, h4⟩ ⟨g1, g2, g3, g5, g4⟩
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h5.trans g5,
      fun x => (h4 x).trans (g4 x)⟩

/-- Every point of ℕ ⊔ {∞} is realized as the faithfulness-within data
    of a simple SYMMETRIC simultaneization of Go: for each k a game
    faithful within k, and one faithful within every distance. (The
    strictness of the k-DSGo radius — the not-within-(k+1) witness —
    is the one held item.) -/
theorem spectrum_partial (hn : 2 ≤ n) :
    (∀ k : Nat, 1 ≤ k → ∃ G1 : SimulGame goMv,
        ∃ ρ : G1.B → BSet (goGame n).S, ∃ rel : G1.B → G1.B → Prop,
        IsEquivB G1 rel ∧ SimOK G1 ∧ SimSym G1 rel
        ∧ IsSimultaneization (goGame n) G1 ρ ∧ IsSimple (goGame n) G1
        ∧ FaithfulWithin (goGame n) G1 ρ k)
    ∧ (∃ G1 : SimulGame goMv, ∃ ρ : G1.B → BSet (goGame n).S,
        ∃ rel : G1.B → G1.B → Prop, IsEquivB G1 rel ∧ SimOK G1
        ∧ SimSym G1 rel ∧ IsSimultaneization (goGame n) G1 ρ
        ∧ IsSimple (goGame n) G1 ∧ ∀ d, FaithfulWithin (goGame n) G1 ρ d) := by
  constructor
  · intro k hk
    exact ⟨kGame n k, rhoK n, kEqv n, kEqv_isEquiv, k_simOK k hk, k_simSym k,
      k_isSimultaneization hn k, k_isSimple, k_faithful_k hn⟩
  · exact ⟨dsgoGame n, rhoD n, sgoEqv n, sgoEqv_isEquiv, dsgo_simOK,
      dsgo_simSym, dsgo_isSimultaneization hn, dsgo_isSimple, dsgo_faithful_all⟩

/-! ### The spectrum, in full -/

/-- The full spectrum corollary at side ≥ 5: every element of ℕ ⊔ {∞}
    is realized as the EXACT faithfulness radius of a simple symmetric
    simultaneization of Go — radius 0 by SGo, radius k (k ≥ 1) by
    k-DSGo, and ∞ by DSGo. The k+1 strictness is the SgoKFin witness
    (with SGo's own not-within-1 covering radius 0). -/
theorem spectrum_full (hn : 5 ≤ n) : SpectrumFull n := by
  refine ⟨?_, ?_⟩
  · intro k
    cases k with
    | zero =>
      exact ⟨sgoGame n, rhoSGo n, sgoEqv n, sgoEqv_isEquiv, sgo_simOK, sgo_simSym,
        sgo_isSimultaneization (by omega), sgo_isSimple, sgo_faithful0 (by omega),
        sgo_not_faithful1 (by omega)⟩
    | succ kk =>
      exact ⟨kGame n (kk+1), rhoK n, kEqv n, kEqv_isEquiv, k_simOK (kk+1) (by omega),
        k_simSym (kk+1), k_isSimultaneization (by omega) (kk+1), k_isSimple,
        k_faithful_k (by omega), not_faithful_kp1 hn (by omega)⟩
  · exact ⟨dsgoGame n, rhoD n, sgoEqv n, sgoEqv_isEquiv, dsgo_simOK,
      dsgo_simSym, dsgo_isSimultaneization (by omega), dsgo_isSimple, dsgo_faithful_all⟩

/-- The same statement in the language of lem_dynamics (SgoDyn): the
    radius spectrum of Go, on a board of side at least five, is all of
    ℕ ⊔ {∞} — every r ∈ ℕ ⊔ {∞} is in the spectrum (`InSpectrum`). -/
theorem spectrum_full_inSpectrum (hn : 5 ≤ n) (r : Option Nat) :
    InSpectrum (goGame n) r := by
  obtain ⟨h1, h2⟩ := spectrum_full hn
  cases r with
  | none =>
    obtain ⟨G1, ρ, rel, heq, hok, hsym, hsim, hsimple, hall⟩ := h2
    exact ⟨G1, ρ, rel, heq, hok, hsym, hsim, hsimple, hall⟩
  | some k =>
    obtain ⟨G1, ρ, rel, heq, hok, hsym, hsim, hsimple, hk, hk1⟩ := h1 k
    exact ⟨G1, ρ, rel, heq, hok, hsym, hsim, hsimple, hk, hk1⟩

/-! ### lem_familysymmetric: the SGo family are symmetric
     simultaneous combinatorial games -/

/-- Lemma lem_familysymmetric, with its SGo companion: SGo, DSGo and
    the delayed games k-DSGo (k ≥ 1) are symmetric simultaneous
    combinatorial games — the conditions of def_simultaneous (`SimOK`)
    and of def_symmetric (`SimSym`), the states compared up to equality
    of the entanglement as a SET, as the printed definition is
    set-based. The SGo clause is the printed Lemma
    thm_simultanezation; the other two are the printed Lemma
    lem_familysymmetric, whose factors are, in this development:
    the placement (`placeJoint`), the serialization map on branch sets
    (`serialP`, symmetric by `SgoSwap`'s color equivariance of the
    whole capture stack), the postprocessing Δ (`delta`), and — for
    k-DSGo — the verdicts and their execution (`verOf`, `execV`).
    Together with condition prop_2 (the moves are shared by
    construction), this is condition (1) of def_symmetrization for the
    whole family. -/
theorem lem_familysymmetric :
    (SimOK (sgoGame n) ∧ SimSym (sgoGame n) (sgoEqv n)) ∧
    (SimOK (dsgoGame n) ∧ SimSym (dsgoGame n) (sgoEqv n)) ∧
    (∀ k, 1 ≤ k → SimOK (kGame n k) ∧ SimSym (kGame n k) (kEqv n)) :=
  ⟨⟨sgo_simOK, sgo_simSym⟩, ⟨dsgo_simOK, dsgo_simSym⟩,
   fun k hk => ⟨k_simOK k hk, k_simSym k⟩⟩

/-! ### thm_zero at Go -/

/-- thm_zero part (1) at Go: the truncated universal simultaneization
    Sim_sc(Go) is a simple symmetric simultaneization of Go, faithful
    within distance zero. (That 0 lies in the spectrum of Go is
    already the theorem's SGo clause; the general statement is
    SgoGames.thm_zero.) -/
theorem thm_zero_go :
    SimOK (simGameSc (goGame n)) ∧ SimSym (simGameSc (goGame n)) Eq ∧
    IsSimultaneization (goGame n) (simGameSc (goGame n)) (fun A => A.1) ∧
    IsSimple (goGame n) (simGameSc (goGame n)) ∧
    FaithfulWithin (goGame n) (simGameSc (goGame n)) (fun A => A.1) 0 :=
  thm_zero_1 (goGame n) goOK

end SgoThm
