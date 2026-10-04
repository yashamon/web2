/- SgoBisimThm.lean — the radius spectrum of Go (the last clause of
   Theorem thm_simplesymetrization): over a minimal game the radius
   spectrum is the raw radius spectrum (Lemma lem_bisimulation (3)), and
   the raw radius spectrum of Go is all of ℕ ⊔ {∞} (`spectrum_full`).

   Statement audit. The minimality of Go — distinct legally obtainable
   diagrams are not bisimilar, Lemma lem_gominimal of the print, proved
   there by the liberty-filling procedure — is NOT formalized: it enters
   as the hypothesis `Minimal (goGame n)`. -/
import SgoBisim
import SgoThm

namespace SgoThm

open SgoGames

variable {n : Nat}

/-- Theorem thm_simplesymetrization, the radius spectrum clause: if Go
    is minimal (Lemma lem_gominimal, paper-only), every element of
    ℕ ⊔ {∞} lies in the radius spectrum of Go. -/
theorem go_radius_spectrum_full (hn : 5 ≤ n) (hmin : Minimal (goGame n)) (r : Option Nat) :
    InRadiusSpectrum (goGame n) r :=
  (lem_bisimulation_3 hmin r).mp (spectrum_full_inSpectrum hn r)

/-- The minimal quotient of Go is a symmetric sequential game. -/
theorem go_quotient_seqSym : SeqSym (QGame (goGame n)) :=
  seqSym_QGame (go_symmetric (n := n))

end SgoThm
