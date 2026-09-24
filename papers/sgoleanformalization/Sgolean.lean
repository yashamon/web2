/- Sgolean.lean — root module of the default build target.

   Importing Step8 pulls in the complete sorry-free chain:
   SgoGo → SgoDisplay → SgoLemma → Infra* → Step0 → Step1 → Step3 →
   Step5 → Infra6 → Step4 → DispInfra → Step6 → Step7 → Step8,
   whose final theorem is `lem_onestage_final` (Step8.lean): the
   one-stage resolution lemma for non pass commuting joint moves,
   at every board side n ≥ 2 and every turn.

   `lake build` kernel-checks all of it. For the axiom certificate,
   run `lake env lean Audit.lean` — see Audit.lean.

   SgoSerial + SgoDelta are the main theorem's game level (milestone 1):
   the SGo, DSGo and k-DSGo evolutions, executable and differentially
   tested (TestSerial.lean, TestDelta.lean). SgoGames + SgoInst state
   the main theorem over the option-C bigraded sequential semantics;
   SgoInv, SgoOK, SgoBridge are the milestone-2 proof layer; SgoThm
   assembles the main theorem. SgoSim and SgoDyn are the simultaneization
   lemmas: lem_symmetric (Sim(G) is symmetric) and lem_dynamics (the
   radii and the spectrum are dynamical isomorphism invariants). -/
import Step8
import SgoSerial
import SgoDelta
import SgoInst
import SgoInv
import SgoOK
import SgoBridge
import SgoNat
import SgoStage1
import SgoSemi
import SgoFaith
import SgoSimple
import SgoWit
import SgoDInv
import SgoDOK
import SgoDNat
import SgoDSemi
import SgoDFaith
import SgoKInv
import SgoKNat
import SgoSwap
import SgoSym
import SgoKWit
import SgoKFin
import SgoSim
import SgoDyn
import SgoThm
import SgoZero
import SgoZeroWit
