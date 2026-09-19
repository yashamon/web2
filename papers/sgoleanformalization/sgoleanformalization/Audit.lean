/- Audit.lean — the verification certificate.

   Run:
     lake env lean Audit.lean

   Expected output, exactly:
     'lem_onestage_final' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoThm.thm52' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoThm.spectrum_full' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoKWit.not_faithful_kp1' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoGames.lem_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoGames.lem_dynamics_2' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoGames.lem_dynamics_3' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoGames.thm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoThm.lem_familysymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
     'SgoGames.lem_universal' depends on axioms: [propext, Classical.choice, Quot.sound]

   Those three axioms are the standard axioms of classical reasoning in Lean's
   core library. What must NOT appear:
     - sorryAx            — would mean an incomplete proof;
     - Lean.ofReduceBool  — would mean a native_decide dependence
                            (trusting the compiler, a larger base).
   Neither occurs in the theorem's cone. The separate 3×3
   exhaustive artifact (Exhaust.lean) does use native_decide, and its
   audit line shows Lean.ofReduceBool — that artifact is independent
   of the general theorem.

   `lem_onestage_final` (Step8) is the one-stage resolution lemma;
   `SgoThm.thm52` is the main theorem in full (side ≥ 5): Go's symmetry and
   the SGo / DSGo / k-DSGo simultaneizations realizing faithfulness
   radii 0, ∞, and exactly k; `spectrum_full` is the ℕ ⊔ {∞} spectrum
   corollary; `not_faithful_kp1` is the k-DSGo not-within-(k+1) witness;
   `lem_symmetric` is the symmetry of Sim(G) (SgoSim); `lem_dynamics_2`
   and `lem_dynamics_3` are the isomorphism invariance of the radii and
   of the spectrum (SgoDyn); `thm_zero` is the zero-in-the-spectrum
   theorem for the truncated universal simultaneization (SgoZero);
   `lem_familysymmetric` is the lemma that the SGo family are
   symmetric simultaneous combinatorial games; `lem_universal` is the
   lemma that Sim(G) is a simultaneization of G with ρ the identity,
   faithful at every legally obtainable state (SgoZero). -/
import Step8
import SgoThm

#print axioms lem_onestage_final
#print axioms SgoThm.thm52
#print axioms SgoThm.spectrum_full
#print axioms SgoKWit.not_faithful_kp1
#print axioms SgoGames.lem_symmetric
#print axioms SgoGames.lem_dynamics_2
#print axioms SgoGames.lem_dynamics_3
#print axioms SgoGames.thm_zero
#print axioms SgoThm.lem_familysymmetric
#print axioms SgoGames.lem_universal
