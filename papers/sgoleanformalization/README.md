# sgolean — Lean 4 formalization of the main theorems, the one-stage lemma, and the simultaneization theory of *The radius spectrum of games, and simultaneous Go via objective quantum reduction*

The manuscript: [sgo.pdf](https://yashamon.github.io/web2/papers/sgo.pdf).
Section, theorem and definition numbers below refer to it.

Play SGo in the browser: [SGo Arena](https://claude.ai/artifact/SVrxvsBVMGSEYUu9ZyJyrw).
Its opponents are the self-play networks of Section 2.1 (9×9, generations 1 to
48) and the Monte Carlo agents, with their ladder ratings; it also has an
illustrated rules sheet and play against a person online.

The sequential-game layer is the paper's `def_sequential` (Definition 4.3): a
game is presented by its cores, its states are `C(G) × Z₂ × Z₃` — here
`PState.live c g j` for pass grading j = 0, 1 and `PState.done c g` for pass
grading 2 — and the printed properties of the evolution are theorems of the
construction (`SgoGames`: `prop_finalnomove`, `sfinal_iff_no_pass`,
`prop_pass0`, `prop_pass1`, `prop_pass_j`, `sE_nonpass`, `prop_nonpass_j`,
`prop_doublepass`). The paper itself carries no verification claims beyond
the link in its introduction; this README is the audit.

STATUS: COMPLETE. All results below are fully proved, sorry-free, in Lean
4.15.0 core (no Mathlib, no other dependency), kernel-checked by `lake build`.

- `SgoThm.thm52` — the main theorem (`thm_simplesymetrization`, Theorem 6.3
  in the current draft): on a board of side at least five, SGo, the
  delayed games k-DSGo (k ≥ 1) and DSGo are simple symmetric simultaneizations
  of Go with faithfulness radii zero, exactly k, and infinity; Go itself is
  symmetric. `SgoThm.spectrum_full` — the corollary: every element of
  ℕ ⊔ {∞} is the radius of a simple symmetric simultaneization of Go.
- `SgoThm.lem_familysymmetric` — the SGo family (SGo, DSGo, every k-DSGo) are
  symmetric simultaneous combinatorial games: def_simultaneous (`SimOK`) and
  def_symmetric (`SimSym`), the states compared up to equality of the
  entanglement as a set.
- `lem_onestage_final` (Step8.lean) — the one-stage lemma (`lem_onestage`), the resolution of
  commuting joint moves: at every board side n ≥ 2 and every turn, for non
  pass joint moves; the pass cases are covered inside the SGo clause of the
  theorem (`SgoStage1.onestage_single`, `SgoSemi.sgo_semiclassical`).
- `SgoGames.lem_symmetric` (SgoSim.lean) — `lem_symmetric`: the universal
  simultaneization Sim(G) of a symmetric sequential game is symmetric
  (def_symmetric, all clauses; `simGame_simOK`: Sim(G) is a combinatorial
  simultaneous game).
- `SgoGames.lem_dynamics_2`, `SgoGames.lem_dynamics_3` (SgoDyn.lean) —
  `lem_dynamics`: a dynamical isomorphism of sequential games transports
  simultaneizations with their faithfulness radii and simplicity (part 2),
  and the radius spectra coincide (part 3); part 1 is `lem_dynamics_1`.
- `SgoGames.thm_zero` (SgoZero.lean) — zero in the radius spectrum, for an
  arbitrary symmetric sequential game G: the truncated universal
  simultaneization Sim_sc(G) — Sim(G) with every state that is not
  semi-classical declared final — is a simple symmetric simultaneization of
  G, faithful within distance zero (part 1); at a conflict its radius is
  exactly zero, so 0 lies in the spectrum of G (part 2); and if instead
  every joint move available at a semi-classical state commutes, the
  spectrum is {∞} (part 3). No hypothesis beyond the symmetry of G;
  `SgoZeroWit` witnesses that the conflict of part 2 is satisfiable, in the
  printed chess mechanism's smallest form.
- `SgoGames.lem_universal` (SgoZero.lean) — `lem_universal`: Sim(G) is a
  simultaneization of G with ρ the identity, its semi-classical states are
  the singletons of their associated states, and it is faithful at every
  legally obtainable state, hence within every distance: radius infinity.
- `SgoGames.lem_bisimulation` (SgoBisim.lean) — `lem_bisimulation` (Lemma
  4.20), on Definition 4.19: bisimulations between sequential games
  (`IsBisim`), bisimilarity (`Bisimilar`: an equivalence relation and
  itself a bisimulation), the minimal quotient G/~ (`QGame`, on the classes
  of legally obtainable cores) and the radius spectrum as the raw radius
  spectrum of the quotient (`InRadiusSpectrum`; the raw one is
  `InSpectrum`). (1) G/~ is a symmetric sequential game and the projection
  is a bisimulation; (2) bisimilar games have the same radius spectrum;
  (3) over a minimal game (`Minimal`) the radius spectrum is the raw
  radius spectrum; (4) the projection π is onto the legally obtainable
  states of G/~ and of Sim(G/~) and commutes with the interfaces,
  availability, finality, the evolution of Sim and the semi-classical
  states.
- `SgoGames.thm_zero_radius` (SgoBisim.lean) — the radius spectrum clauses
  of `thm_zero` (6.9): a conflict whose two outcomes have non bisimilar
  cores (`HasConflictNB`) puts 0 in the radius spectrum (part 2), and if
  every joint move available at a semi-classical state commutes, the
  radius spectrum is {∞} (part 3).
- `SgoGoMin.go_minimal` (SgoGoMin.lean) — `lem_gominimal` (Lemma 6.13): Go
  is minimal, distinct legally obtainable diagrams are not bisimilar, at
  every board side. `SgoGoMin.go_radius_spectrum` — the radius spectrum
  clause of the main theorem (6.3): every element of ℕ ⊔ {∞} lies in the
  radius spectrum of Go (`SgoThm.go_radius_spectrum_full` is the same
  clause with the minimality as an explicit hypothesis).

Axiom footprint of every theorem above: `[propext, Classical.choice,
Quot.sound]` — the standard trio. No `sorryAx` (no incomplete proof) and no
`Lean.ofReduceBool` (no `native_decide`, i.e. no trust in the compiler) in
their dependency cones.

Release 1.6. Hosted at
<https://yashamon.github.io/web2/papers/sgoleanformalization/> — the files
below, this [README](README.md), and the archive
[sgoleanformalization-1.6.zip](sgoleanformalization-1.6.zip). (Release 1.0
carried the main theorem and the one-stage lemma; 1.1 added `lem_symmetric`
and `lem_dynamics`; 1.2 added `thm_zero`, `lem_familysymmetric` and
`lem_universal`, with the sequential-game layer as the paper's def_sequential;
1.3 aligned the definitions with the current print: def_faithful is the single
interface equation (`FaithfulAt`), `#` is undefined at pass grading 2
(`hashOp_done`), and the pass grading is read in Z₃; 1.4 added the
bisimulation layer: Definition 4.19, Lemma 4.20, Lemma 6.13 and the radius
spectrum clauses of Theorems 6.3 and 6.9; 1.5 follows the capture rule of
the paper's `reduce` branch: Condition 4 of def_captured, the residual
capture, with the notions of def_trapped without a turn — statement audit
item 14; 1.6 formalizes the game exactly as printed in the paper's
`reduce2` branch: the stone placement rule of Section 2.3 with its rule
(2), and def_captured in the printed numbering, Conditions 1–5 — items 14
and 15. Releases 1.5 and 1.4, with a q-stone at every conflict, stay
available as [sgoleanformalization-1.5.zip](sgoleanformalization-1.5.zip)
and [sgoleanformalization-1.4.zip](sgoleanformalization-1.4.zip).)

## Verifying this development

Four commands; no dependency beyond Lean itself:

    curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
    curl -LO https://yashamon.github.io/web2/papers/sgoleanformalization/sgoleanformalization-1.6.zip
    unzip sgoleanformalization-1.6.zip && cd sgoleanformalization
    lake build          # kernel-checks the complete chain (lean-toolchain pins v4.15.0; ~2 min)

On Windows, `tar -xf sgoleanformalization-1.6.zip` unpacks the archive in
place (PowerShell's Extract-All wraps it in a second folder of the same
name, and `lake build` then finds no lakefile); on Linux use `unzip`, GNU
tar not reading zip archives.

Then the axiom certificate:

    lake env lean Audit.lean

Expected output, exactly these fifteen lines:

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
    'SgoGames.lem_bisimulation' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SgoGames.thm_zero_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SgoThm.go_radius_spectrum_full' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SgoGoMin.go_minimal' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SgoGoMin.go_radius_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]

Gold-standard extra: replay the build through an external kernel with
lean4checker. The CI workflow (`.github/workflows/ci.yml`, for a git
hosting of the same files) runs the build and greps the fifteen lines.

## What is checked: where the printed notions live

The default target `Sgolean` (lakefile.toml) builds the whole sorry-free
chain. Correspondence with the print is documented at the top of each file.

Classical Go and the display calculus (Section 2):
- `SgoGo` — classical Go on diagrams: the placed diagram B + m, go_captures,
  go_suicide, go_closure (`goMoveN`).
- `SgoDisplay` — the display calculus: q-stones and time stamps,
  def_trapped (on a turn: `trappedOnTurn`, `stoneTrappedBy`; without one:
  `noLibD`, `stoneTrapped`), def_captured (`isCapturedPrint`, Conditions
  1–5 as printed, equal by `isCaptured_eq_print` to `isCaptured`, the form
  the proofs use: `isCapturedOT` or the residual `residualCap`), the basic
  capture reduction, its fixpoint (Cap_n), the stone placement rule of
  Section 2.3 (`placeJoint`; at a conflict `conflictKind`, with
  `wouldTrap` for the trapping conflict of rule (1)), the stage recursion
  (OR).

The one-stage lemma (`lem_onestage_final`): `SgoLemma` (statement, goMoveN factored
through named stages), `Infra`..`Infra6` (components, liberties, legality),
`Step0`, `Step1`, `Step3`, `Step4`, `Step5`, `DispInfra`, `Step6`, `Step7`,
`Step8` (assembly).

The games (Sections 4–6):
- `SgoSerial` — the branch step `#`, the serialization map P (`serialP`, the
  four priority cases), `simEv`, and E_SGo (`sgoEv`).
- `SgoDelta` — the postprocessing Δ (`deltaRound`, `recut`, `delta`), E_DSGo
  (`dsgoEv`), the objective reduction `orOp`, verdicts (`verOf`, `execV`),
  and E_k (`kEv`).
- `SgoGames` — the abstract layer: def_sequential (core states, the turn
  and pass gradings, the ended cores where the pass is undefined; finals),
  the evolution, bar and `#` (`hashOp`, undefined at pass grading 2), the
  position normal form (`sN`), P (`Pmap`), Sim(G) (`simDefP`, `simVal`,
  `simFinal`), def_simultaneous (`SimulGame`, `SimOK`), symmetry (`SeqSym`,
  `SimSym`), def_semiclassical (`CommuteAt`, `SemiC`), def_symmetrization
  conditions 3–4 (`IsSimultaneization`), the interfaces (`Interface0`,
  `Interface1`; `interface0_empty_iff`: 𝕀(a) is empty exactly when a is
  final), def_faithful as the interface equation (`FaithfulAt`, `WithinD`,
  `FaithfulWithin`), its three-clause form (`FaithfulAt3`) and their
  equivalence at reachable states (`faithfulAt_iff`),
  def_simplesymmetrization (`IsSimple`).
- `SgoInst` — Go presented by its core (`goGame`), the four games
  (`sgoGame`, `dsgoGame`, `kGame`), their branch semantics (`rhoSGo`,
  `rhoD`, `rhoK`), and the statements `Thm52_SGo`, `Thm52_DSGo`,
  `Thm52_kDSGo`, `Thm52`, `SpectrumFull`.
- `SgoSim` — Sim(G) as a simultaneous game (`simGame`, on the sets of
  position normal forms `NSet`), `simGame_simOK`, and `lem_symmetric`:
  the swap R̃ (`Rt`), the characterization of P as the pair of its two
  terms' normal forms (`Pmap_eq`), P's insensitivity to the turn grading
  at live states (`Pmap_flip` — the printed "unaffected by the
  normalization"), and P intertwining the swap (`Pmap_Rst`).
- `SgoDyn` — dynamical isomorphisms (`SeqIso`), the renaming of a
  simultaneization (`renameSim`, `renameRho`), the transports of every
  printed condition (`lem_dynamics_2`), the spectrum as a set of realized
  radii (`HasRadius`, `InSpectrum`) and `lem_dynamics_3`;
  `SgoThm.spectrum_full_inSpectrum` restates the spectrum corollary.
- `SgoZero` — the truncation `simGameSc` and `thm_zero`, with
  `lem_universal` (Sim(G) is a simultaneization of G with ρ the identity,
  its semi-classical states are singletons, and it is faithful at every
  legally obtainable state, hence of radius ∞): `semiC_single`,
  `simGame_nonempty`, `simGame_faithfulAt`,
  the swap preserves the semi-classical states (`semiC_Rt`), the interface
  of a live state depends on its core alone (`interface0_live_indep`), and
  the # calculus keeps the cores legally obtainable (`CoreOb`,
  `semiC_coreOb`).
- `SgoZeroWit` — a witness that the conflict hypothesis is satisfiable, in
  the printed chess mechanism's smallest form: two moves, each undefined
  after the other, so that P falls to its lowest priority case and has two
  distinct non final elements; `tGame_zero_inSpectrum` concludes
  `InSpectrum tGame (some 0)` from `thm_zero`.
- `SgoBisim` — Definition 4.19 and Lemma 4.20: bisimulations (`IsBisim`),
  bisimilarity (`Bisimilar`, `isBisim_bisimilar`), the legally obtainable
  cores (`ObC`, `CoreOb`), the minimal quotient (`QGame`), the projection
  on states (`qS`) and its commutation with the evolution, `#`, N, P, the
  interfaces, finality, reachability and Sim (`sE_qS`, `hashOp_qS`,
  `Pmap_qS`, `interface0_qS`, `seqReach_qS_surj`, `simGame_pairE_qN`,
  `semiC_qN`), the symmetry of the quotient (`seqSym_QGame`), the
  isomorphism of minimal quotients induced by a bisimulation (`bisimIso`,
  with `lem_dynamics_3`), the transport of simultaneizations along π over
  a minimal game (`isSimultaneization_push`, `isSimultaneization_pull`),
  `Minimal`, `InRadiusSpectrum`, `lem_bisimulation`, and the radius
  spectrum clauses of `thm_zero` (`HasConflictNB`, `thm_zero_radius`).
- `SgoBisimThm` — the radius spectrum clause of the main theorem for Go,
  under the hypothesis `Minimal (goGame n)` (`go_radius_spectrum_full`).
- `SgoGoMin` — Lemma 6.13, Go is minimal (`go_minimal`), and the clause
  without the hypothesis (`go_radius_spectrum`): the invariant of the
  legally obtainable displays (well-formed, classical, legal, stamps zero:
  `goOb`), bisimilar displays have the same occupancy (`bisim_occ`) and
  bisimilar successors (`bisim_step_b`, `bisim_step_w`), the fill step
  (`fill_step`), the final move (`final_black`, `final_white`), the
  induction on the measure of the black component (`no_bisim_diff`).

The proof of the main theorem (6.3):
- SGo: `SgoInv` (the entanglement invariant), `SgoOK` (def_simultaneous),
  `SgoBridge` (P on position normal forms = `serialP`), `SgoNat`
  (naturality), `SgoStage1` (the single-placement one-stage lemma — the
  pass cases), `SgoSemi` (the semi-classical recursion tracks the display),
  `SgoFaith` (faithful within 0), `SgoSimple` (simplicity), `SgoWit` (not
  faithful within 1, side ≥ 3).
- DSGo: `SgoDInv`, `SgoDOK`, `SgoDNat`, `SgoDSemi` (Δ is the resolution at
  semi-classical states), `SgoDFaith` (faithful within every distance).
- k-DSGo: `SgoKInv`, `SgoKNat` (faithful within k, by projection to a DSGo
  history), `SgoKWit` + `SgoKFin` (not faithful within k+1, side ≥ 5: the
  delayed-verdict witness — collision, pocket-suicide padding, final turn).
- Symmetry: `SgoSwap` (the color swap through the whole capture stack; Go
  is symmetric, `GoOK`), `SgoSym` (the four games are symmetric).
- `SgoThm` — the assembly: `thm52_SGo`, `thm52_DSGo`, `thm52_kDSGo`,
  `thm52`, `spectrum_full`.

## Statement audit — what the kernel cannot check for you

That the checked statements SAY what the paper says. Points to compare
against the print:

1. Board side. `thm52` and `spectrum_full` assume `5 ≤ n`, as the printed
   theorem. Per clause: SGo faithful within 0 at n ≥ 2 and not within 1 at
   n ≥ 3; DSGo faithful within every distance at n ≥ 2; k-DSGo faithful
   within k at n ≥ 2 and not within k+1 at n ≥ 5. The 2×2 board is not
   covered (the paper's footnote cites a separate exhaustion).
2. Finality, as printed: a state is final exactly when the pass is undefined
   there (`SgoGames.sfinal_iff_no_pass`), which at pass grading 0 or 1
   depends on the core alone (`ended`, `prop_pass_j`); the states of pass
   grading 2 (`done`), reached by a double pass, are final. For a game of
   the SGo family a state is final exactly after a double pass turn (the
   `final` flag); no core of Go is ended by play, so Go's finals are the
   states of pass grading 2.
3. def_faithful (4.15) is the single equation I(s) = ⋂ 𝕀(a) with ρ(s)
   nonempty (`FaithfulAt`). The proofs for the four games establish the
   earlier three-clause form (`FaithfulAt3`: nonempty; final only if some
   branch is final; the equation at non final states) and pass through
   `faithfulAt_iff`, which shows the two forms agree at every reachable
   state of a combinatorial simultaneous game — because 𝕀(a) is empty
   exactly when a is final (`interface0_empty_iff`), which in turn is
   because `#` is undefined at every final state (`hashOp_done`,
   `hashOp_ended`), as printed after def_hash (4.7).
4. The sequential-game layer is the printed def_sequential (4.3): `live c g j`
   is (x, i, j) for j < 2 and `done c g` is (x, i, 2); the printed properties
   are theorems of the construction (the list at the top; property (2)'s
   "definedness depending on x and m alone" is `prop_nonpass_j` and
   `prop_pass_j`); the position normal form `sN` is the printed N exactly
   (gradings reset, the core and the finality kept). The bar `sBar` carries
   a value at a `done` for definitional convenience; `hashOp` never reads
   it.
5. Radii are stated in explicit form — faithful within d, not faithful
   within d+1 — with no supremum; the spectrum is the existence statement
   over these (`SpectrumFull`).
6. Not carried: the partition of the final states into wins and draws
   (unused by the theorem's clauses), and finiteness of the move alphabet.
   Consequently def_symmetric's clause that R maps W_0 onto W_1 and D onto
   D is carried as the preservation of finality (`SimSym`), and the
   scoring clause of `lem_dynamics`(3) — repartitioning the final states
   does not change the spectrum — has no formal counterpart beyond the
   fact that no formal notion reads a partition (`InSpectrum` is defined on
   the scoring-free `SeqGame`). Symmetry of the four games is `SimSym`,
   with states compared up to equality of the entanglement as a SET
   (`sgoEqv`, `kEqv`), matching the printed set-based definition; for
   Sim(G) the comparison is equality (`lem_symmetric`).
7. Moves are `Option (Bool × Nat)`: the pass, or a colored intersection;
   off-board indices are undefined moves. Availability is read from the
   display, as printed.
8. Branches: a live branch of the entanglement is the position normal form
   of its diagram (time stamps in branch diagrams ride as 0 and are never
   read). That P's outputs land exactly there is a proved bridge
   (`SgoBridge`), not an assumption.
9. Array encoding: displays are `Display n` with `cells.size = n*n` pinned
   by `WFD`; cell i = column * n + row.
10. `thm_zero` (6.9) assumes only that G is symmetric. Its conflict hypothesis is
   `HasConflict` — P (a, m_0, m_1) has two distinct non final elements at a
   semi-classical state — read off P itself, so the printed chess witness
   (P's lowest priority case, neither composite defined) is covered;
   `SgoZeroWit` is a witness game of that shape. The hypothesis of part (3)
   is `AllCommute`, stated over the associated states of the semi-classical
   states of Sim(G) (`scAssoc_iff_semiC` identifies them as printed). Part
   (3) uses the naturality of the branch semantics, as the print now does.
   The radius spectrum clauses of parts (2) and (3) are `thm_zero_radius`:
   the printed "if the core states of the two elements are not bisimilar"
   is `HasConflictNB` (`HasConflict` with `¬Bisimilar G x.coreOf y.coreOf`),
   and both clauses are proved as the print proves them, by applying
   `thm_zero` to the quotient through the transfer lemmas of part (4)
   (`hasConflict_QGame`, `allCommute_QGame`).
11. Not formalized, by decision: Theorem 6.7 (augmented chess has no simple
    simultaneization of positive radius — a retrograde statement about
    legally obtainable chess positions) and its minimal quotient clause,
    the Nash theorem 5.3 and its corollary 5.4, and the experiments of
    Section 2.1 (their method is Section 7). The rules of SGo are formalized as the engine of
    `SgoDisplay`/`SgoSerial`/`SgoDelta` and differentially tested against
    the paper's engines (below). The placement rule formalized is the
    printed three-tier rule of Section 2.3, in its December wording (item
    15); releases up to 1.5 formalized the simplest rule, a q-stone at
    every conflict, the rule of the submitted text. The August wording of
    the `threetier` branch is implemented and tested in the C++ engine, not
    formalized — see "The engine and the experiments".
12. Bisimulation (Definition 4.19, Lemma 4.20; `SgoBisim`). A bisimulation
    is as printed (`IsBisim`: the initial cores related; at related cores,
    for every turn grading, pass grading j < 2 and move, the evolution
    defined on one side exactly when on the other, with related cores of
    the values). The print's convention that C(G) consists of the legally
    obtainable cores is explicit here: the minimal quotient `QGame G` is
    the quotient of the legally obtainable cores (`ObC`, `CoreOb`) by
    bisimilarity, and `Minimal G` says that bisimilar legally obtainable
    cores are equal. The quotient's action is the action of G where the
    evolution reads it (a graded non pass move at a non ended core) and
    undefined elsewhere (`qmvAux`); its finality is lifted; its scoring is
    not carried (the print declares all its finals drawn). The projection
    `qS` is extended to every state by sending an unobtainable core to the
    class of the initial core; each lemma about it carries the hypothesis
    `CoreOb`, which holds wherever the theory reads a state
    (`coreOb_of_seqReach`, `rho_coreOb`, `semiC_coreOb'`). The radius
    spectrum is `InRadiusSpectrum G r := InSpectrum (QGame G) r`. Part (2)
    is proved through `lem_dynamics_3` on the isomorphism of quotients
    `bisimIso` (a chosen partner for each legally obtainable core; the
    partners of bisimilar cores are bisimilar by the composite
    bisimulation R⁻¹ ∘ ~ ∘ R). Part (3) is proved in both directions by
    transporting a simultaneization along π — the pushforward
    `BSet.img (qS G) ∘ ρ` and the pullback `pullRho` — where the print
    applies `lem_dynamics`; minimality makes π injective on the states of
    legally obtainable core (`qS_inj`), which is what the transport of the
    semi-classical states needs (`semiC_qS_rev`). The Go clause of
    Theorem 6.3 — the radius spectrum of Go is all of ℕ ⊔ {∞} — is
    `SgoGoMin.go_radius_spectrum`, from `SgoThm.go_radius_spectrum_full`
    (the clause under the hypothesis `Minimal (goGame n)`) and Lemma 6.13.
13. Lemma 6.13 (`SgoGoMin.go_minimal`): `Minimal (goGame n)` for every
    board side — bisimilar legally obtainable displays are equal; the
    legally obtainable displays are the print's legal diagrams reached by
    play (well-formed arrays, no q-stone, every component with a liberty,
    stamps zero, `goOb`), and two of them are equal exactly when every
    intersection carries the same stone (`display_ext`). The proof is the
    printed liberty-filling argument in a simplified form: bisimilar
    displays have the same occupancy (`bisim_occ`: a colored move is
    defined exactly at an empty intersection), so take i black in one and
    white in the other, K the black component of i and j a liberty of K;
    while K has a liberty l ≠ j, Black fills l — the stone joins K, which
    keeps j, so it stands, and K gains a stone (`fill_step`); the same
    move is legal in the partner, which stays bisimilar with i white
    (`fill_case`); the induction is on the number of board cells outside
    K (`compMeasure`). When the liberties of K are {j}, White at j
    captures K and stands (`final_black`: i empty, j occupied) while in
    the partner a White move removes a white stone only with the placed
    stone's component, which contains j (`final_white`): the occupancies
    differ at i or at j, against bisimilarity (`final_case`). The print's
    proof fills with White where White's stone would stand and with Black
    otherwise, and ends on the move to i alone; the Lean fills with Black
    throughout and ends on the dichotomy at i or j — the stone at j can
    suicide with i's component in the partner, so the move to i alone
    does not always separate (a 5×5 instance, checked with the engine, has
    i empty on both sides and j white on one). The print's proof now
    follows the same version.
14. The capture rule (release 1.5, the paper's `reduce` branch; numbered
    as in its `reduce2` branch since release 1.6). Definition 2.2 captures
    a white component C if (1) C is trapped and (2) the q-stone condition
    holds, and one of: (3) C is trapped on this turn, and no black stone
    or q-stone adjacent to C is trapped by white on this turn; (4) no
    black stone or q-stone adjacent to C is trapped by white, on any turn,
    with the notions of def_trapped without a turn (the residual capture);
    (5) the suicidal capture, C being trapped on this turn. Mirrored for
    black. `isCapturedPrint` transcribes Conditions 1–5 verbatim (`capCond1`
    … `capCond5`); `isCaptured_eq_print` proves it equal to `isCaptured =
    isCapturedOT || residualCap`, the form the proofs use: `isCapturedOT`
    is trapped on this turn, Condition 2, and 3 or 5 (the 3a/3b of the
    `reduce` text), `residualCap` is Conditions 1, 2 and 4, with
    `stoneTrapped` the turn-free `stoneTrappedBy`. On a component trapped
    on the turn the second form implies the first (`OT_of_residual`,
    `isCapturedOT_of_isCaptured`): Condition 4 gives Condition 3. The
    proofs read it as the print's proof of Lemma 6.4 does. Within Cap_n at a commuting turn every
    captured component still holds or touches a stone of the turn, so it
    is trapped on the turn (Step 6: `trappedOnTurn_of_member` on the live
    case's fresh stone; `SgoStage1.pT_trapped_on_t` for the single
    placement — a libertyless component of the mover's color holds the
    fresh stone, the state being legal, and one of the other color
    touches it); at the later stages no component is trapped, and each
    route needs one (Step 8, `noLibD_of_isCaptured`). The SGo witness
    refutes Condition 4 at the trapped q-stone as it refutes Condition 3
    (`SgoWit`). The color swap covers the new route (`stoneTrapped_swapD`,
    `isCaptured_swapD`), and so does the well-definedness of the
    conversion of q-stones (`cond2_of_isCaptured` in `recolor_excl`). The
    fifteen certificate lines are unchanged.
15. The stone placement rule (release 1.6). Section 2.3 places a stone at
    a conflict, both players moving to the same intersection i: (1)
    a q-stone if the conflict is trapping — a stone of either color added
    at i would be a trapping stone, adjacent to a component of the other
    color with no liberties (`wouldTrap`); (2) a black stone if i is
    adjacent to a black stone and to no white stone and no q-stone,
    mirrored for white; (3) a q-stone otherwise. `conflictKind` is this
    rule, and `placeJoint` uses it at every conflict, so SGo, DSGo and
    k-DSGo all play it (the print's Pl is the same rule). Rule (2) can
    place a colored stone where the entanglement holds both orders of the
    turn; SGo's pruning drops the branch of the other color, while the
    re-cut of DSGo reads occupancy only and keeps it. The proofs needed
    three facts: the rule is color-symmetric (`conflictKind_swapD`, inside
    `placeJoint_swapD`); the commuting turns of the main theorem have no
    conflict, as before; and the conflicts of the two witnesses, A1/A1 of
    the SGo witness and A2/A2 of the k-DSGo witness, are trapping, so they
    still place q-stones (`wit_trap0`, `kwit_trap1`). The fifteen
    certificate lines are unchanged.

## Separate artifacts (larger trusted base: native_decide)

Not in the default target; build or run individually.

- `lake build Exhaust` — `lem_onestage_3x3_exhaustive` (ExhaustBase.lean +
  Exhaust.lean): all 19,683 assignments of the 3×3 board, legality filtered
  in-proof, every commuting non pass ordered pair; ~3 min.
- `lake build Counts` — the 3×3 legal-state census cross-check (12,675).
- Differential tests against the paper's engines (`lake env lean
  <file>`): `Tests.lean` (1,844 legal Go transitions), `TestsDAll.lean`
  (display resolution, 1,722 playout turns; `TestsD300.lean` a 300-turn slice), `TestSerial.lean`
  (SGo, 240 games / 1,917 turns), `TestDelta.lean` (DSGo and k-DSGo, 390
  games / 3,199 turns); `TestsD.lean` is an eval sheet. Release 1.5
  regenerated the five display vectors and two SGo games that Condition 4
  changes (`SGO_ORPHAN=1`). Release 1.6 regenerated every sheet under the
  printed rules with the C++ engine (`SGO_ORPHAN=1 SGO_PLACE=4`; modes
  `dispgen`, `serialgen`, `deltagen`; its `tests/disp_d.txt`,
  `serial_d.txt`, `delta_d.txt`): 209 display vectors, 170 SGo games and
  299 DSGo/k-DSGo games change; 22 and 17 games are cut before a move
  that rule (2) makes unavailable. The DSGo/k-DSGo reference is new to
  the engine (`famStep`, written from the print, the Python one being
  lost); before the regeneration it replays the original sheet exactly.
  Every sheet passes.
- `EvalKWit.lean` — an `#eval` replay of the k-DSGo witness (side 5 for
  k = 1..4, and sides 6, 7, 8 for k = 3, 5, 8): the violation at A3 each
  time; a sanity check of the construction that `SgoKFin` proves.

`tools/` holds the Python generators of the test sheets and the witness
search; they need the paper's original Python engine (`sgo_engine.py`, not
included). The C++ engine below replays the same sheets (`./sgo test`) and
regenerates them under a rule (`dispgen`, `serialgen`, `deltagen`).
`attic/` holds inactive scratch, unrun variants and superseded checkpoints;
nothing there is built.

## The engine and the experiments

The computer experiments of the paper are those of Section 2.1: the depth
ladder of Table 1 and the play of strong networks of Table 2, on the 9×9
board, for SGo and for Go. They were run with `sgoz`, a self-play trainer.
The paper's rules engine (below) plays many games at once. A PyTorch network
(10 residual blocks of 128 channels with global pooling, after KataGo)
evaluates their positions on a GPU. Section 7 of the paper gives the method.
The networks also play in [SGo Arena](https://claude.ai/artifact/SVrxvsBVMGSEYUu9ZyJyrw),
in the browser.

- [sgoz_experiments.zip](sgoz_experiments.zip) — the trainer, the
  configurations, every game of Table 1 (the scores, one file per pair), the
  games of Table 2, the training logs, and the networks of generations 48
  and 56 of both lines. Its README gives the conventions and the commands.

The two tables from the hosted games need Python 3 and numpy only:

    unzip sgoz_experiments.zip && cd sgoz_experiments
    python3 code/fit_paper.py sgo/runs/ladder_o4 go/runs/ladder_o4     # Table 1 and the climbs (a few minutes)
    python3 code/stats.py --table sgo/runs/stats_g48_match.json go/runs/stats_g48_match.json   # Table 2

Replaying the experiments needs PyTorch and an NVIDIA GPU. On one RTX 4070 Ti
each line trained to generation 56 in about 16 hours, a ladder took two to
four hours, and the strong play ten minutes. A new training run gives other
networks and other numbers, within the printed errors.

The rules engine is `sgo.cpp`, a single C++ file: a transcription of the
executable Lean layer (`SgoDisplay`, `SgoSerial`, `SgoGo`). It is in both
packages. The trainer uses it unchanged, except that its scratch state is
per thread.

- [sgo_engine.zip](sgo_engine.zip) — `sgo.cpp`, the test sheets, and the
  Monte Carlo experiments of earlier versions of the paper (random play
  tables, 13×13 Monte Carlo ladders, a small self-play net). These are no
  longer in the paper; the package README documents them.

What ties the engine to this formalization. `SGO_ORPHAN=1 SGO_PLACE=4 ./sgo
test` replays the four Lean test sheets of release 1.6 through the engine —
`TestsDAll` (1,722 display resolutions), `Tests` (1,844 classical moves),
`TestSerial` (240 SGo games, 1,917 turns) and `TestDelta` (390 DSGo and
k-DSGo games, 3,199 turns), displays and entanglement states alike — with
0 mismatches. `SGO_ORPHAN=1` is Condition 4 of def_captured, `SGO_PLACE=4`
the placement rule of Section 2.3; plain `./sgo test` replays the sheets of
releases up to 1.4, `SGO_ORPHAN=1 ./sgo test` those of 1.5. The engine keeps
the slow, literal transcription of the rules as an oracle and drives play
through a chain-table layer; `./sgo difftest 300` plays 300 lockstep random
games on the boards 3×3 to 9×9 comparing the two, cell by cell, and
`SGO_CHECK=1` cross-checks every capture evaluation inside a match.

    unzip sgo_engine.zip && cd sgo_engine
    g++ -O2 -std=c++17 sgo.cpp -o sgo && SGO_ORPHAN=1 SGO_PLACE=4 ./sgo test

## Notes on core Lean (for readers of the proofs)

Core Lean 4.15 lacks Mathlib's `by_contra`, `split_ifs`, `Subperm` and
`LawfulBEq (Array _)`: components are handled by a filter-complement measure,
array equality through `Array.isEqv` bridges, and case analysis by
`by_cases` with `if_pos`/`if_neg`. Symbolic board sides make the component
search (fuel n*n) irreducible under `whnf`, so the witness files are written
entirely with rewriting lemmas rather than evaluation.
