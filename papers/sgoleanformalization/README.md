# sgolean — Lean 4 formalization of the main theorems, the one-stage lemma, and the simultaneization theory of *The radius spectrum of games, and simultaneous Go via objective quantum reduction*

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

Axiom footprint of every theorem above: `[propext, Classical.choice,
Quot.sound]` — the standard trio. No `sorryAx` (no incomplete proof) and no
`Lean.ofReduceBool` (no `native_decide`, i.e. no trust in the compiler) in
their dependency cones.

Release 1.3. Hosted at
<https://yashamon.github.io/web2/papers/sgoleanformalization/> — the files
below, this [README](README.md), and the archive
[sgoleanformalization-1.3.zip](sgoleanformalization-1.3.zip). (Release 1.0
carried the main theorem and the one-stage lemma; 1.1 added `lem_symmetric`
and `lem_dynamics`; 1.2 added `thm_zero`, `lem_familysymmetric` and
`lem_universal`, with the sequential-game layer as the paper's def_sequential;
1.3 aligns the definitions with the current print: def_faithful is the single
interface equation (`FaithfulAt`), `#` is undefined at pass grading 2
(`hashOp_done`), and the pass grading is read in Z₃.)

## Verifying this development

Four commands; no dependency beyond Lean itself:

    curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
    curl -LO https://yashamon.github.io/web2/papers/sgoleanformalization/sgoleanformalization-1.3.zip
    unzip sgoleanformalization-1.3.zip && cd sgoleanformalization
    lake build          # kernel-checks the complete chain (lean-toolchain pins v4.15.0; ~2 min)

On Windows, `tar -xf sgoleanformalization-1.3.zip` unpacks the archive in
place (PowerShell's Extract-All wraps it in a second folder of the same
name, and `lake build` then finds no lakefile); on Linux use `unzip`, GNU
tar not reading zip archives.

Then the axiom certificate:

    lake env lean Audit.lean

Expected output, exactly these ten lines:

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

Gold-standard extra: replay the build through an external kernel with
lean4checker. The CI workflow (`.github/workflows/ci.yml`, for a git
hosting of the same files) runs the build and greps the ten lines.

## What is checked: where the printed notions live

The default target `Sgolean` (lakefile.toml) builds the whole sorry-free
chain. Correspondence with the print is documented at the top of each file.

Classical Go and the display calculus (Section 2):
- `SgoGo` — classical Go on diagrams: the placed diagram B + m, go_captures,
  go_suicide, go_closure (`goMoveN`).
- `SgoDisplay` — the display calculus: q-stones and time stamps,
  def_trapped, def_captured 1/2/3a/3b, the basic capture reduction,
  its fixpoint (Cap_n), placeJoint (collision → q-stone), the stage
  recursion (OR).

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
11. Not formalized, by decision: Theorem 6.7 (augmented chess has no simple
    simultaneization of positive radius — a retrograde statement about
    legally obtainable chess positions), the Nash theorem 5.3 and its
    corollary 5.4, and the empirical Section 7. The rules of SGo are
    formalized as the engine of `SgoDisplay`/`SgoSerial`/`SgoDelta` and
    differentially tested against the paper's Python engine (below).

## Separate artifacts (larger trusted base: native_decide)

Not in the default target; build or run individually.

- `lake build Exhaust` — `lem_onestage_3x3_exhaustive` (ExhaustBase.lean +
  Exhaust.lean): all 19,683 assignments of the 3×3 board, legality filtered
  in-proof, every commuting non pass ordered pair; ~3 min.
- `lake build Counts` — the 3×3 legal-state census cross-check (12,675).
- Differential tests against the paper's Python engine (`lake env lean
  <file>`): `Tests.lean` (1,844 legal Go transitions), `TestsDAll.lean`
  (display resolution, 1,722 playout turns; `TestsD300.lean` a 300-turn slice), `TestSerial.lean`
  (SGo, 240 games / 2,009 turns), `TestDelta.lean` (DSGo and k-DSGo, 390
  games / 3,262 turns); `TestsD.lean` is an eval sheet.
- `EvalKWit.lean` — an `#eval` replay of the k-DSGo witness (side 5 for
  k = 1..4, and sides 6, 7, 8 for k = 3, 5, 8): the violation at A3 each
  time; a sanity check of the construction that `SgoKFin` proves.

`tools/` holds the Python generators of the test sheets and the witness
search; they need the paper's engine (`sgo_engine.py`, not included).
`attic/` holds inactive scratch, unrun variants and superseded checkpoints;
nothing there is built.

## Notes on core Lean (for readers of the proofs)

Core Lean 4.15 lacks Mathlib's `by_contra`, `split_ifs`, `Subperm` and
`LawfulBEq (Array _)`: components are handled by a filter-complement measure,
array equality through `Array.isEqv` bridges, and case analysis by
`by_cases` with `if_pos`/`if_neg`. Symbolic board sides make the component
search (fuel n*n) irreducible under `whnf`, so the witness files are written
entirely with rewriting lemmas rather than evaluation.
