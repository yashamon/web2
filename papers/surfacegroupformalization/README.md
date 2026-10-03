# Lean 4 formalizations for *Invariant arithmetic of closed geodesics*

Two Lean 4 / Mathlib formalizations accompany the paper.  Both compile with no
`sorry`, and every main theorem depends only on the three standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`), as checked by the `AxiomCheck.lean`
file in each repository.

Each repository below is self-contained: its own `README.md` is the audit,
mapping every Lean theorem to the paper statement it formalizes and listing
each named hypothesis against the lemma it stands for.

## 1. `surfacegroupformalization/` — the potency lemma (Lemma `lem_potency`)

Surface groups admit, for every nontrivial element `a` and every prime `p`, a
finite quotient in which `a` has order exactly `p`.  The single named hypothesis
is Baumslag's residual freeness of surface groups; everything else — in
particular the potency of free groups, via a truncated Magnus embedding and the
syllable-coefficient computation — is proved from scratch.

* Sources: [`surfacegroupformalization/`](surfacegroupformalization/) —
  `Potency/NC.lean` (noncommutative power series and their truncations),
  `Potency/Magnus.lean` (the Magnus homomorphism and its injectivity payload),
  `Potency/Order.lean` (the exact-order engine), `Potency/Main.lean`.
* Archive: [`surfacegroupformalization.zip`](surfacegroupformalization.zip).
* Audit: [`surfacegroupformalization/README.md`](surfacegroupformalization/README.md).

## 2. `arithmeticlaws/` — the arithmetic law layer (Theorem `thm_mobius`, §11)

The number-theoretic backbone of the paper, with the geometry entering only as
named hypotheses: the Möbius-inverted odd-class law and its two consequences,
the §11 divisor system (`eq_evendivisors`, Proposition `prop_primitivelaw` in
both directions), the unconditional laws on the torus and on higher-genus
surfaces (the latter also solved: `s_1 = 1`, `s_d = −b_{d/2}` for `d > 1`),
the ±1 sign cancellation that produces the master identity from the covering
bijection and the surface sign law, and the passage from signed counts to
counts (parity of `#P_d`, and `#P_d ≥ |s_d|`).

* Sources: [`arithmeticlaws/`](arithmeticlaws/) — `ArithLaw/Mobius.lean`,
  `ArithLaw/DivisorSystem.lean`, `ArithLaw/SignLaw.lean`,
  `ArithLaw/Counting.lean`.
* Archive: [`arithmeticlaws.zip`](arithmeticlaws.zip).
* Audit: [`arithmeticlaws/README.md`](arithmeticlaws/README.md).

## Building either repository

Both pin the toolchain `leanprover/lean4:v4.35.0-rc3` and Mathlib at commit
`282fbb865d53622ef7f9ef29f6763a0327ee6b5f`.  In the repository directory:

```
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```
