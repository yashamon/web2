# potency

A Lean 4 / Mathlib formalization of the potency lemma of *Invariant
arithmetic of closed geodesics* (Lemma 6.9, `lem_potency`):

> Let `G = π₁(Σ)` for a closed orientable aspherical surface, `a ≠ 1` in
> `G`, and `p` a prime.  Then `G` has a finite quotient in which the image
> of `a` has order **exactly** `p`.

**Status: complete.** Every declaration compiles with no `sorry`; the main
theorems depend only on the three standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`), as verified by
`#print axioms`.

## The single named hypothesis

The formal endpoint is

```lean
theorem potentAt_of_residuallyFree {G : Type*} [Group G]
    (hres : ∀ b : G, b ≠ 1 → ∃ (k : ℕ) (φ : G →* FreeGroup (Fin k)), φ b ≠ 1)
    {a : G} (ha : a ≠ 1) : PotentAt G a
```

where `PotentAt G a` says: for every prime `p` there are a finite group
`Q` and a homomorphism `π : G →* Q` with `orderOf (π a) = p`.  (The finite
quotient of the paper statement is the image `π(G) ≤ Q`; the order of
`π a` in the image equals its order in `Q`.)

The hypothesis `hres` is **Baumslag's residual freeness of surface groups**
[G. Baumslag, *On generalised free products*, Math. Z. 78 (1962) 423–438]
— stated with finite-rank free targets, which is what the surface-group
case provides (for the torus, `ℤ² → ℤ` projection to a coordinate carrying
`b` does it).  This is the *only* classical input.  Everything else —
in particular the potency of free groups, which the paper obtained from
residual torsion-free nilpotence of free groups (Magnus), the structure of
the lower central quotients (Witt), and residual finiteness of finitely
generated nilpotent groups (Segal) — is **proved from scratch** here:

```lean
theorem potentAt_freeGroup {k : ℕ} {x : FreeGroup (Fin k)} (hx : x ≠ 1) :
    PotentAt (FreeGroup (Fin k)) x
```

## The proof route (and why it is simpler than the paper's)

The classical stack is replaced by a direct argument through a *truncated
Magnus embedding*:

1.  `Potency/NC.lean` — the ring `NC k ℤ` of noncommutative power series
    in `k` variables, realized as arbitrary coefficient functions
    `List (Fin k) → ℤ` with convolution product.  Every series with
    constant term `1` is a unit (`unitOfCT`; inverse by recursion on word
    length).  `TNC k c R` is the truncation to words of length `≤ c` —
    a **finite** ring when `R` is finite — and `trunc : NC k R →+* TNC k c R`
    the truncation homomorphism.
2.  `Potency/Magnus.lean` — the Magnus homomorphism
    `magnus : FreeGroup (Fin k) →* (NC k ℤ)ˣ`, `xᵢ ↦ 1 + Xᵢ`.
    The quantitative injectivity (`exists_coeff_ne_zero`): for `x ≠ 1`
    with syllable decomposition `x = x_{j₁}^{a₁} ⋯ x_{j_m}^{a_m}` (maximal
    runs of the reduced word), the coefficient of the *syllable monomial*
    `X_{j₁} X_{j₂} ⋯ X_{j_m}` in `magnus x` is exactly `a₁ a₂ ⋯ a_m ≠ 0`.
    The counting argument: `(1 + X_j)^a` is supported on runs of `j`
    (`coeff_oneAddX_zpow`, with generalized binomial coefficients
    `intBinom` from `Potency/Binom.lean`), and the syllable monomial has
    no two equal adjacent letters, so each of its `m` letters must be
    emitted by a distinct factor, in order, each from the linear term.
3.  `Potency/Order.lean` — the exact-order engine.  Let `c` be the least
    positive degree carrying a nonzero coefficient of `u = magnus x`.
    In the degree-`c` truncation, `u ↦ 1 + P` with `P` supported in degree
    exactly `c`, so `P * P = 0` and `(1 + P)^n = 1 + n • P`.  Let `s` be
    the least `p`-valuation of the integer coefficients of `P`; reduce
    coefficients mod `p^(s+1)`.  Then `p • P̄ = 0` and `P̄ ≠ 0`, so `1 + P̄`
    has order exactly `p` in the units of the finite ring
    `TNC k c (ZMod (p^(s+1)))`.
4.  `Potency/Main.lean` — `PotentAt`, the free-group theorem, the glue
    theorem with the Baumslag hypothesis, and
    `exists_addOrderOf_eq_prime`, the standalone valuation lemma used by
    the paper's case (i) (homologically visible classes), kept for the
    audit although the Magnus route subsumes it.

Note the corollary for the *paper*: Lemma 6.9's proof can be run with this
argument instead, in which case the case split (i)/(ii) disappears and the
only citation left is [Bau62].

## Clause-by-clause audit against Lemma 6.9

| Paper step | Formal statement |
|---|---|
| "finite quotient where `q(a)` has order exactly `p`" | `PotentAt` (`Potency/Main.lean`) |
| case (i): `ā ≠ 0` in `H₁`, valuation functional mod `p^(s+1)` | `exists_addOrderOf_eq_prime` (`Potency/Main.lean`) |
| case (ii): Baumslag residual freeness | hypothesis `hres` of `potentAt_of_residuallyFree` |
| free-group potency (paper: Magnus + Witt + Segal) | `potentAt_freeGroup`, proved via `freeGroup_exists_orderOf_eq` (`Potency/Order.lean`) |
| Magnus embedding injectivity | `exists_coeff_ne_zero` (`Potency/Magnus.lean`), self-contained |
| exact order `p` (valuation + reduction) | `exists_finite_orderOf_eq` (`Potency/Order.lean`) |

## Building

Requires the Lean toolchain pinned in `lean-toolchain`
(`leanprover/lean4:v4.35.0-rc3`) and Mathlib (tested at commit
`282fbb865d53622ef7f9ef29f6763a0327ee6b5f`).  With network access to
`cache.mathlib.org`:

```
lake exe cache get
lake build
```

Alternatively, add `lean_lib Potency` to the lakefile of a Mathlib
checkout, place `Potency.lean` and `Potency/` at its root, and
`lake build Potency` (this is how it was developed).

Axiom check:

```lean
import Potency
#print axioms Potency.potentAt_of_residuallyFree
-- [propext, Classical.choice, Quot.sound]
```
