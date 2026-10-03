# arithmeticlaws

A Lean 4 / Mathlib formalization of the **arithmetic law layer** of
*Invariant arithmetic of closed geodesics* — the number-theoretic backbone the
paper's title names.  The geometry (Fuller index, geodesic strings, covers,
return maps) enters only as named hypotheses; everything proved here is pure
arithmetic over the divisor lattice.

**Status: complete.** Every declaration compiles with no `sorry`; the main
theorems depend only on the three standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`), as verified by `#print axioms`
(see `AxiomCheck.lean`).

## Notation (paper §11 preamble)

For an indivisible class `β₀` and a metric that is `eβ₀`-taut and `eβ₀`-regular,
`P_c` is the set of prime closed geodesic strings of class `cβ₀`, and, with `i`
the local Fuller index `i(o) = −sign det(I − 𝓡_o) ∈ {±1}`:

| symbol | meaning | Lean |
|---|---|---|
| `F d` | `F(g, dβ₀) ∈ ℚ`, the Fuller count | `F : ℕ → ℚ` |
| `s d` | `∑_{o ∈ P_d} i(o)`, signed prime count | `s : ℕ → ℚ` |
| `b d` | `#{o ∈ P_d : o inverse-hyperbolic}` | `b : ℕ → ℚ` |
| `u d` | `#pos-hyperbolic − #elliptic` in `P_d` | `u : ℕ → ℚ` |
| `B_{d/2}` | `∑_{f ∣ d/2} f·b_f` (`0` for `d` odd) | `Bhalf b d` |
| `b_{d/2}` | `b(d/2)` (`0` for `d` odd) | `bhalf b d` |

## The geometric inputs (hypotheses)

Only these enter from outside; each is a printed lemma of the paper:

* **`hodd`** — `eq_oddmobius` (Theorem `thm_mobius`): for odd `e`,
  `e·F(g,eβ) = ∑_{d ∣ e} d·s_d`.
* **`hdF`** — `eq_dF` (Lemma `lem_mobius`, the covering bijection), at the
  divisor levels `d ∣ e`: `d·F(g,dβ₀) = ∑_{c ∣ d} c·I_c(d/c)`,
  `I_c(k) = ∑_{o∈P_c} i(o^k)`.
* **`hiter`** — `lem_iteratesigns`, aggregated, at the iterates `o^k` with
  `c·k ∣ e`: `I_c(k) = u_c + (-1)^k·b_c`.  These are exactly the iterates
  whose class `ckβ₀` is a divisor class of `eβ₀`, so that `o` and `o^k` are
  nondegenerate by `eβ₀`-regularity; nothing is assumed about the
  intermediate iterates `o^j`, `j < k`, whose classes need not divide `eβ₀`.
* **`hsub`** — `s_c = u_c − b_c` (definition of `u`).
* **`hmaster`** — the master identity `d·F = (∑_{c∣d} c·s_c) + 2·B_{d/2}`
  at the divisor levels `d ∣ e`.  Supplied either directly or, via
  `master_of_signlaw`, from `hdF` + `hiter` + `hsub` (so the ±1 cancellation
  is itself machine-checked).

All hypotheses are assumed only where the paper establishes them — at the
divisor levels of `e` — matching the paper's "tautness and regularity of the
divisor classes are automatic".
* **`hF`** (torus) `F ≡ 0` — `thm_torusvanishing`; **`hF`** (surface)
  `F(g,dβ₀) = 1/d` — `thm_surfacevanishing`.

## Theorem ↔ paper map

| Lean (`namespace GeodesicArithmetic`) | Paper |
|---|---|
| `mobius_inversion` | `eq_mobiusinversion` — Möbius inversion `s_e = (1/e)∑_{d∣e} μ(e/d)·d·F(g,dβ)` (divisor-antidiagonal spelling) |
| `s_eq_zero_of_F_eq_zero` | `thm_mobius` (1): `F ≡ 0` on divisors of `e` ⟹ `s_e = 0` |
| `s_eq_indicator_of_F_eq_inv` | `thm_mobius` (2): `F(g,dβ) = 1/d` ⟹ `s_e = 0` (`e>1`), `s_1 = 1` |
| `eq_evendivisors` | `eq_evendivisors`: `∑_{c∣d} c·b_{c/2} = 2·B_{d/2}` |
| `master_of_signlaw` | `eq_dF` + `lem_iteratesigns` ⟹ the master identity (the ±1 cancellation) |
| `solve_divisorsystem` | `eq_divisorsystem` ⟹ `s_d = −b_{d/2}` for all `d ∣ e` (the induction over divisors) |
| `primitivelaw_forward` | `prop_primitivelaw`, forward: `F ≡ 0` ⟹ `s_d = −b_{d/2}` (`eq_primitivelaw` at `d=e`) |
| `primitivelaw_converse` | `prop_primitivelaw`, converse |
| `unconditional_torus` | `cor_unconditionallaw`: `s_e = −b_{e/2}` on `T²` |
| `unconditional_surface` | `cor_unconditionalsurface`: `∑_{c∣d} c·s_c = 1 − 2·B_{d/2}` (genus ≥ 2) |
| `unconditional_surface_solution` | `cor_unconditionalsurface`, solved: `s_1 = 1`, `s_d = −b_{d/2}` for `1 < d ∣ e` (as in the proof of `cor_oddeven`) |
| `even_card_of_signsum_zero`, `two_le_card_of_signsum_zero` | `s_d = 0` ⟹ `#P_d` even, so a prime string is accompanied by another (the pairing) |
| `odd_card_of_signsum_one` | `s_1 = 1` ⟹ `#P_1` odd |
| `abs_signsum_le_card` | `#P_d ≥ \|s_d\|`, giving `#P_{2n} ≥ b_n` from `s_{2n} = −b_n` |

## Proof route

* `ArithLaw/Mobius.lean` — the odd-class law.  The inversion is Mathlib's
  `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on` on the divisor-closed
  set of odd numbers (`odd_of_dvd_odd`).  The two consequences are proved
  directly from `hodd` by strong induction over divisors, independently of the
  inversion formula — matching the paper's "in particular".
* `ArithLaw/DivisorSystem.lean` — the §11 divisor system.  `eq_evendivisors`
  reindexes even divisors `c = 2f` over the divisors of `d/2`;
  `solve_divisorsystem` is the strong induction over divisors solving
  `∑_{c∣d} c·s_c = −2·B_{d/2}`; the primitive law and the two unconditional
  laws follow by feeding in `F ≡ 0` resp. `F = 1/d`, the surface system being
  solved by shifting `s_1` by `1`, which turns it into the torus system.
* `ArithLaw/SignLaw.lean` — the master identity from the raw sign law:
  `(-1)^{d/c} + 1` is `2` exactly when `d/c` is even, i.e. `2c ∣ d`, i.e.
  `c ∣ d/2` (`evenquot`); the ±1 terms telescope to `2·B_{d/2}`.
* `ArithLaw/Counting.lean` — from signed counts to counts: a `±1`-sum is
  congruent to its number of terms mod 2, and is bounded by it in absolute
  value.

## Building

Requires the toolchain in `lean-toolchain` (`leanprover/lean4:v4.35.0-rc3`)
and Mathlib (tested at commit `282fbb865d53622ef7f9ef29f6763a0327ee6b5f`).

```
lake exe cache get
lake build
lake env lean AxiomCheck.lean    -- prints [propext, Classical.choice, Quot.sound] ×16
```
