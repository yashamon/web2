# stablelean — working conventions

Lean 4 formalization of Y. Savelyev, "Incompleteness theorems via stable computability".
Notes recorded during the development, for readers and maintainers of the proofs.

## Toolchain
- Lean 4.35.0, **core only (no Mathlib, no Batteries)**.
- Build: `lake build` (whole library) or
  `lake env lean Stable/Foo.lean` (one file; dependencies must have been `lake build`-ed first,
  stale .olean files give confusing errors — run `lake build Stable.Dep` after changing a dependency).
- `ℕ` is `notation "ℕ" => Nat` (defined in Stable/Comp.lean). `open Classical` is used; `decide`/`if`
  on arbitrary Props elaborates with `Classical.propDecidable`.

## Rules
- Never add `axiom`s. Never leave `sorry` in a file you declare done; if you cannot prove a statement,
  leave the `sorry`, and REPORT it with the reason (false as stated? missing lemma?).
- Do not change the *statement* of an existing theorem/def unless it is false or unprovable; if you must,
  report exactly what changed (downstream files depend on the statements).
- Private helper lemmas are welcome (`private theorem`), put them next to their use or in a new file
  `Stable/Prim.lean` (ℕ-level helpers over `TuringModel`) imported by `Stable/Enc.lean`.
- Keep proofs robust: prefer `cases h : t with | … ` over `cases t` when `t` is not a variable;
  `simp` with explicit lemma lists; `omega` for linear arithmetic.

## Core-Lean potholes (no Mathlib)
- No `by_contra` (use `Classical.byContradiction fun h => …`), no `set`, no `push_neg`, no `Set`,
  no `Finset`, no `Nat.find` (use `Stable.exists_least` + `Classical.choose`), no `Function.Injective`
  (we spell `∀ {a b}, f a = f b → a = b`).
- `Nat.repeat f n a` is `f^[n] a` (core). `List.getElem?` is `l[i]?`; `List.getElem?_eq_some_iff`,
  `List.getElem?_eq_none_iff` exist in core.
- `if_pos/if_neg/dif_pos/dif_neg` are deprecated: use `ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right`.
  `Option.bind`, `Option.map`
  simp lemmas: `Option.bind_some`, `Option.map_some'`, `Option.bind_none`, `Option.map_none'`,
  `Option.some_bind`, `Option.none_bind` — when in doubt `cases h : o <;> simp [h]`.
- `rw` auto-closes goals with `rfl` (a trailing `rfl` errors with "no goals").
- Structure-field `if` statements use the instance available at that point (`Nat.decLe` etc.), while
  `IsCompSet` uses classical `if`; bridge with `by_cases h : … <;> simp [h]` (see `isCompSet_le`).

## More pitfalls (learned)
- **Instance mismatch.** A hand-written `if ∀ j < n, …` or `decide (x = 0)` picks `Nat.decidableBallLT` /
  `instDecidableEqNat`, which does not match the classical instance inside `IsCompSet`/`CompSet`.
  Bridge with `by_cases h : … <;> simp [h]` on the whole `ite`, never by type ascriptions.
- **Leftover beta-redexes.** `rintro ⟨T, hT⟩` on `Comp`/`CompSet`/`Computes` leaves `(fun p => …) (b, n)`
  redexes, so a later `rw` fails: use `show …` to restate the goal, or `simp only []`/`dsimp only` first.
- `e M n` for `n : ℕ` is `(fun n => n) n`, not syntactically `n`: `rw [h]` with `h : M.eval T n = …`
  fails on `M.eval T (e M n)`; use `show M.eval T n = _` first (they are defeq).
- Core names: `Option.map_some`, `Option.map_none`, `Option.bind_some`, `Option.bind_none`,
  `Option.some_ne_none`, `Option.isSome_some`, `List.getElem?_eq_some_iff`, `List.getElem?_eq_none_iff`,
  `List.length_set`, `List.length_replicate`, `List.getElem?_set_self`/`List.getElem?_set_ne` (check with
  `#check` — names drift between versions), `Nat.repeat`.
- Typeclass "stuck" errors `Enc M ?m`: give the implicit type explicitly, e.g. `(compT_fst (A := X) (B := Y))`,
  `(comp_epsilonInv (A := B))`, or bind `∀ b : B` instead of `∀ b`.
- Downstream API (compiled): `Stable/Stab.lean` (IsStable/IsDecided, seqOfDec, decOfSeq, cT/DR, stabilizer
  lemma), `Stable/Machines.lean` (seqOf, decOf, InTB, InDB, Ts, TStable, TDecided, exists_K, exists_Omega,
  exists_decMachine, exists_stabMachine, RB, compSet_RB, tStable_iff_SR_RB, exists_Dec),
  `Stable/Logic.lean` (Language, Translation, DerivI, derivI_iff), `Stable/Arith.lean` (Arith, consistency
  notions, IsNTranslation, compT_on_pi_of_two).

## Lessons from `Undefinable.lean` (Appendix B)
- A `variable (D : UndefData A)` is only included in a theorem that mentions `D` in its *statement*; give
  `(D : UndefData A)` explicitly otherwise (or `include D`).
- Well-founded recursion over an abstract syntax: `match h : D.destruct s with …` plus
  `termination_by s => D.size s` and `decreasing_by all_goals simp_wf; · show D.size a < D.size s; rw [D.destruct_inl s a h]; …`
  (the `show` is needed because the goal mentions the let-bound copy of `s`). Equation lemmas: `rw [f]; split`
  then kill the impossible branches with `rename_i h; rw [D.destruct_neg] at h; cases h`.
- `hT : ∀ n, M.eval T n = (fun n => some (if … then 1 else 0)) n` from unpacking `IsCompSet` keeps a
  beta-redex: restate with `have hq : M.eval T (e M q) = some (if … then 1 else 0) := hT _` before `rw`.
- Core has `Classical.epsilon`/`epsilon_spec` (needs `Nonempty`, pass it with `haveI`), `List.range_succ`,
  `List.mem_filter`, `List.mem_filterMap`, `decide_eq_true_iff`, `Iff.of_eq`, `iff_not_self`; no `choose` tactic
  (use `Classical.choose`/`choose_spec` by hand).

## Lessons from `Perturb.lean` / `UndefinableZFC.lean` (Proposition B.10)
- A section `variable (S : SentSyntax L)` used only in a proof is not included: put `include S in` before
  the theorem (or mention `S` in the statement).
- When a hypothesis is `Z.deriv_of_mem (Or.inr rfl)` and the theory `G` is still a metavariable, Lean may
  infer `fun x => … ∨ a = x` (wrong orientation). Give `(G := Z.ext F a)` explicitly and use
  `Language.deriv_ext_self _ _`.
- `P.I` for a concrete `P : Perturb L` is only *definitionally* `ℕ × L.Sent`: `rw [List.map_map]` on a list
  typed `List (ℕ × L.Sent)` where `List P.I` is expected fails ("not type-correct under implicit
  transparency"). Transport along `L.deriv_mono` membership-wise instead, and state stage lemmas for
  `EN n ψ`, `actN n ψ` rather than for `P.E s`, `P.act s` (use `show` at the interface).
- `Stable.seqOf` already exists (`Closure.lean`); the "prepend a sentence to an enumeration" sequence is
  `seqPre`.
- Complete conjunctions over a list (`Language.vals`) avoid any type of valuations: exhaustiveness
  (`deriv_disj_vals`), exclusivity (`vals_excl`) and decision (`vals_decide`) are short inductions.

