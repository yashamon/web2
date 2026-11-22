import Stable.Logic

/-!
# The deductive closure of a stably c.e. theory (Lemma 3.22, `lemma_closure`)

For a first order language `𝓛` there is a total computable `C : 𝒯 → 𝒯` such that for every `T`,
`C T ∈ 𝒯_𝓛`, `(C T)'` is total, and `(C T)^s = closure (T^s)`.  (In the paper the last clause
is stated for `T ∈ 𝒯_𝓛`; here `T^s = Stab (seqOf T)` makes sense for every `T`, see
`Stable.Machines`, and the clause holds for every `T`.)

The proof is the stabilizer-machine construction applied to the relation `R_C` below:
`(T, γ, u, v) ∈ R_C` iff
1. `u = e (p, l, m̄, k̄)` for some `(p, l, m̄, k̄) ∈ ℕ × L(𝓛) × L(ℕ) × L(ℕ)` with
   `length m̄ = length k̄ = length l`, `(p, l, γ) ∈ Prf`, and
   `(T, m̄(j), k̄(j), e (l(j), +)) ∈ Halt'` for all `j < length l`;
2. and, if `v = e (n̄, k̄')` with `length n̄ = length k̄' = length l`, then for all `j < length l`:
   `n̄(j) ≤ m̄(j)` or `(T, n̄(j), k̄'(j), e (l(j), -)) ∉ Halt'`.
Then `∃ u ∀ v, R_C (T, γ, u, v)` iff there are a list `l` of `T`-stable sentences and a derivation
of `γ` from `l`, i.e. iff `γ ∈ closure (T^s)`.
-/

namespace Stable

open Classical

variable {M : TuringModel} (L : Language M)

/-- Condition (1) of `R_C` on the decoded tuple `(p, l, m̄, k̄)`. -/
def RC₁ (T : M.Code) (γ : L.Sent) (q : ℕ × List L.Sent × List ℕ × List ℕ) : Prop :=
  q.2.2.1.length = q.2.1.length ∧ q.2.2.2.length = q.2.1.length ∧ L.Prf q.1 q.2.1 γ ∧
    ∀ j, j < q.2.1.length → ∃ (γ' : L.Sent) (m k : ℕ),
      q.2.1[j]? = some γ' ∧ q.2.2.1[j]? = some m ∧ q.2.2.2[j]? = some k ∧
        M.run T m k = some (e M (γ', true))

/-- Condition (2) of `R_C`: for the decoded `(n̄, k̄')` of `v`. -/
def RC₂ (T : M.Code) (q : ℕ × List L.Sent × List ℕ × List ℕ) (r : List ℕ × List ℕ) : Prop :=
  r.1.length = q.2.1.length → r.2.length = q.2.1.length →
    ∀ j, j < q.2.1.length → ∃ (γ' : L.Sent) (m n k' : ℕ),
      q.2.1[j]? = some γ' ∧ q.2.2.1[j]? = some m ∧ r.1[j]? = some n ∧ r.2[j]? = some k' ∧
        (n ≤ m ∨ M.run T n k' ≠ some (e M (γ', false)))

/-- The relation `R_C ⊂ 𝒯 × 𝓛 × ℕ × ℕ` of the proof of Lemma 3.22. -/
def RC (T : M.Code) (γ : L.Sent) (u v : ℕ) : Prop :=
  ∃ q : ℕ × List L.Sent × List ℕ × List ℕ, e M q = u ∧ RC₁ L T γ q ∧
    ∀ r : List ℕ × List ℕ, e M r = v → RC₂ L T q r

/-! ### Computability of `R_C`

The predicates are built from the inside out; the bound variables of the nested existentials
are appended on the right of the parameter tuple, `(((y, γ'), m), k)`. -/

/-- `∃ b, (fl a)[fj a]? = some b ∧ Φ a b` for total computable `fl`, `fj` and computable `Φ`. -/
private theorem compSet_exists_nth {A B : Type} [Enc M A] [Enc M B] {fl : A → List B}
    {fj : A → ℕ} (hl : CompT M fl) (hj : CompT M fj) {Φ : A → B → Prop}
    (hΦ : CompSet M (fun p : A × B => Φ p.1 p.2)) :
    CompSet M (fun a => ∃ b, (fl a)[fj a]? = some b ∧ Φ a b) :=
  CompSet.exists_eq_some (compT_nthOpt.comp (CompT.pair hl hj)) hΦ

/-- The inner existential of condition (1), as a predicate of `y = ((T, q), j)`. -/
private theorem compSet_RC₁_nth :
    CompSet M (fun y : (M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × ℕ =>
      ∃ (γ' : L.Sent) (m k : ℕ), y.1.2.2.1[y.2]? = some γ' ∧ y.1.2.2.2.1[y.2]? = some m ∧
        y.1.2.2.2.2[y.2]? = some k ∧ M.run y.1.1 m k = some (e M (γ', true))) := by
  -- `run T m k = some (e (γ', +))`, on `(((y, γ'), m), k)`
  have h3 : CompSet M (fun w : ((((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × ℕ) ×
      L.Sent) × ℕ) × ℕ => M.run w.1.1.1.1.1 w.1.2 w.2 = some (e M (w.1.1.2, true))) :=
    compSet_halt'.comp (CompT.pair
      (compT_fst.comp (compT_fst.comp (compT_fst.comp (compT_fst.comp compT_fst))))
      (CompT.pair (compT_snd.comp compT_fst) (CompT.pair compT_snd
        (compT_e.comp (CompT.pair (compT_snd.comp (compT_fst.comp compT_fst))
          (compT_const true))))))
  -- `∃ k, k̄[j]? = some k ∧ …`, on `((y, γ'), m)`
  have h2 := compSet_exists_nth
    (fl := fun a : (((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × ℕ) × L.Sent) × ℕ =>
      a.1.1.1.2.2.2.2) (fj := fun a => a.1.1.2)
    (Φ := fun a k => M.run a.1.1.1.1 a.2 k = some (e M (a.1.2, true)))
    (compT_snd.comp (compT_snd.comp (compT_snd.comp (compT_snd.comp
      (compT_fst.comp (compT_fst.comp compT_fst))))))
    (compT_snd.comp (compT_fst.comp compT_fst)) h3
  -- `∃ m, m̄[j]? = some m ∧ …`, on `(y, γ')`
  have h1 := compSet_exists_nth
    (fl := fun a : ((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × ℕ) × L.Sent =>
      a.1.1.2.2.2.1) (fj := fun a => a.1.2)
    (Φ := fun a m => ∃ k, a.1.1.2.2.2.2[a.1.2]? = some k ∧
      M.run a.1.1.1 m k = some (e M (a.2, true)))
    (compT_fst.comp (compT_snd.comp (compT_snd.comp (compT_snd.comp
      (compT_fst.comp compT_fst)))))
    (compT_snd.comp compT_fst) h2
  -- `∃ γ', l[j]? = some γ' ∧ …`, on `y`
  have h0 := compSet_exists_nth
    (fl := fun y : (M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × ℕ => y.1.2.2.1)
    (fj := fun y => y.2)
    (Φ := fun y γ' => ∃ m, y.1.2.2.2.1[y.2]? = some m ∧ ∃ k, y.1.2.2.2.2[y.2]? = some k ∧
      M.run y.1.1 m k = some (e M (γ', true)))
    (compT_fst.comp (compT_snd.comp (compT_snd.comp compT_fst))) compT_snd h1
  refine h0.congr fun y => ?_
  constructor
  · rintro ⟨γ', h1, m, h2, k, h3, h4⟩; exact ⟨γ', m, k, h1, h2, h3, h4⟩
  · rintro ⟨γ', m, k, h1, h2, h3, h4⟩; exact ⟨γ', h1, m, h2, k, h3, h4⟩

/-- Condition (1) is computable, as a predicate of `((T, γ), q)`. -/
private theorem compSet_RC₁ :
    CompSet M (fun z : (M.Code × L.Sent) × (ℕ × List L.Sent × List ℕ × List ℕ) =>
      RC₁ L z.1.1 z.1.2 z.2) := by
  have hl : CompT M (fun z : (M.Code × L.Sent) × (ℕ × List L.Sent × List ℕ × List ℕ) =>
      z.2.2.1.length) := compT_length.comp (compT_fst.comp (compT_snd.comp compT_snd))
  have hlen1 : CompSet M (fun z : (M.Code × L.Sent) × (ℕ × List L.Sent × List ℕ × List ℕ) =>
      z.2.2.2.1.length = z.2.2.1.length) :=
    compSet_eq (compT_length.comp (compT_fst.comp (compT_snd.comp (compT_snd.comp compT_snd)))) hl
  have hlen2 : CompSet M (fun z : (M.Code × L.Sent) × (ℕ × List L.Sent × List ℕ × List ℕ) =>
      z.2.2.2.2.length = z.2.2.1.length) :=
    compSet_eq (compT_length.comp (compT_snd.comp (compT_snd.comp (compT_snd.comp compT_snd)))) hl
  have hprf : CompSet M (fun z : (M.Code × L.Sent) × (ℕ × List L.Sent × List ℕ × List ℕ) =>
      L.Prf z.2.1 z.2.2.1 z.1.2) :=
    L.prf_comp.comp (CompT.pair (compT_fst.comp compT_snd)
      (CompT.pair (compT_fst.comp (compT_snd.comp compT_snd)) (compT_snd.comp compT_fst)))
  have hball : CompSet M (fun z : (M.Code × L.Sent) × (ℕ × List L.Sent × List ℕ × List ℕ) =>
      ∀ j, j < z.2.2.1.length → ∃ (γ' : L.Sent) (m k : ℕ), z.2.2.1[j]? = some γ' ∧
        z.2.2.2.1[j]? = some m ∧ z.2.2.2.2[j]? = some k ∧
          M.run z.1.1 m k = some (e M (γ', true))) :=
    (CompSet.ballLt (P := fun (a : M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) j =>
      ∃ (γ' : L.Sent) (m k : ℕ), a.2.2.1[j]? = some γ' ∧ a.2.2.2.1[j]? = some m ∧
        a.2.2.2.2[j]? = some k ∧ M.run a.1 m k = some (e M (γ', true)))
      (compSet_RC₁_nth L)).comp
      (CompT.pair (CompT.pair (compT_fst.comp compT_fst) compT_snd) hl)
  exact (hlen1.and (hlen2.and (hprf.and hball))).congr fun z => Iff.rfl

/-- The inner existential of condition (2), as a predicate of `y = (((T, q), r), j)`. -/
private theorem compSet_RC₂_nth :
    CompSet M (fun y : ((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × (List ℕ × List ℕ)) ×
        ℕ =>
      ∃ (γ' : L.Sent) (m n k' : ℕ), y.1.1.2.2.1[y.2]? = some γ' ∧
        y.1.1.2.2.2.1[y.2]? = some m ∧ y.1.2.1[y.2]? = some n ∧ y.1.2.2[y.2]? = some k' ∧
          (n ≤ m ∨ M.run y.1.1.1 n k' ≠ some (e M (γ', false)))) := by
  -- `n ≤ m ∨ run T n k' ≠ some (e (γ', -))`, on `((((y, γ'), m), n), k')`
  have h4 : CompSet M (fun w : (((((((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) ×
      (List ℕ × List ℕ)) × ℕ) × L.Sent) × ℕ) × ℕ) × ℕ) =>
      w.1.2 ≤ w.1.1.2 ∨ M.run w.1.1.1.1.1.1.1 w.1.2 w.2 ≠ some (e M (w.1.1.1.2, false))) :=
    (compSet_le (compT_snd.comp compT_fst) (compT_snd.comp (compT_fst.comp compT_fst))).or
      (compSet_halt'.comp (CompT.pair
        (compT_fst.comp (compT_fst.comp (compT_fst.comp (compT_fst.comp (compT_fst.comp
          (compT_fst.comp compT_fst))))))
        (CompT.pair (compT_snd.comp compT_fst) (CompT.pair compT_snd
          (compT_e.comp (CompT.pair (compT_snd.comp (compT_fst.comp (compT_fst.comp compT_fst)))
            (compT_const false))))))).not
  -- `∃ k', k̄'[j]? = some k' ∧ …`, on `(((y, γ'), m), n)`
  have h3 := compSet_exists_nth
    (fl := fun a : (((((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × (List ℕ × List ℕ)) ×
      ℕ) × L.Sent) × ℕ) × ℕ => a.1.1.1.1.2.2) (fj := fun a => a.1.1.1.2)
    (Φ := fun a k' => a.2 ≤ a.1.2 ∨ M.run a.1.1.1.1.1.1 a.2 k' ≠ some (e M (a.1.1.2, false)))
    (compT_snd.comp (compT_snd.comp (compT_fst.comp (compT_fst.comp (compT_fst.comp
      compT_fst)))))
    (compT_snd.comp (compT_fst.comp (compT_fst.comp compT_fst))) h4
  -- `∃ n, n̄[j]? = some n ∧ …`, on `((y, γ'), m)`
  have h2 := compSet_exists_nth
    (fl := fun a : ((((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × (List ℕ × List ℕ)) ×
      ℕ) × L.Sent) × ℕ => a.1.1.1.2.1) (fj := fun a => a.1.1.2)
    (Φ := fun a n => ∃ k', a.1.1.1.2.2[a.1.1.2]? = some k' ∧
      (n ≤ a.2 ∨ M.run a.1.1.1.1.1 n k' ≠ some (e M (a.1.2, false))))
    (compT_fst.comp (compT_snd.comp (compT_fst.comp (compT_fst.comp compT_fst))))
    (compT_snd.comp (compT_fst.comp compT_fst)) h3
  -- `∃ m, m̄[j]? = some m ∧ …`, on `(y, γ')`
  have h1 := compSet_exists_nth
    (fl := fun a : (((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × (List ℕ × List ℕ)) ×
      ℕ) × L.Sent => a.1.1.1.2.2.2.1) (fj := fun a => a.1.2)
    (Φ := fun a m => ∃ n, a.1.1.2.1[a.1.2]? = some n ∧ ∃ k', a.1.1.2.2[a.1.2]? = some k' ∧
      (n ≤ m ∨ M.run a.1.1.1.1 n k' ≠ some (e M (a.2, false))))
    (compT_fst.comp (compT_snd.comp (compT_snd.comp (compT_snd.comp
      (compT_fst.comp (compT_fst.comp compT_fst))))))
    (compT_snd.comp compT_fst) h2
  -- `∃ γ', l[j]? = some γ' ∧ …`, on `y`
  have h0 := compSet_exists_nth
    (fl := fun y : ((M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × (List ℕ × List ℕ)) × ℕ =>
      y.1.1.2.2.1) (fj := fun y => y.2)
    (Φ := fun y γ' => ∃ m, y.1.1.2.2.2.1[y.2]? = some m ∧ ∃ n, y.1.2.1[y.2]? = some n ∧
      ∃ k', y.1.2.2[y.2]? = some k' ∧ (n ≤ m ∨ M.run y.1.1.1 n k' ≠ some (e M (γ', false))))
    (compT_fst.comp (compT_snd.comp (compT_snd.comp (compT_fst.comp compT_fst)))) compT_snd h1
  refine h0.congr fun y => ?_
  constructor
  · rintro ⟨γ', h1, m, h2, n, h3, k', h4, h5⟩; exact ⟨γ', m, n, k', h1, h2, h3, h4, h5⟩
  · rintro ⟨γ', m, n, k', h1, h2, h3, h4, h5⟩; exact ⟨γ', h1, m, h2, n, h3, k', h4, h5⟩

/-- Condition (2) is computable, as a predicate of `((T, q), r)`. -/
private theorem compSet_RC₂ :
    CompSet M (fun z : (M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) × (List ℕ × List ℕ) =>
      RC₂ L z.1.1 z.1.2 z.2) := by
  have hl : CompT M (fun z : (M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) ×
      (List ℕ × List ℕ) => z.1.2.2.1.length) :=
    compT_length.comp (compT_fst.comp (compT_snd.comp (compT_snd.comp compT_fst)))
  have hlen1 : CompSet M (fun z : (M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) ×
      (List ℕ × List ℕ) => z.2.1.length = z.1.2.2.1.length) :=
    compSet_eq (compT_length.comp (compT_fst.comp compT_snd)) hl
  have hlen2 : CompSet M (fun z : (M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) ×
      (List ℕ × List ℕ) => z.2.2.length = z.1.2.2.1.length) :=
    compSet_eq (compT_length.comp (compT_snd.comp compT_snd)) hl
  have hball : CompSet M (fun z : (M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) ×
      (List ℕ × List ℕ) =>
      ∀ j, j < z.1.2.2.1.length → ∃ (γ' : L.Sent) (m n k' : ℕ), z.1.2.2.1[j]? = some γ' ∧
        z.1.2.2.2.1[j]? = some m ∧ z.2.1[j]? = some n ∧ z.2.2[j]? = some k' ∧
          (n ≤ m ∨ M.run z.1.1 n k' ≠ some (e M (γ', false)))) :=
    (CompSet.ballLt (P := fun (a : (M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) ×
        (List ℕ × List ℕ)) j =>
      ∃ (γ' : L.Sent) (m n k' : ℕ), a.1.2.2.1[j]? = some γ' ∧ a.1.2.2.2.1[j]? = some m ∧
        a.2.1[j]? = some n ∧ a.2.2[j]? = some k' ∧
          (n ≤ m ∨ M.run a.1.1 n k' ≠ some (e M (γ', false))))
      (compSet_RC₂_nth L)).comp (CompT.pair compT_id hl)
  exact (hlen1.imp (hlen2.imp hball)).congr fun z => Iff.rfl

/-- `R_C` is computable (Proposition 2.4). -/
theorem compSet_RC :
    CompSet M (fun x : M.Code × L.Sent × ℕ × ℕ => RC L x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  -- `∀ r, e r = v → (2)`, as a predicate of `((T, γ, v), q)`
  have hall : CompSet M (fun z : (M.Code × L.Sent × ℕ) × (ℕ × List L.Sent × List ℕ × List ℕ) =>
      ∀ r : List ℕ × List ℕ, e M r = z.1.2.2 → RC₂ L z.1.1 z.2 r) :=
    (CompSet.forall_decode (X := List ℕ × List ℕ)
      (Φ := fun (a : M.Code × (ℕ × List L.Sent × List ℕ × List ℕ)) r => RC₂ L a.1 a.2 r)
      (compSet_RC₂ L)).comp
      (CompT.pair (CompT.pair (compT_fst.comp compT_fst) compT_snd)
        (compT_snd.comp (compT_snd.comp compT_fst)))
  -- condition (1), as a predicate of `((T, γ, v), q)`
  have h1 : CompSet M (fun z : (M.Code × L.Sent × ℕ) × (ℕ × List L.Sent × List ℕ × List ℕ) =>
      RC₁ L z.1.1 z.1.2.1 z.2) :=
    (compSet_RC₁ L).comp (CompT.pair (CompT.pair (compT_fst.comp compT_fst)
      (compT_fst.comp (compT_snd.comp compT_fst))) compT_snd)
  -- decoding `u` as `q`
  have hex := CompSet.exists_decode (X := ℕ × List L.Sent × List ℕ × List ℕ)
    (Φ := fun (a : M.Code × L.Sent × ℕ) q => RC₁ L a.1 a.2.1 q ∧
      ∀ r : List ℕ × List ℕ, e M r = a.2.2 → RC₂ L a.1 q r) (h1.and hall)
  -- `(T, γ, u, v) ↦ ((T, γ, v), u)`
  exact (hex.comp (g := fun x : M.Code × L.Sent × ℕ × ℕ => ((x.1, x.2.1, x.2.2.2), x.2.2.1))
    (CompT.pair (CompT.pair compT_fst (CompT.pair (compT_fst.comp compT_snd)
      (compT_snd.comp (compT_snd.comp compT_snd)))) (compT_fst.comp (compT_snd.comp compT_snd)))).congr
    fun x => Iff.rfl

/-- `S_{R_C} (T) = closure (T^s)`: `∃ u ∀ v, R_C (T, γ, u, v)` iff `γ` is derivable from the
`T`-stable sentences. -/
theorem SR_RC_iff (T : M.Code) (γ : L.Sent) :
    SR (RC L) T γ ↔ L.Deriv (Ts (M := M) L.Sent T) γ := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨⟨p, l, ms, ks⟩, hq, h1, -⟩ := hu 0
    -- `u` determines the decoded tuple, so condition (2) holds for every `r`
    have h2 : ∀ r : List ℕ × List ℕ, RC₂ L T (p, l, ms, ks) r := by
      intro r
      obtain ⟨q', hq', -, h2'⟩ := hu (e M r)
      obtain rfl : q' = (p, l, ms, ks) := Enc.inj (hq'.trans hq.symm)
      exact h2' r rfl
    obtain ⟨-, -, hprf, hrun⟩ := h1
    -- every sentence of `l` is `T`-stable
    have hst : ∀ β, β ∈ l → Ts (M := M) L.Sent T β := by
      intro β hβ
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hβ
      have hjl : j < l.length := (List.getElem?_eq_some_iff.1 hj).1
      obtain ⟨γ', m, k, hγ', hm, -, hr⟩ := hrun j hjl
      obtain rfl : γ' = β := Option.some.inj (hγ'.symm.trans hj)
      refine ⟨m, seqOf_eq_some_iff.2 (TuringModel.eval_eq_some_of_run hr), fun n hn s hs => ?_⟩
      cases s with
      | true => rfl
      | false =>
        exfalso
        obtain ⟨k', hk'⟩ := (M.eval_iff _ _ _).1 (seqOf_eq_some_iff.1 hs)
        -- condition (2) for `r = ((n, …, n), (k', …, k'))` fails at the index `j`
        obtain ⟨γ'', m', n', k'', h1', h2', h3', h4', h5'⟩ :=
          h2 (List.replicate l.length n, List.replicate l.length k') List.length_replicate
            List.length_replicate j hjl
        obtain rfl : γ'' = γ' := Option.some.inj (h1'.symm.trans hγ')
        obtain rfl : m' = m := Option.some.inj (h2'.symm.trans hm)
        obtain rfl : n' = n := Option.some.inj (h3'.symm.trans (List.getElem?_replicate_of_lt hjl))
        obtain rfl : k'' = k' := Option.some.inj (h4'.symm.trans (List.getElem?_replicate_of_lt hjl))
        rcases h5' with h | h
        · exact Nat.not_lt.2 h hn
        · exact h hk'
    exact L.deriv_cut (fun β hβ => L.deriv_of_mem (hst β hβ)) ((L.prf_iff l γ).1 ⟨p, hprf⟩)
  · intro hd
    obtain ⟨l, hl, hld⟩ := L.deriv_compact hd
    obtain ⟨p, hp⟩ := (L.prf_iff l γ).2 hld
    -- for each index `j`: a stage `m` from which `l(j)` is stably `+`, and a step bound `k`
    have hch : ∀ j : ℕ, ∃ mk : ℕ × ℕ, ∀ β, l[j]? = some β →
        M.run T mk.1 mk.2 = some (e M (β, true)) ∧
          ∀ n, mk.1 < n → ∀ s, seqOf (M := M) L.Sent T n = some (β, s) → s = true := by
      intro j
      cases hj : l[j]? with
      | none => exact ⟨(0, 0), fun β hβ => by cases hβ⟩
      | some β =>
        obtain ⟨m, hm, hm'⟩ := hl β (List.mem_of_getElem? hj)
        obtain ⟨k, hk⟩ := (M.eval_iff _ _ _).1 (seqOf_eq_some_iff.1 hm)
        refine ⟨(m, k), fun β' hβ' => ?_⟩
        cases hβ'
        exact ⟨hk, hm'⟩
    have hF := fun j => Classical.choose_spec (hch j)
    refine ⟨e M (p, l, (List.range l.length).map (fun j => (Classical.choose (hch j)).1),
      (List.range l.length).map (fun j => (Classical.choose (hch j)).2)), fun v => ?_⟩
    refine ⟨(p, l, (List.range l.length).map (fun j => (Classical.choose (hch j)).1),
      (List.range l.length).map (fun j => (Classical.choose (hch j)).2)), rfl, ?_, ?_⟩
    · refine ⟨by simp, by simp, hp, fun j hj => ?_⟩
      have hj' : j < l.length := hj
      refine ⟨l[j], (Classical.choose (hch j)).1, (Classical.choose (hch j)).2,
        List.getElem?_eq_getElem hj', ?_, ?_, ((hF j) l[j] (List.getElem?_eq_getElem hj')).1⟩
      · simp [List.getElem?_range hj']
      · simp [List.getElem?_range hj']
    · intro r _ hr1 hr2 j hj
      have hj' : j < l.length := hj
      have hj1 : j < r.1.length := Nat.lt_of_lt_of_eq hj hr1.symm
      have hj2 : j < r.2.length := Nat.lt_of_lt_of_eq hj hr2.symm
      refine ⟨l[j], (Classical.choose (hch j)).1, r.1[j], r.2[j], List.getElem?_eq_getElem hj', ?_,
        List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2, ?_⟩
      · simp [List.getElem?_range hj']
      · by_cases hle : r.1[j] ≤ (Classical.choose (hch j)).1
        · exact Or.inl hle
        · refine Or.inr fun hrun => ?_
          have := ((hF j) l[j] (List.getElem?_eq_getElem hj')).2 r.1[j] (Nat.lt_of_not_le hle)
            false (seqOf_eq_some_iff.2 (TuringModel.eval_eq_some_of_run hrun))
          cases this

/-- Lemma 3.22 (`lemma_closure`): a total computable `C : 𝒯 → 𝒯` with `C T ∈ 𝒯_𝓛`,
`(C T)'` total, and `(C T)^s = closure (T^s)` for every `T`. -/
theorem exists_C : ∃ C : M.Code → M.Code, CompT M C ∧ ∀ T,
    InTB (M := M) L.Sent (C T) ∧ (∀ n, seqOf (M := M) L.Sent (C T) n ≠ none) ∧
    ∀ γ : L.Sent, Ts (M := M) L.Sent (C T) γ ↔ L.Deriv (Ts (M := M) L.Sent T) γ := by
  obtain ⟨C, hC, hC'⟩ := exists_stabMachine (M := M) (B := L.Sent) L.infinite (compSet_RC L)
  refine ⟨C, hC, fun T => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hC' T
  refine ⟨h1, h2, fun γ => ?_⟩
  rw [Ts_def, h3, SR_RC_iff]

end Stable
