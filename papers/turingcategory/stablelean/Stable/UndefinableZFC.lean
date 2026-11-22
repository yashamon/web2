import Stable.Perturb
import Stable.Undefinable
import Stable.Second

/-!
# An undefinable instance of the second incompleteness theorem (Appendix B, Proposition B.10)

We prove, relative to the interface `UndefZData` below: if `ZFC` is arithmetically sound then there
is a translation `i : 𝓩 → 𝓩` with `j := i ∘ i_{𝓐,𝓩}` a `2`-translation, `ZFC ⊢ⁱ ZFC`, `ZFC` `1`- and
`2`-consistent relative to `j`, and `ZFC_{j,𝓐}` not arithmetical (`exists_undefinable_ZFC`). So the
hypotheses of Theorem 5.11 hold for `𝓛 = 𝓩`, `F = ZFC` and this `i`, while the corresponding
arithmetic theory is not arithmetical. More precisely (`undefinableZFC_family`) there is a sequence
of sentences `ε n` of arithmetic, not depending on `X`, such that for every `X ⊂ ℕ` some such
`i = i_X` satisfies `¬ε n ∈ ZFC_{j,𝓐} ↔ n ∈ X`; non-arithmeticity follows by counting.

The proof follows the manuscript, with stages `(n, ψ)` in place of its sentences `E_n`: `ψ` is the
complete conjunction `ψ_ν` of a valuation `ν ∈ V_n`, `E (n, ψ) = ε_n* ∧ ζ ∧ ψ`, and the manuscript's
`b^{(n)}` is `(b^{ι_ν})*` on the models of `E (n, ψ)`. The language-independent part (the maps `θ_K`,
`θ` and the translation) is `Perturb.lean`. Two deviations, both immaterial: `x_n` is the conjunction
of the sentences `PA_r ∧ Con_{τ_ν}`, `ν ∈ V_n`; and `d_n` is the conjunction of sentences `d_ν`,
`ν ∈ V_n`, one for each theory `U⁰_ν`, as in the manuscript.

`UndefZData` collects, as assumptions, the classical facts and the syntax used:

* unique readability of the sentences of `𝓩` (`SentSyntax`), and the computability of the syntactic
  operation replacing each prime constituent `p` of a sentence by `wrap p`;
* the standard interpretation `i_{𝓐,𝓩}` (`star`), a computable translation; the guard `ζ` with the
  list of its prime constituents; a set `P₀` of prime sentences of `𝓩` such that every `a*`, `a ∈ 𝓑`,
  is a Boolean combination of sentences of `P₀`, and each element of `P₀` is some `a*` with `a ∈ 𝓑`,
  or a prime constituent of `ζ`, or a sentence `p` with `η* = ζ → p` or `η* = ζ ∧ p` for some
  `η ∈ 𝓑` (in the manuscript `p = η^ω` for an atomic sentence `η`);
* `ZFC`: a c.e. set of sentences of `𝓩` proving `ζ` and `q*` for each axiom `q` of `Q`;
* a true sentence `PA_r`; `Σ⁰₃`-definable theories in the language `𝓩` (an abstract type `Def3`), with
  the definition `baseDef` of `ZFC ∪ Tr_𝓑*` (built from the partial truth definition `Sat_𝓑` of fact
  (1) and `Σ₁`-completeness), closed under adding finitely many sentences; the arithmetized
  completeness theorem for them (fact (2) for the language `𝓩`);
* fact (3) in the form used: a theory `ZFC ∪ Tr_𝓑* ∪ l`, `l` finite, which proves `d*` only for true
  `Π⁰₃` sentences `d`, does not prove `d*` for every true `Π⁰₃` sentence `d`.

The incompleteness of `ZFC + w*` for true `w`, used in the construction, is derived from the
formalized Theorem 1.5 (`first_incompleteness`) for the translation `i_{𝓐,𝓩}`.
-/

namespace Stable

open Classical UndefData

variable {M : TuringModel}

/-! ### The interface -/

/-- The data and classical facts of Proposition B.10; see the module docstring. -/
structure UndefZData (A : Arith M) (Z : Language M) where
  /-- Unique readability of the sentences of `𝓩`. -/
  syn : SentSyntax Z
  /-- `wrapAll s`: `s` with each prime constituent `p` replaced by `wrap p`. -/
  wrapAll : Z.Sent → Z.Sent
  wrapAll_prime : ∀ p, syn.Prime p → wrapAll p = syn.wrap p
  wrapAll_neg : ∀ a, wrapAll (Z.neg a) = Z.neg (wrapAll a)
  wrapAll_and : ∀ a b, wrapAll (Z.and a b) = Z.and (wrapAll a) (wrapAll b)
  wrapAll_comp : CompT M wrapAll
  /-- The standard interpretation `i_{𝓐,𝓩}` (Example 2.8). -/
  star : Translation A.toLanguage Z
  star_comp : CompT M star.i
  /-- The guard `ζ`. -/
  zeta : Z.Sent
  /-- The prime constituents of `ζ`. -/
  zetaPC : List Z.Sent
  /-- `P₀`. -/
  P0 : Z.Sent → Prop
  P0_prime : ∀ p, P0 p → syn.Prime p
  star_bool : ∀ β, A.InB β → BoolOver Z P0 (star.i β)
  P0_cases : ∀ p, P0 p → (∃ β, A.InB β ∧ p = star.i β) ∨ p ∈ zetaPC ∨
    ∃ η, A.InB η ∧ (star.i η = Z.imp zeta p ∨ star.i η = Z.and zeta p)
  -- `ZFC`
  ZFC : Z.Sent → Prop
  ZFC_ce : ∃ f : ℕ → Z.Sent, CompT M f ∧ ∀ φ, ZFC φ ↔ ∃ k, f k = φ
  ZFC_zeta : Z.Deriv ZFC zeta
  ZFC_Q : ∀ q, A.Q q → Z.Deriv ZFC (star.i q)
  -- arithmetic
  /-- The conjunction of the axioms of a finite fragment of `PA`. -/
  PAr : A.Sent
  PAr_true : A.TrueN PAr
  /-- `Σ⁰₃`-definable theories `τ` in the language `𝓩`; `tau τ β` is the sentence `τ (⌜β⌝)`. -/
  Def3 : Type
  tau : Def3 → Z.Sent → A.Sent
  /-- The sentence `Con_τ`. -/
  con : Def3 → A.Sent
  con_true : ∀ τ, Z.Consistent (fun β => A.TrueN (tau τ β)) → A.TrueN (con τ)
  /-- The definition of `ZFC ∪ Tr_𝓑*`. -/
  baseDef : Def3
  base_ax : ∀ φ, ZFC φ → A.Deriv (A.single PAr) (tau baseDef φ)
  base_sat : ∀ β, A.InB β → A.Deriv (A.single PAr) (A.imp β (tau baseDef (star.i β)))
  base_true : ∀ γ, A.TrueN (tau baseDef γ) → ZFC γ ∨ ∃ β, A.TrB β ∧ γ = star.i β
  /-- `τ ∨ "v ∈ l"`. -/
  addFin : Def3 → List Z.Sent → Def3
  addFin_mem : ∀ τ l β, β ∈ l → A.Deriv (A.single PAr) (tau (addFin τ l) β)
  addFin_of : ∀ τ l β, A.Deriv (A.single (tau τ β)) (tau (addFin τ l) β)
  addFin_true : ∀ τ l β, A.TrueN (tau (addFin τ l) β) → A.TrueN (tau τ β) ∨ β ∈ l
  /-- Fact (2) for the language `𝓩`: for `x_τ := PA_r ∧ Con_τ` there is an interpretation `β ↦ β^ι` of
  `𝓩` in `𝓐` commuting with the connectives, with `S ⊢ β` implying `{x_τ} ∪ S^ι ⊢ β^ι`, and
  `{x_τ} ⊢ τ (⌜β⌝) → β^ι` for every `β`. -/
  act : ∀ τ, ∃ tr : Z.Sent → A.Sent,
    (∀ a, tr (Z.neg a) = A.neg (tr a)) ∧ (∀ a b, tr (Z.and a b) = A.and (tr a) (tr b)) ∧
    (∀ (S : Z.Sent → Prop) β, Z.Deriv S β →
      A.Deriv (fun γ => γ = A.and PAr (con τ) ∨ ∃ δ, S δ ∧ γ = tr δ) (tr β)) ∧
    (∀ β, A.Deriv (A.single (A.and PAr (con τ))) (A.imp (tau τ β) (tr β)))
  /-- Fact (3) in the form used. -/
  pi3_indep : ∀ l : List Z.Sent,
    (∀ d, A.IsPi 3 d →
      Z.Deriv (fun γ => ZFC γ ∨ (∃ β, A.TrB β ∧ γ = star.i β) ∨ γ ∈ l) (star.i d) → A.TrueN d) →
    ∃ d, A.IsPi 3 d ∧ A.TrueN d ∧
      ¬ Z.Deriv (fun γ => ZFC γ ∨ (∃ β, A.TrB β ∧ γ = star.i β) ∨ γ ∈ l) (star.i d)

/-- `UndefZData` together with the hypothesis of Proposition B.10: `ZFC` is arithmetically sound. -/
structure UndefZSound (A : Arith M) (Z : Language M) extends UndefZData A Z where
  sound : ∀ a, Z.Deriv ZFC (star.i a) → A.TrueN a

/-! ### Enumerations with a prepended sentence -/

/-- The sequence `w, f 0, f 1, …`, never withdrawing. -/
noncomputable def seqPre {B : Type} (f : ℕ → B) (w : B) (k : ℕ) : Option (B × Bool) :=
  some (if k = 0 then w else f (k - 1), true)

theorem comp_seqPre {B : Type} [Enc M B] {f : ℕ → B} (hf : CompT M f) (w : B) : Comp M (seqPre f w) := by
  have h1 : CompT M (fun k : ℕ => if k = 0 then w else f (k - 1)) := by
    have := CompT.cases (M := M) (P := fun k : ℕ => k = 0) (f := fun _ => w) (g := fun k => f (k - 1))
      (compSet_eq compT_id (compT_const 0)) (compT_const w) (hf.comp compT_pred)
    exact this.congr fun k => by by_cases h : k = 0 <;> simp [h]
  exact (CompT.pair h1 (compT_const true)).toComp

theorem stab_seqPre {B : Type} (f : ℕ → B) (w β : B) :
    Stab (seqPre f w) β ↔ (∃ k, f k = β) ∨ β = w := by
  show IsStable (seqPre f w) β ↔ _
  rw [isStable_of_all_true (fun k x hx => by
    simp only [seqPre, Option.some.injEq] at hx
    rw [← hx])]
  constructor
  · rintro ⟨k, hk⟩
    simp only [seqPre, Option.some.injEq, Prod.mk.injEq] at hk
    by_cases h : k = 0
    · rw [ite_eq_left h] at hk; exact Or.inr hk.1.symm
    · rw [ite_eq_right h] at hk; exact Or.inl ⟨k - 1, hk.1⟩
  · rintro (⟨k, hk⟩ | hβ)
    · exact ⟨k + 1, by simp [seqPre, hk]⟩
    · exact ⟨0, by simp [seqPre, hβ]⟩

namespace UndefZSound

variable {A : Arith M} {Z : Language M} (D : UndefZSound A Z)

/-! ### Basic consequences -/

/-- `ZFC ∪ Tr_𝓐* ∪ {ψ}`. -/
def U (ψ : Z.Sent) : Z.Sent → Prop :=
  fun γ => D.ZFC γ ∨ (∃ a, A.TrueN a ∧ γ = D.star.i a) ∨ γ = ψ

/-- `ZFC ∪ Tr_𝓑* ∪ l`. -/
def U0 (l : List Z.Sent) : Z.Sent → Prop :=
  fun γ => D.ZFC γ ∨ (∃ β, A.TrB β ∧ γ = D.star.i β) ∨ γ ∈ l

/-- A logically valid sentence of `𝓩`. -/
noncomputable def zt : Z.Sent := Z.topOf (D.star.i (a0 A))

theorem star_top : D.star.i (top A) = D.zt := D.star.map_topOf (a0 A)

/-- `i_{𝓐,𝓩}` is a `2`-translation. -/
theorem star_isN2 : D.star.IsNTranslation 2 := by
  obtain ⟨T, hT⟩ := D.star_comp
  exact ⟨T, fun σ => hT σ.1⟩

/-- A consistent theory `ZFC ∪ Tr_𝓐* ∪ {ψ}` proves `a*` only for true `a`. -/
theorem trueN_of_deriv_U {ψ : Z.Sent} (hc : Z.Consistent (D.U ψ)) {a : A.Sent}
    (h : Z.Deriv (D.U ψ) (D.star.i a)) : A.TrueN a := by
  refine Classical.byContradiction fun ha => hc.elim fun c hcn => hcn ?_
  have h1 : Z.Deriv (D.U ψ) (D.star.i (A.neg a)) :=
    Z.deriv_of_mem (Or.inr (Or.inl ⟨A.neg a, (A.trueN_neg a).2 ha, rfl⟩))
  rw [D.star.map_neg] at h1
  exact Z.deriv_explosion h h1

/-- `ZFC + w*` is incomplete for true `w`: for some true `c`, `ZFC + w* ⊬ c*`. This is Theorem 1.5
(3) and (1) for the translation `i_{𝓐,𝓩}` and a machine enumerating `ZFC + w*`. -/
theorem exists_true_not_deriv {w : A.Sent} (hw : A.TrueN w) :
    ∃ c, A.TrueN c ∧ ¬ Z.Deriv (Z.ext D.ZFC (D.star.i w)) (D.star.i c) := by
  obtain ⟨f, hfc, hf⟩ := D.ZFC_ce
  obtain ⟨G, _, hG⟩ := first_incompleteness D.star D.star_isN2
  obtain ⟨T, hT⟩ := comp_seqPre hfc (D.star.i w)
  have hTN : StablyComputes (M := M) T (seqPre f (D.star.i w)) := stablyComputes_of_computes hT
  have hStab : ∀ β, Stab (seqPre f (D.star.i w)) β ↔ Z.ext D.ZFC (D.star.i w) β := fun β => by
    rw [stab_seqPre]
    exact ⟨fun h => h.elim (fun hk => Or.inl ((hf β).2 hk)) Or.inr,
      fun h => h.elim (fun hk => Or.inl ((hf β).1 hk)) Or.inr⟩
  have hsound : ∀ a, Z.Deriv (Stab (seqPre f (D.star.i w))) (D.star.i a) → A.TrueN a := by
    intro a h
    have h1 : Z.Deriv (Z.ext D.ZFC (D.star.i w)) (D.star.i a) :=
      Z.deriv_mono (fun β hβ => (hStab β).1 hβ) h
    have h2 : Z.Deriv D.ZFC (D.star.i (A.imp w a)) := by
      rw [D.star.map_imp]; exact Language.deriv_imp_intro h1
    exact trueN_imp.1 (D.sound _ h2) hw
  have hone : D.star.OneConsistent (Stab (seqPre f (D.star.i w))) := by
    refine ⟨fun q hq => ?_, fun σ hσ hd => ?_⟩
    · rw [Translation.derivI_iff]
      exact Z.deriv_mono (fun β hβ => (hStab β).2 (Or.inl hβ)) (D.ZFC_Q q hq)
    · rw [Translation.derivI_iff] at hd
      obtain ⟨v, hv⟩ := (A.trueN_sigma 0 σ hσ).1 (hsound σ hd)
      refine ⟨v, fun h => ?_⟩
      rw [Translation.derivI_iff] at h
      exact (A.trueN_neg _).1 (hsound _ h) hv
  obtain ⟨h1, _, h3⟩ := hG T _ hTN
  refine ⟨G T, h3 hone, fun h => h1 hone ?_⟩
  rw [Translation.derivI_iff]
  exact Z.deriv_mono (fun β hβ => (hStab β).2 hβ) h

/-! ### Valuations of `Γ_n` -/

/-- `Γ_n`: the sentences of `𝓩` with code `≤ n`, and the prime constituents of `ζ`. -/
noncomputable def Gam (n : ℕ) : List Z.Sent := Z.firstN n ++ D.zetaPC

/-- The complete conjunctions `ψ_ν` of the valuations `ν` of `Γ_n`. -/
noncomputable def allV (n : ℕ) : List Z.Sent := Z.vals D.zt (D.Gam n)

/-- `V_n`: those consistent with `ZFC ∪ Tr_𝓐*`. -/
noncomputable def Vl (n : ℕ) : List Z.Sent :=
  (D.allV n).filter (fun ψ => decide (Z.Consistent (D.U ψ)))

/-- The valuations not in `V_n`. -/
noncomputable def Vbad (n : ℕ) : List Z.Sent :=
  (D.allV n).filter (fun ψ => decide (¬ Z.Consistent (D.U ψ)))

theorem mem_Vl {n : ℕ} {ψ : Z.Sent} : ψ ∈ D.Vl n ↔ ψ ∈ D.allV n ∧ Z.Consistent (D.U ψ) := by
  unfold Vl
  rw [List.mem_filter, decide_eq_true_iff]

theorem mem_Vbad {n : ℕ} {ψ : Z.Sent} : ψ ∈ D.Vbad n ↔ ψ ∈ D.allV n ∧ ¬ Z.Consistent (D.U ψ) := by
  unfold Vbad
  rw [List.mem_filter, decide_eq_true_iff]

theorem mem_Vl_or_Vbad {n : ℕ} {ψ : Z.Sent} (h : ψ ∈ D.allV n) : ψ ∈ D.Vl n ∨ ψ ∈ D.Vbad n := by
  by_cases hc : Z.Consistent (D.U ψ)
  · exact Or.inl (D.mem_Vl.2 ⟨h, hc⟩)
  · exact Or.inr (D.mem_Vbad.2 ⟨h, hc⟩)

/-- Finitely many sentences of `ZFC ∪ Tr_𝓐* ∪ {ψ}` follow from `ZFC ∪ {a*, ψ}` for one true `a`. -/
theorem exists_true_cover (ψ : Z.Sent) : ∀ l : List Z.Sent, (∀ γ, γ ∈ l → D.U ψ γ) →
    ∃ a, A.TrueN a ∧ ∀ γ, γ ∈ l → Z.Deriv (Z.ext (Z.ext D.ZFC (D.star.i a)) ψ) γ
  | [], _ => ⟨top A, trueN_top, fun γ hγ => by cases hγ⟩
  | γ₀ :: l, hl => by
    obtain ⟨a', ha', hd'⟩ := exists_true_cover ψ l fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)
    rcases hl γ₀ (List.mem_cons_self) with h0 | ⟨a₁, ha₁, rfl⟩ | h0
    · refine ⟨a', ha', fun γ hγ => ?_⟩
      rw [List.mem_cons] at hγ
      rcases hγ with rfl | hγ
      · exact Z.deriv_of_mem (Or.inl (Or.inl h0))
      · exact hd' γ hγ
    · refine ⟨A.and a₁ a', (A.trueN_and _ _).2 ⟨ha₁, ha'⟩, fun γ hγ => ?_⟩
      have hboth : Z.Deriv (Z.ext (Z.ext D.ZFC (D.star.i (A.and a₁ a'))) ψ)
          (Z.and (D.star.i a₁) (D.star.i a')) := by
        rw [← D.star.map_and]
        exact Language.deriv_ext_of _ (Language.deriv_ext_self _ _)
      rw [List.mem_cons] at hγ
      rcases hγ with rfl | hγ
      · exact Z.deriv_and_left hboth
      · refine Z.deriv_cut (fun β hβ => ?_) (hd' γ hγ)
        rcases hβ with (hβ | hβ) | hβ
        · exact Z.deriv_of_mem (Or.inl (Or.inl hβ))
        · rw [hβ]; exact Z.deriv_and_right hboth
        · exact Z.deriv_of_mem (Or.inr hβ)
    · refine ⟨a', ha', fun γ hγ => ?_⟩
      rw [List.mem_cons] at hγ
      rcases hγ with rfl | hγ
      · rw [h0]; exact Language.deriv_ext_self _ _
      · exact hd' γ hγ

/-- A valuation not in `V_n` is refuted by `ZFC` and one true sentence of arithmetic. -/
theorem exists_true_refuting {ψ : Z.Sent} (h : ¬ Z.Consistent (D.U ψ)) :
    ∃ a, A.TrueN a ∧ Z.Deriv (Z.ext D.ZFC (D.star.i a)) (Z.neg ψ) := by
  obtain ⟨l, hl, hd⟩ := Z.deriv_compact ((Z.not_consistent_iff _).1 h (Z.neg ψ))
  obtain ⟨a, ha, hcov⟩ := D.exists_true_cover ψ l hl
  refine ⟨a, ha, ?_⟩
  have h1 : Z.Deriv (Z.ext (Z.ext D.ZFC (D.star.i a)) ψ) (Z.neg ψ) :=
    Z.deriv_cut (fun β hβ => hcov β hβ) hd
  exact Language.deriv_neg_of (Language.deriv_ext_self _ ψ) h1

/-- `a_ν`, for `ν ∉ V_n`. -/
noncomputable def aBad (ψ : Z.Sent) : A.Sent :=
  pick A fun a => A.TrueN a ∧ Z.Deriv (Z.ext D.ZFC (D.star.i a)) (Z.neg ψ)

theorem aBad_spec {ψ : Z.Sent} (h : ¬ Z.Consistent (D.U ψ)) :
    A.TrueN (D.aBad ψ) ∧ Z.Deriv (Z.ext D.ZFC (D.star.i (D.aBad ψ))) (Z.neg ψ) :=
  pick_spec (D.exists_true_refuting h)

end UndefZSound

/-! ### The construction: levels `(d_n, ε_n)` -/

/-- The data produced at level `n`. -/
structure LStage (A : Arith M) where
  d : A.Sent
  eps : A.Sent

namespace UndefZSound

variable {A : Arith M} {Z : Language M} (D : UndefZSound A Z)

/-- `¬ε_m*` for the earlier levels `m`. -/
noncomputable def lTp (prev : List (LStage A)) : List Z.Sent :=
  prev.map (fun st => Z.neg (D.star.i st.eps))

/-- `d_ν`: a true `Π⁰₃` sentence with `U⁰_ν ⊬ d_ν*`. -/
noncomputable def dPsi (prev : List (LStage A)) (ψ : Z.Sent) : A.Sent :=
  pick A fun d => A.IsPi 3 d ∧ A.TrueN d ∧ ¬ Z.Deriv (D.U0 (ψ :: D.lTp prev)) (D.star.i d)

/-- `d_n := ⋀_{ν ∈ V_n} d_ν`. -/
noncomputable def dNp (n : ℕ) (prev : List (LStage A)) : A.Sent :=
  A.conjList (top A) ((D.Vl n).map (D.dPsi prev))

/-- `τ_ν`, defining `U_ν = U⁰_ν ∪ {¬d_n*}`. -/
noncomputable def tauP (n : ℕ) (prev : List (LStage A)) (ψ : Z.Sent) : D.Def3 :=
  D.addFin D.baseDef (ψ :: (D.lTp prev ++ [Z.neg (D.star.i (D.dNp n prev))]))

/-- `PA_r ∧ Con_{τ_ν}`. -/
noncomputable def xP (n : ℕ) (prev : List (LStage A)) (ψ : Z.Sent) : A.Sent :=
  A.and D.PAr (D.con (D.tauP n prev ψ))

/-- `x_n`. -/
noncomputable def xNp (n : ℕ) (prev : List (LStage A)) : A.Sent :=
  A.conjList (top A) ((D.Vl n).map (D.xP n prev))

/-- `w_n`. -/
noncomputable def wNp (n : ℕ) (prev : List (LStage A)) : A.Sent :=
  A.conjList (top A) (D.xNp n prev :: ((D.Vbad n).map D.aBad ++
    prev.map (fun st => A.neg st.eps) ++ prev.map LStage.d ++ [D.dNp n prev]))

/-- The true sentence `c_n` with `ZFC + w_n* ⊬ c_n*`. -/
noncomputable def cNp (n : ℕ) (prev : List (LStage A)) : A.Sent :=
  pick A fun c => A.TrueN c ∧ ¬ Z.Deriv (Z.ext D.ZFC (D.star.i (D.wNp n prev))) (D.star.i c)

/-- Level `n`, given the earlier levels. -/
noncomputable def step (n : ℕ) (prev : List (LStage A)) : LStage A where
  d := D.dNp n prev
  eps := A.and (D.wNp n prev) (A.neg (D.cNp n prev))

/-- The levels `0, …, n - 1`. -/
noncomputable def stages : ℕ → List (LStage A)
  | 0 => []
  | n + 1 => stages n ++ [D.step n (stages n)]

/-- Level `n`. -/
noncomputable def stage (n : ℕ) : LStage A := D.step n (D.stages n)

theorem stages_eq (n : ℕ) : D.stages n = (List.range n).map D.stage := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show D.stages n ++ [D.stage n] = _
    rw [ih, List.range_succ, List.map_append]
    rfl

/-- Abbreviations. -/
noncomputable def dN (n : ℕ) : A.Sent := (D.stage n).d
noncomputable def epsN (n : ℕ) : A.Sent := (D.stage n).eps
noncomputable def lT (n : ℕ) : List Z.Sent := D.lTp (D.stages n)
noncomputable def tauN (n : ℕ) (ψ : Z.Sent) : D.Def3 := D.tauP n (D.stages n) ψ
noncomputable def xPsi (n : ℕ) (ψ : Z.Sent) : A.Sent := D.xP n (D.stages n) ψ
noncomputable def xN (n : ℕ) : A.Sent := D.xNp n (D.stages n)
noncomputable def wN (n : ℕ) : A.Sent := D.wNp n (D.stages n)
noncomputable def cN (n : ℕ) : A.Sent := D.cNp n (D.stages n)
/-- `ι_ν` on sentences. -/
noncomputable def trN (n : ℕ) (ψ : Z.Sent) : Z.Sent → A.Sent := choose (D.act (D.tauN n ψ))

theorem dN_eq (n : ℕ) : D.dN n = A.conjList (top A) ((D.Vl n).map (D.dPsi (D.stages n))) := rfl
theorem epsN_eq (n : ℕ) : D.epsN n = A.and (D.wN n) (A.neg (D.cN n)) := rfl
theorem xPsi_eq (n : ℕ) (ψ : Z.Sent) : D.xPsi n ψ = A.and D.PAr (D.con (D.tauN n ψ)) := rfl
theorem xN_eq (n : ℕ) : D.xN n = A.conjList (top A) ((D.Vl n).map (D.xPsi n)) := rfl
theorem tauN_eq (n : ℕ) (ψ : Z.Sent) :
    D.tauN n ψ = D.addFin D.baseDef (ψ :: (D.lT n ++ [Z.neg (D.star.i (D.dN n))])) := rfl

theorem lT_eq (n : ℕ) : D.lT n = (List.range n).map (fun m => Z.neg (D.star.i (D.epsN m))) := by
  show (D.stages n).map (fun st => Z.neg (D.star.i st.eps)) = _
  rw [stages_eq, List.map_map]; rfl

theorem mem_lT {n : ℕ} {b : Z.Sent} : b ∈ D.lT n ↔ ∃ m, m < n ∧ b = Z.neg (D.star.i (D.epsN m)) := by
  rw [lT_eq, List.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, List.mem_range.1 hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, List.mem_range.2 hm, rfl⟩

theorem wN_eq (n : ℕ) :
    D.wN n = A.conjList (top A) (D.xN n :: ((D.Vbad n).map D.aBad ++
      (List.range n).map (fun m => A.neg (D.epsN m)) ++ (List.range n).map D.dN ++ [D.dN n])) := by
  show A.conjList (top A) (D.xN n :: ((D.Vbad n).map D.aBad ++
    (D.stages n).map (fun st => A.neg st.eps) ++ (D.stages n).map LStage.d ++ [D.dN n])) = _
  rw [stages_eq, List.map_map, List.map_map]; rfl

/-- The specification of `ι_ν` (fact (2)). -/
theorem trN_spec (n : ℕ) (ψ : Z.Sent) :
    (∀ a, D.trN n ψ (Z.neg a) = A.neg (D.trN n ψ a)) ∧
    (∀ a b, D.trN n ψ (Z.and a b) = A.and (D.trN n ψ a) (D.trN n ψ b)) ∧
    (∀ (S : Z.Sent → Prop) β, Z.Deriv S β →
      A.Deriv (fun γ => γ = D.xPsi n ψ ∨ ∃ δ, S δ ∧ γ = D.trN n ψ δ) (D.trN n ψ β)) ∧
    (∀ β, A.Deriv (A.single (D.xPsi n ψ)) (A.imp (D.tau (D.tauN n ψ) β) (D.trN n ψ β))) :=
  choose_spec (D.act (D.tauN n ψ))

theorem trN_neg (n : ℕ) (ψ a : Z.Sent) : D.trN n ψ (Z.neg a) = A.neg (D.trN n ψ a) :=
  (D.trN_spec n ψ).1 a

theorem trN_and (n : ℕ) (ψ a b : Z.Sent) :
    D.trN n ψ (Z.and a b) = A.and (D.trN n ψ a) (D.trN n ψ b) := (D.trN_spec n ψ).2.1 a b

/-! ### The interpretations `ι_ν` -/

theorem xPsi_deriv_PAr (n : ℕ) (ψ : Z.Sent) : A.Deriv (A.single (D.xPsi n ψ)) D.PAr :=
  A.deriv_and_left (Language.deriv_single_self (D.xPsi n ψ))

/-- `⊢ b` gives `{x_ν} ⊢ b^{ι_ν}`. -/
theorem x_deriv_tr_of_valid (n : ℕ) (ψ : Z.Sent) {b : Z.Sent} (h : Z.Valid b) :
    A.Deriv (A.single (D.xPsi n ψ)) (D.trN n ψ b) := by
  have := (D.trN_spec n ψ).2.2.1 _ b h
  refine A.deriv_mono (fun γ hγ => ?_) this
  rcases hγ with hγ | ⟨δ, hδ, _⟩
  · exact hγ
  · exact hδ.elim

/-- `{a} ⊢ b` gives `{x_ν} ⊢ a^{ι_ν} → b^{ι_ν}`. -/
theorem x_deriv_tr_imp (n : ℕ) (ψ : Z.Sent) {a b : Z.Sent} (h : Z.Deriv (Z.single a) b) :
    A.Deriv (A.single (D.xPsi n ψ)) (A.imp (D.trN n ψ a) (D.trN n ψ b)) := by
  have := (D.trN_spec n ψ).2.2.1 _ b h
  refine Language.deriv_imp_intro (A.deriv_mono (fun γ hγ => ?_) this)
  rcases hγ with hγ | ⟨δ, hδ, hγ⟩
  · exact Or.inl hγ
  · exact Or.inr (by rw [hγ, show δ = a from hδ])

/-- `{x_ν} ⊢ β^{ι_ν}` for `β` in the finite part of `U_ν`. -/
theorem x_deriv_tr_of_mem (n : ℕ) (ψ : Z.Sent) {β : Z.Sent}
    (h : β ∈ ψ :: (D.lT n ++ [Z.neg (D.star.i (D.dN n))])) :
    A.Deriv (A.single (D.xPsi n ψ)) (D.trN n ψ β) := by
  have h2 : A.Deriv (A.single (D.xPsi n ψ)) (D.tau (D.tauN n ψ) β) :=
    Language.deriv_of_single (D.xPsi_deriv_PAr n ψ) (D.addFin_mem _ _ β h)
  exact Language.deriv_mp ((D.trN_spec n ψ).2.2.2 β) h2

/-- `{x_ν} ⊢ φ^{ι_ν}` for the axioms `φ` of `ZFC`. -/
theorem x_deriv_tr_of_ZFC (n : ℕ) (ψ : Z.Sent) {φ : Z.Sent} (h : D.ZFC φ) :
    A.Deriv (A.single (D.xPsi n ψ)) (D.trN n ψ φ) := by
  have h2 : A.Deriv (A.single (D.xPsi n ψ)) (D.tau (D.tauN n ψ) φ) :=
    Language.deriv_of_single (Language.deriv_of_single (D.xPsi_deriv_PAr n ψ) (D.base_ax φ h))
      (D.addFin_of _ _ φ)
  exact Language.deriv_mp ((D.trN_spec n ψ).2.2.2 φ) h2

/-- `ZFC ⊢ b` gives `{x_ν} ⊢ b^{ι_ν}`: the structure defined by `ι_ν` is a model of `ZFC`. -/
theorem x_deriv_tr_of_deriv_ZFC (n : ℕ) (ψ : Z.Sent) {b : Z.Sent} (h : Z.Deriv D.ZFC b) :
    A.Deriv (A.single (D.xPsi n ψ)) (D.trN n ψ b) := by
  refine A.deriv_cut (fun γ hγ => ?_) ((D.trN_spec n ψ).2.2.1 _ b h)
  rcases hγ with hγ | ⟨δ, hδ, hγ⟩
  · rw [hγ]; exact Language.deriv_single_self _
  · rw [hγ]; exact D.x_deriv_tr_of_ZFC n ψ hδ

/-- `{x_ν} ⊢ β → (β*)^{ι_ν}` for `β ∈ 𝓑`. -/
theorem x_deriv_imp_tr_star (n : ℕ) (ψ : Z.Sent) {β : A.Sent} (hβ : A.InB β) :
    A.Deriv (A.single (D.xPsi n ψ)) (A.imp β (D.trN n ψ (D.star.i β))) := by
  have t1 : A.Deriv (A.single (D.xPsi n ψ)) (A.imp β (D.tau D.baseDef (D.star.i β))) :=
    Language.deriv_of_single (D.xPsi_deriv_PAr n ψ) (D.base_sat β hβ)
  have t2 : A.Deriv (A.single (D.xPsi n ψ))
      (A.imp (D.tau D.baseDef (D.star.i β)) (D.tau (D.tauN n ψ) (D.star.i β))) :=
    Language.deriv_imp_intro (Language.deriv_ext_of_single (D.addFin_of D.baseDef _ _))
  exact Language.deriv_imp_trans t1 (Language.deriv_imp_trans t2 ((D.trN_spec n ψ).2.2.2 _))

/-! ### What `ε_n` proves -/

theorem eps_deriv_wN (n : ℕ) : A.Deriv (A.single (D.epsN n)) (D.wN n) :=
  A.deriv_and_left (Language.deriv_single_self (D.epsN n))

theorem eps_deriv_conj (n : ℕ) {c : A.Sent}
    (hc : c ∈ D.xN n :: ((D.Vbad n).map D.aBad ++
      (List.range n).map (fun m => A.neg (D.epsN m)) ++ (List.range n).map D.dN ++ [D.dN n])) :
    A.Deriv (A.single (D.epsN n)) c := by
  have h := D.eps_deriv_wN n
  rw [wN_eq] at h
  exact Language.deriv_conjList_of_mem h hc

theorem eps_deriv_xPsi (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) :
    A.Deriv (A.single (D.epsN n)) (D.xPsi n ψ) := by
  have h1 : A.Deriv (A.single (D.epsN n)) (D.xN n) := D.eps_deriv_conj n (List.Mem.head _)
  rw [xN_eq] at h1
  exact Language.deriv_conjList_of_mem h1 (List.mem_map.2 ⟨ψ, hψ, rfl⟩)

theorem eps_deriv_aBad (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vbad n) :
    A.Deriv (A.single (D.epsN n)) (D.aBad ψ) :=
  D.eps_deriv_conj n (List.Mem.tail _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
    (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨ψ, hψ, rfl⟩))))))))

theorem eps_deriv_neg_eps_lt (n : ℕ) {m : ℕ} (hm : m < n) :
    A.Deriv (A.single (D.epsN n)) (A.neg (D.epsN m)) :=
  D.eps_deriv_conj n (List.Mem.tail _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
    (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩))))))))

theorem eps_deriv_d_lt (n : ℕ) {m : ℕ} (hm : m < n) : A.Deriv (A.single (D.epsN n)) (D.dN m) :=
  D.eps_deriv_conj n (List.Mem.tail _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
    (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩))))))

theorem eps_deriv_d (n : ℕ) : A.Deriv (A.single (D.epsN n)) (D.dN n) :=
  D.eps_deriv_conj n (List.Mem.tail _ (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))))

/-- The `ε_n` are pairwise inconsistent. -/
theorem eps_deriv_neg_eps (n : ℕ) {m : ℕ} (hm : m ≠ n) :
    A.Deriv (A.single (D.epsN n)) (A.neg (D.epsN m)) := by
  rcases Nat.lt_or_gt_of_ne hm with h | h
  · exact D.eps_deriv_neg_eps_lt n h
  · have := D.eps_deriv_neg_eps_lt m h
    exact Language.deriv_neg_of (Language.deriv_ext_of _ (Language.deriv_single_self _))
      (Language.deriv_ext_of_single this)

/-! ### The invariant of the construction -/

/-- The invariant at level `n`: `d_n` is true and `U⁰_ν ⊬ d_n*` for `ν ∈ V_n`; `x_n`, `w_n`, `c_n` are
true; `ZFC + w_n* ⊬ c_n*`; and `ε_n` is false. -/
def Good (n : ℕ) : Prop :=
  A.TrueN (D.dN n) ∧ (∀ ψ, ψ ∈ D.Vl n → ¬ Z.Deriv (D.U0 (ψ :: D.lT n)) (D.star.i (D.dN n))) ∧
    A.TrueN (D.xN n) ∧ A.TrueN (D.wN n) ∧ A.TrueN (D.cN n) ∧
    ¬ Z.Deriv (Z.ext D.ZFC (D.star.i (D.wN n))) (D.star.i (D.cN n)) ∧ ¬ A.TrueN (D.epsN n)

/-- `U⁰_ν ⊆ ZFC ∪ Tr_𝓐* ∪ {ψ_ν}`. -/
theorem U0_sub_U (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (D.epsN m)) (ψ : Z.Sent) :
    ∀ γ, D.U0 (ψ :: D.lT n) γ → D.U ψ γ := by
  intro γ hγ
  rcases hγ with h | ⟨β, hβ, rfl⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨β, hβ.2, rfl⟩)
  · rw [List.mem_cons] at h
    rcases h with h | h
    · exact Or.inr (Or.inr h)
    · obtain ⟨m, hm, rfl⟩ := D.mem_lT.1 h
      exact Or.inr (Or.inl ⟨A.neg (D.epsN m), (A.trueN_neg _).2 (ih m hm), (D.star.map_neg _).symm⟩)

theorem dPsi_spec (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (D.epsN m)) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) :
    A.IsPi 3 (D.dPsi (D.stages n) ψ) ∧ A.TrueN (D.dPsi (D.stages n) ψ) ∧
      ¬ Z.Deriv (D.U0 (ψ :: D.lT n)) (D.star.i (D.dPsi (D.stages n) ψ)) := by
  refine pick_spec (D.pi3_indep (ψ :: D.lT n) fun d _ hd => ?_)
  exact D.trueN_of_deriv_U (D.mem_Vl.1 hψ).2 (Z.deriv_mono (D.U0_sub_U n ih ψ) hd)

theorem dN_spec (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (D.epsN m)) :
    A.TrueN (D.dN n) ∧ ∀ ψ, ψ ∈ D.Vl n → ¬ Z.Deriv (D.U0 (ψ :: D.lT n)) (D.star.i (D.dN n)) := by
  constructor
  · rw [dN_eq, trueN_conjList]
    refine ⟨trueN_top, fun a ha => ?_⟩
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 ha
    exact (D.dPsi_spec n ih hψ).2.1
  · intro ψ hψ h
    rw [dN_eq, D.star.map_conjList] at h
    exact (D.dPsi_spec n ih hψ).2.2 (Language.deriv_conjList_of_mem h
      (List.mem_map.2 ⟨_, List.mem_map.2 ⟨ψ, hψ, rfl⟩, rfl⟩))

/-- `U_ν` is consistent. -/
theorem consistent_U (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (D.epsN m)) {ψ : Z.Sent}
    (hψ : ψ ∈ D.Vl n) : Z.Consistent (fun β => A.TrueN (D.tau (D.tauN n ψ) β)) := by
  refine ⟨D.star.i (D.dN n), fun h => ?_⟩
  have hsub : ∀ β, A.TrueN (D.tau (D.tauN n ψ) β) →
      Z.ext (D.U0 (ψ :: D.lT n)) (Z.neg (D.star.i (D.dN n))) β := by
    intro β hβ
    rw [tauN_eq] at hβ
    rcases D.addFin_true _ _ β hβ with h1 | h1
    · rcases D.base_true β h1 with h2 | ⟨β', hβ', rfl⟩
      · exact Or.inl (Or.inl h2)
      · exact Or.inl (Or.inr (Or.inl ⟨β', hβ', rfl⟩))
    · rw [List.mem_cons, List.mem_append, List.mem_singleton] at h1
      rcases h1 with h1 | h1 | h1
      · exact Or.inl (Or.inr (Or.inr (by rw [h1]; exact List.mem_cons_self)))
      · exact Or.inl (Or.inr (Or.inr (List.mem_cons_of_mem _ h1)))
      · exact Or.inr h1
  have h2 : Z.Deriv (Z.ext (D.U0 (ψ :: D.lT n)) (Z.neg (D.star.i (D.dN n)))) (D.star.i (D.dN n)) :=
    Z.deriv_mono hsub h
  have h3 : Z.Deriv (D.U0 (ψ :: D.lT n)) (D.star.i (D.dN n)) :=
    Z.deriv_dne (Language.deriv_neg_of h2 (Language.deriv_ext_self _ _))
  exact (D.dN_spec n ih).2 ψ hψ h3

theorem trueN_xN_of (n : ℕ) (ih : ∀ m, m < n → ¬ A.TrueN (D.epsN m)) : A.TrueN (D.xN n) := by
  rw [xN_eq, trueN_conjList]
  refine ⟨trueN_top, fun a ha => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 ha
  rw [xPsi_eq, A.trueN_and]
  exact ⟨D.PAr_true, D.con_true _ (D.consistent_U n ih hψ)⟩

theorem trueN_wN_of (n : ℕ) (ih : ∀ m, m < n → D.Good m) : A.TrueN (D.wN n) := by
  have ihe : ∀ m, m < n → ¬ A.TrueN (D.epsN m) := fun m hm => (ih m hm).2.2.2.2.2.2
  rw [wN_eq, trueN_conjList]
  refine ⟨trueN_top, fun a ha => ?_⟩
  rw [List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact D.trueN_xN_of n ihe
  · rw [List.mem_append, List.mem_append, List.mem_append, List.mem_singleton] at ha
    rcases ha with ((ha | ha) | ha) | ha
    · obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 ha
      exact (D.aBad_spec (D.mem_Vbad.1 hψ).2).1
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
      exact (A.trueN_neg _).2 (ihe m (List.mem_range.1 hm))
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
      exact (ih m (List.mem_range.1 hm)).1
    · rw [ha]; exact (D.dN_spec n ihe).1

theorem cN_spec (n : ℕ) (hw : A.TrueN (D.wN n)) :
    A.TrueN (D.cN n) ∧ ¬ Z.Deriv (Z.ext D.ZFC (D.star.i (D.wN n))) (D.star.i (D.cN n)) :=
  pick_spec (D.exists_true_not_deriv hw)

theorem good_aux : ∀ n m, m < n → D.Good m := by
  intro n
  induction n with
  | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
  | succ n ih =>
    intro m hm
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with h | rfl
    · exact ih m h
    · have ihe : ∀ k, k < m → ¬ A.TrueN (D.epsN k) := fun k hk => (ih k hk).2.2.2.2.2.2
      have hd := D.dN_spec m ihe
      have hx := D.trueN_xN_of m ihe
      have hw := D.trueN_wN_of m ih
      have hc := D.cN_spec m hw
      refine ⟨hd.1, hd.2, hx, hw, hc.1, hc.2, fun h => ?_⟩
      rw [epsN_eq, A.trueN_and, A.trueN_neg] at h
      exact h.2 hc.1

theorem good (n : ℕ) : D.Good n := D.good_aux (n + 1) n (Nat.lt_succ_self n)

theorem not_trueN_epsN (n : ℕ) : ¬ A.TrueN (D.epsN n) := (D.good n).2.2.2.2.2.2
theorem not_deriv_cN (n : ℕ) :
    ¬ Z.Deriv (Z.ext D.ZFC (D.star.i (D.wN n))) (D.star.i (D.cN n)) := (D.good n).2.2.2.2.2.1

/-- `ZFC + ε_n*` is consistent. -/
theorem consistent_ZFC_eps (n : ℕ) : Z.Consistent (Z.ext D.ZFC (D.star.i (D.epsN n))) := by
  refine ⟨D.star.i (D.cN n), fun h => D.not_deriv_cN n ?_⟩
  have h1 : Z.Deriv (Z.ext (Z.ext D.ZFC (D.star.i (D.wN n))) (Z.neg (D.star.i (D.cN n))))
      (D.star.i (D.cN n)) := by
    refine Language.deriv_cut_ext (a := D.star.i (D.epsN n)) ?_ ?_
    · rw [epsN_eq, D.star.map_and, D.star.map_neg]
      exact Z.deriv_and_intro (Language.deriv_ext_of _ (Language.deriv_ext_self _ _))
        (Language.deriv_ext_self _ _)
    · exact Z.deriv_mono (fun β hβ => by
        rcases hβ with hβ | hβ
        · exact Or.inl (Or.inl (Or.inl hβ))
        · exact Or.inr hβ) h
  exact Z.deriv_dne (Language.deriv_neg_of h1 (Language.deriv_ext_self _ _))

/-! ### The stages `(n, ψ_ν)`, `ν ∈ V_n` -/

/-- `E (n, ν) := ε_n* ∧ ζ ∧ ψ_ν`. -/
noncomputable def EN (n : ℕ) (ψ : Z.Sent) : Z.Sent := Z.and (Z.and (D.star.i (D.epsN n)) D.zeta) ψ

/-- `b ↦ (b^{ι_ν})*`: "the structure defined by `ι_ν` satisfies `b`". -/
noncomputable def actN (n : ℕ) (ψ b : Z.Sent) : Z.Sent := D.star.i (D.trN n ψ b)

theorem actN_neg (n : ℕ) (ψ a : Z.Sent) : D.actN n ψ (Z.neg a) = Z.neg (D.actN n ψ a) := by
  unfold actN; rw [trN_neg, D.star.map_neg]

theorem actN_and (n : ℕ) (ψ a b : Z.Sent) :
    D.actN n ψ (Z.and a b) = Z.and (D.actN n ψ a) (D.actN n ψ b) := by
  unfold actN; rw [trN_and, D.star.map_and]

theorem actN_imp (n : ℕ) (ψ a b : Z.Sent) :
    D.actN n ψ (Z.imp a b) = Z.imp (D.actN n ψ a) (D.actN n ψ b) := by
  unfold Language.imp; rw [actN_neg, actN_and, actN_neg]

theorem E_deriv_eps (n : ℕ) (ψ : Z.Sent) : Z.Deriv (Z.single (D.EN n ψ)) (D.star.i (D.epsN n)) :=
  Z.deriv_and_left (Z.deriv_and_left (Language.deriv_single_self (D.EN n ψ)))

theorem E_deriv_zeta (n : ℕ) (ψ : Z.Sent) : Z.Deriv (Z.single (D.EN n ψ)) D.zeta :=
  Z.deriv_and_right (Z.deriv_and_left (Language.deriv_single_self (D.EN n ψ)))

theorem E_deriv_psi (n : ℕ) (ψ : Z.Sent) : Z.Deriv (Z.single (D.EN n ψ)) ψ :=
  Z.deriv_and_right (Language.deriv_single_self (D.EN n ψ))

/-- `{ε_n} ⊢ c` in `𝓐` gives `{E (n, ν)} ⊢ c*`. -/
theorem E_deriv_star_of_eps (n : ℕ) (ψ : Z.Sent) {c : A.Sent}
    (h : A.Deriv (A.single (D.epsN n)) c) : Z.Deriv (Z.single (D.EN n ψ)) (D.star.i c) :=
  Language.deriv_of_single (D.E_deriv_eps n ψ) (D.star.deriv_single h)

/-- `{x_ν} ⊢ c` in `𝓐` gives `{E (n, ν)} ⊢ c*`, for `ν ∈ V_n`. -/
theorem E_deriv_star_of_x (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) {c : A.Sent}
    (h : A.Deriv (A.single (D.xPsi n ψ)) c) : Z.Deriv (Z.single (D.EN n ψ)) (D.star.i c) :=
  D.E_deriv_star_of_eps n ψ (Language.deriv_of_single (D.eps_deriv_xPsi n hψ) h)

theorem E_deriv_act_of_valid (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) {b : Z.Sent} (h : Z.Valid b) :
    Z.Deriv (Z.single (D.EN n ψ)) (D.actN n ψ b) :=
  D.E_deriv_star_of_x n hψ (D.x_deriv_tr_of_valid n ψ h)

theorem E_deriv_act_imp (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) {a b : Z.Sent}
    (h : Z.Deriv (Z.single a) b) :
    Z.Deriv (Z.single (D.EN n ψ)) (Z.imp (D.actN n ψ a) (D.actN n ψ b)) := by
  have := D.E_deriv_star_of_x n hψ (D.x_deriv_tr_imp n ψ h)
  rw [D.star.map_imp] at this
  exact this

theorem E_deriv_act_of_mem (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) {β : Z.Sent}
    (h : β ∈ ψ :: (D.lT n ++ [Z.neg (D.star.i (D.dN n))])) :
    Z.Deriv (Z.single (D.EN n ψ)) (D.actN n ψ β) :=
  D.E_deriv_star_of_x n hψ (D.x_deriv_tr_of_mem n ψ h)

/-- The structure defined by `ι_ν` is a model of `ZFC`. -/
theorem E_deriv_act_of_deriv_ZFC (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) {b : Z.Sent}
    (h : Z.Deriv D.ZFC b) : Z.Deriv (Z.single (D.EN n ψ)) (D.actN n ψ b) :=
  D.E_deriv_star_of_x n hψ (D.x_deriv_tr_of_deriv_ZFC n ψ h)

/-- (ii): `{E (n, ν)} ⊢ β* ↔ (β*)^{(n)}` for `β ∈ 𝓑`. -/
theorem E_deriv_iff_act_star (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) {β : A.Sent} (hβ : A.InB β) :
    Z.Deriv (Z.single (D.EN n ψ)) (Z.iff (D.star.i β) (D.actN n ψ (D.star.i β))) := by
  have key : ∀ γ, A.InB γ →
      Z.Deriv (Z.single (D.EN n ψ)) (Z.imp (D.star.i γ) (D.actN n ψ (D.star.i γ))) := fun γ hγ => by
    have := D.E_deriv_star_of_x n hψ (D.x_deriv_imp_tr_star n ψ hγ)
    rw [D.star.map_imp] at this
    exact this
  refine Language.deriv_iff_intro (Language.deriv_ext_of_imp (key β hβ)) ?_
  have h2 := key (A.neg β) (Arith.InB.neg hβ)
  rw [D.star.map_neg, actN_neg] at h2
  have h3 := Language.deriv_imp_neg_of_neg h2
  exact Z.deriv_dne (Language.deriv_mp (Language.deriv_ext_of _ h3)
    (Z.deriv_dni (Language.deriv_ext_self _ _)))

/-- (iii): `{E (n, ν)} ⊢ b ↔ b^{(n)}` for `b ∈ Γ_n`. -/
theorem E_deriv_iff_act_of_mem_Gam (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) {b : Z.Sent}
    (hb : b ∈ D.Gam n) : Z.Deriv (Z.single (D.EN n ψ)) (Z.iff b (D.actN n ψ b)) := by
  have hψx : A.Deriv (A.single (D.xPsi n ψ)) (D.trN n ψ ψ) :=
    D.x_deriv_tr_of_mem n ψ List.mem_cons_self
  rcases Language.vals_decide (D.mem_Vl.1 hψ).1 hb with h | h
  · have h1 : Z.Deriv (Z.single (D.EN n ψ)) b :=
      Language.deriv_of_single (D.E_deriv_psi n ψ) h
    have h2 : Z.Deriv (Z.single (D.EN n ψ)) (D.actN n ψ b) :=
      D.E_deriv_star_of_x n hψ (Language.deriv_mp (D.x_deriv_tr_imp n ψ h) hψx)
    exact Language.deriv_iff_of_both h1 h2
  · have h1 : Z.Deriv (Z.single (D.EN n ψ)) (Z.neg b) :=
      Language.deriv_of_single (D.E_deriv_psi n ψ) h
    have h2 : Z.Deriv (Z.single (D.EN n ψ)) (Z.neg (D.actN n ψ b)) := by
      have := D.E_deriv_star_of_x n hψ (Language.deriv_mp (D.x_deriv_tr_imp n ψ h) hψx)
      rw [trN_neg, D.star.map_neg] at this
      exact this
    exact Language.deriv_iff_of_both_neg h1 h2

/-- (iv): `{E (n, ν)} ⊢ ¬ (ε_m*)^{(n)}` for `m < n`. -/
theorem E_deriv_neg_act_eps_lt (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) {m : ℕ} (hm : m < n) :
    Z.Deriv (Z.single (D.EN n ψ)) (Z.neg (D.actN n ψ (D.star.i (D.epsN m)))) := by
  have := D.E_deriv_act_of_mem n hψ (β := Z.neg (D.star.i (D.epsN m)))
    (List.mem_cons_of_mem _ (List.mem_append.2 (Or.inl (D.mem_lT.2 ⟨m, hm, rfl⟩))))
  rw [actN_neg] at this
  exact this

/-- (iv): `{E (n, ν)} ⊢ ¬ (d_n*)^{(n)}`. -/
theorem E_deriv_neg_act_d (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) :
    Z.Deriv (Z.single (D.EN n ψ)) (Z.neg (D.actN n ψ (D.star.i (D.dN n)))) := by
  have := D.E_deriv_act_of_mem n hψ (β := Z.neg (D.star.i (D.dN n)))
    (List.mem_cons_of_mem _ (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))))
  rw [actN_neg] at this
  exact this

/-- Distinct stages are inconsistent with each other. -/
theorem E_excl {n m : ℕ} {ψ ψ' : Z.Sent} (hψ : ψ ∈ D.Vl n) (hψ' : ψ' ∈ D.Vl m)
    (hne : (n, ψ) ≠ (m, ψ')) : Z.Deriv (Z.single (D.EN n ψ)) (Z.neg (D.EN m ψ')) := by
  by_cases hn : n = m
  · subst hn
    have hψne : ψ ≠ ψ' := fun h => hne (by rw [h])
    have h1 : Z.Deriv (Z.single ψ) (Z.neg ψ') :=
      Language.vals_excl (D.mem_Vl.1 hψ).1 (D.mem_Vl.1 hψ').1 hψne
    exact Language.deriv_neg_of (b := ψ') (Z.deriv_and_right (Language.deriv_ext_self _ _))
      (Language.deriv_ext_of _ (Language.deriv_of_single (D.E_deriv_psi n ψ) h1))
  · have h1 : Z.Deriv (Z.single (D.EN n ψ)) (Z.neg (D.star.i (D.epsN m))) := by
      have := D.E_deriv_star_of_eps n ψ (D.eps_deriv_neg_eps n (m := m) (fun h => hn h.symm))
      rw [D.star.map_neg] at this
      exact this
    exact Language.deriv_neg_of (b := D.star.i (D.epsN m))
      (Z.deriv_and_left (Z.deriv_and_left (Language.deriv_ext_self _ _)))
      (Language.deriv_ext_of _ h1)

/-- The stages of the construction, as a `Perturb 𝓩`. A stage `(n, ψ)` is live if `ψ = ψ_ν` for some
`ν ∈ V_n`. -/
noncomputable def pert : Perturb Z where
  I := ℕ × Z.Sent
  E := fun s => D.EN s.1 s.2
  act := fun s b => D.actN s.1 s.2 b
  lvl := fun s => s.1
  live := fun s => s.2 ∈ D.Vl s.1
  below := fun K => (List.range K).flatMap (fun n => (D.Vl n).map (fun ψ => (n, ψ)))
  mem_below := fun K s => by
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨n, hn, hs⟩
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hs
      exact ⟨hψ, List.mem_range.1 hn⟩
    · rintro ⟨hl, hlt⟩
      exact ⟨s.1, List.mem_range.2 hlt, List.mem_map.2 ⟨s.2, hl, rfl⟩⟩
  z0 := D.star.i (a0 A)
  excl := fun _ _ hs ht hne => D.E_excl hs ht hne
  act_neg := fun s a => D.actN_neg s.1 s.2 a
  act_and := fun s a b => D.actN_and s.1 s.2 a b
  act_valid := fun s _ hl h => D.E_deriv_act_of_valid s.1 hl h
  act_ev := fun s _ hl hb =>
    D.E_deriv_iff_act_of_mem_Gam s.1 hl (List.mem_append.2 (Or.inl (Language.mem_firstN.2 hb)))

/-- Every stage fixes the sentences of `P₀`. -/
theorem P0_fix {p : Z.Sent} (hp : D.P0 p) (n : ℕ) {ψ : Z.Sent} (hψ : ψ ∈ D.Vl n) :
    Z.Deriv (Z.single (D.EN n ψ)) (Z.iff p (D.actN n ψ p)) := by
  rcases D.P0_cases p hp with ⟨β, hβ, rfl⟩ | hz | ⟨η, hη, h⟩
  · exact D.E_deriv_iff_act_star n hψ hβ
  · exact D.E_deriv_iff_act_of_mem_Gam n hψ (List.mem_append.2 (Or.inr hz))
  · have hζ := D.E_deriv_zeta n ψ
    have hζ' : Z.Deriv (Z.single (D.EN n ψ)) (D.actN n ψ D.zeta) :=
      D.E_deriv_act_of_deriv_ZFC n hψ D.ZFC_zeta
    have h1 := D.E_deriv_iff_act_star n hψ hη
    rcases h with h | h
    · rw [h, actN_imp] at h1
      exact Language.deriv_iff_of_imp_iff hζ hζ' h1
    · rw [h, actN_and] at h1
      exact Language.deriv_iff_of_and_iff hζ hζ' h1

/-! ### The translation `i_X` -/

/-- The stages `(n, ν)` with `n ∈ X`. -/
def YX (X : ℕ → Prop) : ℕ × Z.Sent → Prop := fun s => X s.1

/-- The translation `i = i_X : 𝓩 → 𝓩`. -/
noncomputable def iT (X : ℕ → Prop) : Translation Z Z :=
  D.pert.trans (YX X) D.syn D.P0 (fun _ hp s hl => D.P0_fix hp s.1 hl)

theorem iT_equiv_theta (X : ℕ → Prop) (b : Z.Sent) :
    Z.Equiv ((D.iT X).i b) (D.pert.theta (YX X) b) :=
  D.pert.imap_equiv_theta (YX X) D.syn D.P0 (fun _ hp s hl => D.P0_fix hp s.1 hl) b

/-- `ZFC ⊢ b` implies `ZFC ⊢ i (b)`; in particular `ZFC ⊢ⁱ ZFC`. -/
theorem iT_of_deriv_ZFC (X : ℕ → Prop) {b : Z.Sent} (h : Z.Deriv D.ZFC b) :
    Z.Deriv D.ZFC ((D.iT X).i b) := by
  rw [(D.iT_equiv_theta X b).deriv_iff D.ZFC]
  refine D.pert.theta_intro (YX X) (fun s hl _ => ?_) [] (fun s hs => by cases hs)
    (Z.deriv_mono (fun β hβ => Or.inl hβ) h)
  exact Language.deriv_ext_of_single (D.E_deriv_act_of_deriv_ZFC s.1 hl h)

/-- `i (β*)` is logically equivalent to `β*` for `β ∈ 𝓑`. -/
theorem iT_star_equiv (X : ℕ → Prop) {β : A.Sent} (hβ : A.InB β) :
    Z.Equiv ((D.iT X).i (D.star.i β)) (D.star.i β) :=
  (D.iT_equiv_theta X _).trans
    (D.pert.theta_fix (YX X) (fun s hl => D.E_deriv_iff_act_star s.1 hl hβ))

/-- `j = i ∘ i_{𝓐,𝓩}` is computable on `Σ⁰₂` sentences: there `i` replaces each prime constituent `p`
of `a*` by `wrap p`. -/
theorem jT_isN2 (X : ℕ → Prop) : ((D.iT X).comp D.star).IsNTranslation 2 := by
  obtain ⟨T, hT⟩ := D.wrapAll_comp.comp D.star_comp
  refine ⟨T, fun σ => ?_⟩
  show M.eval T (e M σ.1) = (some ((D.iT X).i (D.star.i σ.1))).map (e M)
  have h : (D.iT X).i (D.star.i σ.1) = D.wrapAll (D.star.i σ.1) :=
    D.pert.imap_eq_of_boolOver (YX X) D.syn D.P0 D.wrapAll_prime D.wrapAll_neg D.wrapAll_and
      D.P0_prime (D.star_bool σ.1 (Arith.InB.sigma σ.2))
  rw [h]
  exact hT σ.1

/-- `ZFC` is `2`-consistent relative to `j`, being arithmetically sound. -/
theorem jT_twoConsistent (X : ℕ → Prop) : ((D.iT X).comp D.star).TwoConsistent D.ZFC := by
  have hclause : ∀ σ, A.IsSigma 2 σ → ((D.iT X).comp D.star).DerivI D.ZFC σ →
      ∃ v, ¬ ((D.iT X).comp D.star).DerivI D.ZFC (A.neg (A.instS σ v)) := by
    intro σ hσ hd
    rw [Translation.derivI_iff, Translation.comp_i,
      (D.iT_star_equiv X (Arith.InB.sigma hσ)).deriv_iff] at hd
    obtain ⟨v, hv⟩ := (A.trueN_sigma 1 σ hσ).1 (D.sound σ hd)
    refine ⟨v, fun h => ?_⟩
    have hB : A.InB (A.neg (A.instS σ v)) :=
      Arith.InB.neg (Arith.InB.pi (A.pi_succ 1 _ (A.instS_pi 1 σ v hσ)))
    rw [Translation.derivI_iff, Translation.comp_i, (D.iT_star_equiv X hB).deriv_iff] at h
    exact (A.trueN_neg _).1 (D.sound _ h) hv
  refine ⟨⟨fun q hq => ?_, fun σ hσ hd => hclause σ (A.sigma_succ 1 σ hσ) hd⟩, hclause⟩
  rw [Translation.derivI_iff, Translation.comp_i]
  exact D.iT_of_deriv_ZFC X (D.ZFC_Q q hq)

/-! ### The induced theory -/

/-- A theory containing `ZFC`, proving `ε_n*` and `¬E (n, ν)` for every `ν ∈ V_n`, is inconsistent:
in a model of `ZFC` and `ε_n*` some valuation of `Γ_n` holds, and it is in `V_n`. -/
theorem inconsistent_of_eps {G : Z.Sent → Prop} (n : ℕ) (hZ : ∀ β, D.ZFC β → G β)
    (he : Z.Deriv G (D.star.i (D.epsN n)))
    (hE : ∀ ψ, ψ ∈ D.Vl n → Z.Deriv G (Z.neg (D.EN n ψ))) (γ : Z.Sent) : Z.Deriv G γ := by
  have hdisj := Language.deriv_disj_vals (F := G) (z := Z.botOf (D.star.i (a0 A)))
    (Language.deriv_topOf G (D.star.i (a0 A))) (D.Gam n)
  refine Language.deriv_disjList_elim hdisj (fun ψ hψ => ?_) (Language.deriv_of_botOf _ _)
  rcases D.mem_Vl_or_Vbad hψ with hV | hV
  · have h1 : Z.Deriv (Z.ext G ψ) (D.EN n ψ) :=
      Z.deriv_and_intro (Z.deriv_and_intro (Language.deriv_ext_of _ he)
        (Z.deriv_mono (fun β hβ => Or.inl (hZ β hβ)) D.ZFC_zeta)) (Language.deriv_ext_self _ _)
    exact Z.deriv_explosion h1 (Language.deriv_ext_of _ (hE ψ hV))
  · have ha : Z.Deriv (Z.ext G ψ) (D.star.i (D.aBad ψ)) :=
      Language.deriv_ext_of _
        (Language.deriv_of_single he (D.star.deriv_single (D.eps_deriv_aBad n hV)))
    have hn : Z.Deriv (Z.ext G ψ) (Z.neg ψ) := by
      refine Z.deriv_cut (fun β hβ => ?_) (D.aBad_spec (D.mem_Vbad.1 hV).2).2
      rcases hβ with hβ | hβ
      · exact Z.deriv_of_mem (Or.inl (hZ β hβ))
      · rw [hβ]; exact ha
    exact Z.deriv_explosion (Language.deriv_ext_self _ _) hn

/-- `ZFC ∪ {¬E (n, ν)}_{ν ∈ V_n} ⊢ ¬ε_n*`. -/
theorem deriv_neg_eps_star (n : ℕ) :
    Z.Deriv (Z.extList D.ZFC ((D.Vl n).map (fun ψ => Z.neg (D.EN n ψ))))
      (Z.neg (D.star.i (D.epsN n))) :=
  Z.deriv_neg_intro fun γ => D.inconsistent_of_eps
    (G := Z.ext (Z.extList D.ZFC ((D.Vl n).map (fun ψ => Z.neg (D.EN n ψ)))) (D.star.i (D.epsN n)))
    n (fun _ hβ => Or.inl (Or.inl hβ)) (Language.deriv_ext_self _ _)
    (fun ψ hψ => Z.deriv_of_mem (Or.inl (Or.inr (List.mem_map.2 ⟨ψ, hψ, rfl⟩)))) γ

/-- The encoding, first half: for `n ∈ X`, `ZFC ⊢ i ((¬ε_n)*)`. -/
theorem induced_of_mem (X : ℕ → Prop) {n : ℕ} (hn : X n) :
    Z.Deriv D.ZFC ((D.iT X).i (D.star.i (A.neg (D.epsN n)))) := by
  rw [(D.iT_equiv_theta X _).deriv_iff D.ZFC, D.star.map_neg]
  refine D.pert.theta_intro (YX X) (fun s hl _ => ?_) ((D.Vl n).map (fun ψ => (n, ψ)))
    (fun s hs => ?_) ?_
  · -- on the models of `E (m, ν)`: `¬ (ε_n*)^{(m)}`
    show Z.Deriv (Z.ext D.ZFC (D.EN s.1 s.2)) (D.actN s.1 s.2 (Z.neg (D.star.i (D.epsN n))))
    rw [actN_neg]
    refine Language.deriv_ext_of_single ?_
    rcases Nat.lt_trichotomy s.1 n with h | h | h
    · -- `m < n`: `ε_n ⊢ d_m`, and `¬ (d_m*)^{(m)}`
      exact Language.deriv_neg_of_imp
        (D.E_deriv_act_imp s.1 hl (D.star.deriv_single (D.eps_deriv_d_lt n h)))
        (D.E_deriv_neg_act_d s.1 hl)
    · -- `m = n`: `ε_n ⊢ d_n`, and `¬ (d_n*)^{(n)}`
      have hd : A.Deriv (A.single (D.epsN n)) (D.dN s.1) := by rw [h]; exact D.eps_deriv_d n
      exact Language.deriv_neg_of_imp (D.E_deriv_act_imp s.1 hl (D.star.deriv_single hd))
        (D.E_deriv_neg_act_d s.1 hl)
    · -- `m > n`: `¬ (ε_n*)^{(m)}` by (iv)
      exact D.E_deriv_neg_act_eps_lt s.1 hl h
  · obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hs
    exact ⟨hψ, hn⟩
  · -- where no `E (n, ν)`, `ν ∈ V_n`, holds: `¬ε_n*`
    refine Z.deriv_mono (fun β hβ => ?_) (D.deriv_neg_eps_star n)
    rcases hβ with hβ | hβ
    · exact Or.inl hβ
    · obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hβ
      exact Or.inr (List.mem_map.2 ⟨(n, ψ), List.mem_map.2 ⟨ψ, hψ, rfl⟩, rfl⟩)

/-- The encoding, second half: for `n ∉ X`, `ZFC ⊬ i ((¬ε_n)*)`. -/
theorem not_induced_of_not_mem (X : ℕ → Prop) {n : ℕ} (hn : ¬ X n) :
    ¬ Z.Deriv D.ZFC ((D.iT X).i (D.star.i (A.neg (D.epsN n)))) := by
  intro h
  rw [(D.iT_equiv_theta X _).deriv_iff D.ZFC, D.star.map_neg] at h
  obtain ⟨c, hc⟩ := D.consistent_ZFC_eps n
  apply hc
  -- in `ZFC + ε_n*` no `E (m, ν)`, `m ∈ X`, holds
  have hoff : Z.Deriv (Z.ext D.ZFC (D.star.i (D.epsN n)))
      (Z.iff (D.pert.theta (YX X) (Z.neg (D.star.i (D.epsN n)))) (Z.neg (D.star.i (D.epsN n)))) := by
    refine D.pert.theta_off (YX X) (fun s _ hY => ?_) _
    have hne : s.1 ≠ n := fun h' => hn (h' ▸ hY)
    have h1 : Z.Deriv (Z.ext D.ZFC (D.star.i (D.epsN n))) (Z.neg (D.star.i (D.epsN s.1))) := by
      have := D.star.deriv_single (D.eps_deriv_neg_eps n hne)
      rw [D.star.map_neg] at this
      exact Language.deriv_ext_of_single this
    exact Language.deriv_neg_of (b := D.star.i (D.epsN s.1))
      (Z.deriv_and_left (Z.deriv_and_left (Language.deriv_ext_self _ _)))
      (Language.deriv_ext_of _ h1)
  have h2 : Z.Deriv (Z.ext D.ZFC (D.star.i (D.epsN n))) (Z.neg (D.star.i (D.epsN n))) :=
    Language.deriv_iff_mp hoff (Language.deriv_ext_of _ h)
  exact Z.deriv_explosion (Language.deriv_ext_self _ _) h2

/-- The family of translations `i_X`. -/
theorem family (X : ℕ → Prop) : ∃ i : Translation Z Z,
    (i.comp D.star).IsNTranslation 2 ∧ i.DerivISet D.ZFC D.ZFC ∧
    (i.comp D.star).OneConsistent D.ZFC ∧ (i.comp D.star).TwoConsistent D.ZFC ∧
    ∀ n, ((i.comp D.star).induced D.ZFC (A.neg (D.epsN n)) ↔ X n) :=
  ⟨D.iT X, D.jT_isN2 X,
    fun φ hφ => ((D.iT X).derivI_iff D.ZFC φ).2 (D.iT_of_deriv_ZFC X (Z.deriv_of_mem hφ)),
    (D.jT_twoConsistent X).1, D.jT_twoConsistent X,
    fun _ => ⟨fun h => Classical.byContradiction fun hn => D.not_induced_of_not_mem X hn h,
      fun hn => D.induced_of_mem X hn⟩⟩

end UndefZSound

/-! ### Proposition B.10 -/

/-- A family of sets of sentences of arithmetic which determines `X ⊂ ℕ` has a non-arithmetical
member: only countably many sets of sentences are arithmetical. -/
theorem exists_not_arithmetical {A : Arith M} (S : (ℕ → Prop) → (A.Sent → Prop))
    (hinj : ∀ X Y, S X = S Y → X = Y) : ∃ X, ¬ Arithmetical (A := A) (S X) := by
  let g : ℕ → (ℕ → Prop) := fun k =>
    if h : ∃ X, arithEnum (A := A) k = S X then Classical.choose h else fun _ => False
  obtain ⟨X₀, hX₀⟩ := cantor g
  refine ⟨X₀, fun ha => ?_⟩
  obtain ⟨c, hc⟩ := exists_arithEnum_eq ha
  have hex : ∃ X, arithEnum (A := A) c = S X := ⟨X₀, hc⟩
  apply hX₀ c
  show (if h : ∃ X, arithEnum (A := A) c = S X then Classical.choose h else fun _ => False) = X₀
  rw [dite_eq_left hex]
  exact hinj _ _ ((Classical.choose_spec hex).symm.trans hc)

variable {A : Arith M} {Z : Language M}

/-- Proposition B.10, family form. Suppose that `ZFC` is arithmetically sound. Then there is a sequence
`ε_n` of sentences of arithmetic such that for every `X ⊂ ℕ` there is a translation `i_X : 𝓩 → 𝓩` with
`j_X := i_X ∘ i_{𝓐,𝓩}` a `2`-translation, `ZFC ⊢^{i_X} ZFC`, `ZFC` `1`- and `2`-consistent relative to
`j_X`, and `¬ε_n ∈ ZFC_{j_X,𝓐}` iff `n ∈ X`. The sequence `ε_n` does not depend on `X`. -/
theorem undefinableZFC_family (D : UndefZData A Z)
    (hs : ∀ a, Z.Deriv D.ZFC (D.star.i a) → A.TrueN a) :
    ∃ eps : ℕ → A.Sent, ∀ X : ℕ → Prop, ∃ i : Translation Z Z,
      (i.comp D.star).IsNTranslation 2 ∧ i.DerivISet D.ZFC D.ZFC ∧
      (i.comp D.star).OneConsistent D.ZFC ∧ (i.comp D.star).TwoConsistent D.ZFC ∧
      ∀ n, ((i.comp D.star).induced D.ZFC (A.neg (eps n)) ↔ X n) :=
  ⟨(UndefZSound.mk D hs).epsN, (UndefZSound.mk D hs).family⟩

/-- Proposition B.10. Suppose that `ZFC` is arithmetically sound. Then there is a translation
`i : 𝓩 → 𝓩` with `j := i ∘ i_{𝓐,𝓩}` a `2`-translation (so `i` is a `2`-translation in the sense of
Definition B.1), `ZFC ⊢ⁱ ZFC`, `ZFC` `1`- and `2`-consistent relative to `j`, and `ZFC_{j,𝓐}` not
arithmetical. (By counting: `X ↦ ZFC_{j_X,𝓐}` is injective, and there are only countably many
arithmetical sets of sentences.) -/
theorem exists_undefinable_ZFC (D : UndefZData A Z)
    (hs : ∀ a, Z.Deriv D.ZFC (D.star.i a) → A.TrueN a) :
    ∃ i : Translation Z Z,
      (i.comp D.star).IsNTranslation 2 ∧ i.DerivISet D.ZFC D.ZFC ∧
      (i.comp D.star).OneConsistent D.ZFC ∧ (i.comp D.star).TwoConsistent D.ZFC ∧
      ¬ Arithmetical (A := A) ((i.comp D.star).induced D.ZFC) := by
  obtain ⟨eps, hX⟩ := undefinableZFC_family D hs
  let i : (ℕ → Prop) → Translation Z Z := fun X => Classical.choose (hX X)
  have hi : ∀ X, ((i X).comp D.star).IsNTranslation 2 ∧ (i X).DerivISet D.ZFC D.ZFC ∧
      ((i X).comp D.star).OneConsistent D.ZFC ∧ ((i X).comp D.star).TwoConsistent D.ZFC ∧
      ∀ n, (((i X).comp D.star).induced D.ZFC (A.neg (eps n)) ↔ X n) :=
    fun X => Classical.choose_spec (hX X)
  obtain ⟨X₀, hX₀⟩ := exists_not_arithmetical (fun X => ((i X).comp D.star).induced D.ZFC)
    (fun X Y h => by
      funext n
      apply propext
      exact (((hi X).2.2.2.2 n).symm.trans (Iff.of_eq (congrFun h (A.neg (eps n))))).trans
        ((hi Y).2.2.2.2 n))
  exact ⟨i X₀, (hi X₀).1, (hi X₀).2.1, (hi X₀).2.2.1, (hi X₀).2.2.2.1, hX₀⟩

end Stable
