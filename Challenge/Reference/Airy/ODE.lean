import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Airy differential equation `y'' = x y`

This file introduces the predicate `RMTFoundations.Airy.IsAirySolution f f'`, which says that
the pair of real functions `(f, f')` solves the Airy equation in the sense that `f'` is the
derivative of `f` everywhere and `x * f x` is the derivative of `f'` everywhere.  Carrying the
derivative as a second explicit function (rather than writing `deriv f`) keeps every statement
below free of differentiability side conditions.

## What is proved here

* the solution set is a vector space: `airySolution_zero`, `airySolution_add`,
  `airySolution_smul`, `airySolution_neg`, `airySolution_sub`;
* every solution is continuous and differentiable, and in fact `C^n` for every `n`, hence
  `C^∞`: `IsAirySolution.contDiff_natCast`, `IsAirySolution.contDiff_infty`;
* **uniqueness**: a solution is determined by its value and the value of its derivative at one
  point, `airySolution_unique_pair`, `airySolution_unique`, `airySolution_unique_deriv`.  This is
  obtained from mathlib's `ODE_solution_unique_of_mem_Ioo` applied to the first-order system
  `(y, z)' = (z, x y)` on `ℝ × ℝ`; the Lipschitz constant of that system is unbounded in `x`, so
  the globally-Lipschitz form `ODE_solution_unique_univ` does not apply and uniqueness is first
  obtained on an arbitrary bounded interval and then transported to all of `ℝ`;
* the Wronskian of two solutions is constant, `airyWronskian_eq`.

## What is NOT proved here

* existence of solutions in this abstract ODE file. Concrete Ai is constructed in Core
  and connected to this interface by AbstractBridge; Bi remains absent.
  The former power-series construction survives only as a regression witness under
  `Tests/AiryLegacy/`; concrete complex constructions can use `ComplexRestriction`.
* analyticity.  `C^∞` is proved by bootstrapping the equation; real-analyticity of an arbitrary
  solution is not proved here (it follows from uniqueness together with the series solution, but
  that implication is not formalised).
* no asymptotics of any kind.
-/

namespace RMTFoundations.Airy

/-- `IsAirySolution f f'` says that the pair `(f, f')` solves the Airy equation `y'' = x y`:
`f'` is the derivative of `f`, and the derivative of `f'` at `x` is `x * f x`. -/
structure IsAirySolution (f f' : ℝ → ℝ /- [definition] -/ ) : Prop where
  /-- `f'` is the derivative of `f`. -/
  hasDerivAt_left : ∀ x, HasDerivAt f (f' x) x
  /-- The derivative of `f'` at `x` is `x * f x`; this is the equation itself. -/
  hasDerivAt_right : ∀ x, HasDerivAt f' (x * f x) x

variable {f f' g g' : ℝ → ℝ /- [definition] -/ }

theorem IsAirySolution.differentiable (hf : IsAirySolution f f' /- [standing] -/ ) : Differentiable ℝ f :=
  fun x => (hf.hasDerivAt_left x).differentiableAt

theorem IsAirySolution.differentiable_deriv (hf : IsAirySolution f f' /- [standing] -/ ) : Differentiable ℝ f' :=
  fun x => (hf.hasDerivAt_right x).differentiableAt

theorem IsAirySolution.continuous (hf : IsAirySolution f f' /- [standing] -/ ) : Continuous f :=
  hf.differentiable.continuous

theorem IsAirySolution.continuous_deriv (hf : IsAirySolution f f' /- [standing] -/ ) : Continuous f' :=
  hf.differentiable_deriv.continuous

theorem IsAirySolution.deriv_eq (hf : IsAirySolution f f' /- [standing] -/ ) : deriv f = f' :=
  funext fun x => (hf.hasDerivAt_left x).deriv

theorem IsAirySolution.deriv_deriv_eq (hf : IsAirySolution f f' /- [standing] -/ ) :
    deriv f' = fun x => x * f x :=
  funext fun x => (hf.hasDerivAt_right x).deriv

/-! ### The solution set is a vector space -/

theorem airySolution_zero : IsAirySolution (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ)) where
  hasDerivAt_left _ := hasDerivAt_const _ _
  hasDerivAt_right x := by
    have : x * (0 : ℝ) = 0 := mul_zero x
    rw [this]
    exact hasDerivAt_const _ _

theorem airySolution_add (hf : IsAirySolution f f' /- [standing] -/ ) (hg : IsAirySolution g g' /- [standing] -/ ) :
    IsAirySolution (fun x => f x + g x) (fun x => f' x + g' x) where
  hasDerivAt_left x := (hf.hasDerivAt_left x).add (hg.hasDerivAt_left x)
  hasDerivAt_right x := by
    have h := (hf.hasDerivAt_right x).add (hg.hasDerivAt_right x)
    have hx : x * f x + x * g x = x * (f x + g x) := (mul_add x (f x) (g x)).symm
    rwa [hx] at h

theorem airySolution_smul (c : ℝ /- [definition] -/ ) (hf : IsAirySolution f f' /- [standing] -/ ) :
    IsAirySolution (fun x => c * f x) (fun x => c * f' x) where
  hasDerivAt_left x := (hf.hasDerivAt_left x).const_mul c
  hasDerivAt_right x := by
    have h := (hf.hasDerivAt_right x).const_mul c
    have hx : c * (x * f x) = x * (c * f x) := by ring
    rwa [hx] at h

theorem airySolution_neg (hf : IsAirySolution f f' /- [standing] -/ ) :
    IsAirySolution (fun x => -f x) (fun x => -f' x) where
  hasDerivAt_left x := (hf.hasDerivAt_left x).neg
  hasDerivAt_right x := by
    have h := (hf.hasDerivAt_right x).neg
    have hx : -(x * f x) = x * -f x := (mul_neg x (f x)).symm
    rwa [hx] at h

theorem airySolution_sub (hf : IsAirySolution f f' /- [standing] -/ ) (hg : IsAirySolution g g' /- [standing] -/ ) :
    IsAirySolution (fun x => f x - g x) (fun x => f' x - g' x) where
  hasDerivAt_left x := (hf.hasDerivAt_left x).sub (hg.hasDerivAt_left x)
  hasDerivAt_right x := by
    have h := (hf.hasDerivAt_right x).sub (hg.hasDerivAt_right x)
    have hx : x * f x - x * g x = x * (f x - g x) := (mul_sub x (f x) (g x)).symm
    rwa [hx] at h

/-- Linear combinations of solutions are solutions. -/
theorem airySolution_linearCombination (a b : ℝ /- [definition] -/ ) (hf : IsAirySolution f f' /- [standing] -/ )
    (hg : IsAirySolution g g' /- [standing] -/ ) :
    IsAirySolution (fun x => a * f x + b * g x) (fun x => a * f' x + b * g' x) :=
  airySolution_add (airySolution_smul a hf) (airySolution_smul b hg)

/-! ### Smoothness by bootstrapping the equation -/

theorem IsAirySolution.contDiff_natCast (hf : IsAirySolution f f' /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    ContDiff ℝ (n : WithTop ℕ∞) f ∧ ContDiff ℝ (n : WithTop ℕ∞) f' := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_zero, contDiff_zero]
      exact hf.continuous
    · rw [Nat.cast_zero, contDiff_zero]
      exact hf.continuous_deriv
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
      push_cast
      rfl
    have hne : ((n : WithTop ℕ∞) = ⊤ → AnalyticOn ℝ f Set.univ) := by
      intro h
      exact absurd h (by exact_mod_cast (WithTop.natCast_ne_top n))
    have hne' : ((n : WithTop ℕ∞) = ⊤ → AnalyticOn ℝ f' Set.univ) := by
      intro h
      exact absurd h (by exact_mod_cast (WithTop.natCast_ne_top n))
    refine ⟨?_, ?_⟩
    · rw [hcast, contDiff_succ_iff_deriv, hf.deriv_eq]
      exact ⟨hf.differentiable, hne, ih.2⟩
    · rw [hcast, contDiff_succ_iff_deriv, hf.deriv_deriv_eq]
      exact ⟨hf.differentiable_deriv, hne', contDiff_id.mul ih.1⟩

/-- Every solution of the Airy equation is infinitely differentiable. -/
theorem IsAirySolution.contDiff_infty (hf : IsAirySolution f f' /- [standing] -/ ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
  _root_.contDiff_infty.2 fun n => (hf.contDiff_natCast n).1

/-- The derivative of a solution of the Airy equation is infinitely differentiable. -/
theorem IsAirySolution.contDiff_infty_deriv (hf : IsAirySolution f f' /- [standing] -/ ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' :=
  _root_.contDiff_infty.2 fun n => (hf.contDiff_natCast n).2

/-! ### Uniqueness -/

/-- The vector field of the first-order system equivalent to the Airy equation:
`(y, z) ↦ (z, x * y)`. -/
def airyField (x : ℝ /- [definition] -/ ) (p : ℝ × ℝ /- [definition] -/ ) : ℝ × ℝ := (p.2, x * p.1)

theorem lipschitzWith_airyField {x K : ℝ /- [definition] -/ } (hK : 1 ≤ K /- [standing] -/ ) (hxK : |x| ≤ K /- [standing] -/ ) :
    LipschitzWith (Real.toNNReal K) (airyField x) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal K hK0, Prod.dist_eq, Prod.dist_eq]
  refine max_le ?_ ?_
  · calc dist p.2 q.2 ≤ max (dist p.1 q.1) (dist p.2 q.2) := le_max_right _ _
      _ = 1 * max (dist p.1 q.1) (dist p.2 q.2) := (one_mul _).symm
      _ ≤ K * max (dist p.1 q.1) (dist p.2 q.2) := by
          refine mul_le_mul_of_nonneg_right hK ?_
          exact le_trans dist_nonneg (le_max_left _ _)
  · have hd : dist (airyField x p).2 (airyField x q).2 = |x| * dist p.1 q.1 := by
      show dist (x * p.1) (x * q.1) = |x| * dist p.1 q.1
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    rw [hd]
    calc |x| * dist p.1 q.1 ≤ K * dist p.1 q.1 :=
          mul_le_mul_of_nonneg_right hxK dist_nonneg
      _ ≤ K * max (dist p.1 q.1) (dist p.2 q.2) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hK0

/-- Two solutions of the Airy equation agreeing together with their derivatives at one point are
equal, as pairs.  This is the main uniqueness statement; `airySolution_unique` and
`airySolution_unique_deriv` are its two components. -/
theorem airySolution_unique_pair (hf : IsAirySolution f f' /- [standing] -/ ) (hg : IsAirySolution g g' /- [standing] -/ ) {t₀ : ℝ /- [definition] -/ }
    (h0 : f t₀ = g t₀ /- [standing] -/ ) (h1 : f' t₀ = g' t₀ /- [standing] -/ ) :
    (fun x => (f x, f' x)) = fun x => (g x, g' x) := by
  funext t
  set a : ℝ := min t t₀ - 1 with ha
  set b : ℝ := max t t₀ + 1 with hb
  set K : ℝ := max 1 (max |a| |b|) with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hmem : ∀ s ∈ Set.Ioo a b, |s| ≤ K := by
    intro s hs
    refine le_trans (abs_le.2 ⟨?_, ?_⟩) (le_max_right 1 (max |a| |b|))
    · exact le_trans (neg_le_neg (le_max_left |a| |b|)) (le_trans (neg_abs_le a) hs.1.le)
    · exact le_trans hs.2.le (le_trans (le_abs_self b) (le_max_right |a| |b|))
  have hta : t ∈ Set.Ioo a b := by
    constructor
    · have : min t t₀ ≤ t := min_le_left _ _
      rw [ha]; linarith
    · have : t ≤ max t t₀ := le_max_left _ _
      rw [hb]; linarith
  have ht₀ : t₀ ∈ Set.Ioo a b := by
    constructor
    · have : min t t₀ ≤ t₀ := min_le_right _ _
      rw [ha]; linarith
    · have : t₀ ≤ max t t₀ := le_max_right _ _
      rw [hb]; linarith
  have key : Set.EqOn (fun x => (f x, f' x)) (fun x => (g x, g' x)) (Set.Ioo a b) := by
    refine ODE_solution_unique_of_mem_Ioo
      (v := airyField) (s := fun _ => (Set.univ : Set (ℝ × ℝ)))
      (K := Real.toNNReal K) (fun s hs => (lipschitzWith_airyField hK1 (hmem s hs)).lipschitzOnWith)
      ht₀ (fun s _ => ⟨?_, trivial⟩) (fun s _ => ⟨?_, trivial⟩) ?_
    · exact (hf.hasDerivAt_left s).prodMk (hf.hasDerivAt_right s)
    · exact (hg.hasDerivAt_left s).prodMk (hg.hasDerivAt_right s)
    · rw [Prod.mk.injEq]
      exact ⟨h0, h1⟩
  exact key hta

/-- A solution of the Airy equation is determined by `f t₀` and `f' t₀`. -/
theorem airySolution_unique (hf : IsAirySolution f f' /- [standing] -/ ) (hg : IsAirySolution g g' /- [standing] -/ ) {t₀ : ℝ /- [definition] -/ }
    (h0 : f t₀ = g t₀ /- [standing] -/ ) (h1 : f' t₀ = g' t₀ /- [standing] -/ ) : f = g := by
  funext x
  have h := congrFun (airySolution_unique_pair hf hg h0 h1) x
  exact congrArg Prod.fst h

/-- The derivative of a solution of the Airy equation is determined by `f t₀` and `f' t₀`. -/
theorem airySolution_unique_deriv (hf : IsAirySolution f f' /- [standing] -/ ) (hg : IsAirySolution g g' /- [standing] -/ ) {t₀ : ℝ /- [definition] -/ }
    (h0 : f t₀ = g t₀ /- [standing] -/ ) (h1 : f' t₀ = g' t₀ /- [standing] -/ ) : f' = g' := by
  funext x
  have h := congrFun (airySolution_unique_pair hf hg h0 h1) x
  exact congrArg Prod.snd h

/-- A solution vanishing to first order at a point vanishes identically. -/
theorem airySolution_eq_zero (hf : IsAirySolution f f' /- [standing] -/ ) {t₀ : ℝ /- [definition] -/ } (h0 : f t₀ = 0 /- [standing] -/ )
    (h1 : f' t₀ = 0 /- [standing] -/ ) : f = fun _ => (0 : ℝ) :=
  airySolution_unique hf airySolution_zero h0 h1

/-! ### The Wronskian -/

/-- The Wronskian of two solutions of the Airy equation is constant: `f g' - f' g` has zero
derivative because both functions satisfy the same second-order equation. -/
theorem airyWronskian_eq (hf : IsAirySolution f f' /- [standing] -/ ) (hg : IsAirySolution g g' /- [standing] -/ ) (x y : ℝ /- [definition] -/ ) :
    f x * g' x - f' x * g x = f y * g' y - f' y * g y := by
  have hderiv : ∀ z : ℝ, HasDerivAt (fun w => f w * g' w - f' w * g w) 0 z := by
    intro z
    have h1 : HasDerivAt (fun w => f w * g' w) (f' z * g' z + f z * (z * g z)) z :=
      (hf.hasDerivAt_left z).mul (hg.hasDerivAt_right z)
    have h2 : HasDerivAt (fun w => f' w * g w) (z * f z * g z + f' z * g' z) z :=
      (hf.hasDerivAt_right z).mul (hg.hasDerivAt_left z)
    have h3 := h1.sub h2
    have hz : f' z * g' z + f z * (z * g z) - (z * f z * g z + f' z * g' z) = 0 := by ring
    rwa [hz] at h3
  have hdiff : Differentiable ℝ fun w => f w * g' w - f' w * g w :=
    fun z => (hderiv z).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun z => (hderiv z).deriv) x y

end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.IsAirySolution
#print axioms RMTFoundations.Airy.IsAirySolution.differentiable
#print axioms RMTFoundations.Airy.IsAirySolution.differentiable_deriv
#print axioms RMTFoundations.Airy.IsAirySolution.continuous
#print axioms RMTFoundations.Airy.IsAirySolution.continuous_deriv
#print axioms RMTFoundations.Airy.IsAirySolution.deriv_eq
#print axioms RMTFoundations.Airy.IsAirySolution.deriv_deriv_eq
#print axioms RMTFoundations.Airy.airySolution_zero
#print axioms RMTFoundations.Airy.airySolution_add
#print axioms RMTFoundations.Airy.airySolution_smul
#print axioms RMTFoundations.Airy.airySolution_neg
#print axioms RMTFoundations.Airy.airySolution_sub
#print axioms RMTFoundations.Airy.airySolution_linearCombination
#print axioms RMTFoundations.Airy.IsAirySolution.contDiff_natCast
#print axioms RMTFoundations.Airy.IsAirySolution.contDiff_infty
#print axioms RMTFoundations.Airy.IsAirySolution.contDiff_infty_deriv
#print axioms RMTFoundations.Airy.airyField
#print axioms RMTFoundations.Airy.lipschitzWith_airyField
#print axioms RMTFoundations.Airy.airySolution_unique_pair
#print axioms RMTFoundations.Airy.airySolution_unique
#print axioms RMTFoundations.Airy.airySolution_unique_deriv
#print axioms RMTFoundations.Airy.airySolution_eq_zero
#print axioms RMTFoundations.Airy.airyWronskian_eq
