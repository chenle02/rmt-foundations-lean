import Tests.AiryLegacy.Coefficients
import RMTFoundations.Airy.ODE

/-!
# The power series solution of the Airy equation

Combining the coefficient recursion of `RMTFoundations.Airy.Coefficients` with the term-by-term
differentiation of `RMTFoundations.Airy.Series` and the uniqueness theorem of
`RMTFoundations.Airy.ODE`, this file constructs, for each pair of initial data `(a₀, a₁)`, an
honest solution of `y'' = x y` on all of `ℝ` and shows that it is the only one.

## What is proved here

* `isAirySolution_airySol`: `airySol a₀ a₁` together with `airySolDeriv a₀ a₁` satisfies
  `IsAirySolution`.  The heart of the proof is `seriesSum_airyCoeff_two`, which identifies the
  twice-differentiated series with `x` times the original one; this is exactly the coefficient
  recursion together with the vanishing of the coefficient of `x ^ 2`;
* `airySol_zero_eq`, `airySolDeriv_zero_eq`: the initial data are `a₀` and `a₁`;
* `airySolution_exists`: existence of a solution with arbitrary prescribed initial data;
* `IsAirySolution.eq_airySol`, `IsAirySolution.eq_airySolDeriv`: **every** solution of the Airy
  equation is one of these power series, namely the one attached to its own initial data;
* `airySol_eq_linearCombination`, `airySolDeriv_eq_linearCombination`: every solution is the
  linear combination `a₀ * airySol 1 0 + a₁ * airySol 0 1` of the two solutions with initial data
  `(1, 0)` and `(0, 1)`, with `a₀ = f 0` and `a₁ = f' 0`.

## What is NOT proved here

* the two-dimensionality of the solution space is not stated as a `Module.rank` or
  `FiniteDimensional` fact, and linear *independence* of the two basis solutions is not stated
  either; only the parametrisation by initial data and the spanning statement are proved.
* nothing here identifies `airySol` with the classical `Ai`/`Bi` integral representations, and
  nothing here is asymptotic.
-/

namespace RMTFoundations.Airy

/-- The solution of `y'' = x y` with `y 0 = a₀`, `y' 0 = a₁`, defined by its power series. -/
noncomputable def airySol (a₀ a₁ : ℝ /- [definition] -/ ) : ℝ → ℝ := seriesSum (airyCoeff a₀ a₁)

/-- The derivative of `airySol a₀ a₁`, defined by the formally differentiated power series. -/
noncomputable def airySolDeriv (a₀ a₁ : ℝ /- [definition] -/ ) : ℝ → ℝ :=
  seriesSum fun n => ((n : ℝ) + 1) * airyCoeff a₀ a₁ (n + 1)

variable (a₀ a₁ : ℝ /- [definition] -/ )

theorem hasEntireCoeffs_airyCoeff_one :
    HasEntireCoeffs fun n => ((n : ℝ) + 1) * airyCoeff a₀ a₁ (n + 1) :=
  hasEntireCoeffs_derivCoeffs (hasEntireCoeffs_airyCoeff a₀ a₁)

/-- The coefficient sequence of the second derivative of the Airy series. -/
theorem hasEntireCoeffs_airyCoeff_two :
    HasEntireCoeffs fun n => ((n : ℝ) + 1) * ((n : ℝ) + 2) * airyCoeff a₀ a₁ (n + 2) := by
  have h := hasEntireCoeffs_derivCoeffs (hasEntireCoeffs_airyCoeff_one a₀ a₁)
  refine fun r hr => (h r hr).congr fun n => ?_
  have hc : ((n : ℝ) + 1) * ((((n + 1 : ℕ) : ℝ) + 1) * airyCoeff a₀ a₁ (n + 1 + 1))
      = ((n : ℝ) + 1) * ((n : ℝ) + 2) * airyCoeff a₀ a₁ (n + 2) := by
    push_cast
    ring
  simp only [hc]

/-- The twice-differentiated Airy series is `x` times the original one.  This *is* the Airy
equation at the level of coefficients: the coefficient of `x ^ 0` on the left is
`2 * airyCoeff a₀ a₁ 2 = 0`, and the coefficient of `x ^ (n + 1)` on the left is
`(n + 3) (n + 2) a (n + 3) = a n`. -/
theorem seriesSum_airyCoeff_two (x : ℝ /- [definition] -/ ) :
    seriesSum (fun n => ((n : ℝ) + 1) * ((n : ℝ) + 2) * airyCoeff a₀ a₁ (n + 2)) x
      = x * seriesSum (airyCoeff a₀ a₁) x := by
  have hc := hasEntireCoeffs_airyCoeff a₀ a₁
  have hc2 := hasEntireCoeffs_airyCoeff_two a₀ a₁
  have hsum2 := summable_seriesTerm hc2 x
  have hsum := summable_seriesTerm hc x
  -- the left-hand side, after peeling off the vanishing constant term
  have hleft : seriesSum (fun n => ((n : ℝ) + 1) * ((n : ℝ) + 2) * airyCoeff a₀ a₁ (n + 2)) x
      = ∑' n : ℕ, airyCoeff a₀ a₁ n * x ^ (n + 1) := by
    rw [seriesSum, hsum2.tsum_eq_zero_add]
    have hzero : (((0 : ℕ) : ℝ) + 1) * (((0 : ℕ) : ℝ) + 2) * airyCoeff a₀ a₁ (0 + 2) * x ^ 0 = 0 := by
      rw [airyCoeff_two]
      ring
    rw [hzero, zero_add]
    refine tsum_congr fun n => ?_
    have hrec : (((n : ℝ) + 1) + 1) * (((n : ℝ) + 1) + 2) * airyCoeff a₀ a₁ (n + 1 + 2)
        = airyCoeff a₀ a₁ n := by
      have h := airyCoeff_recursion a₀ a₁ n
      have hidx : n + 1 + 2 = n + 3 := rfl
      rw [hidx, ← h]
      ring
    have hcast : ((((n + 1 : ℕ)) : ℝ) + 1) * ((((n + 1 : ℕ)) : ℝ) + 2) * airyCoeff a₀ a₁ (n + 1 + 2)
        = (((n : ℝ) + 1) + 1) * (((n : ℝ) + 1) + 2) * airyCoeff a₀ a₁ (n + 1 + 2) := by
      push_cast
      ring
    rw [hcast, hrec]
  -- the right-hand side
  have hright : x * seriesSum (airyCoeff a₀ a₁) x = ∑' n : ℕ, airyCoeff a₀ a₁ n * x ^ (n + 1) := by
    rw [seriesSum, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [pow_succ]
    ring
  rw [hleft, hright]

/-- The power series solves the Airy equation. -/
theorem isAirySolution_airySol : IsAirySolution (airySol a₀ a₁) (airySolDeriv a₀ a₁) where
  hasDerivAt_left x := hasDerivAt_seriesSum (hasEntireCoeffs_airyCoeff a₀ a₁) x
  hasDerivAt_right x := by
    have h := hasDerivAt_seriesSum (hasEntireCoeffs_airyCoeff_one a₀ a₁) x
    have hcoeff : (fun n : ℕ => ((n : ℝ) + 1) * ((((n + 1 : ℕ) : ℝ)) + 1) * airyCoeff a₀ a₁ (n + 1 + 1))
        = fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * airyCoeff a₀ a₁ (n + 2) := by
      funext n
      push_cast
      ring
    have hval : seriesSum
        (fun n : ℕ => ((n : ℝ) + 1) * (((((n + 1 : ℕ)) : ℝ) + 1) * airyCoeff a₀ a₁ (n + 1 + 1))) x
        = x * airySol a₀ a₁ x := by
      have hre : (fun n : ℕ => ((n : ℝ) + 1) * (((((n + 1 : ℕ)) : ℝ) + 1)
          * airyCoeff a₀ a₁ (n + 1 + 1)))
          = fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * airyCoeff a₀ a₁ (n + 2) := by
        funext n
        push_cast
        ring
      rw [hre, seriesSum_airyCoeff_two, airySol]
    rw [← hval]
    exact h

theorem airySol_zero_eq : airySol a₀ a₁ 0 = a₀ := by
  rw [airySol, seriesSum_zero (hasEntireCoeffs_airyCoeff a₀ a₁), airyCoeff_zero]

theorem airySolDeriv_zero_eq : airySolDeriv a₀ a₁ 0 = a₁ := by
  rw [airySolDeriv, seriesSum_zero (hasEntireCoeffs_airyCoeff_one a₀ a₁)]
  rw [Nat.cast_zero, zero_add, one_mul, zero_add, airyCoeff_one]

/-- Existence: the Airy equation has a solution with arbitrary prescribed initial data. -/
theorem airySolution_exists (a₀ a₁ : ℝ /- [definition] -/ ) :
    ∃ f f' : ℝ → ℝ, IsAirySolution f f' ∧ f 0 = a₀ ∧ f' 0 = a₁ :=
  ⟨airySol a₀ a₁, airySolDeriv a₀ a₁, isAirySolution_airySol a₀ a₁, airySol_zero_eq a₀ a₁,
    airySolDeriv_zero_eq a₀ a₁⟩

variable {f f' : ℝ → ℝ /- [definition] -/ }

/-- Every solution of the Airy equation is the power series solution attached to its own initial
data.  Together with `airySolution_exists` this parametrises the whole solution space. -/
theorem IsAirySolution.eq_airySol (hf : IsAirySolution f f' /- [standing] -/ ) : f = airySol (f 0) (f' 0) :=
  airySolution_unique hf (isAirySolution_airySol (f 0) (f' 0))
    (airySol_zero_eq (f 0) (f' 0)).symm (airySolDeriv_zero_eq (f 0) (f' 0)).symm

theorem IsAirySolution.eq_airySolDeriv (hf : IsAirySolution f f' /- [standing] -/ ) :
    f' = airySolDeriv (f 0) (f' 0) :=
  airySolution_unique_deriv hf (isAirySolution_airySol (f 0) (f' 0))
    (airySol_zero_eq (f 0) (f' 0)).symm (airySolDeriv_zero_eq (f 0) (f' 0)).symm

/-! ### A basis of the solution space -/

theorem isAirySolution_airyBasis (a₀ a₁ : ℝ /- [definition] -/ ) :
    IsAirySolution (fun x => a₀ * airySol 1 0 x + a₁ * airySol 0 1 x)
      (fun x => a₀ * airySolDeriv 1 0 x + a₁ * airySolDeriv 0 1 x) :=
  airySolution_linearCombination a₀ a₁ (isAirySolution_airySol 1 0) (isAirySolution_airySol 0 1)

/-- Every solution of the Airy equation is the linear combination of the two solutions with
initial data `(1, 0)` and `(0, 1)` prescribed by its own initial data. -/
theorem airySol_eq_linearCombination (a₀ a₁ : ℝ /- [definition] -/ ) :
    airySol a₀ a₁ = fun x => a₀ * airySol 1 0 x + a₁ * airySol 0 1 x := by
  refine airySolution_unique (isAirySolution_airySol a₀ a₁) (isAirySolution_airyBasis a₀ a₁)
    (t₀ := 0) ?_ ?_
  · rw [airySol_zero_eq, airySol_zero_eq, airySol_zero_eq]
    ring
  · rw [airySolDeriv_zero_eq, airySolDeriv_zero_eq, airySolDeriv_zero_eq]
    ring

theorem airySolDeriv_eq_linearCombination (a₀ a₁ : ℝ /- [definition] -/ ) :
    airySolDeriv a₀ a₁ = fun x => a₀ * airySolDeriv 1 0 x + a₁ * airySolDeriv 0 1 x := by
  refine airySolution_unique_deriv (isAirySolution_airySol a₀ a₁) (isAirySolution_airyBasis a₀ a₁)
    (t₀ := 0) ?_ ?_
  · rw [airySol_zero_eq, airySol_zero_eq, airySol_zero_eq]
    ring
  · rw [airySolDeriv_zero_eq, airySolDeriv_zero_eq, airySolDeriv_zero_eq]
    ring

end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.airySol
#print axioms RMTFoundations.Airy.airySolDeriv
#print axioms RMTFoundations.Airy.hasEntireCoeffs_airyCoeff_one
#print axioms RMTFoundations.Airy.hasEntireCoeffs_airyCoeff_two
#print axioms RMTFoundations.Airy.seriesSum_airyCoeff_two
#print axioms RMTFoundations.Airy.isAirySolution_airySol
#print axioms RMTFoundations.Airy.airySol_zero_eq
#print axioms RMTFoundations.Airy.airySolDeriv_zero_eq
#print axioms RMTFoundations.Airy.airySolution_exists
#print axioms RMTFoundations.Airy.IsAirySolution.eq_airySol
#print axioms RMTFoundations.Airy.IsAirySolution.eq_airySolDeriv
#print axioms RMTFoundations.Airy.isAirySolution_airyBasis
#print axioms RMTFoundations.Airy.airySol_eq_linearCombination
#print axioms RMTFoundations.Airy.airySolDeriv_eq_linearCombination
