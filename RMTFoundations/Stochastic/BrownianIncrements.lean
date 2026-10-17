import Mathlib.Probability.BrownianMotion.Basic

/-!
# The first and second moments of a Brownian increment

Mathlib builds Brownian motion from its finite-dimensional laws and records
`ProbabilityTheory.IsPreBrownianReal.covariance_eval : cov[B s, B t] = min s t`, but it
does not record the second moment of an increment in the form the Itô isometry needs.
This file supplies it.

## What is proved

* `integral_increment_isPreBrownianReal`: `E[B s - B t] = 0`.
* `integral_sq_increment_isPreBrownianReal`: `E[(B s - B t)²] = |s - t|`.
* `integral_sq_increment_isPreBrownianReal_le`: for `s ≤ t`, `E[(B t - B s)²] = t - s`.

This is the centring and clock input to the Brownian Itô isometry.  The other input,
that Brownian motion is a martingale for its natural filtration, is proved in
`RMTFoundations/Stochastic/BrownianMartingale.lean`, which also combines the two.

## What is *not* proved

No filtration is attached to `B` here, and no martingale property is claimed here; those
live in `RMTFoundations/Stochastic/BrownianMartingale.lean`.  Nothing about higher
moments of an increment, and nothing about the joint law of several increments beyond
what `ProbabilityTheory.IsPreBrownianReal.hasLaw_sub` already gives.
-/

namespace RMTFoundations.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type* /- [definition] -/ } {mΩ : MeasurableSpace Ω /- [definition] -/ } {P : Measure Ω /- [definition] -/ } {B : ℝ≥0 → Ω → ℝ /- [definition] -/ }

/-- A pre-Brownian increment is centred. -/
theorem integral_increment_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ ) (s t : ℝ≥0 /- [definition] -/ ) :
    ∫ ω, (B s ω - B t ω) ∂P = 0 := by
  have h := (hB.hasLaw_sub s t).integral_eq
  rw [integral_id_gaussianReal] at h
  exact h

/-- **The second moment of a pre-Brownian increment.** -/
theorem integral_sq_increment_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ ) (s t : ℝ≥0 /- [definition] -/ ) :
    ∫ ω, (B s ω - B t ω) ^ 2 ∂P = |(s : ℝ) - (t : ℝ)| := by
  have haem : AEMeasurable (B s - B t) P := (hB.aemeasurable s).sub (hB.aemeasurable t)
  have hvar := (hB.hasLaw_sub s t).variance_eq
  rw [variance_id_gaussianReal] at hvar
  rw [variance_eq_integral haem] at hvar
  have hmean : P[B s - B t] = 0 := integral_increment_isPreBrownianReal hB s t
  rw [hmean] at hvar
  have hpt : ∀ ω, ((B s - B t) ω - 0) ^ 2 = (B s ω - B t ω) ^ 2 := by
    intro ω
    rw [sub_zero, Pi.sub_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hvar
  rw [hvar, coe_nndist, Real.dist_eq]
  rfl

/-- For `s ≤ t` the second moment of the increment is the elapsed time. -/
theorem integral_sq_increment_isPreBrownianReal_le (hB : IsPreBrownianReal B P /- [standing] -/ ) {s t : ℝ≥0 /- [definition] -/ }
    (hst : s ≤ t /- [standing] -/ ) :
    ∫ ω, (B t ω - B s ω) ^ 2 ∂P = (t : ℝ) - (s : ℝ) := by
  rw [integral_sq_increment_isPreBrownianReal hB t s, abs_of_nonneg]
  exact sub_nonneg.mpr (by exact_mod_cast hst)

end RMTFoundations.Stochastic

#print axioms RMTFoundations.Stochastic.integral_increment_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.integral_sq_increment_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.integral_sq_increment_isPreBrownianReal_le
