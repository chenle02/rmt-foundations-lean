import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Martingale.Basic

/-

# Continuous-time adaptedness on `ℝ≥0`

## What is proved

* `isStronglyProgressive_of_continuous_nnreal` and `isProgressive_of_continuous_nnreal`:
  a real process on `ℝ≥0` with continuous paths, strongly adapted to `ℱ`, is
  (strongly) progressively measurable.
* `stronglyAdapted_stoppedProcess_of_continuous_nnreal`: the process stopped at a
  stopping time is again strongly adapted.
* `Martingale.isStronglyProgressive_of_continuous_nnreal`: a continuous martingale
  on `ℝ≥0` is progressively measurable.

## What is *not* proved

Nothing about càdlàg paths, usual conditions, or the existence of a continuous
modification; mathlib's `MeasureTheory.Filtration.IsRightContinuous` exists but the
usual-conditions completion does not.

-/

namespace RMTFoundations.Stochastic

open MeasureTheory
open scoped NNReal

variable {Ω : Type* /- [definition] -/ } {m0 : MeasurableSpace Ω /- [definition] -/ } {ℱ : Filtration ℝ≥0 m0 /- [definition] -/ } {u : ℝ≥0 → Ω → ℝ /- [definition] -/ }

/-- A real process on the continuous time axis `ℝ≥0` with continuous paths that is
strongly adapted is strongly progressively measurable. -/
theorem isStronglyProgressive_of_continuous_nnreal
    (hu : StronglyAdapted ℱ u /- [standing] -/ ) (hcont : ∀ ω, Continuous fun t => u t ω /- [standing] -/ ) :
    IsStronglyProgressive ℱ u :=
  hu.isStronglyProgressive_of_continuous hcont

/-- The `IsProgressive` form of `isStronglyProgressive_of_continuous_nnreal`. -/
theorem isProgressive_of_continuous_nnreal
    (hu : StronglyAdapted ℱ u /- [standing] -/ ) (hcont : ∀ ω, Continuous fun t => u t ω /- [standing] -/ ) :
    IsProgressive ℱ u :=
  (isStronglyProgressive_of_continuous_nnreal hu hcont).isProgressive

/-- A continuous adapted process stopped at a stopping time is again adapted. -/
theorem stronglyAdapted_stoppedProcess_of_continuous_nnreal
    {τ : Ω → WithTop ℝ≥0 /- [definition] -/ } (hu : StronglyAdapted ℱ u /- [standing] -/ )
    (hcont : ∀ ω, Continuous fun t => u t ω /- [standing] -/ ) (hτ : IsStoppingTime ℱ τ /- [standing] -/ ) :
    StronglyAdapted ℱ (stoppedProcess u τ) :=
  (isStronglyProgressive_of_continuous_nnreal hu hcont).stronglyAdapted_stoppedProcess hτ

/-- A martingale on `ℝ≥0` with continuous paths is progressively measurable. -/
theorem isStronglyProgressive_of_continuous_martingale {μ : Measure Ω /- [definition] -/ }
    (hu : Martingale u ℱ μ /- [standing] -/ ) (hcont : ∀ ω, Continuous fun t => u t ω /- [standing] -/ ) :
    IsStronglyProgressive ℱ u :=
  isStronglyProgressive_of_continuous_nnreal hu.stronglyAdapted hcont

end RMTFoundations.Stochastic

#print axioms RMTFoundations.Stochastic.isStronglyProgressive_of_continuous_nnreal
#print axioms RMTFoundations.Stochastic.isProgressive_of_continuous_nnreal
#print axioms RMTFoundations.Stochastic.stronglyAdapted_stoppedProcess_of_continuous_nnreal
#print axioms RMTFoundations.Stochastic.isStronglyProgressive_of_continuous_martingale
