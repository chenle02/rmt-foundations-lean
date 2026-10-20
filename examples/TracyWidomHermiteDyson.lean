import RMTFoundations.TracyWidom.HermiteLimits
import RMTFoundations.TracyWidom.FiniteDysonMarginals
set_option autoImplicit false
open Real Set MeasureTheory
open RMTFoundations.TracyWidom.HermiteEdgeReduction
open RMTFoundations.TracyWidom.FiniteDysonGaussianLaw
open RMTFoundations.TracyWidom.GUEIdentification
example (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ y : ℝ, s ≤ y →
      |edgeMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) ∧
      |RMTFoundations.TracyWidom.HermiteTailComparison.previousMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) :=
  RMTFoundations.TracyWidom.HermiteLimits.uniform_tail s
example (m n : ℕ /- [definition] -/) (t : ℕ → ℝ /- [definition] -/)
    (ht : Monotone t /- [standing] -/) (j : Fin (m+1) /- [definition] -/) :
    (innovationMeasure m n).map (ouCoordinates m n t j) = gueMeasure n :=
  RMTFoundations.TracyWidom.FiniteDysonMarginals.stationary_GUE_coordinate_law m n t ht j
