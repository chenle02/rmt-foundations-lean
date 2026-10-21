import RMTFoundations.TracyWidom.HermiteLimits
import RMTFoundations.TracyWidom.FiniteDysonMarginals
import RMTFoundations.TracyWidom.OUMehlerConjugation
set_option autoImplicit false
namespace Tests.TracyWidomHermiteDyson
open scoped BigOperators
open Real Set MeasureTheory Filter Matrix ProbabilityTheory
open RMTFoundations.Airy RMTFoundations.TracyWidom.HermiteEdgeReduction
open RMTFoundations.TracyWidom.HermiteTailComparison
open RMTFoundations.TracyWidom.GUEIdentification
open RMTFoundations.TracyWidom.FiniteDysonGaussianLaw
open RMTFoundations.TracyWidom.GUEExtendedHermite RMTFoundations.TracyWidom.OUMehlerConjugation
/-- A nondegenerate instance satisfying the stated hypotheses. -/
theorem hermite_tail_probe (s : ℝ /- [definition] -/)
    (k : ℕ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, k < N ∧ 0 < N ∧
      Polynomial.hermite N ≠ 0 ∧ ∀ T : ℝ, s ≤ T →
      IntegrableOn (fun y => (edgeMode N y)^2) (Ioi T) ∧
      IntegrableOn (fun y => (previousMode N y)^2) (Ioi T) ∧
      (∫ y in Ioi T, (edgeMode N y)^2) ≤ C^2*exp (-(T-s)) ∧
      (∫ y in Ioi T, (previousMode N y)^2) ≤ C^2*exp (-(T-s)) :=
  RMTFoundations.TracyWidom.HermiteUniformTailMass.uniform_mass_joint_probe s k

/-- A nondegenerate instance satisfying the stated hypotheses. -/
theorem stationary_probe :
    ∃ t : ℕ → ℝ, StrictMono t ∧ Monotone t ∧
      0 < ouCoefficient 1 t 1 1 ∧
      (∀ m n, IsProbabilityMeasure (innovationMeasure m n)) ∧
      (∀ m j, ∑ k : Fin (m+1), (ouCoefficient m t j k)^2 = 1) ∧
      (∀ m n j, (innovationMeasure m n).map (ouCoordinates m n t j) = gueMeasure n) ∧
      (∀ j : Fin 2, (innovationMeasure 1 2).map (ouCoordinates 1 2 t j) = gueMeasure 2) :=
  RMTFoundations.TracyWidom.FiniteDysonMarginals.stationary_all_binder_joint_probe

/-- A nondegenerate instance satisfying the stated hypotheses. -/
theorem scalar_law_probe :
    ∃ tau : ℝ, ∃ x y : Fin 2 → ℝ, tau < 0 ∧ x 0 < x 1 ∧ y 0 < y 1 ∧
      0 < Matrix.det (fun i j => mehlerKernel tau (x i) (y j)) ∧
      (∀ z : ℝ × ℝ, 0 < scalarJointDensity tau z) ∧
      Integrable (scalarJointDensity tau) ((volume : Measure ℝ).prod volume) ∧
      (∫ z : ℝ × ℝ, scalarJointDensity tau z ∂(volume : Measure ℝ).prod volume) = 1 ∧
      IsProbabilityMeasure (scalarHermiteJointLaw tau) :=
  RMTFoundations.TracyWidom.OUMehlerConjugation.scalar_law_all_binder_joint_probe

end Tests.TracyWidomHermiteDyson

#print axioms Tests.TracyWidomHermiteDyson.hermite_tail_probe
#print axioms Tests.TracyWidomHermiteDyson.stationary_probe
#print axioms Tests.TracyWidomHermiteDyson.scalar_law_probe
