import Challenge.Reference.Stieltjes.Defs
import Mathlib
namespace RMTFoundations.AnalyticHalfPlane
open MeasureTheory Set
open RMTFoundations.Stieltjes (stieltjes)
def upper : Set ℂ := {z | 0 < z.im}
theorem isOpen_upper : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im
def HerglotzBorel : Prop :=
  ∀ (F : ℂ → ℂ) (M : ℝ), DifferentiableOn ℂ F upper → (∀ z ∈ upper, 0 ≤ (F z).im) →
    (∀ z ∈ upper, ‖F z‖ ≤ M / z.im) →
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ.real univ ≤ M ∧ ∀ z ∈ upper, F z = stieltjes μ z
end RMTFoundations.AnalyticHalfPlane

#print axioms RMTFoundations.AnalyticHalfPlane.upper
#print axioms RMTFoundations.AnalyticHalfPlane.isOpen_upper
#print axioms RMTFoundations.AnalyticHalfPlane.HerglotzBorel
