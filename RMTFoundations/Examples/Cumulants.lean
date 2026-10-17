import RMTFoundations.Probability.Cumulants
import Mathlib.Probability.Distributions.Gaussian.Real
namespace RMTFoundations.CumulantsProbe
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
/-- Every recursion binder is realized at order four by a genuine positive-variance Gaussian. -/
theorem joint :
    ∃ (μ : Measure ℝ) (X : ℝ → ℝ) (n : ℕ),
      IsProbabilityMeasure μ ∧ μ ≠ 0 ∧ 0 < n ∧
      (0 : ℝ) ∈ interior (integrableExpSet X μ) ∧ Var[X; μ] = 1 ∧
      μ[X ^ (n+1)] = ∑ j ∈ Finset.range (n+1),
        (n.choose j : ℝ) * RMTFoundations.Cumulants.cumulant (j+1) X μ * μ[X ^ (n-j)] := by
  let μ := gaussianReal 0 1
  have h : (0 : ℝ) ∈ interior (integrableExpSet id μ) := by
    simp [μ,integrableExpSet_id_gaussianReal]
  exact ⟨μ,id,3,inferInstance,MeasureTheory.IsProbabilityMeasure.ne_zero μ,by norm_num,h,
    by simp [μ,variance_id_gaussianReal],
    RMTFoundations.Cumulants.moment_succ_eq_sum_cumulant_mul_moment h 3⟩
end RMTFoundations.CumulantsProbe

#print axioms RMTFoundations.CumulantsProbe.joint
