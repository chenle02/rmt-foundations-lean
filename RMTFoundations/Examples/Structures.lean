import RMTFoundations.Concentration.Bernstein
import RMTFoundations.Stochastic.SimpleIntegral
import Mathlib.Probability.Distributions.Gaussian.Real
namespace RMTFoundations.StructureProbe
open MeasureTheory ProbabilityTheory
/-- Bernstein fields hold jointly for the standard Gaussian, with positive variance. -/
theorem bernstein_gaussian :
    RMTFoundations.Concentration.HasBernsteinMGF id 1 0 (gaussianReal 0 1) ∧
      Var[id; gaussianReal 0 1] = 1 ∧ gaussianReal 0 1 ≠ 0 := by
  refine ⟨?_, by simp [variance_id_gaussianReal], IsProbabilityMeasure.ne_zero _⟩
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro t _ _
    simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t)
  · intro t _ _
    simp [mgf_id_gaussianReal]
/-- A constant nonzero integrand over strictly increasing times inhabits every field. -/
theorem simple_predictable :
    ∃ (ℱ : Filtration ℕ (inferInstance : MeasurableSpace ℝ)),
      RMTFoundations.Stochastic.IsSimplePredictable ℱ id (fun _ _ => 1) ∧
      StrictMono (id : ℕ → ℕ) ∧ (1 : ℝ) ≠ 0 := by
  refine ⟨⊥, ⟨monotone_id, ?_, ?_⟩, strictMono_id, one_ne_zero⟩
  · intro i
    exact stronglyMeasurable_const
  · exact ⟨1, fun i ω => by norm_num⟩
end RMTFoundations.StructureProbe

#print axioms RMTFoundations.StructureProbe.bernstein_gaussian
#print axioms RMTFoundations.StructureProbe.simple_predictable
