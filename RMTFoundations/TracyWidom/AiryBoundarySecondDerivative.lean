import RMTFoundations.TracyWidom.AiryBoundaryDerivative
import RMTFoundations.TracyWidom.AiryWeightedBoundary


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.AiryBoundarySecondDerivative
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.AiryBoundaryDerivative
open RMTFoundations.TracyWidom.AiryWeightedBoundary

/-- Genuine weak derivative, proved for every L² test vector by dominated differentiation. -/
theorem airyBoundaryDerivative_pairing_hasDerivAt
    (v : Lp ℝ 2 halfLineMeasure) -- [definition]
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => inner ℝ v (airyBoundaryDerivative t))
      (inner ℝ v (airyBoundaryODEVector s)) s := by
  obtain ⟨D,hD,hb⟩ := weightedAi_local_bound s
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun x => deriv airyAiReal (t+x)*v x) halfLineMeasure :=
    (continuous_deriv_airyAiReal.comp (continuous_const.add continuous_id)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable v)
  have hdmeas : AEStronglyMeasurable
      (fun x => ((s+x)*airyAiReal (s+x))*v x) halfLineMeasure :=
    ((continuous_const.add continuous_id).mul (continuous_airyAiReal.comp (continuous_const.add continuous_id))).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable v)
  have hi : Integrable (fun x => deriv airyAiReal (s+x)*v x) halfLineMeasure := by
    have hh := (Lp.memLp (airyBoundaryDerivative s)).integrable_mul (Lp.memLp v)
    apply hh.congr
    filter_upwards [airyBoundaryDerivative_apply_ae s] with x hx
    simp only [Pi.mul_apply]
    rw [hx]
  have hmajor : Integrable (fun x : ℝ => D*Real.exp (-(1/2:ℝ)*x)*|v x|) halfLineMeasure := by
    have hh := ((memLp_halfline_exp_rate (-(1/2:ℝ)) (by norm_num)).integrable_mul
      (Lp.memLp v).norm).const_mul D
    simpa only [Real.norm_eq_abs, Pi.mul_apply, mul_assoc] using hh
  have hbound : ∀ᵐ x ∂halfLineMeasure, ∀ t ∈ Metric.ball s 1,
      ‖((t+x)*airyAiReal (t+x))*v x‖ ≤ D*Real.exp (-(1/2:ℝ)*x)*|v x| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro t ht
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_right (hb t ht x hx.le) (abs_nonneg (v x))
  have hdiff : ∀ᵐ x ∂halfLineMeasure, ∀ t ∈ Metric.ball s 1,
      HasDerivAt (fun t => deriv airyAiReal (t+x)*v x) (((t+x)*airyAiReal (t+x))*v x) t := by
    apply ae_of_all
    intro x t _
    simpa only [Function.comp_def, mul_one, id_eq] using!
      ((hasDerivAt_deriv_airyAiReal' (t+x)).comp t ((hasDerivAt_id t).add_const x)).mul_const (v x)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1)) (Eventually.of_forall hmeas)
    hi hdmeas hbound hmajor hdiff).2
  simpa only [airyBoundaryDerivative_pairing, airyBoundaryODEVector_pairing] using h

/-- Actual norm derivative of the Airy boundary vector; no physical regularity premise. -/
theorem hasDerivAt_airyBoundaryDerivative
    (s : ℝ) -- [definition]
    : HasDerivAt airyBoundaryDerivative (airyBoundaryODEVector s) s :=
  RMTFoundations.TracyWidom.hasDerivAt_vector_of_pairings airyBoundaryDerivative
    airyBoundaryODEVector airyBoundaryODEVector_continuous
    airyBoundaryDerivative_pairing_hasDerivAt s


/-- A genuine positive-shift derivative row is nonzero. -/
theorem airyBoundaryDerivative_one_ne : airyBoundaryDerivative 1 ≠ 0 := by
  intro hz
  have h := airyBoundaryVector_derivative_pairing 1
  rw [hz,inner_zero_right,mul_zero] at h
  have hp := sq_pos_of_pos (airyAiReal_pos_of_nonneg (by norm_num : (0:ℝ)≤1))
  linarith

/-- All second-derivative binders are realized on genuine nonzero Airy rows at shift one. -/
theorem airy_boundary_second_derivative_joint_probe :
    (∀ (v : Lp ℝ 2 halfLineMeasure) (s : ℝ),
      HasDerivAt (fun t => inner ℝ v (airyBoundaryDerivative t))
        (inner ℝ v (airyBoundaryODEVector s)) s) ∧
      (∀ s : ℝ, HasDerivAt airyBoundaryDerivative (airyBoundaryODEVector s) s) ∧
      airyBoundaryVector 1 ≠ 0 ∧ airyBoundaryDerivative 1 ≠ 0 ∧ airyBoundaryODEVector 1 ≠ 0 ∧
      (airyBoundaryODEVector 1 =ᵐ[halfLineMeasure] fun x => (1+x)*airyAiReal (1+x)) :=
  ⟨airyBoundaryDerivative_pairing_hasDerivAt,hasDerivAt_airyBoundaryDerivative,
    airyBoundaryVector_ne_zero 1,airyBoundaryDerivative_one_ne,airyBoundaryODEVector_one_ne,
    airyBoundaryODEVector_apply_ae 1⟩

end RMTFoundations.TracyWidom.AiryBoundarySecondDerivative
#print axioms RMTFoundations.TracyWidom.AiryBoundarySecondDerivative.airyBoundaryDerivative_pairing_hasDerivAt
#print axioms RMTFoundations.TracyWidom.AiryBoundarySecondDerivative.hasDerivAt_airyBoundaryDerivative
#print axioms RMTFoundations.TracyWidom.AiryBoundarySecondDerivative.airyBoundaryDerivative_one_ne
#print axioms RMTFoundations.TracyWidom.AiryBoundarySecondDerivative.airy_boundary_second_derivative_joint_probe
