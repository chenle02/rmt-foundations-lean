import Mathlib
import RMTFoundations.Airy.Core
import RMTFoundations.TracyWidom.DecayingODEFoundation
namespace RMTFoundations.TracyWidom.AiryGreenFoundation
open MeasureTheory Set Filter Real
open scoped Topology
open RMTFoundations.Airy

theorem ai_tendsto_zero : Tendsto airyAiReal atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := airyAiReal_abs_le_exp'
  apply squeeze_zero_norm' (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hbound t)
  simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C

theorem ai_twist_tendsto_zero : Tendsto (fun t : ℝ => t*(airyAiReal t)^2) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := airyAiReal_abs_le_exp'
  apply squeeze_zero'
    (by filter_upwards [eventually_ge_atTop 0] with t ht; positivity)
    (by filter_upwards [eventually_ge_atTop 0] with t ht
        calc t*(airyAiReal t)^2 = t*|airyAiReal t|^2 := by rw [sq_abs]
          _ ≤ t*(C*exp (-t))^2 := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hbound t) 2) ht
          _ = C^2*(t*exp (-(2*t))) := by rw [mul_pow,exp_neg_sq]; ring
          _ ≤ C^2*exp (-t) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
            calc t*exp (-(2*t)) ≤ exp t*exp (-(2*t)) :=
                mul_le_mul_of_nonneg_right ((by linarith : t ≤ t+1).trans (add_one_le_exp t)) (exp_pos _).le
              _ = exp (-t) := by rw [← exp_add]; congr 1; ring)
    (by simpa using tendsto_exp_neg_atTop_nhds_zero.const_mul (C^2))

theorem ai_prime_tendsto_zero : Tendsto (deriv airyAiReal) atTop (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => (deriv airyAiReal t)^2) atTop (𝓝 0) := by
    convert airyEnergy_tendsto_zero.add ai_twist_tendsto_zero using 1
    · funext t; dsimp [airyEnergy]; ring
    · simp
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def,Real.sqrt_sq_eq_abs,Real.sqrt_zero] at H
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using H)

/-- The physical Airy outgoing component has its vanishing boundary term. -/
theorem ai_outgoing_tendsto_zero
    (c : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/) :
    Tendsto (fun t : ℝ => exp (-c*t)*(deriv airyAiReal t+c*airyAiReal t))
      atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => exp (-c*t)) atTop (𝓝 0) := by
    convert tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hc) using 1
    · funext t; simp only [Function.comp_def,id_eq]; congr 1; ring
  simpa using he.mul (ai_prime_tendsto_zero.add (ai_tendsto_zero.const_mul c))

/-- Exponential ratio bound at rate sqrt(s) for the actual Ai, with the ODE,
positivity and outgoing boundary term all derived from Airy results. -/
theorem ai_relative_exponential
    (s x t : ℝ /- [definition] -/)
    (hs : 0 < s /- [standing] -/)
    (hsx : s ≤ x /- [standing] -/)
    (hxt : x ≤ t /- [standing] -/) :
    airyAiReal t / airyAiReal x ≤ exp (-sqrt s*(t-x)) := by
  have hc : 0 < sqrt s := sqrt_pos.mpr hs
  have H := RMTFoundations.TracyWidom.DecayingODEFoundation.relative_exponential_tail
    airyAiReal (deriv airyAiReal) id
    hasDerivAt_airyAiReal' hasDerivAt_deriv_airyAiReal' x (sqrt s)
    (fun r hr => (airyAiReal_pos_of_nonneg (hs.le.trans (hsx.trans hr))).le)
    (fun r hr => by simpa only [id_eq,sq_sqrt hs.le] using hsx.trans hr)
    (ai_outgoing_tendsto_zero (sqrt s) hc) t hxt
  exact (div_le_iff₀ (airyAiReal_pos_of_nonneg (hs.le.trans hsx))).mpr (by simpa [mul_comm] using H)

/-- All Airy comparison binders jointly hold on a nonzero half-line. -/
theorem airy_exponential_all_binder_joint_probe
    (t : ℝ /- [definition] -/)
    (ht : 1 ≤ t /- [standing] -/) :
    airyAiReal t / airyAiReal 1 ≤ exp (-(t-1)) := by
  simpa using ai_relative_exponential 1 1 t (by norm_num) le_rfl ht

end RMTFoundations.TracyWidom.AiryGreenFoundation

#print axioms RMTFoundations.TracyWidom.AiryGreenFoundation.ai_tendsto_zero
#print axioms RMTFoundations.TracyWidom.AiryGreenFoundation.ai_twist_tendsto_zero
#print axioms RMTFoundations.TracyWidom.AiryGreenFoundation.ai_prime_tendsto_zero
#print axioms RMTFoundations.TracyWidom.AiryGreenFoundation.ai_outgoing_tendsto_zero
#print axioms RMTFoundations.TracyWidom.AiryGreenFoundation.ai_relative_exponential
#print axioms RMTFoundations.TracyWidom.AiryGreenFoundation.airy_exponential_all_binder_joint_probe
