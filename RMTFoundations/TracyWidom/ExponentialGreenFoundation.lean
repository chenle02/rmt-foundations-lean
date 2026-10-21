import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ExponentialGreenFoundation
open MeasureTheory Set Real

/-- Reduction-of-order kernel normalized by the positive reference solution. -/
noncomputable def normalizedGreen
    (A : ℝ → ℝ /- [definition] -/)
    (x t : ℝ /- [definition] -/) : ℝ :=
  ∫ r in x..t, (A t / A r)^2

/-- Reduction-of-order identity; no differential equation is assumed. -/
theorem normalizedGreen_factor
    (A : ℝ → ℝ /- [definition] -/)
    (x t : ℝ /- [definition] -/) :
    normalizedGreen A x t = (A t)^2 * ∫ r in x..t, ((A r)^2)⁻¹ := by
  unfold normalizedGreen
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext r
  simp only [div_eq_mul_inv,mul_pow,inv_pow]

/-- Exact exponentially dominated kernel mass on a finite interval. -/
theorem exponential_mass
    (c x t : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/) :
    (∫ r in x..t, exp (-2*c*(t-r))) =
      (1 - exp (-2*c*(t-x))) / (2*c) := by
  have hden : 2*c ≠ 0 := by positivity
  have hd (r : ℝ) : HasDerivAt (fun r => exp (-2*c*(t-r)) / (2*c))
      (exp (-2*c*(t-r))) r := by
    convert! ((((hasDerivAt_const r t).sub (hasDerivAt_id r)).const_mul (-2*c)).exp).div_const (2*c) using 1 <;>
      (try simp only [Pi.sub_apply,Pi.neg_apply,id_eq]) <;> field_simp [hden] <;> ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable x t)
  simpa only [sub_self, mul_zero, exp_zero, ← sub_div] using H

/-- The genuine kernel has the explicit local exponential bound and a uniform
mass ceiling. Positivity and continuity of the reference are ordinary ODE data. -/
theorem normalizedGreen_bounds
    (A : ℝ → ℝ /- [definition] -/)
    (c x t : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/)
    (hxt : x ≤ t /- [standing] -/)
    (hA : ContinuousOn A (Icc x t) /- [standing] -/)
    (hpos : ∀ r ∈ Icc x t, 0 < A r /- [standing] -/)
    (hratio : ∀ r ∈ Icc x t, A t / A r ≤ exp (-c*(t-r)) /- [standing] -/) :
    0 ≤ normalizedGreen A x t ∧
    normalizedGreen A x t ≤ (1 - exp (-2*c*(t-x))) / (2*c) ∧
    (1 - exp (-2*c*(t-x))) / (2*c) ≤ 1 / (2*c) := by
  have hf : ContinuousOn (fun r => (A t/A r)^2) (Icc x t) :=
    ((continuousOn_const.div hA (fun r hr => ne_of_gt (hpos r hr))).pow 2)
  have hi : IntervalIntegrable (fun r => (A t/A r)^2) volume x t :=
    ContinuousOn.intervalIntegrable_of_Icc hxt hf
  have hg : IntervalIntegrable (fun r => exp (-2*c*(t-r))) volume x t :=
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable x t)
  refine ⟨?_,?_,?_⟩
  · exact intervalIntegral.integral_nonneg hxt (fun r _ => sq_nonneg _)
  · rw [← exponential_mass c x t hc]
    apply intervalIntegral.integral_mono_on hxt hi hg
    intro r hr
    have H := pow_le_pow_left₀ (div_nonneg (hpos t ⟨hxt,le_rfl⟩).le (hpos r hr).le) (hratio r hr) 2
    have he : (exp (-c*(t-r)))^2 = exp (-2*c*(t-r)) := by
      rw [sq, ← exp_add]; congr 1; ring
    exact H.trans_eq he
  · exact div_le_div_of_nonneg_right (by linarith [exp_pos (-2*c*(t-x))]) (by positivity)

/-- Every analytic kernel binder is jointly realized by a strictly positive,
nonconstant reference and a nonzero interval. -/
theorem green_all_binder_joint_probe :
    0 ≤ normalizedGreen (fun r : ℝ => exp (-r)) 0 1 ∧
    normalizedGreen (fun r : ℝ => exp (-r)) 0 1 ≤ (1 - exp (-2)) / 2 ∧
    (1 - exp (-2)) / 2 ≤ 1 / 2 := by
  have H := normalizedGreen_bounds (fun r : ℝ => exp (-r)) 1 0 1
    (by norm_num) (by norm_num) (Real.continuous_exp.comp continuous_neg).continuousOn
    (by intro r hr; exact exp_pos _)
    (by intro r hr; rw [← exp_sub]; apply le_of_eq; congr 1; ring)
  simpa using H

end RMTFoundations.TracyWidom.ExponentialGreenFoundation

#print axioms RMTFoundations.TracyWidom.ExponentialGreenFoundation.normalizedGreen
#print axioms RMTFoundations.TracyWidom.ExponentialGreenFoundation.exponential_mass
#print axioms RMTFoundations.TracyWidom.ExponentialGreenFoundation.normalizedGreen_bounds
#print axioms RMTFoundations.TracyWidom.ExponentialGreenFoundation.green_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.ExponentialGreenFoundation.normalizedGreen_factor
