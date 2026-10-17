import RMTFoundations.TracyWidom.RightTailPositive
import RMTFoundations.TracyWidom.TWSharpAiryTails
import RMTFoundations.TracyWidom.TW1RightTail
import RMTFoundations.TracyWidom.RightTailAsymptoticTransfer
import RMTFoundations.TracyWidom.RightTailRelativeBounds
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter Asymptotics
open scoped Topology Asymptotics
open RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWLeftTail

/-- The sharp GUE upper-tail prefactor in the canonical Airy normalization. -/
theorem TW2_rightTail_isEquivalent :
    (fun s : ℝ => 1-TW2R s) ~[atTop]
      (fun s => Real.exp (-(4/3:ℝ)*s^(3/2:ℝ))/(16*Real.pi*s^(3/2:ℝ))) := by
  have h := rightTail_asymptotic_of_quadratic_error
    (fun s => 1-TW2R s) airyTraceIntegral
    (tailModel (1/(16*Real.pi)) (-3/2) (4/3))
    airyTraceIntegral_tendsto_atTop_zero airyTraceIntegral_isEquivalent
    (Eventually.of_forall TW2_rightTail_trace_error)
  refine h.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  dsimp [tailModel]
  rw [show (-3/2:ℝ)=-(3/2:ℝ) by norm_num, Real.rpow_neg hs.le]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Literal normalized tail converges to one, including the exact constant. -/
theorem TW2_rightTail_ratio_tendsto_one :
    Tendsto (fun s : ℝ => (1-TW2R s) /
      (Real.exp (-(4/3:ℝ)*s^(3/2:ℝ))/(16*Real.pi*s^(3/2:ℝ))))
      atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one _).mp TW2_rightTail_isEquivalent
  filter_upwards [eventually_gt_atTop 0] with s hs
  exact (show 0 < Real.exp (-(4/3:ℝ)*s^(3/2:ℝ))/(16*Real.pi*s^(3/2:ℝ)) by positivity).ne'

/-- Arbitrarily sharp two-sided bounds with the right exponential rate and constant. -/
theorem TW2_rightTail_sharp_bounds
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ s in atTop,
      (1-ε)*(Real.exp (-(4/3:ℝ)*s^(3/2:ℝ))/(16*Real.pi*s^(3/2:ℝ))) ≤ 1-TW2R s ∧
      1-TW2R s ≤ (1+ε)*(Real.exp (-(4/3:ℝ)*s^(3/2:ℝ))/(16*Real.pi*s^(3/2:ℝ))) := by
  apply rightTail_relative_bounds_of_isEquivalent _ _ TW2_rightTail_isEquivalent _ ε hε
  filter_upwards [eventually_gt_atTop 0] with s hs
  positivity

/-- Trace controls the logarithmic determinant error once the trace is at most one half. -/
theorem TW2_rightTail_logdet_quadratic
    (s : ℝ /- [definition] -/)
    (hsmall : airyTraceIntegral s ≤ (1/2:ℝ) /- [standing] -/) :
    |Real.log (TW2R s)+airyTraceIntegral s| ≤ 2*(airyTraceIntegral s)^2 := by
  have ht := airyTraceIntegral_nonneg s
  obtain ⟨hl,hu⟩ := TW2_rightTail_trace_bounds s
  have hx : 0 ≤ 1-TW2R s := sub_nonneg.mpr (RMTFoundations.AiryBounds.TW2R_mem_Icc s).2
  have hxhalf : |1-TW2R s| ≤ (1/2:ℝ) := by
    rw [abs_of_nonneg hx]
    exact hu.trans hsmall
  have hd : 0 < TW2R s := by linarith
  have hscalar := signed_log_quadratic_remainder (1-TW2R s) hxhalf
  rw [show 1-(1-TW2R s)=TW2R s by ring] at hscalar
  have hlo := (abs_le.mp hscalar).1
  have hup : Real.log (TW2R s) ≤ -airyTraceIntegral s :=
    (Real.log_le_iff_le_exp hd).mpr (TW2R_trace_bound_unconditional s).2
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu) (add_nonneg ht hx)]
  · nlinarith [sq_nonneg (airyTraceIntegral s)]

/-- The logarithmic trace estimate holds eventually on the actual Airy kernel. -/
theorem TW2_rightTail_logdet_quadratic_eventually :
    ∀ᶠ s in atTop, |Real.log (TW2R s)+airyTraceIntegral s| ≤ 2*(airyTraceIntegral s)^2 := by
  have hb := airyTraceIntegral_tendsto_atTop_zero.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hb] with s hs
  exact TW2_rightTail_logdet_quadratic s hs.le

/-- Every asymptotic, quadratic-error, and small-trace input is realized
jointly on the genuine nonzero Airy model at a positive cutoff. -/
theorem TW2_rightTail_all_binder_joint_probe :
    ∃ s : ℝ, 1 < s ∧ airyAiReal s ≠ 0 ∧
      0 < airyTraceIntegral s ∧ airyTraceIntegral s ≤ (1/2:ℝ) ∧
      Tendsto airyTraceIntegral atTop (𝓝 0) ∧
      (airyTraceIntegral ~[atTop] tailModel (1/(16*Real.pi)) (-3/2) (4/3)) ∧
      (∀ u : ℝ, |(1-TW2R u)-airyTraceIntegral u| ≤ (airyTraceIntegral u)^2/2) ∧
      ((fun u : ℝ => 1-TW2R u) ~[atTop]
        (fun u => Real.exp (-(4/3:ℝ)*u^(3/2:ℝ))/(16*Real.pi*u^(3/2:ℝ)))) ∧
      0 < (1/2:ℝ) ∧
      (∀ᶠ u in atTop, 0 < Real.exp (-(4/3:ℝ)*u^(3/2:ℝ))/(16*Real.pi*u^(3/2:ℝ))) ∧
      (∀ᶠ u in atTop,
        (1-(1/2:ℝ))*(Real.exp (-(4/3:ℝ)*u^(3/2:ℝ))/(16*Real.pi*u^(3/2:ℝ))) ≤ 1-TW2R u ∧
        1-TW2R u ≤ (1+(1/2:ℝ))*(Real.exp (-(4/3:ℝ)*u^(3/2:ℝ))/(16*Real.pi*u^(3/2:ℝ)))) ∧
      |Real.log (TW2R s)+airyTraceIntegral s| ≤ 2*(airyTraceIntegral s)^2 := by
  have hg : ∀ᶠ u in atTop, 0 ≤ tailModel (1/(16*Real.pi)) (-3/2) (4/3) u := by
    filter_upwards [eventually_gt_atTop 0] with u hu
    unfold tailModel
    positivity
  have hb := rightTail_relative_bounds_of_isEquivalent airyTraceIntegral _
    airyTraceIntegral_isEquivalent hg (1/2) (by norm_num)
  have hsmall := airyTraceIntegral_tendsto_atTop_zero.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  obtain ⟨s,hs,hb,hsmall⟩ := ((eventually_gt_atTop (1:ℝ)).and (hb.and hsmall)).exists
  have hs0 : 0 < s := by linarith
  have hm : 0 < tailModel (1/(16*Real.pi)) (-3/2) (4/3) s := by
    unfold tailModel
    positivity
  have ht : 0 < airyTraceIntegral s := by
    have h := hb.1
    nlinarith
  have hmodelPos : ∀ᶠ u in atTop,
      0 < Real.exp (-(4/3:ℝ)*u^(3/2:ℝ))/(16*Real.pi*u^(3/2:ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with u hu
    positivity
  exact ⟨s,hs,(airyAiReal_pos hs0).ne',ht,hsmall.le,
    airyTraceIntegral_tendsto_atTop_zero,airyTraceIntegral_isEquivalent,
    TW2_rightTail_trace_error,TW2_rightTail_isEquivalent,by norm_num,hmodelPos,
    TW2_rightTail_sharp_bounds (1/2) (by norm_num),
    TW2_rightTail_logdet_quadratic s hsmall.le⟩

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW2_rightTail_isEquivalent
#print axioms RMTFoundations.TracyWidom.TW2_rightTail_ratio_tendsto_one
#print axioms RMTFoundations.TracyWidom.TW2_rightTail_sharp_bounds
#print axioms RMTFoundations.TracyWidom.TW2_rightTail_logdet_quadratic
#print axioms RMTFoundations.TracyWidom.TW2_rightTail_logdet_quadratic_eventually
#print axioms RMTFoundations.TracyWidom.TW2_rightTail_all_binder_joint_probe
