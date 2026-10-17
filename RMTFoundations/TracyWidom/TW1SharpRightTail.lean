import RMTFoundations.TracyWidom.TW1RightTail
import RMTFoundations.TracyWidom.TWSharpAiryTails
import RMTFoundations.TracyWidom.RightTailRelativeBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom
open MeasureTheory Filter Asymptotics
open scoped Topology Asymptotics
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds RMTFoundations.TWLeftTail

/-- Literal physical signed-trace bridge; no spectral or integral binder. -/
theorem signedTrace_eq_hankelSignedTrace
    (s : ℝ /- [definition] -/) :
    trace (airyHankelShift s) = hankelSignedTrace s := by
  rw [trace_airyHankelShift_eq_diagonal]
  exact hankelSignedTrace_diagonal s

/-- Literal physical square-trace bridge. -/
theorem squareTrace_eq_airyTraceIntegral
    (s : ℝ /- [definition] -/) :
    trace (airyKernelShift s) = airyTraceIntegral s := by
  exact trace_airyKernelShift_eq_tail s

theorem TW1R_tail_div_signedTrace_tendsto_one :
    Tendsto (fun s => (1 - TW1R s) / hankelSignedTrace s) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun s => trace (airyKernelShift s) / trace (airyHankelShift s))
      atTop (𝓝 0) := by
    simpa only [squareTrace_eq_airyTraceIntegral, signedTrace_eq_hankelSignedTrace] using
      trace_div_signedTrace_tendsto_zero
  simpa only [signedTrace_eq_hankelSignedTrace] using
    TW1R_tail_ratio_of_square_trace_ratio hsmall

theorem TW1R_sharp_right_tail :
    (fun s => 1 - TW1R s) ~[atTop]
      tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3) := by
  have h : (fun s => 1 - TW1R s) ~[atTop] hankelSignedTrace :=
    isEquivalent_of_tendsto_one TW1R_tail_div_signedTrace_tendsto_one
  exact h.trans hankelSignedTrace_isEquivalent

theorem TW1R_sharp_right_tail_ratio :
    Tendsto (fun s => (1 - TW1R s) /
      tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3) s) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one ?_).mp TW1R_sharp_right_tail
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  unfold tailModel
  positivity

theorem TW1R_sharp_right_tail_relative_bounds
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ s : ℝ in atTop,
      (1 - ε) * tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3) s ≤ 1 - TW1R s ∧
      1 - TW1R s ≤ (1 + ε) * tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3) s := by
  apply rightTail_relative_bounds_of_isEquivalent (fun s => 1 - TW1R s)
    (tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3)) TW1R_sharp_right_tail _ ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  unfold tailModel
  positivity


/-- Requested F1 normalization with its literal exponential and denominator. -/
theorem TW1_rightTail_isEquivalent :
    (fun s => 1 - TW1R s) ~[atTop]
      (fun s => Real.exp (-(2 / 3 : ℝ) * s ^ (3 / 2 : ℝ)) /
        (4 * Real.sqrt Real.pi * s ^ (3 / 4 : ℝ))) := by
  refine TW1R_sharp_right_tail.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  dsimp [tailModel]
  rw [show (-3 / 4 : ℝ) = -(3 / 4 : ℝ) by norm_num, Real.rpow_neg hs.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem TW1_rightTail_ratio_tendsto_one :
    Tendsto (fun s => (1 - TW1R s) /
      (Real.exp (-(2 / 3 : ℝ) * s ^ (3 / 2 : ℝ)) /
        (4 * Real.sqrt Real.pi * s ^ (3 / 4 : ℝ)))) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one ?_).mp TW1_rightTail_isEquivalent
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (show 0 < Real.exp (-(2 / 3 : ℝ) * s ^ (3 / 2 : ℝ)) /
    (4 * Real.sqrt Real.pi * s ^ (3 / 4 : ℝ)) by positivity).ne'

theorem TW1_rightTail_sharp_bounds
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ s : ℝ in atTop,
      (1 - ε) * (Real.exp (-(2 / 3 : ℝ) * s ^ (3 / 2 : ℝ)) /
        (4 * Real.sqrt Real.pi * s ^ (3 / 4 : ℝ))) ≤ 1 - TW1R s ∧
      1 - TW1R s ≤ (1 + ε) * (Real.exp (-(2 / 3 : ℝ) * s ^ (3 / 2 : ℝ)) /
        (4 * Real.sqrt Real.pi * s ^ (3 / 4 : ℝ))) := by
  apply rightTail_relative_bounds_of_isEquivalent _ _ TW1_rightTail_isEquivalent _ ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  positivity

/-- All analytic and determinant inputs occur together on the genuine Airy law. -/
theorem TW1R_sharp_right_tail_all_binder_joint_probe :
    ∃ s : ℝ,
      ‖airyHankelShift s‖ ≤ (1 / 2 : ℝ) ∧ airyAiReal 0 > 0 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      trace (airyHankelShift s) = hankelSignedTrace s ∧
      trace (airyKernelShift s) = airyTraceIntegral s ∧
      (∀ᶠ t : ℝ in atTop, 0 < trace (airyHankelShift t)) ∧
      (∀ᶠ t : ℝ in atTop,
        trace (airyHankelShift t) / (1 + trace (airyHankelShift t)) ≤ 1 - TW1R t ∧
        1 - TW1R t ≤ trace (airyHankelShift t) + 2 * trace (airyKernelShift t)) ∧
      Tendsto (fun t => trace (airyHankelShift t)) atTop (𝓝 0) ∧
      Tendsto (fun t => trace (airyKernelShift t) / trace (airyHankelShift t)) atTop (𝓝 0) ∧
      (hankelSignedTrace ~[atTop] tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3)) ∧
      ((fun t => 1 - TW1R t) ~[atTop] tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3)) ∧
      (∀ᶠ t : ℝ in atTop, 0 ≤ tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3) t) ∧
      Tendsto (fun t => (1 - TW1R t) /
        tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3) t) atTop (𝓝 1) ∧
      ((fun t => 1 - TW1R t) ~[atTop] (fun t => Real.exp (-(2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) /
        (4 * Real.sqrt Real.pi * t ^ (3 / 4 : ℝ)))) ∧
      Tendsto (fun t => (1 - TW1R t) /
        (Real.exp (-(2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) /
          (4 * Real.sqrt Real.pi * t ^ (3 / 4 : ℝ)))) atTop (𝓝 1) ∧
      (0 : ℝ) < 1 / 4 ∧
      (∀ᶠ t : ℝ in atTop,
        (1 - (1 / 4 : ℝ)) * tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3) t ≤ 1 - TW1R t ∧
        1 - TW1R t ≤ (1 + (1 / 4 : ℝ)) * tailModel (1 / (4 * Real.sqrt Real.pi)) (-3 / 4) (2 / 3) t) ∧
      (∀ᶠ t : ℝ in atTop, 0 ≤ Real.exp (-(2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) /
        (4 * Real.sqrt Real.pi * t ^ (3 / 4 : ℝ))) ∧
      (∀ᶠ t : ℝ in atTop,
        (1 - (1 / 4 : ℝ)) * (Real.exp (-(2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) /
          (4 * Real.sqrt Real.pi * t ^ (3 / 4 : ℝ))) ≤ 1 - TW1R t ∧
        1 - TW1R t ≤ (1 + (1 / 4 : ℝ)) * (Real.exp (-(2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) /
          (4 * Real.sqrt Real.pi * t ^ (3 / 4 : ℝ)))) := by
  obtain ⟨s, hs, hAi, hu, _⟩ := TW1R_right_tail_all_binder_joint_probe
  have hp : ∀ᶠ t : ℝ in atTop, 0 < trace (airyHankelShift t) :=
    Eventually.of_forall (fun t => by
      rw [trace_airyHankelShift_eq_half_tail]
      exact mul_pos (by norm_num) (airy_tail_positive t))
  have ht : Tendsto (fun t => trace (airyHankelShift t)) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => ∫ x in Set.Ioi t, airyAiReal x) atTop (𝓝 0) :=
      tendsto_integral_Ioi_zero tendsto_id
    simpa only [trace_airyHankelShift_eq_half_tail, mul_zero] using h.const_mul (1 / 2 : ℝ)
  have hsmall : Tendsto (fun t => trace (airyKernelShift t) / trace (airyHankelShift t))
      atTop (𝓝 0) := by
    simpa only [squareTrace_eq_airyTraceIntegral, signedTrace_eq_hankelSignedTrace] using
      trace_div_signedTrace_tendsto_zero
  exact ⟨s, hs, hAi, hu, signedTrace_eq_hankelSignedTrace s, squareTrace_eq_airyTraceIntegral s,
    hp, TW1R_tail_trace_sandwich_eventually, ht, hsmall, hankelSignedTrace_isEquivalent,
    TW1R_sharp_right_tail, (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      unfold tailModel
      positivity), TW1R_sharp_right_tail_ratio, TW1_rightTail_isEquivalent, TW1_rightTail_ratio_tendsto_one, by norm_num,
    TW1R_sharp_right_tail_relative_bounds (1 / 4) (by norm_num), (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      positivity), TW1_rightTail_sharp_bounds (1 / 4) (by norm_num)⟩

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.signedTrace_eq_hankelSignedTrace
#print axioms RMTFoundations.TracyWidom.squareTrace_eq_airyTraceIntegral
#print axioms RMTFoundations.TracyWidom.TW1R_tail_div_signedTrace_tendsto_one
#print axioms RMTFoundations.TracyWidom.TW1R_sharp_right_tail
#print axioms RMTFoundations.TracyWidom.TW1R_sharp_right_tail_ratio
#print axioms RMTFoundations.TracyWidom.TW1R_sharp_right_tail_relative_bounds
#print axioms RMTFoundations.TracyWidom.TW1R_sharp_right_tail_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.TW1_rightTail_isEquivalent
#print axioms RMTFoundations.TracyWidom.TW1_rightTail_ratio_tendsto_one
#print axioms RMTFoundations.TracyWidom.TW1_rightTail_sharp_bounds
