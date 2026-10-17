import RMTFoundations.TracyWidom.OrderOneBounds



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.AiryBoundaryContinuity

open MeasureTheory Filter
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds

/-- The cross inner product of actual Airy boundary rows is the actual Airy kernel. -/
theorem airyBoundaryVector_inner_cross
    (s t : ℝ) -- [definition]
    : inner ℝ (airyBoundaryVector s) (airyBoundaryVector t) = airyKernelIntegral s t := by
  rw [L2.inner_def]
  change (∫ x, inner ℝ ((airyBoundaryVector s) x) ((airyBoundaryVector t) x)
      ∂halfLineMeasure) = ∫ x, airyAiReal (s+x) * airyAiReal (t+x) ∂halfLineMeasure
  apply integral_congr_ae
  filter_upwards [airyBoundaryVector_apply_ae s, airyBoundaryVector_apply_ae t] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Polarization expresses actual L² row distance through scalar energy and kernel values. -/
theorem airyBoundaryVector_norm_sub_sq
    (s t : ℝ) -- [definition]
    : ‖airyBoundaryVector t - airyBoundaryVector s‖^2 =
        airyEnergy t + airyEnergy s - 2 * airyKernelIntegral t s := by
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    airyBoundaryVector_inner_self, airyBoundaryVector_inner_self,
    airyBoundaryVector_inner_cross, airyBoundaryVector_inner_cross,
    airyKernelIntegral_symm s t]
  ring

/-- The energy derivative gives genuine scalar continuity. -/
theorem airyEnergy_continuous : Continuous airyEnergy := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact (hasDerivAt_airyEnergy s).continuousAt

set_option maxHeartbeats 2000000 in
/-- Actual Airy boundary rows vary continuously in L² norm, without an added regularity premise. -/
theorem airyBoundaryVector_continuous : Continuous airyBoundaryVector := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun t => ‖airyBoundaryVector t - airyBoundaryVector s‖^2) := by
    have he : (fun t => ‖airyBoundaryVector t - airyBoundaryVector s‖^2) =
        (fun t => airyEnergy t + airyEnergy s - 2 * airyKernelIntegral t s) := by
      funext t
      exact airyBoundaryVector_norm_sub_sq s t
    rw [he]
    have hpair : Continuous (fun t : ℝ => (t, s)) :=
      continuous_id.prodMk continuous_const
    have hk : Continuous (fun t : ℝ => airyKernelIntegral t s) := by
      simpa only [Function.comp_def] using K_Ai_continuous.comp hpair
    exact (airyEnergy_continuous.add continuous_const).sub (continuous_const.mul hk)
  have hsq : Tendsto (fun t => ‖airyBoundaryVector t - airyBoundaryVector s‖^2)
      (𝓝 s) (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hc.tendsto s
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- The actual negative rank-one kernel derivative is continuous in operator norm. -/
theorem airyBoundaryRankOne_continuous :
    Continuous (fun s => -InnerProductSpace.rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) := by
  exact (((InnerProductSpace.rankOne ℝ).continuous.comp airyBoundaryVector_continuous).clm_apply
    airyBoundaryVector_continuous).neg

/-- The same nonzero actual Airy instance jointly realizes continuity and both scalar identities. -/
theorem airyBoundary_continuity_joint_probe :
    Continuous airyBoundaryVector ∧
      Continuous (fun s => -InnerProductSpace.rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) ∧
      0 < airyAiReal 0 ∧ airyBoundaryVector 0 ≠ 0 ∧
      inner ℝ (airyBoundaryVector 0) (airyBoundaryVector 0) = airyKernelIntegral 0 0 ∧
      ‖airyBoundaryVector 0‖^2 = airyEnergy 0 ∧ 0 < airyEnergy 0 :=
  ⟨airyBoundaryVector_continuous, airyBoundaryRankOne_continuous, airyAiReal_zero_pos,
    airyBoundaryVector_ne_zero 0, airyBoundaryVector_inner_cross 0 0,
    airyBoundaryVector_norm_sq 0, airyEnergy_pos 0⟩

end RMTFoundations.TracyWidom.AiryBoundaryContinuity

#print axioms RMTFoundations.TracyWidom.AiryBoundaryContinuity.airyBoundaryVector_inner_cross
#print axioms RMTFoundations.TracyWidom.AiryBoundaryContinuity.airyBoundaryVector_norm_sub_sq
#print axioms RMTFoundations.TracyWidom.AiryBoundaryContinuity.airyEnergy_continuous
#print axioms RMTFoundations.TracyWidom.AiryBoundaryContinuity.airyBoundaryVector_continuous
#print axioms RMTFoundations.TracyWidom.AiryBoundaryContinuity.airyBoundaryRankOne_continuous
#print axioms RMTFoundations.TracyWidom.AiryBoundaryContinuity.airyBoundary_continuity_joint_probe
