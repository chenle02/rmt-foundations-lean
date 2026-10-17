import RMTFoundations.TracyWidom.DensityTail
import RMTFoundations.Airy.Continuity
import RMTFoundations.Airy.KernelDeterminant


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryBounds
open RMTFoundations.TWOneBounds RMTFoundations.AiryKernel RMTFoundations.AiryContinuity

theorem continuous_curve_of_continuous_gram
    {X E : Type* /- [definition] -/}
    [TopologicalSpace X /- [standing] -/]
    [NormedAddCommGroup E /- [standing] -/]
    [InnerProductSpace ℝ E /- [standing] -/]
    (u : X → E /- [definition] -/)
    (k : X × X → ℝ /- [definition] -/)
    (hk : Continuous k /- [standing] -/)
    (hpair : ∀ s t, inner ℝ (u s) (u t) = k (s,t) /- [standing] -/) :
    Continuous u := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hid : ∀ s, ‖u s-u t‖^2 = k (s,s)-k (s,t)-k (t,s)+k (t,t) := by
    intro s
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [hpair]
    ring
  have hc : Continuous (fun s => ‖u s-u t‖^2) := by
    have h : Continuous (fun s => k (s,s)-k (s,t)-k (t,s)+k (t,t)) :=
      (((hk.comp (continuous_id.prodMk continuous_id)).sub
      (hk.comp (continuous_id.prodMk continuous_const))).sub
      (hk.comp (continuous_const.prodMk continuous_id))).add continuous_const
    exact h.congr fun s => (hid s).symm
  have hs := (Real.continuous_sqrt.comp hc).tendsto t
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, sub_self, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), Real.sqrt_zero] using hs

theorem boundary_inner_kernel
    (s t : ℝ /- [definition] -/) :
    inner ℝ (airyBoundaryVector s) (airyBoundaryVector t) = airyKernelIntegral s t := by
  rw [L2.inner_def]
  unfold airyKernelIntegral
  apply integral_congr_ae
  filter_upwards [airyBoundaryVector_apply_ae s, airyBoundaryVector_apply_ae t] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]

theorem boundaryVector_continuous : Continuous airyBoundaryVector :=
  continuous_curve_of_continuous_gram airyBoundaryVector
    (fun q => airyKernelIntegral q.1 q.2) K_Ai_continuous boundary_inner_kernel

theorem hankel_continuous : Continuous airyHankelShift := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : ∀ s, ‖airyHankelShift s-airyHankelShift t‖ₑ ≤
      edist (airyKernelLp s) (airyKernelLp t) := by
    intro s
    have h := enorm_kernelOperator_le
      ((memLp_airyHankelShiftKernel s).sub (memLp_airyHankelShiftKernel t))
    rw [kernelOperator_sub _ _ (memLp_airyHankelShiftKernel s)
      (memLp_airyHankelShiftKernel t)] at h
    simpa only [airyHankelShift, airyKernelLp, Ai_kernelLp, Lp.edist_toLp_toLp,
      airyHankelShiftKernel_eq_Ai_kernel] using h
  have h := (airyKernelLp_continuous.tendsto t).edist
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => airyKernelLp t) (𝓝 t) (𝓝 (airyKernelLp t)))
  simp only [edist_self] at h
  have he : Tendsto (fun s => ‖airyHankelShift s-airyHankelShift t‖ₑ) (𝓝 t) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall hb)
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  simpa only [Function.comp_def, ENNReal.toReal_zero, toReal_enorm] using hr

theorem hankel_resolvent_continuous :
    Continuous (fun s => Ring.inverse (1-airyHankelShift s)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hi : ContinuousAt Ring.inverse (1-airyHankelShift t) := by
    simpa only [Units.val_oneSub] using
      NormedRing.inverse_continuousAt (Units.oneSub (airyHankelShift t) (norm_airyHankelShift_lt_one t))
  have hsub : ContinuousAt (fun s : ℝ => 1-airyHankelShift s) t :=
    (continuous_const.sub hankel_continuous).continuousAt
  exact hi.comp (f := fun s : ℝ => 1-airyHankelShift s) hsub

theorem TW1Density_continuous : Continuous TW1Density := by
  unfold TW1Density
  exact (TW1R_continuous.mul (Ai_continuous.add
    (boundaryVector_continuous.inner
      (hankel_resolvent_continuous.clm_apply boundaryVector_continuous)))).div_const 2

theorem TW1R_contDiff_one : ContDiff ℝ 1 TW1R := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨TW1R_differentiable, ?_⟩
  have he : deriv TW1R = TW1Density := funext fun s => (TW1R_hasDerivAt s).deriv
  rw [he]
  exact TW1Density_continuous

theorem C1_all_binder_joint_probe :
    (∀ s t, inner ℝ (airyBoundaryVector s) (airyBoundaryVector t) = airyKernelIntegral s t) ∧
    Continuous (fun q : ℝ × ℝ => airyKernelIntegral q.1 q.2) ∧
    airyBoundaryVector 0 ≠ 0 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
    Continuous airyBoundaryVector ∧ Continuous airyHankelShift ∧
    Continuous (fun s => Ring.inverse (1-airyHankelShift s)) ∧
    Continuous TW1Density ∧ ContDiff ℝ 1 TW1R ∧ 0 < TW1Density 0 :=
  ⟨boundary_inner_kernel, K_Ai_continuous, airyBoundaryVector_ne_zero 0,
    shiftedUnitVector_norm 0, boundaryVector_continuous, hankel_continuous,
    hankel_resolvent_continuous, TW1Density_continuous, TW1R_contDiff_one,
    TW1Density_pos_nonnegative 0 (by norm_num)⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.continuous_curve_of_continuous_gram
#print axioms RMTFoundations.TracyWidom.boundary_inner_kernel
#print axioms RMTFoundations.TracyWidom.boundaryVector_continuous
#print axioms RMTFoundations.TracyWidom.hankel_continuous
#print axioms RMTFoundations.TracyWidom.hankel_resolvent_continuous
#print axioms RMTFoundations.TracyWidom.TW1Density_continuous
#print axioms RMTFoundations.TracyWidom.TW1R_contDiff_one
#print axioms RMTFoundations.TracyWidom.C1_all_binder_joint_probe
