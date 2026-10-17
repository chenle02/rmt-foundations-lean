import RMTFoundations.TracyWidom.Functions
import RMTFoundations.TracyWidom.OrderOneMonotone
import RMTFoundations.TracyWidom.LeftTail
import RMTFoundations.TracyWidom.OrderTwo

/-! Distribution-function properties with all analytic premises discharged upstream. -/
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

/-- GOE monotonicity at every real cutoff, including the oscillatory Airy region. -/
theorem monotone_TW1R : Monotone TW1R := RMTFoundations.TWOneMonotone.monotone_TW1R
/-- GUE monotonicity from positive Airy-kernel compression determinants. -/
theorem monotone_TW2R : Monotone TW2R := RMTFoundations.AiryBounds.TW2R_monotone
/-- The real GOE function tends to zero at the left endpoint. -/
theorem tendsto_TW1R_atBot : Tendsto TW1R atBot (𝓝 0) :=
  RMTFoundations.TWLeftTail.TW1R_tendsto_atBot_zero_unconditional
/-- The real GUE function tends to zero at the left endpoint. -/
theorem tendsto_TW2R_atBot : Tendsto TW2R atBot (𝓝 0) :=
  RMTFoundations.TWLeftTail.TW2R_tendsto_atBot_zero_unconditional
/-- The real GOE function tends to one at the right endpoint. -/
theorem tendsto_TW1R_atTop : Tendsto TW1R atTop (𝓝 1) :=
  RMTFoundations.AiryKernel.TW1R_tendsto_atTop_one
/-- The real GUE function tends to one at the right endpoint. -/
theorem tendsto_TW2R_atTop : Tendsto TW2R atTop (𝓝 1) :=
  RMTFoundations.AiryKernel.TW2R_tendsto_atTop_one
/-- Strict GOE bounds at every finite cutoff. -/
theorem TW1R_bounds (s : ℝ /- [definition] -/) : 0 < TW1R s ∧ TW1R s < 1 :=
  ⟨(RMTFoundations.TWOneBounds.TW1R_positive_bounds s).1, RMTFoundations.TWOneBounds.TW1R_lt_one s⟩
/-- GUE values lie in the closed unit interval. -/
theorem TW2R_bounds (s : ℝ /- [definition] -/) : TW2R s ∈ Icc (0 : ℝ) 1 :=
  RMTFoundations.AiryBounds.TW2R_mem_Icc s
/-- Certified GOE exponential upper bound from the integrated Airy tail. -/
theorem TW1R_le_exp_tail (s : ℝ /- [definition] -/) :
    TW1R s ≤ Real.exp (-(RMTFoundations.TWOneBounds.airyTailIntegral
      RMTFoundations.Airy.airyAiReal s / 2)) :=
  (RMTFoundations.TWOneBounds.TW1R_positive_bounds s).2.1
/-- Certified GUE exponential trace bound; this is not a sharp tail asymptotic. -/
theorem TW2R_le_exp_trace (s : ℝ /- [definition] -/) :
    TW2R s ≤ Real.exp (-RMTFoundations.TWLeftTail.airyTraceIntegral s) :=
  (RMTFoundations.TWLeftTail.TW2R_trace_bound_unconditional s).2
/-- Canonical GOE derivative-resolvent identity in the actual Airy Hilbert space. -/
theorem hasDerivAt_TW1R_canonical_resolvent (s : ℝ /- [definition] -/) :
    HasDerivAt TW1R
      (TW1R s * (RMTFoundations.Airy.airyAiReal s +
        inner ℝ (RMTFoundations.TWOneBounds.airyBoundaryVector s)
          (Ring.inverse (1 - RMTFoundations.Airy.airyHankelShift s)
            (RMTFoundations.TWOneBounds.airyBoundaryVector s))) / 2) s :=
  RMTFoundations.TWOneMonotone.hasDerivAt_TW1R_canonical_resolvent s
/-- Every CDF property holds together on genuine nonzero Airy data. -/
theorem distribution_all_binder_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
      ‖RMTFoundations.Airy.shiftedUnitVector 0‖ = 1 ∧
      Monotone TW1R ∧ Monotone TW2R ∧ Continuous TW1R ∧ Continuous TW2R ∧
      Tendsto TW1R atBot (𝓝 0) ∧ Tendsto TW2R atBot (𝓝 0) ∧
      Tendsto TW1R atTop (𝓝 1) ∧ Tendsto TW2R atTop (𝓝 1) ∧
      (∀ s : ℝ, 0 < TW1R s ∧ TW1R s < 1 ∧ TW2R s ∈ Icc (0 : ℝ) 1) := by
  exact ⟨RMTFoundations.Airy.airyAiReal_zero_pos.ne',
    RMTFoundations.Airy.shiftedUnitVector_norm 0,
    monotone_TW1R, monotone_TW2R, continuous_TW1R, continuous_TW2R,
    tendsto_TW1R_atBot, tendsto_TW2R_atBot, tendsto_TW1R_atTop, tendsto_TW2R_atTop,
    fun s => ⟨(TW1R_bounds s).1, (TW1R_bounds s).2, TW2R_bounds s⟩⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.monotone_TW1R
#print axioms RMTFoundations.TracyWidom.monotone_TW2R
#print axioms RMTFoundations.TracyWidom.tendsto_TW1R_atBot
#print axioms RMTFoundations.TracyWidom.tendsto_TW2R_atBot
#print axioms RMTFoundations.TracyWidom.tendsto_TW1R_atTop
#print axioms RMTFoundations.TracyWidom.tendsto_TW2R_atTop
#print axioms RMTFoundations.TracyWidom.TW1R_bounds
#print axioms RMTFoundations.TracyWidom.TW2R_bounds
#print axioms RMTFoundations.TracyWidom.TW1R_le_exp_tail
#print axioms RMTFoundations.TracyWidom.TW2R_le_exp_trace
#print axioms RMTFoundations.TracyWidom.hasDerivAt_TW1R_canonical_resolvent
#print axioms RMTFoundations.TracyWidom.distribution_all_binder_joint_probe
