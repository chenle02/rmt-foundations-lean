import RMTFoundations.TracyWidom.PhysicalPainleveII
import RMTFoundations.TracyWidom.PhysicalFirstOrderSystem
import RMTFoundations.TracyWidom.OrderTwoC1
import RMTFoundations.TracyWidom.StrictDensity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.TWDensityRegularity2
open scoped ContDiff
open RMTFoundations.TracyWidom
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.AiryBoundaryDerivative RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.EndpointCalculus RMTFoundations.TracyWidom.PhysicalPainleveII
open RMTFoundations.TracyWidom.OrderTwoLogDerivative
open RMTFoundations.TracyWidom.PhysicalFirstOrderSystem

/-- The genuine GUE density has its classical derivative on the entire line. -/
theorem hasDerivAt_TW2Density
    (s : ℝ /- [definition] -/) :
    HasDerivAt TW2Density (TW2R s * ((resolventU s)^2 - (resolventQ s)^2)) s := by
  have h := (TW2R_hasDerivAt s).mul (hasDerivAt_resolventU_negative_q_sq s)
  change HasDerivAt TW2Density _ s at h
  convert h using 1
  unfold TW2Density
  ring

/-- The derivative of the actual GUE density is continuous. -/
theorem continuous_deriv_TW2Density : Continuous (deriv TW2Density) := by
  have he : deriv TW2Density = fun s =>
      TW2R s * ((resolventU s)^2 - (resolventQ s)^2) :=
    funext fun s => (hasDerivAt_TW2Density s).deriv
  rw [he]
  have hq : Continuous resolventQ :=
    (show Differentiable ℝ resolventQ from
      fun s => (hasDerivAt_resolventQ s).differentiableAt).continuous
  exact TW2R_continuous.mul ((resolventU_continuous.pow 2).sub (hq.pow 2))

/-- The GUE density is C1, with no regularity premise. -/
theorem TW2Density_contDiff_one : ContDiff ℝ 1 TW2Density := by
  apply contDiff_one_iff_deriv.mpr
  exact ⟨fun s => (hasDerivAt_TW2Density s).differentiableAt,
    continuous_deriv_TW2Density⟩

/-- The actual GUE CDF is C2 on the full real line. -/
theorem TW2R_contDiff_two : ContDiff ℝ 2 TW2R := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨TW2R_differentiable, ?_, ?_⟩
  · simp
  · have he : deriv TW2R = TW2Density := funext fun s => (TW2R_hasDerivAt s).deriv
    rw [he]
    exact TW2Density_contDiff_one

/-- Negative, zero and positive physical rows jointly realize the derivative claims. -/
theorem density2_all_binder_joint_probe :
    airyBoundaryVector (-3) ≠ 0 ∧ airyBoundaryVector 0 ≠ 0 ∧
    airyBoundaryVector 3 ≠ 0 ∧ 0 < TW2Density (-3) ∧ 0 < TW2Density 0 ∧
    0 < TW2Density 3 ∧
    (∀ s : ℝ, HasDerivAt TW2Density
      (TW2R s * ((resolventU s)^2 - (resolventQ s)^2)) s) ∧
    ContDiff ℝ 1 TW2Density ∧ ContDiff ℝ 2 TW2R :=
  ⟨airyBoundaryVector_ne_zero (-3), airyBoundaryVector_ne_zero 0,
    airyBoundaryVector_ne_zero 3, TW2Density_positive (-3), TW2Density_positive 0,
    TW2Density_positive 3, hasDerivAt_TW2Density, TW2Density_contDiff_one, TW2R_contDiff_two⟩

end RMTFoundations.TracyWidom.TWDensityRegularity2

#print axioms RMTFoundations.TracyWidom.TWDensityRegularity2.hasDerivAt_TW2Density
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity2.continuous_deriv_TW2Density
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity2.TW2Density_contDiff_one
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity2.TW2R_contDiff_two
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity2.density2_all_binder_joint_probe
