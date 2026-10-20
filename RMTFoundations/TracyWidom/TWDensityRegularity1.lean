import RMTFoundations.TracyWidom.PhysicalPainleveII
import RMTFoundations.TracyWidom.PhysicalFirstOrderSystem
import RMTFoundations.TracyWidom.OrderTwoC1
import RMTFoundations.TracyWidom.StrictDensity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.TWDensityRegularity1
open scoped ContDiff
open RMTFoundations.TracyWidom
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.AiryBoundaryDerivative RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.EndpointCalculus RMTFoundations.TracyWidom.PhysicalPainleveII
open RMTFoundations.TracyWidom.OrderTwoLogDerivative
open RMTFoundations.TracyWidom.PhysicalFirstOrderSystem

/-- The genuine GOE density equals the canonical Painleve-coordinate expression. -/
theorem TW1Density_eq_coordinates
    (s : ℝ /- [definition] -/) :
    TW1Density s = TW1R s * (resolventQ s + resolventU s) / 2 :=
  (TW1R_hasDerivAt s).unique (hasDerivAt_TW1R_coordinates s)

/-- The actual GOE density has a derivative, including the negative-shift region. -/
theorem hasDerivAt_TW1Density
    (s : ℝ /- [definition] -/) :
    HasDerivAt TW1Density
      ((TW1Density s * (resolventQ s + resolventU s) +
        TW1R s * (resolventP s - resolventU s * resolventQ s - (resolventQ s)^2)) / 2) s := by
  have he : (fun t => TW1R t * (resolventQ t + resolventU t) / 2) = TW1Density :=
    funext fun t => (TW1Density_eq_coordinates t).symm
  have h := ((TW1R_hasDerivAt s).mul
    ((hasDerivAt_resolventQ s).add (hasDerivAt_resolventU_negative_q_sq s))).div_const 2
  change HasDerivAt (fun t => TW1R t * (resolventQ t + resolventU t) / 2) _ s at h
  simp only [Pi.add_apply] at h
  rw [he] at h
  convert h using 1 <;> ring

/-- The GOE density derivative is continuous by actual endpoint calculus. -/
theorem continuous_deriv_TW1Density : Continuous (deriv TW1Density) := by
  have he : deriv TW1Density = fun s =>
      (TW1Density s * (resolventQ s + resolventU s) +
        TW1R s * (resolventP s - resolventU s * resolventQ s - (resolventQ s)^2)) / 2 :=
    funext fun s => (hasDerivAt_TW1Density s).deriv
  rw [he]
  have hq : Continuous resolventQ :=
    (show Differentiable ℝ resolventQ from
      fun s => (hasDerivAt_resolventQ s).differentiableAt).continuous
  have hp : Continuous resolventP :=
    (show Differentiable ℝ resolventP from
      fun s => (hasDerivAt_resolventP s).differentiableAt).continuous
  exact ((TW1Density_continuous.mul (hq.add resolventU_continuous)).add
    (TW1R_continuous.mul ((hp.sub (resolventU_continuous.mul hq)).sub (hq.pow 2)))).div_const 2

/-- The GOE density is C1 globally. -/
theorem TW1Density_contDiff_one : ContDiff ℝ 1 TW1Density := by
  apply contDiff_one_iff_deriv.mpr
  exact ⟨fun s => (hasDerivAt_TW1Density s).differentiableAt,
    continuous_deriv_TW1Density⟩

/-- The actual GOE CDF is C2 on the full real line. -/
theorem TW1R_contDiff_two : ContDiff ℝ 2 TW1R := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨TW1R_differentiable, ?_, ?_⟩
  · simp
  · have he : deriv TW1R = TW1Density := funext fun s => (TW1R_hasDerivAt s).deriv
    rw [he]
    exact TW1Density_contDiff_one

/-- All inputs hold in the same genuine physical model across the sign branches. -/
theorem density1_all_binder_joint_probe :
    airyBoundaryVector (-6) ≠ 0 ∧ airyBoundaryVector 0 ≠ 0 ∧
    airyBoundaryVector 3 ≠ 0 ∧ 0 < TW1Density (-6) ∧ 0 < TW1Density 0 ∧
    0 < TW1Density 3 ∧
    (∀ s : ℝ, TW1Density s = TW1R s * (resolventQ s + resolventU s) / 2) ∧
    (∀ s : ℝ, HasDerivAt TW1Density
      ((TW1Density s * (resolventQ s + resolventU s) +
        TW1R s * (resolventP s - resolventU s * resolventQ s - (resolventQ s)^2)) / 2) s) ∧
    ContDiff ℝ 1 TW1Density ∧ ContDiff ℝ 2 TW1R :=
  ⟨airyBoundaryVector_ne_zero (-6), airyBoundaryVector_ne_zero 0,
    airyBoundaryVector_ne_zero 3, TW1Density_positive (-6), TW1Density_positive 0,
    TW1Density_positive 3, TW1Density_eq_coordinates, hasDerivAt_TW1Density,
    TW1Density_contDiff_one, TW1R_contDiff_two⟩

end RMTFoundations.TracyWidom.TWDensityRegularity1

#print axioms RMTFoundations.TracyWidom.TWDensityRegularity1.TW1Density_eq_coordinates
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity1.hasDerivAt_TW1Density
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity1.continuous_deriv_TW1Density
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity1.TW1Density_contDiff_one
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity1.TW1R_contDiff_two
#print axioms RMTFoundations.TracyWidom.TWDensityRegularity1.density1_all_binder_joint_probe
