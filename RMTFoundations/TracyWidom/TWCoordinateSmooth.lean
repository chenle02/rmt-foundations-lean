import RMTFoundations.TracyWidom.PhysicalPainleveII
import RMTFoundations.TracyWidom.PhysicalFirstOrderSystem
import RMTFoundations.TracyWidom.OrderTwoC1
import RMTFoundations.TracyWidom.StrictDensity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.TWCoordinateSmooth
open scoped ContDiff
open RMTFoundations.TracyWidom
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.AiryBoundaryDerivative RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.EndpointCalculus RMTFoundations.TracyWidom.PhysicalPainleveII
open RMTFoundations.TracyWidom.OrderTwoLogDerivative
open RMTFoundations.TracyWidom.PhysicalFirstOrderSystem

/-- Every finite differentiability order for the actual polynomial endpoint system. -/
theorem coordinates_contDiff_nat
    (n : ℕ /- [definition] -/) :
    ContDiff ℝ n resolventQ ∧ ContDiff ℝ n resolventP ∧
      ContDiff ℝ n resolventU ∧ ContDiff ℝ n resolventV := by
  have dq : Differentiable ℝ resolventQ := fun s => (hasDerivAt_resolventQ s).differentiableAt
  have dp : Differentiable ℝ resolventP := fun s => (hasDerivAt_resolventP s).differentiableAt
  have du : Differentiable ℝ resolventU := fun s => (hasDerivAt_resolventU_negative_q_sq s).differentiableAt
  have dv : Differentiable ℝ resolventV := fun s => (hasDerivAt_resolventV s).differentiableAt
  induction n with
  | zero =>
    exact ⟨contDiff_zero.mpr dq.continuous, contDiff_zero.mpr dp.continuous,
      contDiff_zero.mpr du.continuous, contDiff_zero.mpr dv.continuous⟩
  | succ n ih =>
    rcases ih with ⟨hq,hp,hu,hv⟩
    have eqQ : deriv resolventQ = fun s => resolventP s - resolventU s * resolventQ s :=
      funext fun s => (hasDerivAt_resolventQ s).deriv
    have eqP : deriv resolventP = fun s =>
        s * resolventQ s + resolventU s * resolventP s - 2 * resolventV s * resolventQ s :=
      funext fun s => (hasDerivAt_resolventP s).deriv
    have eqU : deriv resolventU = fun s => -(resolventQ s)^2 :=
      funext fun s => (hasDerivAt_resolventU_negative_q_sq s).deriv
    have eqV : deriv resolventV = fun s => -(resolventP s * resolventQ s) :=
      funext fun s => (hasDerivAt_resolventV s).deriv
    simp only [Nat.cast_succ]
    refine ⟨contDiff_succ_iff_deriv.mpr ⟨dq, ?_, ?_⟩,
      contDiff_succ_iff_deriv.mpr ⟨dp, ?_, ?_⟩,
      contDiff_succ_iff_deriv.mpr ⟨du, ?_, ?_⟩,
      contDiff_succ_iff_deriv.mpr ⟨dv, ?_, ?_⟩⟩
    · simp
    · rw [eqQ]
      exact hp.sub (hu.mul hq)
    · simp
    · rw [eqP]
      exact ((contDiff_id.mul hq).add (hu.mul hp)).sub ((contDiff_const.mul hv).mul hq)
    · simp
    · rw [eqU]
      exact (hq.pow 2).neg
    · simp
    · rw [eqV]
      exact (hp.mul hq).neg

/-- Smoothness is derived by bootstrapping the genuine system, not assumed. -/
theorem coordinates_contDiff_infty :
    ContDiff ℝ ∞ resolventQ ∧ ContDiff ℝ ∞ resolventP ∧
      ContDiff ℝ ∞ resolventU ∧ ContDiff ℝ ∞ resolventV :=
  ⟨contDiff_infty.mpr (fun n => (coordinates_contDiff_nat n).1),
    contDiff_infty.mpr (fun n => (coordinates_contDiff_nat n).2.1),
    contDiff_infty.mpr (fun n => (coordinates_contDiff_nat n).2.2.1),
    contDiff_infty.mpr (fun n => (coordinates_contDiff_nat n).2.2.2)⟩

/-- All orders and all coordinates coexist in the actual nonzero Airy model. -/
theorem coordinate_smooth_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧
    responseVector 0 ≠ 0 ∧ 0 < resolventU 0 ∧
    (∀ n : ℕ, ContDiff ℝ n resolventQ ∧ ContDiff ℝ n resolventP ∧
      ContDiff ℝ n resolventU ∧ ContDiff ℝ n resolventV) ∧
    ContDiff ℝ ∞ resolventQ ∧ ContDiff ℝ ∞ resolventP ∧
      ContDiff ℝ ∞ resolventU ∧ ContDiff ℝ ∞ resolventV :=
  ⟨airyBoundaryVector_ne_zero 0, airyBoundaryDerivative_zero_ne,
    response_derivative_all_binder_joint_probe.2.2.1, airy_inverse_square_boundary_positive 0,
    coordinates_contDiff_nat, coordinates_contDiff_infty⟩

end RMTFoundations.TracyWidom.TWCoordinateSmooth

#print axioms RMTFoundations.TracyWidom.TWCoordinateSmooth.coordinates_contDiff_nat
#print axioms RMTFoundations.TracyWidom.TWCoordinateSmooth.coordinates_contDiff_infty
#print axioms RMTFoundations.TracyWidom.TWCoordinateSmooth.coordinate_smooth_all_binder_joint_probe
