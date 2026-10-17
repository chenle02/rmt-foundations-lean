import RMTFoundations.TracyWidom.OrderOneMonotone
import RMTFoundations.TracyWidom.LeftTail


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Filter
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone RMTFoundations.TWLeftTail

noncomputable def TW1Density (s : ℝ /- [definition] -/) : ℝ :=
  TW1R s * (airyAiReal s + inner ℝ (airyBoundaryVector s)
    (Ring.inverse (1 - airyHankelShift s) (airyBoundaryVector s))) / 2

theorem TW1R_hasDerivAt
    (s : ℝ /- [definition] -/) : HasDerivAt TW1R (TW1Density s) s :=
  hasDerivAt_TW1R_canonical_resolvent s

theorem TW1R_differentiable : Differentiable ℝ TW1R :=
  fun s => (TW1R_hasDerivAt s).differentiableAt

theorem TW1R_log_derivative
    (s : ℝ /- [definition] -/) :
    HasDerivAt (fun t => Real.log (TW1R t))
      ((airyAiReal s + inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1 - airyHankelShift s) (airyBoundaryVector s))) / 2) s := by
  have h := (TW1R_hasDerivAt s).log (ne_of_gt (TW1R_positive_bounds s).1)
  convert h using 1
  unfold TW1Density
  field_simp [ne_of_gt (TW1R_positive_bounds s).1]

/-- The global sign theorem gives nonnegative density everywhere. -/
theorem TW1Density_nonneg
    (s : ℝ /- [definition] -/) : 0 ≤ TW1Density s :=
  div_nonneg (mul_nonneg (TW1R_positive_bounds s).1.le
    (airy_canonical_boundary_nonnegative s)) (by norm_num)

/-- Strict density is currently available on the nonnegative half-line. -/
theorem TW1Density_pos_nonnegative
    (s : ℝ /- [definition] -/)
    (hs : 0 ≤ s /- [standing] -/) : 0 < TW1Density s :=
  div_pos (mul_pos (TW1R_positive_bounds s).1
    (airy_hankel_inverse_boundary_pos_of_nonneg s hs)) (by norm_num)

/-- A faithful linear left-tail bound; the cubic tail requires additional analysis. -/
theorem TW2R_linear_left_tail
    (s : ℝ /- [definition] -/)
    (hs : s ≤ 0 /- [standing] -/) :
    TW2R s ≤ Real.exp (-originMass * |s|) := by
  have h := (TW2R_trace_bound_unconditional s).2
  have ht := airyTraceIntegral_linear_lower s hs
  apply h.trans
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonpos hs]
  nlinarith

theorem density_all_binder_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ 0 < TW1R 0 ∧
      HasDerivAt TW1R (TW1Density 0) 0 ∧ 0 < TW1Density 0 ∧
      HasDerivAt (fun t => Real.log (TW1R t))
        ((airyAiReal 0 + inner ℝ (airyBoundaryVector 0)
          (Ring.inverse (1 - airyHankelShift 0) (airyBoundaryVector 0))) / 2) 0 ∧
      (0:ℝ) < originMass ∧ TW2R (-1) ≤ Real.exp (-originMass * |(-1:ℝ)|) :=
  ⟨airyBoundaryVector_ne_zero 0, (TW1R_positive_bounds 0).1,
    TW1R_hasDerivAt 0, TW1Density_pos_nonnegative 0 (by norm_num),
    TW1R_log_derivative 0, originMass_pos, TW2R_linear_left_tail (-1) (by norm_num)⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW1Density
#print axioms RMTFoundations.TracyWidom.TW1R_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW1R_differentiable
#print axioms RMTFoundations.TracyWidom.TW1R_log_derivative
#print axioms RMTFoundations.TracyWidom.TW1Density_nonneg
#print axioms RMTFoundations.TracyWidom.TW1Density_pos_nonnegative
#print axioms RMTFoundations.TracyWidom.TW2R_linear_left_tail
#print axioms RMTFoundations.TracyWidom.density_all_binder_joint_probe
