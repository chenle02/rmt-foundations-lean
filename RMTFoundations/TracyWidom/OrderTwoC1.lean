import RMTFoundations.TracyWidom.OrderTwoLogDerivative
import RMTFoundations.TracyWidom.Probability


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory
open scoped InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.OrderTwoLogDerivative
open RMTFoundations.AiryContinuity

/-- The density of the actual GUE Fredholm distribution, with canonical square resolvent. -/
noncomputable def TW2Density (s : ℝ /- [definition] -/) : ℝ := TW2R s * resolventU s

theorem TW2R_hasDerivAt (s : ℝ /- [definition] -/) :
    HasDerivAt TW2R (TW2Density s) s := hasDerivAt_TW2R_coordinates s

theorem TW2R_differentiable : Differentiable ℝ TW2R :=
  fun s => (TW2R_hasDerivAt s).differentiableAt

/-- All shifts have strictly positive density, since the physical boundary vector is nonzero. -/
theorem TW2Density_positive (s : ℝ /- [definition] -/) : 0 < TW2Density s :=
  mul_pos (RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive s) (airy_inverse_square_boundary_positive s)

theorem TW2R_log_derivative (s : ℝ /- [definition] -/) :
    HasDerivAt (fun t => Real.log (TW2R t))
      (inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s))) s :=
  hasDerivAt_log_TW2R_coordinates s

theorem TW2Density_continuous : Continuous TW2Density :=
  TW2R_continuous.mul resolventU_continuous

/-- The actual GUE CDF is continuously differentiable at every real shift. -/
theorem TW2R_contDiff_one : ContDiff ℝ 1 TW2R := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨TW2R_differentiable, ?_⟩
  have he : deriv TW2R = TW2Density := funext fun s => (TW2R_hasDerivAt s).deriv
  rw [he]
  exact TW2Density_continuous

theorem TW2R_strictMono : StrictMono TW2R := by
  apply strictMono_of_deriv_pos
  intro s
  rw [(TW2R_hasDerivAt s).deriv]
  exact TW2Density_positive s

/-- Every interior probability has exactly one actual GUE quantile. -/
theorem TW2R_quantile_exists_unique
    (q : ℝ /- [definition] -/)
    (hq0 : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : ∃! s, TW2R s = q := by
  obtain ⟨s,hs⟩ := TW2R_quantile_exists q hq0 hq1
  exact ⟨s,hs,fun t ht => TW2R_strictMono.injective (ht.trans hs.symm)⟩

theorem TW2R_median_exists_unique : ∃! s, TW2R s = 1/2 :=
  TW2R_quantile_exists_unique (1/2) (by norm_num) (by norm_num)

/-- Negative shifts exercise the physical square resolvent and noncollapsed quantile interval. -/
theorem TW2C1_all_binder_joint_probe :
    airyBoundaryVector (-3) ≠ 0 ∧ 0 < TW2R (-3) ∧ 0 < resolventU (-3) ∧
    HasDerivAt TW2R (TW2Density (-3)) (-3) ∧ 0 < TW2Density (-3) ∧
    HasDerivAt (fun t => Real.log (TW2R t))
      (inner ℝ (airyBoundaryVector (-3))
        (Ring.inverse (1-airyKernelShift (-3)) (airyBoundaryVector (-3)))) (-3) ∧
    ContDiff ℝ 1 TW2R ∧ Continuous TW2Density ∧ StrictMono TW2R ∧
    (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ (∃! s, TW2R s = 1/2) :=
  ⟨airyBoundaryVector_ne_zero (-3),RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive (-3),airy_inverse_square_boundary_positive (-3),
    TW2R_hasDerivAt (-3),TW2Density_positive (-3),TW2R_log_derivative (-3),TW2R_contDiff_one,
    TW2Density_continuous,TW2R_strictMono,by norm_num,by norm_num,TW2R_median_exists_unique⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW2Density
#print axioms RMTFoundations.TracyWidom.TW2R_hasDerivAt
#print axioms RMTFoundations.TracyWidom.TW2R_differentiable
#print axioms RMTFoundations.TracyWidom.TW2Density_positive
#print axioms RMTFoundations.TracyWidom.TW2R_log_derivative
#print axioms RMTFoundations.TracyWidom.TW2Density_continuous
#print axioms RMTFoundations.TracyWidom.TW2R_contDiff_one
#print axioms RMTFoundations.TracyWidom.TW2R_strictMono
#print axioms RMTFoundations.TracyWidom.TW2R_quantile_exists_unique
#print axioms RMTFoundations.TracyWidom.TW2R_median_exists_unique
#print axioms RMTFoundations.TracyWidom.TW2C1_all_binder_joint_probe
