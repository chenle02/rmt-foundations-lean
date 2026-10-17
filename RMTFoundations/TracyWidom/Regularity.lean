import RMTFoundations.TracyWidom.Distribution
import RMTFoundations.TracyWidom.StrictDensity
import RMTFoundations.TracyWidom.OrderTwoC1
import RMTFoundations.TracyWidom.ActualFactorization

/-! Continuously differentiable Fredholm CDFs, continuous positive densities,
strict monotonicity and unique interior quantiles for both canonical laws. -/
set_option autoImplicit false
namespace RMTFoundations.TracyWidom

/-- The GOE CDF is continuously differentiable on the entire real line. -/
theorem contDiff_TW1R : ContDiff ℝ 1 TW1R := TW1R_contDiff_one
/-- The GUE CDF is continuously differentiable on the entire real line. -/
theorem contDiff_TW2R : ContDiff ℝ 1 TW2R := TW2R_contDiff_one
/-- The GOE CDF increases strictly at every pair of ordered cutoffs. -/
theorem strictMono_TW1R : StrictMono TW1R := TW1R_strictMono
/-- The GUE CDF increases strictly at every pair of ordered cutoffs. -/
theorem strictMono_TW2R : StrictMono TW2R := TW2R_strictMono
/-- The actual GUE Fredholm CDF is strictly between zero and one at finite cutoffs. -/
theorem TW2R_strict_bounds (s : ℝ /- [definition] -/) : 0 < TW2R s ∧ TW2R s < 1 :=
  ⟨OrderTwoPositive.TW2R_positive s,lt_of_lt_of_le (TW2R_strictMono (lt_add_one s)) ((TW2R_bounds (s+1)).2)⟩
/-- Both genuine laws simultaneously have C1 CDFs and continuous everywhere positive densities. -/
theorem regularity_api_joint_probe :
    RMTFoundations.TWOneBounds.airyBoundaryVector (-3) ≠ 0 ∧
    ContDiff ℝ 1 TW1R ∧ ContDiff ℝ 1 TW2R ∧
    Continuous TW1Density ∧ Continuous TW2Density ∧
    (∀ s, 0 < TW1Density s) ∧ (∀ s, 0 < TW2Density s) ∧
    StrictMono TW1R ∧ StrictMono TW2R ∧
    (∃! s, TW1R s = 1/2) ∧ (∃! s, TW2R s = 1/2) :=
  ⟨RMTFoundations.TWOneBounds.airyBoundaryVector_ne_zero (-3),
    contDiff_TW1R,contDiff_TW2R,TW1Density_continuous,TW2Density_continuous,
    TW1Density_positive,TW2Density_positive,strictMono_TW1R,strictMono_TW2R,
    TW1R_median_exists_unique,TW2R_median_exists_unique⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.contDiff_TW1R
#print axioms RMTFoundations.TracyWidom.contDiff_TW2R
#print axioms RMTFoundations.TracyWidom.strictMono_TW1R
#print axioms RMTFoundations.TracyWidom.strictMono_TW2R
#print axioms RMTFoundations.TracyWidom.TW2R_strict_bounds
#print axioms RMTFoundations.TracyWidom.regularity_api_joint_probe
