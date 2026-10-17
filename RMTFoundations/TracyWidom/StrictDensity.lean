import RMTFoundations.TracyWidom.StrictContraction
import RMTFoundations.TracyWidom.StrictWindow
import RMTFoundations.TracyWidom.C1
import RMTFoundations.TracyWidom.Probability


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set
open scoped InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone

/-- The physical GOE boundary resolvent is strictly positive on the entire line. -/
theorem airy_canonical_boundary_positive
    (s : ℝ /- [definition] -/) :
    0 < airyAiReal s + inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1-airyHankelShift s) (airyBoundaryVector s)) := by
  by_cases hl : s ≤ (-27/5:ℝ)
  · exact airy_boundary_positive_left s hl
  by_cases hr : 0 ≤ s
  · exact airy_hankel_inverse_boundary_pos_of_nonneg s hr
  have hm := airy_first_square_margin_window s ⟨le_of_not_ge hl,le_of_not_ge hr⟩
  have hc := hm.trans (airy_square_one_term_lower s)
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/10000) hc

/-- The actual GOE CDF density is strictly positive at every real shift. -/
theorem TW1Density_positive
    (s : ℝ /- [definition] -/) : 0 < TW1Density s :=
  div_pos (mul_pos (TW1R_positive_bounds s).1 (airy_canonical_boundary_positive s))
    (by norm_num)

theorem TW1R_strictMono : StrictMono TW1R := by
  apply strictMono_of_deriv_pos
  intro s
  rw [(TW1R_hasDerivAt s).deriv]
  exact TW1Density_positive s

/-- Every interior probability has exactly one GOE quantile. -/
theorem TW1R_quantile_exists_unique
    (q : ℝ /- [definition] -/)
    (hq0 : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : ∃! s, TW1R s = q := by
  obtain ⟨s,hs⟩ := TW1R_quantile_exists q hq0 hq1
  exact ⟨s,hs,fun t ht => TW1R_strictMono.injective (ht.trans hs.symm)⟩

theorem TW1R_median_exists_unique : ∃! s, TW1R s = 1/2 :=
  TW1R_quantile_exists_unique (1/2) (by norm_num) (by norm_num)

/-- Physical negative and nonnegative rows jointly instantiate every branch and quantile premise. -/
theorem TW1_strict_all_binder_joint_probe :
    airyBoundaryVector (-6) ≠ 0 ∧ airyBoundaryVector (-3) ≠ 0 ∧
    airyBoundaryVector 0 ≠ 0 ∧
    0 < TW1Density (-6) ∧ 0 < TW1Density (-3) ∧ 0 < TW1Density 0 ∧
    ContDiff ℝ 1 TW1R ∧ StrictMono TW1R ∧
    (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ (∃! s, TW1R s = 1/2) :=
  ⟨airyBoundaryVector_ne_zero (-6),airyBoundaryVector_ne_zero (-3),airyBoundaryVector_ne_zero 0,
    TW1Density_positive (-6),TW1Density_positive (-3),TW1Density_positive 0,
    TW1R_contDiff_one,TW1R_strictMono,by norm_num,by norm_num,TW1R_median_exists_unique⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.airy_canonical_boundary_positive
#print axioms RMTFoundations.TracyWidom.TW1Density_positive
#print axioms RMTFoundations.TracyWidom.TW1R_strictMono
#print axioms RMTFoundations.TracyWidom.TW1R_quantile_exists_unique
#print axioms RMTFoundations.TracyWidom.TW1R_median_exists_unique
#print axioms RMTFoundations.TracyWidom.TW1_strict_all_binder_joint_probe
