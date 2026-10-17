import RMTFoundations.Measure.FreeConvolution
import RMTFoundations.Stieltjes.Semicircle

namespace RMTFoundations.SemicircleBridge
open MeasureTheory Set

/-- The general subordination semicircle and original density law agree at variance one. -/
theorem variance_one_semicircle_eq :
    RMTFoundations.FreeConvolution.semicircle 1 = RMTFoundations.Stieltjes.semicircle := by
  rw [RMTFoundations.FreeConvolution.semicircle_eq_withDensity (by norm_num : (0 : ℝ) < 1),
    RMTFoundations.Stieltjes.semicircle, ← withDensity_indicator measurableSet_Icc]
  apply withDensity_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · rw [indicator_of_mem hx]
    congr 1
    simp [RMTFoundations.FreeConvolution.scDens,
      RMTFoundations.Stieltjes.semicircleDensity, div_eq_mul_inv, mul_comm]
  · rw [indicator_of_notMem hx]
    apply ENNReal.ofReal_eq_zero.mpr
    have hs : 4 - x ^ 2 ≤ 0 := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx <;> nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 2)]
    simp [RMTFoundations.FreeConvolution.scDens, Real.sqrt_eq_zero_of_nonpos hs]

/-- The original density-defined standard semicircle has the genuine analytic transform. -/
theorem stieltjes_standard_semicircle {z : ℂ /- [definition] -/}
    (hz : 0 < z.im /- [standing] -/) :
    RMTFoundations.Stieltjes.stieltjes RMTFoundations.Stieltjes.semicircle z =
      RMTFoundations.FreeConvolution.gsc 1 z := by
  rw [← variance_one_semicircle_eq]
  exact RMTFoundations.FreeConvolution.stieltjes_semicircle (by norm_num) hz

end RMTFoundations.SemicircleBridge

#print axioms RMTFoundations.SemicircleBridge.variance_one_semicircle_eq
#print axioms RMTFoundations.SemicircleBridge.stieltjes_standard_semicircle
