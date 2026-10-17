import RMTFoundations.Measure.FreeConvolution
namespace RMTFoundations.FreeConvolutionProbe
open MeasureTheory Set
open RMTFoundations.FreeConvolution
/-- All ShiftBounds fields hold jointly for a nonzero semicircle shift function. -/
theorem shift_bounds_joint :
    ShiftBounds (hfun (semicircle 1)) (scEdge 1) ((scEdge 1)^2) (9*scEdge 1) (2*scEdge 1) ∧
      IsProbabilityMeasure (semicircle 1) ∧ 0 < scEdge 1 ∧
      hfun (semicircle 1) Complex.I ≠ 0 := by
  have hs : (0 : ℝ) < 1 := by norm_num
  haveI := semicircle_prob hs
  refine ⟨shiftBounds_hfun (semicircle_supported hs) (scEdge_pos hs), inferInstance,
    scEdge_pos hs, ?_⟩
  rw [hfun_semicircle hs (by simp)]
  apply mul_ne_zero (by norm_num)
  intro hz
  have hp := gsc_im_pos hs (z := Complex.I) (by simp)
  rw [hz] at hp
  simpa using hp
/-- Subordination readiness is realized by two positive-variance semicircle laws. -/
theorem free_conv_joint :
    IsProbabilityMeasure (semicircle 1) ∧ IsProbabilityMeasure (semicircle 2) ∧
      SupportedIn (semicircle 1) 4 ∧ SupportedIn (semicircle 2) 4 ∧
      IsFreeConv (semicircle 1) (semicircle 2) (semicircle 3) := by
  have h1 : (0 : ℝ) < 1 := by norm_num
  have h2 : (0 : ℝ) < 2 := by norm_num
  haveI := semicircle_prob h1
  haveI := semicircle_prob h2
  have b1 : scEdge 1 ≤ 4 := by norm_num [scEdge]
  have b2 : scEdge 2 ≤ 4 := by
    have : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
    unfold scEdge; linarith
  refine ⟨inferInstance, inferInstance, (semicircle_supported h1).mono b1,
    (semicircle_supported h2).mono b2, ?_⟩
  have h := freeConv_isFreeConv ((semicircle_supported h1).mono b1)
    ((semicircle_supported h2).mono b2) (by norm_num : (0 : ℝ) < 4)
  simpa only [freeConv_semicircle h1 h2, show (1:ℝ)+2=3 by norm_num] using h
end RMTFoundations.FreeConvolutionProbe

#print axioms RMTFoundations.FreeConvolutionProbe.shift_bounds_joint
#print axioms RMTFoundations.FreeConvolutionProbe.free_conv_joint
