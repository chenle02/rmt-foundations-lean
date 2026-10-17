import Challenge.Reference.Stieltjes.Defs

/-!
# The Stieltjes transform on the open upper half-plane

## What is proved here

* `im_stieltjes`: the imaginary part of the transform as a positive integral.
* `im_stieltjes_pos`: `0 < (stieltjes μ z).im` whenever `0 < z.im` and
  `μ ≠ 0` — Herglotz positivity in the upper half-plane.
* `norm_stieltjes_le`: `‖stieltjes μ z‖ ≤ μ.real univ / z.im`.
* `analyticOn_stieltjes`: analyticity on the open upper half-plane, obtained
  from mathlib's `analyticOn_resolventTransform`.

## What is NOT proved here

* No Stieltjes **inversion** formula and no Herglotz/Nevanlinna representation:
  neither the recovery of `μ` from `stieltjes μ` nor the converse direction
  (every Herglotz function is such a transform) appears anywhere in this
  package.
* No behaviour as `z.im → 0`, no boundary values, no square-root edge
  behaviour.
* Nothing about the lower half-plane, and no statement relating
  `stieltjes μ (conj z)` to `stieltjes μ z`.
* The transform of no specific measure is computed here.
-/

namespace RMTFoundations.Stieltjes

open MeasureTheory Complex

variable {μ : Measure ℝ /- [definition] -/ } {z : ℂ /- [definition] -/ }

/-! ### Positivity and the resolvent bound -/

/-- The imaginary part of the transform, written as an integral. -/
theorem im_stieltjes (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] (hz : 0 < z.im /- [standing] -/ ) :
    (stieltjes μ z).im = ∫ x : ℝ, z.im / Complex.normSq ((x : ℂ) - z) ∂μ := by
  have h : ∫ x : ℝ, (((x : ℂ) - z)⁻¹).im ∂μ = (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ).im :=
    integral_im (𝕜 := ℂ) (integrable_stieltjesKernel μ hz)
  rw [stieltjes_apply, ← h]
  congr 1
  funext x
  exact im_stieltjesKernel z x

/-- **Herglotz positivity.**  A nonzero finite measure has a Stieltjes
transform with strictly positive imaginary part on the upper half-plane. -/
theorem im_stieltjes_pos (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] (hμ : μ ≠ 0 /- [standing] -/ )
    (hz : 0 < z.im /- [standing] -/ ) : 0 < (stieltjes μ z).im := by
  have hpos : ∀ x : ℝ, 0 < z.im / Complex.normSq ((x : ℂ) - z) := fun x =>
    div_pos hz (Complex.normSq_pos.mpr (stieltjesKernel_ne_zero hz x))
  have hint : Integrable (fun x : ℝ => z.im / Complex.normSq ((x : ℂ) - z)) μ := by
    have h := (integrable_stieltjesKernel μ hz).im
    refine h.congr ?_
    filter_upwards with x using im_stieltjesKernel z x
  rw [im_stieltjes μ hz, integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hint]
  have hsupp : Function.support (fun x : ℝ => z.im / Complex.normSq ((x : ℂ) - z))
      = Set.univ := by
    ext x
    exact iff_of_true (hpos x).ne' (Set.mem_univ x)
  rw [hsupp]
  exact Measure.measure_univ_pos.mpr hμ

/-- **The resolvent bound.**  `‖m z‖ ≤ μ(ℝ) / Im z`. -/
theorem norm_stieltjes_le (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] (hz : 0 < z.im /- [standing] -/ ) :
    ‖stieltjes μ z‖ ≤ μ.real Set.univ / z.im := by
  rw [stieltjes_apply, div_eq_inv_mul]
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall fun x => norm_stieltjesKernel_le hz x)

/-! ### Analyticity -/

/-- The open upper half-plane misses the real axis, hence the (real) support of
any measure. -/
theorem upperHalfPlane_subset_compl_image (μ : Measure ℝ /- [definition] -/ ) :
    {w : ℂ | 0 < w.im} ⊆ (algebraMap ℝ ℂ '' μ.support)ᶜ := by
  intro w hw hmem
  obtain ⟨x, _, hx⟩ := hmem
  rw [Complex.coe_algebraMap] at hx
  have : w.im = 0 := by rw [← hx]; exact Complex.ofReal_im x
  exact absurd this (ne_of_gt hw)

/-- The Stieltjes transform is analytic on the open upper half-plane.  This is
mathlib's `analyticOn_resolventTransform` transported along
`stieltjes_eq_resolventTransform`. -/
theorem analyticOn_stieltjes (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] :
    AnalyticOn ℂ (stieltjes μ) {w : ℂ | 0 < w.im} := by
  rw [stieltjes_eq_resolventTransform_fun μ]
  exact (MeasureTheory.analyticOn_resolventTransform (𝕜 := ℝ) (μ := μ)).mono
    (upperHalfPlane_subset_compl_image μ)

end RMTFoundations.Stieltjes

#print axioms RMTFoundations.Stieltjes.im_stieltjes
#print axioms RMTFoundations.Stieltjes.im_stieltjes_pos
#print axioms RMTFoundations.Stieltjes.norm_stieltjes_le
#print axioms RMTFoundations.Stieltjes.upperHalfPlane_subset_compl_image
#print axioms RMTFoundations.Stieltjes.analyticOn_stieltjes
