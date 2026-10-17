import Mathlib.MeasureTheory.Measure.ResolventTransform

/-!
# The Stieltjes transform of a finite measure on `ℝ`: definition

Mathlib already has the general object: `MeasureTheory.resolventTransform μ a`
for a measure on a normed field valued in a normed algebra.  Specialising the
field to `ℝ` and the algebra to `ℂ` gives exactly the Stieltjes transform.  We
do **not** redefine it; we introduce the notation-level wrapper

`stieltjes μ z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ`

purely because the general definition is phrased through `resolvent` and
`Ring.inverse`, which is inconvenient for the elementary half-plane estimates,
and we immediately relate the two by `stieltjes_eq_resolventTransform`.  Every
statement may be expressed in either form.

## What is proved here

* `stieltjes_eq_resolventTransform`: the wrapper *is* mathlib's
  `resolventTransform`, pointwise and for every measure.
* `stieltjesKernel_ne_zero`, `im_le_norm_ofReal_sub`, `norm_stieltjesKernel_le`,
  `im_stieltjesKernel`: the elementary pointwise facts about the integrand
  `(x - z)⁻¹` for `z` in the open upper half-plane.
* `integrable_stieltjesKernel`: integrability against a finite measure.

## What is NOT proved here

Nothing analytic: no positivity, no bound on the transform itself, no
analyticity.  Those are in `RMTFoundations.Stieltjes.HalfPlane`.  Nothing at
all about the lower half-plane or about the real axis.
-/

namespace RMTFoundations.Stieltjes

open MeasureTheory Complex

variable {μ : Measure ℝ /- [definition] -/ } {z : ℂ /- [definition] -/ }

/-- The Stieltjes transform of a measure on `ℝ`, `m z = ∫ (x - z)⁻¹ dμ`.  This
is mathlib's `MeasureTheory.resolventTransform` for the pair `(ℝ, ℂ)`, written
out; see `stieltjes_eq_resolventTransform`. -/
noncomputable def stieltjes (μ : Measure ℝ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ

theorem stieltjes_apply (μ : Measure ℝ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) :
    stieltjes μ z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ := rfl

/-- The wrapper agrees with mathlib's general resolvent transform. -/
theorem stieltjes_eq_resolventTransform (μ : Measure ℝ /- [definition] -/ ) (z : ℂ /- [definition] -/ ) :
    stieltjes μ z = MeasureTheory.resolventTransform μ z := by
  rw [stieltjes_apply, MeasureTheory.resolventTransform_apply]
  congr 1
  funext x
  rw [resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap]

theorem stieltjes_eq_resolventTransform_fun (μ : Measure ℝ /- [definition] -/ ) :
    stieltjes μ = MeasureTheory.resolventTransform (A := ℂ) μ :=
  funext (stieltjes_eq_resolventTransform μ)

/-! ### Elementary half-plane estimates -/

/-- For `z` off the real axis the integrand never blows up. -/
theorem stieltjesKernel_ne_zero (hz : 0 < z.im /- [standing] -/ ) (x : ℝ /- [definition] -/ ) : (x : ℂ) - z ≠ 0 := by
  intro h
  have him : ((x : ℂ) - z).im = 0 := by rw [h]; exact Complex.zero_im
  rw [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_eq_zero] at him
  exact absurd him hz.ne'

/-- `Im z ≤ ‖x - z‖` for every real `x`. -/
theorem im_le_norm_ofReal_sub (hz : 0 ≤ z.im /- [standing] -/ ) (x : ℝ /- [definition] -/ ) : z.im ≤ ‖(x : ℂ) - z‖ := by
  have h := Complex.abs_im_le_norm ((x : ℂ) - z)
  rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_nonneg hz] at h
  exact h

/-- The uniform bound `‖(x - z)⁻¹‖ ≤ (Im z)⁻¹` on the upper half-plane. -/
theorem norm_stieltjesKernel_le (hz : 0 < z.im /- [standing] -/ ) (x : ℝ /- [definition] -/ ) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ (z.im)⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hz (im_le_norm_ofReal_sub hz.le x)

/-- The imaginary part of the integrand is `Im z / ‖x - z‖²`. -/
theorem im_stieltjesKernel (z : ℂ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) :
    (((x : ℂ) - z)⁻¹).im = z.im / Complex.normSq ((x : ℂ) - z) := by
  rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]

/-- Integrability of the integrand for a finite measure and `z` in the open
upper half-plane. -/
theorem integrable_stieltjesKernel (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] (hz : 0 < z.im /- [standing] -/ ) :
    Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
  refine ⟨?_, ?_⟩
  · exact (Complex.measurable_ofReal.sub measurable_const).inv.aestronglyMeasurable
  · exact HasFiniteIntegral.of_bounded (C := (z.im)⁻¹)
      (Filter.Eventually.of_forall fun x => norm_stieltjesKernel_le hz x)


end RMTFoundations.Stieltjes

#print axioms RMTFoundations.Stieltjes.stieltjes
#print axioms RMTFoundations.Stieltjes.stieltjes_apply
#print axioms RMTFoundations.Stieltjes.stieltjes_eq_resolventTransform
#print axioms RMTFoundations.Stieltjes.stieltjes_eq_resolventTransform_fun
#print axioms RMTFoundations.Stieltjes.stieltjesKernel_ne_zero
#print axioms RMTFoundations.Stieltjes.im_le_norm_ofReal_sub
#print axioms RMTFoundations.Stieltjes.norm_stieltjesKernel_le
#print axioms RMTFoundations.Stieltjes.im_stieltjesKernel
#print axioms RMTFoundations.Stieltjes.integrable_stieltjesKernel
