import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.TriangleVolterraFoundation
open MeasureTheory Set

/-- Improper Fubini on the Volterra triangle. The joint absolute-integrability
premise is stated for the actual two-variable integrand. -/
theorem triangle_swap
    (p q : ℝ → ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (hint : Integrable (fun z : ℝ × ℝ => if z.1 < z.2 then p z.1 * q z.2 else 0)
      ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) /- [standing] -/) :
    (∫ t in Ioi x, ∫ r in Ioi t, p t * q r) =
      ∫ r in Ioi x, (∫ t in x..r, p t) * q r := by
  let μ : Measure ℝ := volume.restrict (Ioi x)
  let f : ℝ → ℝ → ℝ := fun t r => if t < r then p t * q r else 0
  have hl (t : ℝ) (ht : x < t) :
      (∫ r, f t r ∂μ) = ∫ r in Ioi t, p t * q r := by
    have he : Ioi t ∩ Ioi x = Ioi t := by
      ext r; simp only [mem_inter_iff, mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h,ht.trans h⟩
    calc
      (∫ r, f t r ∂μ) = ∫ r, (Ioi t).indicator (fun r => p t * q r) r ∂μ := by
        rfl
      _ = ∫ r in Ioi t, p t * q r ∂μ := integral_indicator measurableSet_Ioi
      _ = ∫ r in Ioi t, p t * q r := by
        dsimp [μ]; rw [Measure.restrict_restrict measurableSet_Ioi, he]
  have hr (r : ℝ) (hr : x < r) :
      (∫ t, f t r ∂μ) = (∫ t in x..r, p t) * q r := by
    have he : Iio r ∩ Ioi x = Ioo x r := by
      ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; exact and_comm
    calc
      (∫ t, f t r ∂μ) = ∫ t, (Iio r).indicator (fun t => p t * q r) t ∂μ := by
        rfl
      _ = ∫ t in Iio r, p t * q r ∂μ := integral_indicator measurableSet_Iio
      _ = ∫ t in Ioo x r, p t * q r := by
        dsimp [μ]; rw [Measure.restrict_restrict measurableSet_Iio, he]
      _ = (∫ t in x..r, p t) * q r := by
        rw [intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo, integral_mul_const]
  have H : (∫ t, ∫ r, f t r ∂μ ∂μ) = ∫ r, ∫ t, f t r ∂μ ∂μ :=
    integral_integral_swap hint
  calc
    (∫ t in Ioi x, ∫ r in Ioi t, p t * q r) = ∫ t, ∫ r, f t r ∂μ ∂μ := by
      apply integral_congr_ae
      exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => (hl t ht).symm)
    _ = ∫ r, ∫ t, f t r ∂μ ∂μ := H
    _ = ∫ r in Ioi x, (∫ t in x..r, p t) * q r := by
      apply integral_congr_ae
      exact ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr' => hr r hr')

/-- Genuinely nonzero infinite triangle, with integrable exponential factors,
realizes the complete improper-Fubini premise. -/
theorem triangle_all_binder_joint_probe :
    (∫ t in Ioi (0 : ℝ), ∫ r in Ioi t, Real.exp (-t) * Real.exp (-r)) =
      ∫ r in Ioi (0 : ℝ), (∫ t in (0 : ℝ)..r, Real.exp (-t)) * Real.exp (-r) := by
  have hi : Integrable (fun t : ℝ => Real.exp (-t)) (volume.restrict (Ioi 0)) :=
    integrableOn_exp_neg_Ioi 0
  have hp := hi.mul_prod hi
  have H := hp.indicator (measurableSet_lt measurable_fst measurable_snd)
  apply triangle_swap
  convert! H using 1

end RMTFoundations.TracyWidom.TriangleVolterraFoundation

#print axioms RMTFoundations.TracyWidom.TriangleVolterraFoundation.triangle_swap
#print axioms RMTFoundations.TracyWidom.TriangleVolterraFoundation.triangle_all_binder_joint_probe
