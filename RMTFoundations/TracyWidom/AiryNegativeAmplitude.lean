import RMTFoundations.TracyWidom.AiryOscillatoryEnergy
import RMTFoundations.Airy.Core

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryNegativeAmplitude
open RMTFoundations.TracyWidom.AiryOscillatoryEnergy RMTFoundations.Airy

theorem airy_all_binder_probe :
    ∃ f df : ℝ → ℝ, ∃ r : ℝ,
      (∀ x, HasDerivAt f (df x) x) ∧
      (∀ x, HasDerivAt df (x * f x) x) ∧ 1 ≤ r ∧ 0 < f 0 := by
  exact ⟨RMTFoundations.Airy.airyAiReal,
    deriv RMTFoundations.Airy.airyAiReal, 1,
    RMTFoundations.Airy.hasDerivAt_airyAiReal',
    RMTFoundations.Airy.hasDerivAt_deriv_airyAiReal', le_rfl,
    RMTFoundations.Airy.airyAiReal_zero_pos⟩

/-- Explicit negative-side oscillatory bound, derived from the actual Ai equation. -/
theorem airy_negative_bound (x : ℝ /- [definition] -/)
    (hx : x ≤ -1 /- [standing] -/) :
    |RMTFoundations.Airy.airyAiReal x| ≤
      Real.sqrt (energy RMTFoundations.Airy.airyAiReal
        (deriv RMTFoundations.Airy.airyAiReal) 1) * (-x) ^ (-1/4 : ℝ) := by
  have hx0 : 0 ≤ -x := by linarith
  have hr : 1 ≤ Real.sqrt (-x) := Real.one_le_sqrt.mpr (by linarith)
  have hb := amplitude_bound RMTFoundations.Airy.airyAiReal
    (deriv RMTFoundations.Airy.airyAiReal)
    RMTFoundations.Airy.hasDerivAt_airyAiReal'
    RMTFoundations.Airy.hasDerivAt_deriv_airyAiReal' (Real.sqrt (-x)) hr
  have harg : -(Real.sqrt (-x) ^ 2) = x := by rw [Real.sq_sqrt hx0]; ring
  rw [harg] at hb
  have hs : Real.sqrt (Real.sqrt (-x)) = (-x) ^ (1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
    norm_num
  calc |RMTFoundations.Airy.airyAiReal x| ≤ _ := hb
       _ = _ := by rw [hs, show (-1/4 : ℝ) = -(1/4 : ℝ) by norm_num, Real.rpow_neg hx0]; rfl

/-- The negative-argument floor and the same nonzero Airy equation hold jointly. -/
theorem airy_negative_joint_probe :
    ∃ x : ℝ, x ≤ -1 ∧ 1 ≤ Real.sqrt (-x) ∧ 0 < airyAiReal 0 ∧
      (∀ y, HasDerivAt airyAiReal (deriv airyAiReal y) y) ∧
      (∀ y, HasDerivAt (deriv airyAiReal) (y * airyAiReal y) y) := by
  refine ⟨-1, le_rfl, ?_, airyAiReal_zero_pos,
    hasDerivAt_airyAiReal', hasDerivAt_deriv_airyAiReal'⟩
  norm_num

end RMTFoundations.TracyWidom.AiryNegativeAmplitude

#print axioms RMTFoundations.TracyWidom.AiryNegativeAmplitude.airy_all_binder_probe
#print axioms RMTFoundations.TracyWidom.AiryNegativeAmplitude.airy_negative_bound
#print axioms RMTFoundations.TracyWidom.AiryNegativeAmplitude.airy_negative_joint_probe
