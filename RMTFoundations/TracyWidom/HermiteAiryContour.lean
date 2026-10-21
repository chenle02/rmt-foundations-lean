import RMTFoundations.TracyWidom.AiryGaussianIntegral
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteAiryContour
open MeasureTheory Complex
open RMTFoundations.Airy

/-- The actual limiting cubic integrand on a left vertical line. -/
noncomputable def verticalIntegrand (β x t : ℝ /- [definition] -/) : ℂ :=
  let u : ℂ := -(β : ℂ)+Complex.I*t
  Complex.exp ((x : ℂ)*u-u^3/3)

lemma vertical_integrand_re (β x t : ℝ /- [definition] -/) :
    (verticalIntegrand β x t).re =
      Real.exp (-β*x+β^3/3-β*t^2) *
      Real.cos (t*(x-β^2)+t^3/3) := by
  rw [verticalIntegrand,Complex.exp_re]
  congr 1 <;> simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    pow_succ] <;> ring

/-- This identity pins the cubic saddle's orientation and all 2pi factors. -/
lemma vertical_integrand_damped (β x ξ : ℝ /- [definition] -/) :
    verticalIntegrand β x (2*Real.pi*ξ) =
      (Real.exp (-β*x) : ℂ)*RMTFoundations.TracyWidom.AiryGaussianIntegral.integrand β x ξ := by
  rw [verticalIntegrand,RMTFoundations.TracyWidom.AiryGaussianIntegral.integrand,Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  simp only [RMTFoundations.Airy.airyLaplaceFrequency]
  push_cast
  ring

lemma vertical_integrand_integrable (β x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    Integrable (verticalIntegrand β x) := by
  have hg : Integrable (fun t : ℝ =>
      Real.exp (-β*x+β^3/3)*Real.exp (-β*t^2)) :=
    (integrable_exp_neg_mul_sq hβ).const_mul _
  apply hg.mono'
  · exact (by unfold verticalIntegrand; fun_prop : Continuous (verticalIntegrand β x)).aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [verticalIntegrand,Complex.norm_exp,← Real.exp_add]
    apply le_of_eq
    congr 1
    simp [Complex.add_re,Complex.mul_re,Complex.mul_im,pow_succ]
    ring

/-- Exact identification of the limiting contour with the  genuine Ai,
for every real x, derived from the existing proved Fourier inversion. -/
theorem airy_vertical_integral (β x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    airyAiReal x = (1/(2*Real.pi))*
      ∫ t : ℝ, (verticalIntegrand β x t).re := by
  have h := RMTFoundations.TracyWidom.AiryGaussianIntegral.damped_integral β x hβ
  have hr : (fun ξ : ℝ => (verticalIntegrand β x (2*Real.pi*ξ)).re) =
      fun ξ => Real.exp (-β*x)*
        (Real.exp (β^3/3-β*(2*Real.pi*ξ)^2)*
          Real.cos ((2*Real.pi*ξ)*(x-β^2)+(2*Real.pi*ξ)^3/3)) := by
    funext ξ
    rw [vertical_integrand_re]
    rw [show -β*x+β^3/3-β*(2*Real.pi*ξ)^2 =
      -β*x+(β^3/3-β*(2*Real.pi*ξ)^2) by ring,Real.exp_add]
    ring
  have hs := Measure.integral_comp_mul_left
    (fun t : ℝ => (verticalIntegrand β x t).re) (2*Real.pi)
  simp only [abs_inv,abs_of_pos (mul_pos two_pos Real.pi_pos),smul_eq_mul] at hs
  rw [hr,integral_const_mul,← h] at hs
  have he : Real.exp (-β*x)*Real.exp (β*x) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa only [← mul_assoc,he,one_mul,one_div] using hs

/-- Complete nonzero growing example: all damping, source, integrability and exact
identification inputs supplied simultaneously, with actual Ai strictly positive. -/
theorem airy_contour_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, let β : ℝ := n+1
      0 < β ∧ 0 < airyAiReal 1 ∧
      Integrable (verticalIntegrand β 1) ∧
      airyAiReal 1 = (1/(2*Real.pi))*
        ∫ t : ℝ, (verticalIntegrand β 1 t).re) := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,fun n => ?_⟩
  have hn : (0 : ℝ) < n+1 := by positivity
  exact ⟨hn,airyAiReal_pos_of_nonneg zero_le_one,
    vertical_integrand_integrable _ 1 hn,airy_vertical_integral _ 1 hn⟩
end RMTFoundations.TracyWidom.HermiteAiryContour

#print axioms RMTFoundations.TracyWidom.HermiteAiryContour.verticalIntegrand
#print axioms RMTFoundations.TracyWidom.HermiteAiryContour.vertical_integrand_re
#print axioms RMTFoundations.TracyWidom.HermiteAiryContour.vertical_integrand_damped
#print axioms RMTFoundations.TracyWidom.HermiteAiryContour.vertical_integrand_integrable
#print axioms RMTFoundations.TracyWidom.HermiteAiryContour.airy_vertical_integral
#print axioms RMTFoundations.TracyWidom.HermiteAiryContour.airy_contour_joint_probe
