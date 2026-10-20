import Mathlib
import RMTFoundations.TracyWidom.AiryGreenFoundation
import RMTFoundations.TracyWidom.ExponentialGreenFoundation
import RMTFoundations.TracyWidom.HMAiryKernel
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryGreenKernelFoundation
open MeasureTheory Set Real
open RMTFoundations.Airy RMTFoundations.TracyWidom.ExponentialGreenFoundation

/-- Actual Ai reduction-of-order kernel has a uniform explicit mass bound.
The reference's positivity, ODE and boundary decay are derived, not assumed. -/
theorem ai_green_bounds
    (s x t : ℝ /- [definition] -/)
    (hs : 0 < s /- [standing] -/)
    (hsx : s ≤ x /- [standing] -/)
    (hxt : x ≤ t /- [standing] -/) :
    0 ≤ normalizedGreen airyAiReal x t ∧
      normalizedGreen airyAiReal x t ≤ 1 / (2 * sqrt s) := by
  have hcont : Continuous airyAiReal := continuous_iff_continuousAt.mpr
    (fun r => (hasDerivAt_airyAiReal' r).continuousAt)
  have H := normalizedGreen_bounds airyAiReal (sqrt s) x t
    (sqrt_pos.mpr hs) hxt hcont.continuousOn
    (fun r hr => airyAiReal_pos_of_nonneg (hs.le.trans (hsx.trans hr.1)))
    (fun r hr => RMTFoundations.TracyWidom.AiryGreenFoundation.ai_relative_exponential s r t hs
      (hsx.trans hr.1) hr.2)
  exact ⟨H.1,H.2.1.trans H.2.2⟩

/-- Forward half-line kernel; the strict triangle agrees with Lebesgue tail
integration and avoids introducing a diagonal singleton boundary term. -/
noncomputable def halflineKernel
    (x t : ℝ /- [definition] -/) : ℝ :=
  if x < t then normalizedGreen airyAiReal x t else 0

theorem halflineKernel_bound
    (s x t : ℝ /- [definition] -/)
    (hs : 0 < s /- [standing] -/)
    (hsx : s ≤ x /- [standing] -/)
    (hst : s ≤ t /- [standing] -/) :
    |halflineKernel x t| ≤ 1 / (2 * sqrt s) := by
  by_cases hxt : x < t
  · have H := ai_green_bounds s x t hs hsx hxt.le
    rw [halflineKernel,if_pos hxt,abs_of_nonneg H.1]
    exact H.2
  · rw [halflineKernel,if_neg hxt,abs_zero]
    positivity

/-- Exact conversion between a moving Volterra tail and a fixed-domain
integral operator. No integrability or equation is silently presumed. -/
theorem fixed_domain_integral
    (s x : ℝ /- [definition] -/)
    (ε u : ℝ → ℝ /- [definition] -/)
    (hsx : s ≤ x /- [standing] -/) :
    (∫ t in Ioi s, halflineKernel x t * ε t * u t) =
      ∫ t in Ioi x, normalizedGreen airyAiReal x t * ε t * u t := by
  have he : Ioi x ∩ Ioi s = Ioi x := by
    ext t; simp only [mem_inter_iff,mem_Ioi]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h,hsx.trans_lt h⟩
  calc
    (∫ t in Ioi s, halflineKernel x t*ε t*u t) =
        ∫ t in Ioi s, (Ioi x).indicator
          (fun t => normalizedGreen airyAiReal x t*ε t*u t) t := by
      congr 1
      ext t
      by_cases ht : x < t <;> simp [halflineKernel,indicator,mem_Ioi,ht]
    _ = ∫ t in Ioi x, normalizedGreen airyAiReal x t*ε t*u t ∂volume.restrict (Ioi s) :=
      integral_indicator measurableSet_Ioi
    _ = ∫ t in Ioi x, normalizedGreen airyAiReal x t*ε t*u t := by
      rw [Measure.restrict_restrict measurableSet_Ioi,he]

/-- Literal bridge to the Hastings--McLeod kernel.
Its nonlinear-source normalization contributes exactly two Ai-squared factors. -/
theorem hm_relativeGreen_eq
    (x t : ℝ /- [definition] -/) :
    RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen x t =
      2*(airyAiReal t)^2*normalizedGreen airyAiReal x t := by
  have hi : (∫ r in x..t, 2/(airyAiReal r)^2) =
      2*(∫ r in x..t, ((airyAiReal r)^2)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
  unfold RMTFoundations.TracyWidom.HMAiryKernel.relativeGreen
  rw [hi,normalizedGreen_factor]
  ring

/-- Nonzero actual Airy reference on a nonzero interval jointly realizes all
kernel comparison and fixed-domain binders. -/
theorem airy_kernel_all_binder_joint_probe :
    0 ≤ normalizedGreen airyAiReal 1 2 ∧
    normalizedGreen airyAiReal 1 2 ≤ 1 / 2 ∧
    |halflineKernel 1 2| ≤ 1 / 2 ∧
    (∫ t in Ioi (1 : ℝ), halflineKernel 2 t * Real.exp (-t)) =
      ∫ t in Ioi (2 : ℝ), normalizedGreen airyAiReal 2 t * Real.exp (-t) := by
  have H := ai_green_bounds 1 1 2 (by norm_num) le_rfl (by norm_num)
  have J := halflineKernel_bound 1 1 2 (by norm_num) le_rfl (by norm_num)
  have Q := fixed_domain_integral 1 2 (fun t => Real.exp (-t)) (fun _ => 1) (by norm_num)
  exact ⟨H.1,by simpa using H.2,by simpa using J,by simpa using Q⟩

end RMTFoundations.TracyWidom.AiryGreenKernelFoundation

#print axioms RMTFoundations.TracyWidom.AiryGreenKernelFoundation.ai_green_bounds
#print axioms RMTFoundations.TracyWidom.AiryGreenKernelFoundation.halflineKernel
#print axioms RMTFoundations.TracyWidom.AiryGreenKernelFoundation.halflineKernel_bound
#print axioms RMTFoundations.TracyWidom.AiryGreenKernelFoundation.fixed_domain_integral
#print axioms RMTFoundations.TracyWidom.AiryGreenKernelFoundation.airy_kernel_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.AiryGreenKernelFoundation.hm_relativeGreen_eq
