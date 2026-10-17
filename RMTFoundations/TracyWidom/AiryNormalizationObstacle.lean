import RMTFoundations.Airy.Core
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryNormalizationObstacle
open RMTFoundations.Airy
/-- Positive solutions of the Airy ODE need an independent amplitude selection.
This is a method obstruction, not a counterexample to Hermite edge asymptotics. -/
theorem positive_airy_ode_does_not_fix_amplitude :
    ∃ u v : ℝ → ℝ, 0 < u 0 ∧
      (∀ x, HasDerivAt u (v x) x) ∧
      (∀ x, HasDerivAt v (x * u x) x) ∧ u 0 ≠ airyAiReal 0 := by
  refine ⟨fun x => 2 * airyAiReal x, fun x => 2 * deriv airyAiReal x,
    mul_pos (by norm_num) airyAiReal_zero_pos, ?_, ?_, ?_⟩
  · intro x
    simpa only [deriv_airyAiReal] using (hasDerivAt_airyAiReal x).const_mul 2
  · intro x
    have he := iteratedDeriv_two_airyAiReal x
    rw [show (2 : ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at he
    have h := (hasDerivAt_deriv_airyAiReal x).const_mul 2
    have hd := (hasDerivAt_deriv_airyAiReal x).deriv
    rw [hd] at he
    convert h using 1 <;> first | rfl | (rw [he]; ring)
  · have h := airyAiReal_zero_pos
    intro he; linarith
end RMTFoundations.TracyWidom.AiryNormalizationObstacle

#print axioms RMTFoundations.TracyWidom.AiryNormalizationObstacle.positive_airy_ode_does_not_fix_amplitude
