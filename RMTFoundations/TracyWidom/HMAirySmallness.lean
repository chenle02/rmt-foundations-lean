import RMTFoundations.TracyWidom.HMAiryEnvelope
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HMAirySmallness
open Filter Set
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.HMAiryEnvelope
/-- The candidate reduction-of-order contraction coefficient vanishes.
This proves smallness of the coefficient, not the missing Green identity. -/
theorem airy_cubic_coefficient_atTop (M : ℝ /- [definition] -/)
    : Tendsto (fun s => 3*M^2*(airyAiReal s)^2/2) atTop (𝓝 0) := by
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_div] using
    ((airyAi_atTop_zero.pow 2).const_mul (3*M^2)).div_const 2
/-- A common tail floor with positive Ai and strict smallness is constructed. -/
theorem eventually_airy_cubic_coefficient_small (M : ℝ /- [definition] -/)
    : ∃ a ≥ (1:ℝ), ∀ s ≥ a, 0<airyAiReal s ∧ 3*M^2*(airyAiReal s)^2/2<1 := by
  have h := (airy_cubic_coefficient_atTop M).eventually_lt_const (by norm_num : (0:ℝ)<1)
  obtain ⟨a,ha⟩ := (h.and (eventually_ge_atTop (1:ℝ))).exists_forall_of_atTop
  refine ⟨max a 1,le_max_right _ _,fun s hs => ?_⟩
  have hs' := (le_max_left a 1).trans hs
  exact ⟨airyAiReal_pos_of_nonneg (by linarith [(ha s hs').2]),(ha s hs').1⟩
/-- Nonzero physical Airy instance with the actual normalized radius two. -/
theorem airy_smallness_joint_probe :
    airyAiReal 1 ≠ 0 ∧
    ∃ a ≥ (1:ℝ), ∀ s ≥ a, 0<airyAiReal s ∧ 3*(2:ℝ)^2*(airyAiReal s)^2/2<1 :=
  ⟨(airyAiReal_pos_of_nonneg (by norm_num : (0:ℝ)≤1)).ne',eventually_airy_cubic_coefficient_small 2⟩
end RMTFoundations.TracyWidom.HMAirySmallness
#print axioms RMTFoundations.TracyWidom.HMAirySmallness.airy_cubic_coefficient_atTop
#print axioms RMTFoundations.TracyWidom.HMAirySmallness.eventually_airy_cubic_coefficient_small
#print axioms RMTFoundations.TracyWidom.HMAirySmallness.airy_smallness_joint_probe
