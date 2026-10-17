import RMTFoundations.TracyWidom.CanonicalPainleveWitness
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMPainleveWronskian
open RMTFoundations.Airy
/-- The Airy/PII Wronskian derivative is the forcing term used by reduction of order. -/
theorem pii_airy_wronskian_derivative
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hq : DifferentiableAt ℝ q s /- [standing] -/)
    (hqq : HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    : HasDerivAt
      (fun t => airyAiReal t*deriv q t-deriv airyAiReal t*q t)
      (2*airyAiReal s*(q s)^3) s := by
  have haa : HasDerivAt (deriv airyAiReal) (s*airyAiReal s) s := by
    convert hasDerivAt_deriv_airyAiReal s using 1
    rw [← (hasDerivAt_deriv_airyAiReal s).deriv,deriv_deriv_airyAiReal]
  convert! ((hasDerivAt_airyAiReal' s).fun_mul hqq).fun_sub (haa.fun_mul hq.hasDerivAt) using 1; ring
/-- Multiplying the relative derivative by Ai squared gives the same Wronskian. -/
theorem pii_airy_relative_derivative
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hq : DifferentiableAt ℝ q s /- [standing] -/)
    (hA : airyAiReal s ≠ 0 /- [standing] -/)
    : (airyAiReal s)^2*deriv (fun t => q t/airyAiReal t) s =
      airyAiReal s*deriv q s-deriv airyAiReal s*q s := by
  rw [(hq.hasDerivAt.fun_div (hasDerivAt_airyAiReal' s) hA).deriv]
  field_simp
/-- All differential and relative derivative binders hold jointly for the
actual canonical global PII solution and positive Airy value at one. -/
theorem wronskian_canonical_joint_probe :
    ∃ q : ℝ → ℝ,
      Differentiable ℝ q ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      airyAiReal 1 ≠ 0 ∧
      (∀ s, HasDerivAt (fun t => airyAiReal t*deriv q t-deriv airyAiReal t*q t)
        (2*airyAiReal s*(q s)^3) s) ∧
      (airyAiReal 1)^2*deriv (fun t => q t/airyAiReal t) 1 =
        airyAiReal 1*deriv q 1-deriv airyAiReal 1*q 1 := by
  rcases RMTFoundations.TracyWidom.CanonicalPainleveWitness.canonical_painleveII_classical_tracyWidom_witness with
    ⟨_,_,_,_,q,_,hq,_,_,_,_,hode,_,_⟩
  have hA : airyAiReal 1 ≠ 0 := (airyAiReal_pos_of_nonneg (by norm_num : (0:ℝ)≤1)).ne'
  exact ⟨q,hq,hode,hA,(fun s => pii_airy_wronskian_derivative q s (hq s) (hode s)),
    pii_airy_relative_derivative q 1 (hq 1) hA⟩
end RMTFoundations.TracyWidom.HMPainleveWronskian
#print axioms RMTFoundations.TracyWidom.HMPainleveWronskian.pii_airy_wronskian_derivative
#print axioms RMTFoundations.TracyWidom.HMPainleveWronskian.pii_airy_relative_derivative

#print axioms RMTFoundations.TracyWidom.HMPainleveWronskian.wronskian_canonical_joint_probe
