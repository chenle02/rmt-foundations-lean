import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteGenerating
open Polynomial Complex
noncomputable def generating (x z : ℂ /- [definition] -/) : ℂ :=
  Complex.exp (x*z-z^2/2)
lemma generating_hasDerivAt (x z : ℂ /- [definition] -/) :
    HasDerivAt (generating x) ((x-z)*generating x z) z := by
  have hp := (hasDerivAt_const z x).mul (hasDerivAt_id z)
  have hq := (hasDerivAt_pow 2 z).div_const 2
  have H := (hp.sub hq).cexp
  convert H using 1 <;> first | rfl | (dsimp [generating]; ring)
lemma hermite_generating_hasDerivAt
    (n : ℕ /- [definition] -/) (x z : ℂ /- [definition] -/) :
    HasDerivAt (fun w => aeval (x-w) (hermite n)*generating x w)
      (aeval (x-z) (hermite (n+1))*generating x z) z := by
  have H := (((hermite n).hasDerivAt_aeval (x-z)).comp z
    ((hasDerivAt_const z x).sub (hasDerivAt_id z))).mul (generating_hasDerivAt x z)
  have hr : aeval (x-z) (hermite (n+1)) =
      (x-z)*aeval (x-z) (hermite n)-aeval (x-z) (derivative (hermite n)) := by
    rw [hermite_succ, map_sub, map_mul, aeval_X]
  convert H using 1 <;> first | rfl | (dsimp [Function.comp_apply]; rw [hr]; ring)
lemma iteratedDeriv_generating (n : ℕ /- [definition] -/)
    (x z : ℂ /- [definition] -/) :
    iteratedDeriv n (generating x) z = aeval (x-z) (hermite n)*generating x z := by
  induction n generalizing z with
  | zero => simp [hermite_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv n (generating x) =
      (fun w => aeval (x-w) (hermite n)*generating x w) from funext ih]
    exact (hermite_generating_hasDerivAt n x z).deriv
lemma iteratedDeriv_generating_zero (n : ℕ /- [definition] -/)
    (x : ℂ /- [definition] -/) :
    iteratedDeriv n (generating x) 0 = aeval x (hermite n) := by
  simp [iteratedDeriv_generating, generating]
/-- Positive radius and unbounded degree can coexist in the generating interface. -/
theorem generating_joint_probe (n : ℕ /- [definition] -/) :
    ∃ x z : ℂ, x ≠ 0 ∧ z ≠ 0 ∧
      HasDerivAt (generating x) ((x-z)*generating x z) z ∧
      iteratedDeriv n (generating x) 0 = aeval x (hermite n) := by
  exact ⟨2,1,by norm_num,by norm_num,generating_hasDerivAt 2 1,
    iteratedDeriv_generating_zero n 2⟩
/-- Exact Cauchy coefficient formula for the  probabilists convention. -/
theorem hermite_cauchy_circle (n : ℕ /- [definition] -/)
    (x : ℂ /- [definition] -/)
    (r : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    (∮ z in C(0,r), (z^(n+1))⁻¹*generating x z) =
      ((2*Real.pi*Complex.I)/(n.factorial:ℂ))*aeval x (hermite n) := by
  have hc : DifferentiableOn ℂ (generating x) (Metric.closedBall 0 r) :=
    fun z _ => (generating_hasDerivAt x z).differentiableAt.differentiableWithinAt
  simpa only [sub_zero,one_div,smul_eq_mul,iteratedDeriv_generating_zero] using
    DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hr n hc
theorem cauchy_joint_probe (n : ℕ /- [definition] -/) :
    ∃ x : ℂ, ∃ r : ℝ, x ≠ 0 ∧ 0 < r ∧
      (∮ z in C(0,r), (z^(n+1))⁻¹*generating x z) =
        ((2*Real.pi*Complex.I)/(n.factorial:ℂ))*aeval x (hermite n) := by
  exact ⟨2,(n:ℝ)+1,by norm_num,by positivity,
    hermite_cauchy_circle n 2 ((n:ℝ)+1) (by positivity)⟩
end RMTFoundations.TracyWidom.HermiteGenerating

#print axioms RMTFoundations.TracyWidom.HermiteGenerating.generating
#print axioms RMTFoundations.TracyWidom.HermiteGenerating.generating_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteGenerating.hermite_generating_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteGenerating.iteratedDeriv_generating
#print axioms RMTFoundations.TracyWidom.HermiteGenerating.iteratedDeriv_generating_zero
#print axioms RMTFoundations.TracyWidom.HermiteGenerating.generating_joint_probe
#print axioms RMTFoundations.TracyWidom.HermiteGenerating.hermite_cauchy_circle
#print axioms RMTFoundations.TracyWidom.HermiteGenerating.cauchy_joint_probe
