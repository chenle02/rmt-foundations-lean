import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ExponentialTailIntegral
open Set Filter Topology Real MeasureTheory

/-- An exponential envelope implies a genuine square-integrable tail and an
explicit tail-mass bound. This is a domination lemma for later trace estimates. -/
theorem square_tail_integral
    (u : ℝ → ℝ /- [definition] -/)
    (hu : Continuous u /- [standing] -/)
    (a c A : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/)
    (hA : 0 ≤ A /- [standing] -/)
    (hbound : ∀ x, a ≤ x → |u x| ≤ A*exp (-c*(x-a)) /- [standing] -/)
    (T : ℝ /- [definition] -/)
    (hT : a ≤ T /- [standing] -/) :
    IntegrableOn (fun x => (u x)^2) (Ioi T) ∧
    (∫ x in Ioi T, (u x)^2) ≤ A^2*exp (-2*c*(T-a))/(2*c) := by
  let E : ℝ → ℝ := fun x => (A^2*exp (2*c*a))*exp ((-2*c)*x)
  have hi : IntegrableOn E (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith : (-2*c)<0) T).const_mul _
  have hb (x : ℝ) (hx : x ∈ Ioi T) : (u x)^2 ≤ E x := by
    have H := hbound x (hT.trans hx.le)
    have hpos : 0 ≤ A*exp (-c*(x-a)) := mul_nonneg hA (exp_pos _).le
    have hs : (u x)^2 ≤ (A*exp (-c*(x-a)))^2 := by nlinarith [sq_abs (u x),abs_nonneg (u x)]
    calc
      _ ≤ _ := hs
      _ = E x := by
        dsimp [E]
        rw [mul_pow,←exp_nat_mul,mul_assoc,←exp_add]
        congr 2 <;> ring
  have haemeas : AEStronglyMeasurable (fun x => (u x)^2) (volume.restrict (Ioi T)) :=
    (hu.pow 2).aestronglyMeasurable
  have hiae : ∀ᵐ x ∂volume.restrict (Ioi T), ‖(u x)^2‖ ≤ E x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (u x))] using hb x hx
  have huint : IntegrableOn (fun x => (u x)^2) (Ioi T) := hi.mono' haemeas hiae
  refine ⟨huint,?_⟩
  calc
    _ ≤ ∫ x in Ioi T, E x := integral_mono_ae huint hi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact hb x hx)
    _ = A^2*exp (-2*c*(T-a))/(2*c) := by
      dsimp [E]
      rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : (-2*c)<0) T]
      have hc0 : 2*c ≠ 0 := by positivity
      field_simp
      rw [mul_assoc,←exp_add]
      congr 2 <;> ring

/-- Nonconstant concrete control supplies every envelope binder and tail limit. -/
theorem square_tail_joint_probe (T : ℝ /- [definition] -/)
    (hT : 0 ≤ T /- [standing] -/) :
    IntegrableOn (fun x : ℝ => (exp (-x))^2) (Ioi T) ∧
      (∫ x in Ioi T, (exp (-x))^2) ≤ exp (-2*T)/2 := by
  have H := square_tail_integral (fun x => exp (-x)) (Real.continuous_exp.comp continuous_id.neg)
    0 1 1 (by norm_num) (by norm_num) (by intro x hx; simp [abs_of_pos (exp_pos _)]) T hT
  simpa using H
end RMTFoundations.TracyWidom.ExponentialTailIntegral

#print axioms RMTFoundations.TracyWidom.ExponentialTailIntegral.square_tail_integral
#print axioms RMTFoundations.TracyWidom.ExponentialTailIntegral.square_tail_joint_probe
