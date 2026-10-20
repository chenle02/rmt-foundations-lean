import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.PerturbedAiryVolterra
open Real MeasureTheory intervalIntegral

/-- Wronskian forcing identity for a perturbed second-order scalar ODE. -/
theorem wronskian_forcing_derivative
    (u v g h q r : ℝ → ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t*u t) t /- [standing] -/)
    (hg : ∀ t, HasDerivAt g (h t) t /- [standing] -/)
    (hh : ∀ t, HasDerivAt h (r t*g t) t /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    HasDerivAt (fun t => g t*v t-h t*u t) (g x*(q x-r x)*u x) x := by
  convert! ((hg x).mul (hv x)).sub ((hh x).mul (hu x)) using 1 <;> ring

/-- Exact oriented interval integral, valid on both sides of zero. -/
theorem wronskian_forcing_integral
    (u v g h q r : ℝ → ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t*u t) t /- [standing] -/)
    (hg : ∀ t, HasDerivAt g (h t) t /- [standing] -/)
    (hh : ∀ t, HasDerivAt h (r t*g t) t /- [standing] -/)
    (hq : Continuous q /- [standing] -/)
    (hr : Continuous r /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    (∫ t in 0..x, g t*(q t-r t)*u t) =
      (g x*v x-h x*u x)-(g 0*v 0-h 0*u 0) := by
  have cu : Continuous u := continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt
  have cg : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => wronskian_forcing_derivative u v g h q r hu hv hg hh t)
    (((cg.mul (hq.sub hr)).mul cu).intervalIntegrable 0 x)

/-- Duhamel formula with both initial-data coefficients and the literal forcing.
The Wronskian at the evaluation point selects an invertible fundamental pair. -/
theorem variation_of_constants
    (u v g h G H q r : ℝ → ℝ /- [definition] -/)
    (hu : ∀ t, HasDerivAt u (v t) t /- [standing] -/)
    (hv : ∀ t, HasDerivAt v (q t*u t) t /- [standing] -/)
    (hg : ∀ t, HasDerivAt g (h t) t /- [standing] -/)
    (hh : ∀ t, HasDerivAt h (r t*g t) t /- [standing] -/)
    (hG : ∀ t, HasDerivAt G (H t) t /- [standing] -/)
    (hH : ∀ t, HasDerivAt H (r t*G t) t /- [standing] -/)
    (hq : Continuous q /- [standing] -/)
    (hr : Continuous r /- [standing] -/)
    (w x : ℝ /- [definition] -/)
    (hw : w ≠ 0 /- [standing] -/)
    (hW : g x*H x-h x*G x=w /- [standing] -/) :
    u x = ((H 0*u 0-G 0*v 0)*g x + (g 0*v 0-h 0*u 0)*G x +
      G x*(∫ t in 0..x, g t*(q t-r t)*u t) -
      g x*(∫ t in 0..x, G t*(q t-r t)*u t))/w := by
  rw [wronskian_forcing_integral u v g h q r hu hv hg hh hq hr x,
    wronskian_forcing_integral u v G H q r hu hv hG hH hq hr x]
  apply (eq_div_iff hw).mpr
  linear_combination -(u x)*hW

/-- Joint witness: growing nonzero exponential solution, a linear fundamental
pair, Wronskian one, and nonzero coefficient forcing. No analytic input is re-taken. -/
theorem variation_of_constants_joint_probe (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    ((n+1:ℕ):ℝ)*exp x = ((n+1:ℕ):ℝ)*(1+x) +
      x*(∫ t in 0..x, ((n+1:ℕ):ℝ)*exp t) -
      (∫ t in 0..x, t*(((n+1:ℕ):ℝ)*exp t)) := by
  have hd (t : ℝ) : HasDerivAt (fun t => ((n+1:ℕ):ℝ)*exp t)
      (((n+1:ℕ):ℝ)*exp t) t := (hasDerivAt_exp t).const_mul _
  have hf := variation_of_constants
    (fun t => ((n+1:ℕ):ℝ)*exp t) (fun t => ((n+1:ℕ):ℝ)*exp t)
    (fun _ => 1) (fun _ => 0) id (fun _ => 1) (fun _ => 1) (fun _ => 0)
    hd (by simpa using hd) (fun t => hasDerivAt_const t 1)
    (by intro t; simpa using hasDerivAt_const t (0:ℝ))
    (fun t => hasDerivAt_id t) (by intro t; simpa using hasDerivAt_const t (1:ℝ))
    continuous_const continuous_const 1 x (by norm_num) (by simp)
  simp only [sub_zero,one_mul,zero_mul,exp_zero,mul_one,div_one,id_eq] at hf
  convert hf using 1 <;> ring
end RMTFoundations.TracyWidom.PerturbedAiryVolterra

#print axioms RMTFoundations.TracyWidom.PerturbedAiryVolterra.wronskian_forcing_derivative
#print axioms RMTFoundations.TracyWidom.PerturbedAiryVolterra.wronskian_forcing_integral
#print axioms RMTFoundations.TracyWidom.PerturbedAiryVolterra.variation_of_constants
#print axioms RMTFoundations.TracyWidom.PerturbedAiryVolterra.variation_of_constants_joint_probe
