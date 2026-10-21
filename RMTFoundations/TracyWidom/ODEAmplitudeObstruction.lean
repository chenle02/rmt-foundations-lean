import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ODEAmplitudeObstruction
open Filter Topology Real

/-- Route counterexample: a positive potential and decay do NOT normalize a
family. This does not refute a uniform bound for the actual normalized Hermite modes. -/
theorem ode_decay_does_not_bound_amplitudes :
    ∃ u v : ℕ → ℝ → ℝ,
      (∀ n t, HasDerivAt (u n) (v n t) t) ∧
      (∀ n t, HasDerivAt (v n) (4*u n t) t) ∧
      (∀ n, Tendsto (u n) atTop (𝓝 0)) ∧
      (∀ n, 0 < u n 0) ∧
      ¬(∃ A : ℝ, ∀ n, |u n 0| ≤ A) := by
  let u : ℕ → ℝ → ℝ := fun n t => ((n+1:ℕ):ℝ)*exp (-2*t)
  let v : ℕ → ℝ → ℝ := fun n t => -2*u n t
  have hu (n : ℕ) (t : ℝ) : HasDerivAt (u n) (v n t) t := by
    convert! (((hasDerivAt_id t).const_mul (-2)).exp).const_mul ((n+1:ℕ):ℝ) using 1 <;>
      simp only [u,v,id_eq] <;> ring
  have hv (n : ℕ) (t : ℝ) : HasDerivAt (v n) (4*u n t) t := by
    convert! (hu n t).const_mul (-2) using 1 <;> simp only [v] <;> ring
  have ht (n : ℕ) : Tendsto (u n) atTop (𝓝 0) := by
    have H := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0:ℝ)<2 by norm_num))
    simpa only [Function.comp_def,id_eq,neg_mul,u,mul_zero] using H.const_mul ((n+1:ℕ):ℝ)
  refine ⟨u,v,hu,hv,ht,?_,?_⟩
  · intro n; simp only [u,mul_zero,exp_zero,mul_one]; positivity
  · rintro ⟨A,hA⟩
    obtain ⟨n,hn⟩ := exists_nat_gt A
    have H := hA n
    simp only [u,mul_zero,exp_zero,mul_one] at H
    rw [abs_of_nonneg (by positivity)] at H
    simp only [Nat.cast_add,Nat.cast_one] at H
    linarith
end RMTFoundations.TracyWidom.ODEAmplitudeObstruction

#print axioms RMTFoundations.TracyWidom.ODEAmplitudeObstruction.ode_decay_does_not_bound_amplitudes
