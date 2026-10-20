import RMTFoundations.TracyWidom.HermiteUniformTail
import RMTFoundations.TracyWidom.ExponentialTailIntegral
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteUniformTailMass
open Real Set MeasureTheory
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.TracyWidom.HermiteTailComparison
open RMTFoundations.TracyWidom.HermiteUniformTail RMTFoundations.TracyWidom.ExponentialTailIntegral
/-- Uniform square-tail masses of both actual neighboring modes, with vanishing truncation error. -/
theorem uniform_tail_masses (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ T : ℝ, s ≤ T →
      IntegrableOn (fun y => (edgeMode N y)^2) (Ioi T) ∧
      IntegrableOn (fun y => (previousMode N y)^2) (Ioi T) ∧
      (∫ y in Ioi T, (edgeMode N y)^2) ≤ C^2*exp (-(T-s)) ∧
      (∫ y in Ioi T, (previousMode N y)^2) ≤ C^2*exp (-(T-s)) := by
  obtain ⟨C,hC,h⟩ := uniform_halfline_tail s
  refine ⟨C,hC,?_⟩
  intro N hN T hT
  have hc : Continuous (edgeMode N) := continuous_iff_continuousAt.mpr
    (fun y => (edgeMode_hasDerivAt N y).continuousAt)
  have hp : Continuous (previousMode N) := continuous_iff_continuousAt.mpr
    (fun y => (previousMode_hasDerivAt N y).continuousAt)
  have Hc := square_tail_integral (edgeMode N) hc s (1/2) C (by norm_num) hC.le
    (fun y hy => (h N hN y hy).1) T hT
  have Hp := square_tail_integral (previousMode N) hp s (1/2) C (by norm_num) hC.le
    (fun y hy => (h N hN y hy).2) T hT
  refine ⟨Hc.1,Hp.1,?_,?_⟩
  · convert Hc.2 using 1 <;> norm_num
  · convert Hp.2 using 1 <;> norm_num
/-- A common product envelope for the two modes used in the Hermite kernel. -/
theorem uniform_adjacent_product (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ x y : ℝ, s ≤ x → s ≤ y →
      |edgeMode N x*previousMode N y| ≤
        C^2*exp (-(1/2:ℝ)*(x-s))*exp (-(1/2:ℝ)*(y-s)) := by
  obtain ⟨C,hC,h⟩ := uniform_halfline_tail s
  refine ⟨C,hC,?_⟩
  intro N hN x y hx hy
  rw [abs_mul]
  have H := mul_le_mul (h N hN x hx).1 (h N hN y hy).2
    (abs_nonneg _) (by positivity : 0 ≤ C*exp (-(1/2:ℝ)*(x-s)))
  calc
    _ ≤ (C*exp (-(1/2:ℝ)*(x-s)))*(C*exp (-(1/2:ℝ)*(y-s))) := H
    _ = _ := by ring
/-- Every endpoint and growing positive dimensions jointly witness both tail-mass conclusions. -/
theorem uniform_mass_joint_probe (s : ℝ /- [definition] -/)
    (k : ℕ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, k < N ∧ 0 < N ∧
      Polynomial.hermite N ≠ 0 ∧ ∀ T : ℝ, s ≤ T →
      IntegrableOn (fun y => (edgeMode N y)^2) (Ioi T) ∧
      IntegrableOn (fun y => (previousMode N y)^2) (Ioi T) ∧
      (∫ y in Ioi T, (edgeMode N y)^2) ≤ C^2*exp (-(T-s)) ∧
      (∫ y in Ioi T, (previousMode N y)^2) ≤ C^2*exp (-(T-s)) := by
  obtain ⟨C,hC,h⟩ := uniform_tail_masses s
  exact ⟨C,hC,k+1,by omega,by omega,(Polynomial.hermite_monic (k+1)).ne_zero,
    h (k+1) (by omega)⟩
theorem uniform_product_joint_probe (s : ℝ /- [definition] -/)
    (k : ℕ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, k < N ∧ 0 < N ∧
      ∀ x y : ℝ, s ≤ x → s ≤ y →
      |edgeMode N x*previousMode N y| ≤
        C^2*exp (-(1/2:ℝ)*(x-s))*exp (-(1/2:ℝ)*(y-s)) := by
  obtain ⟨C,hC,h⟩ := uniform_adjacent_product s
  exact ⟨C,hC,k+1,by omega,by omega,h (k+1) (by omega)⟩
end RMTFoundations.TracyWidom.HermiteUniformTailMass

#print axioms RMTFoundations.TracyWidom.HermiteUniformTailMass.uniform_tail_masses
#print axioms RMTFoundations.TracyWidom.HermiteUniformTailMass.uniform_adjacent_product
#print axioms RMTFoundations.TracyWidom.HermiteUniformTailMass.uniform_mass_joint_probe
#print axioms RMTFoundations.TracyWidom.HermiteUniformTailMass.uniform_product_joint_probe
