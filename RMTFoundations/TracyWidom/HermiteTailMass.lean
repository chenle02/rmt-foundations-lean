import RMTFoundations.TracyWidom.HermiteTailComparison
import RMTFoundations.TracyWidom.ExponentialTailIntegral
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteTailMass
open Set Filter Topology Real MeasureTheory
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.TracyWidom.HermiteTailComparison
open RMTFoundations.TracyWidom.ExponentialTailIntegral

/-- The actual scaled Hermite mode has an integrable square on every right tail. -/
theorem edgeMode_square_tail
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (T : ℝ /- [definition] -/)
    (hT : 1 ≤ T /- [standing] -/) :
    IntegrableOn (fun x => (edgeMode N x)^2) (Ioi T) ∧
      (∫ x in Ioi T, (edgeMode N x)^2) ≤ |edgeMode N 1|^2*exp (-(T-1)) := by
  have H := square_tail_integral (edgeMode N)
    (continuous_iff_continuousAt.mpr fun x => (edgeMode_hasDerivAt N x).continuousAt)
    1 (1/2) |edgeMode N 1| (by norm_num) (abs_nonneg _)
    (edgeMode_relative_tail N hN) T hT
  norm_num at H
  simpa only [sq_abs,neg_sub] using H

/-- Neighboring mode square tail on exactly the same N-dependent edge scale. -/
theorem previousMode_square_tail
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (T : ℝ /- [definition] -/)
    (hT : 1 ≤ T /- [standing] -/) :
    IntegrableOn (fun x => (previousMode N x)^2) (Ioi T) ∧
      (∫ x in Ioi T, (previousMode N x)^2) ≤ |previousMode N 1|^2*exp (-(T-1)) := by
  have H := square_tail_integral (previousMode N)
    (continuous_iff_continuousAt.mpr fun x => (previousMode_hasDerivAt N x).continuousAt)
    1 (1/2) |previousMode N 1| (by norm_num) (abs_nonneg _)
    (previousMode_relative_tail N hN) T hT
  norm_num at H
  simpa only [sq_abs,neg_sub] using H

/-- Off-diagonal product domination for the two actual neighboring modes.
The literal boundary amplitudes are retained in the kernel-product constant. -/
theorem adjacent_product_tail
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x y : ℝ /- [definition] -/)
    (hx : 1 ≤ x /- [standing] -/)
    (hy : 1 ≤ y /- [standing] -/) :
    |edgeMode N x*previousMode N y| ≤
      (|edgeMode N 1| *|previousMode N 1|)*exp (-(1/2:ℝ)*(x+y-2)) := by
  rw [abs_mul]
  calc
    _ ≤ (|edgeMode N 1| *exp (-(1/2:ℝ)*(x-1)))*
        (|previousMode N 1| *exp (-(1/2:ℝ)*(y-1))) :=
      mul_le_mul (edgeMode_relative_tail N hN x hx) (previousMode_relative_tail N hN y hy)
        (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm,←exp_add]
      congr 2 <;> ring

/-- Growing actual Hermite witness supplies every mass and product binder. -/
theorem hermite_tail_mass_joint_probe (n : ℕ /- [definition] -/) :
    0 < RMTFoundations.TracyWidom.GUEHermite.hermiteDensity (n+1) (fun i => (i.val:ℝ)) ∧
    (∀ T : ℝ, 1 ≤ T →
      IntegrableOn (fun x => (edgeMode (n+1) x)^2) (Ioi T) ∧
      (∫ x in Ioi T, (edgeMode (n+1) x)^2) ≤ |edgeMode (n+1) 1|^2*exp (-(T-1))) ∧
    (∀ T : ℝ, 1 ≤ T →
      IntegrableOn (fun x => (previousMode (n+1) x)^2) (Ioi T) ∧
      (∫ x in Ioi T, (previousMode (n+1) x)^2) ≤ |previousMode (n+1) 1|^2*exp (-(T-1))) ∧
    (∀ x y : ℝ, 1 ≤ x → 1 ≤ y → |edgeMode (n+1) x*previousMode (n+1) y| ≤
      (|edgeMode (n+1) 1| *|previousMode (n+1) 1|)*exp (-(1/2:ℝ)*(x+y-2))) := by
  refine ⟨RMTFoundations.TracyWidom.GUEHermite.hermite_density_all_binder_joint_probe.2 n,?_,?_,?_⟩
  · intro T hT; exact edgeMode_square_tail _ (by omega) T hT
  · intro T hT; exact previousMode_square_tail _ (by omega) T hT
  · intro x y hx hy; exact adjacent_product_tail _ (by omega) x y hx hy
end RMTFoundations.TracyWidom.HermiteTailMass

#print axioms RMTFoundations.TracyWidom.HermiteTailMass.edgeMode_square_tail
#print axioms RMTFoundations.TracyWidom.HermiteTailMass.previousMode_square_tail
#print axioms RMTFoundations.TracyWidom.HermiteTailMass.adjacent_product_tail
#print axioms RMTFoundations.TracyWidom.HermiteTailMass.hermite_tail_mass_joint_probe
