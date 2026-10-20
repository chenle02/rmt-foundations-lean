import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourCircleIntegral
open Complex
/-- Shift the norm integral to the centered angular interval without weakening Cauchy. -/
theorem norm_circle_integral_le_centered (f : ℂ → ℂ /- [definition] -/)
    (r : ℝ /- [definition] -/) :
    ‖∮ z in C(0,r), f z‖ ≤
      ∫ t in (-Real.pi)..Real.pi, ‖deriv (circleMap 0 r) t*f (circleMap 0 r t)‖ := by
  let path : ℝ → ℂ := fun t => deriv (circleMap 0 r) t*f (circleMap 0 r t)
  have hp : Function.Periodic (fun t => ‖path t‖) (2*Real.pi) := by
    intro t
    dsimp [path]
    rw [deriv_circleMap,deriv_circleMap,(periodic_circleMap 0 r) t]
  have H := hp.intervalIntegral_add_eq 0 (-Real.pi)
  have H' : (∫ t in 0..2*Real.pi, ‖path t‖) =
      ∫ t in (-Real.pi)..Real.pi, ‖path t‖ := by
    simpa only [zero_add,show -Real.pi+2*Real.pi=Real.pi by ring] using H
  calc
    _ ≤ ∫ t in 0..2*Real.pi, ‖path t‖ := by
      simpa only [circleIntegral,smul_eq_mul,path] using
        (intervalIntegral.norm_integral_le_integral_norm (f:=path) Real.two_pi_pos.le)
    _ = _ := H'
/-- Nonzero inverse kernels and arbitrarily large positive radii witness the interface. -/
theorem centered_integral_joint_probe (n : ℕ /- [definition] -/) :
    ∃ r : ℝ, 0 < r ∧ (∀ t : ℝ, circleMap 0 r t ≠ 0) ∧
      ‖∮ z in C(0,r), (z:ℂ)⁻¹‖ ≤
        ∫ t in (-Real.pi)..Real.pi,
          ‖deriv (circleMap 0 r) t*(circleMap 0 r t)⁻¹‖ := by
  refine ⟨(n:ℝ)+1,by positivity,?_,norm_circle_integral_le_centered (fun z => z⁻¹) ((n:ℝ)+1)⟩
  intro t
  exact circleMap_ne_center (by positivity : (n:ℝ)+1 ≠ 0)
end RMTFoundations.TracyWidom.ContourCircleIntegral

#print axioms RMTFoundations.TracyWidom.ContourCircleIntegral.norm_circle_integral_le_centered
#print axioms RMTFoundations.TracyWidom.ContourCircleIntegral.centered_integral_joint_probe
