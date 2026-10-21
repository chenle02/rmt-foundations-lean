import RMTFoundations.TracyWidom.GUEDensity
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUEEndpointSign
open RMTFoundations.TracyWidom.GUEProjection

/-- Endpoint determinant is strictly positive on an ordered two-particle slice. -/
theorem endpoint_det_two_pos (x : Fin 2 → ℝ /- [definition] -/)
    (hx : x 0 < x 1 /- [standing] -/) :
    0 < Matrix.det (fun i k : Fin 2 => hermiteFunction k.val (x i)) := by
  rw [hermite_function_det]
  have hv : 0 < (Matrix.vandermonde x).det := by
    simpa [Matrix.det_fin_two, Matrix.vandermonde] using sub_pos.mpr hx
  apply mul_pos
  · exact mul_pos (Finset.prod_pos (fun i hi => Real.exp_pos _)) hv
  · exact Finset.prod_pos (fun k hk => inv_pos.mpr (hermiteNorm_pos k.val))

theorem endpoint_two_all_binder_joint_probe :
    ∃ x : Fin 2 → ℝ, x 0 < x 1 ∧ Function.Injective x ∧
      0 < Matrix.det (fun i k : Fin 2 => hermiteFunction k.val (x i)) := by
  let x : Fin 2 → ℝ := ![-1,2]
  have hx : x 0 < x 1 := by norm_num [x]
  refine ⟨x,hx,?_,endpoint_det_two_pos x hx⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [x] at *
end RMTFoundations.TracyWidom.GUEEndpointSign

#print axioms RMTFoundations.TracyWidom.GUEEndpointSign.endpoint_det_two_pos
#print axioms RMTFoundations.TracyWidom.GUEEndpointSign.endpoint_two_all_binder_joint_probe
