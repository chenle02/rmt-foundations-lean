import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.OUTransitionPositivity
open Matrix

/-- Stationary variance-one OU transition density with correlation q.
This definition does not assume the Karlin-McGregor representation. -/
noncomputable def ouTransition (q x y : ℝ /- [definition] -/) : ℝ :=
  Real.exp (-(y-q*x)^2/(2*(1-q^2))) /
    Real.sqrt (2*Real.pi*(1-q^2))

lemma variance_pos (q : ℝ /- [definition] -/)
    (hq : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : 0 < 1-q^2 := by
  nlinarith [mul_pos hq (sub_pos.mpr hq1)]

lemma ouTransition_pos (q x y : ℝ /- [definition] -/)
    (hq : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/) : 0 < ouTransition q x y := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.2
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (variance_pos q hq hq1)))

/-- Exact strict TP2 ingredient for ordered two-particle Gaussian transitions.
The all-N total-positivity and path normalization theorems remain separate. -/
theorem ordered_transition_product_lt
    (q x0 x1 y0 y1 : ℝ /- [definition] -/)
    (hq : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/)
    (hx : x0 < x1 /- [standing] -/)
    (hy : y0 < y1 /- [standing] -/) :
    ouTransition q x0 y1 * ouTransition q x1 y0 <
      ouTransition q x0 y0 * ouTransition q x1 y1 := by
  have hv := variance_pos q hq hq1
  have hd : 0 < Real.sqrt (2*Real.pi*(1-q^2)) := by
    exact Real.sqrt_pos.2 (mul_pos (mul_pos (by norm_num) Real.pi_pos) hv)
  unfold ouTransition
  rw [← mul_div_mul_comm, ← mul_div_mul_comm, ← Real.exp_add, ← Real.exp_add]
  apply (div_lt_div_iff_of_pos_right (mul_pos hd hd)).2
  apply Real.exp_lt_exp.mpr
  rw [← add_div, ← add_div]
  apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) hv)).2
  have hgap : 0 < q*((x1-x0)*(y1-y0)) :=
    mul_pos hq (mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy))
  nlinarith [hgap]

noncomputable def transitionDetTwo (q : ℝ /- [definition] -/)
    (x y : Fin 2 → ℝ /- [definition] -/) : ℝ :=
  Matrix.det (fun i j => ouTransition q (x i) (y j))

theorem transitionDetTwo_pos
    (q : ℝ /- [definition] -/)
    (x y : Fin 2 → ℝ /- [definition] -/)
    (hq : 0 < q /- [standing] -/)
    (hq1 : q < 1 /- [standing] -/)
    (hx : x 0 < x 1 /- [standing] -/)
    (hy : y 0 < y 1 /- [standing] -/) :
    0 < transitionDetTwo q x y := by
  change 0 < Matrix.det (Matrix.of (fun i j : Fin 2 => ouTransition q (x i) (y j)))
  rw [Matrix.det_fin_two]
  exact sub_pos.mpr (ordered_transition_product_lt q (x 0) (x 1) (y 0) (y 1) hq hq1 hx hy)

/-- Every standing condition holds on the same strict, nonzero Gaussian
transition and two separated ordered configurations. -/
theorem transition_all_binder_joint_probe :
    ∃ q : ℝ, ∃ x y : Fin 2 → ℝ,
      0 < q ∧ q < 1 ∧ x 0 < x 1 ∧ y 0 < y 1 ∧
      (∀ i j, 0 < ouTransition q (x i) (y j)) ∧
      0 < transitionDetTwo q x y := by
  let x : Fin 2 → ℝ := ![0,1]
  let y : Fin 2 → ℝ := ![-1,2]
  have hq : 0 < (1/2 : ℝ) := by norm_num
  have hq1 : (1/2 : ℝ) < 1 := by norm_num
  have hx : x 0 < x 1 := by norm_num [x]
  have hy : y 0 < y 1 := by norm_num [y]
  exact ⟨1/2,x,y,hq,hq1,hx,hy,
    fun i j => ouTransition_pos (1/2) (x i) (y j) hq hq1,
    transitionDetTwo_pos (1/2) x y hq hq1 hx hy⟩

end RMTFoundations.TracyWidom.OUTransitionPositivity

#print axioms RMTFoundations.TracyWidom.OUTransitionPositivity.ouTransition
#print axioms RMTFoundations.TracyWidom.OUTransitionPositivity.variance_pos
#print axioms RMTFoundations.TracyWidom.OUTransitionPositivity.ouTransition_pos
#print axioms RMTFoundations.TracyWidom.OUTransitionPositivity.ordered_transition_product_lt
#print axioms RMTFoundations.TracyWidom.OUTransitionPositivity.transitionDetTwo
#print axioms RMTFoundations.TracyWidom.OUTransitionPositivity.transitionDetTwo_pos
#print axioms RMTFoundations.TracyWidom.OUTransitionPositivity.transition_all_binder_joint_probe
