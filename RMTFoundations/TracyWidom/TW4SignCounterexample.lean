import RMTFoundations.TracyWidom.C1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom

/- This finite-dimensional probe limits a proof route. It makes no assertion
about the actual Airy operator or the Tracy-Widom GSE distribution. -/
noncomputable def tw4ProbeEigen1 (t : ℝ /- [definition] -/) : ℝ := 3/5-t
noncomputable def tw4ProbeEigen2 (t : ℝ /- [definition] -/) : ℝ := -1/5-t
noncomputable def tw4ProbeMatrix (t : ℝ /- [definition] -/) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![tw4ProbeEigen1 t, tw4ProbeEigen2 t]
noncomputable def tw4ProbeMinus (t : ℝ /- [definition] -/) : ℝ :=
  (1-tw4ProbeEigen1 t)*(1-tw4ProbeEigen2 t)
noncomputable def tw4ProbePlus (t : ℝ /- [definition] -/) : ℝ :=
  (1+tw4ProbeEigen1 t)*(1+tw4ProbeEigen2 t)
noncomputable def tw4ProbeSquare (t : ℝ /- [definition] -/) : ℝ :=
  (1-(tw4ProbeEigen1 t)^2)*(1-(tw4ProbeEigen2 t)^2)
noncomputable def tw4ProbeAverage (t : ℝ /- [definition] -/) : ℝ :=
  (tw4ProbeMinus t+tw4ProbePlus t)/2

theorem tw4_probe_actual_determinants
    (t : ℝ /- [definition] -/) :
    (1-tw4ProbeMatrix t).det = tw4ProbeMinus t ∧
    (1+tw4ProbeMatrix t).det = tw4ProbePlus t ∧
    (1-tw4ProbeMatrix t*tw4ProbeMatrix t).det = tw4ProbeSquare t := by
  simp [tw4ProbeMatrix, tw4ProbeMinus, tw4ProbePlus, tw4ProbeSquare,
    Matrix.det_fin_two, pow_two]

theorem tw4_probe_factorization
    (t : ℝ /- [definition] -/) :
    tw4ProbeSquare t = tw4ProbeMinus t*tw4ProbePlus t := by
  dsimp [tw4ProbeSquare, tw4ProbeMinus, tw4ProbePlus]
  ring

theorem tw4_probe_polynomials
    (t : ℝ /- [definition] -/) :
    tw4ProbeMinus t = 12/25+(8/5)*t+t^2 ∧
    tw4ProbeSquare t = 384/625+(112/125)*t-(52/25)*t^2-(4/5)*t^3+t^4 ∧
    tw4ProbeAverage t = 22/25-(2/5)*t+t^2 := by
  dsimp [tw4ProbeMinus, tw4ProbeSquare, tw4ProbeAverage, tw4ProbePlus,
    tw4ProbeEigen1, tw4ProbeEigen2]
  constructor
  · ring
  constructor <;> ring

theorem tw4_probe_derivatives :
    HasDerivAt tw4ProbeMinus (8/5) 0 ∧
    HasDerivAt tw4ProbeSquare (112/125) 0 ∧
    HasDerivAt tw4ProbeAverage (-2/5) 0 := by
  have h1 : HasDerivAt tw4ProbeEigen1 (-1) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (3/5 : ℝ)).fun_sub (hasDerivAt_id (0 : ℝ)) using 1 <;>
      norm_num [tw4ProbeEigen1]
  have h2 : HasDerivAt tw4ProbeEigen2 (-1) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (-1/5 : ℝ)).fun_sub (hasDerivAt_id (0 : ℝ)) using 1 <;>
      norm_num [tw4ProbeEigen2]
  have hc := hasDerivAt_const (0 : ℝ) (1 : ℝ)
  have hm : HasDerivAt tw4ProbeMinus (8/5) 0 := by
    convert! (hc.fun_sub h1).fun_mul (hc.fun_sub h2) using 1 <;>
      norm_num [tw4ProbeMinus, tw4ProbeEigen1, tw4ProbeEigen2]
  have hp : HasDerivAt tw4ProbePlus (-12/5) 0 := by
    convert! (hc.fun_add h1).fun_mul (hc.fun_add h2) using 1 <;>
      norm_num [tw4ProbePlus, tw4ProbeEigen1, tw4ProbeEigen2]
  refine ⟨hm, ?_, ?_⟩
  · convert! (hc.fun_sub (h1.pow 2)).fun_mul (hc.fun_sub (h2.pow 2)) using 1 <;>
      norm_num [tw4ProbeSquare, tw4ProbeEigen1, tw4ProbeEigen2]
  · convert! (hm.fun_add hp).div_const (2 : ℝ) using 1 <;>
      norm_num [tw4ProbeAverage]

/-- Joint nondegenerate contraction eigenvalues, positive determinant values,
positive F1/F2 slopes, negative determinant-average slope, and factorization. -/
theorem tw4_sign_route_all_binder_joint_probe :
    ∃ t : ℝ, tw4ProbeEigen1 t ≠ 0 ∧ tw4ProbeEigen2 t ≠ 0 ∧
      |tw4ProbeEigen1 t| < 1 ∧ |tw4ProbeEigen2 t| < 1 ∧
      0 < tw4ProbeMinus t ∧ 0 < tw4ProbeSquare t ∧
      0 < tw4ProbeAverage t ∧ tw4ProbeAverage t < 1 ∧
      tw4ProbeSquare t = tw4ProbeMinus t*tw4ProbePlus t ∧
      HasDerivAt tw4ProbeMinus (8/5) t ∧
      HasDerivAt tw4ProbeSquare (112/125) t ∧
      HasDerivAt tw4ProbeAverage (-2/5) t ∧
      (0 : ℝ) < 8/5 ∧ (0 : ℝ) < 112/125 ∧ (-2/5 : ℝ) < 0 := by
  refine ⟨0, ?_⟩
  have hd := tw4_probe_derivatives
  norm_num [tw4ProbeEigen1, tw4ProbeEigen2, tw4ProbeMinus, tw4ProbeSquare,
    tw4ProbeAverage, tw4ProbePlus] at hd ⊢
  exact hd

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.tw4ProbeEigen1
#print axioms RMTFoundations.TracyWidom.tw4ProbeEigen2
#print axioms RMTFoundations.TracyWidom.tw4ProbeMatrix
#print axioms RMTFoundations.TracyWidom.tw4ProbeMinus
#print axioms RMTFoundations.TracyWidom.tw4ProbePlus
#print axioms RMTFoundations.TracyWidom.tw4ProbeSquare
#print axioms RMTFoundations.TracyWidom.tw4ProbeAverage
#print axioms RMTFoundations.TracyWidom.tw4_probe_actual_determinants
#print axioms RMTFoundations.TracyWidom.tw4_probe_factorization
#print axioms RMTFoundations.TracyWidom.tw4_probe_polynomials
#print axioms RMTFoundations.TracyWidom.tw4_probe_derivatives
#print axioms RMTFoundations.TracyWidom.tw4_sign_route_all_binder_joint_probe
