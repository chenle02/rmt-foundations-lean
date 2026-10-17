import RMTFoundations.TracyWidom.GUEHermiteFunctions
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUEProjection
open MeasureTheory Polynomial Real
noncomputable def hermitePolynomialKernel (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : ℝ :=
  ∑ k ∈ Finset.range N, aeval x (hermite k)*aeval y (hermite k)/(k.factorial:ℝ)

theorem hermite_eval_recur (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    aeval x (hermite (n+1)) = x*aeval x (hermite n)-(n:ℝ)*aeval x (hermite (n-1)) := by
  rw [hermite_succ,derivative_hermite]
  simp [nsmul_eq_mul]

theorem hermitePolynomialKernel_cd (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    (x-y)*hermitePolynomialKernel N x y =
      (aeval x (hermite N)*aeval y (hermite (N-1))-
        aeval x (hermite (N-1))*aeval y (hermite N))/((N-1).factorial:ℝ) := by
  unfold hermitePolynomialKernel
  induction N with
  | zero => simp
  | succ N ih =>
    cases N with
    | zero => simp [hermite_zero]
    | succ n =>
      rw [Finset.sum_range_succ,mul_add,ih]
      simp only [Nat.add_sub_cancel]
      have hnum : aeval x (hermite (n+1+1))*aeval y (hermite (n+1))-
          aeval x (hermite (n+1))*aeval y (hermite (n+1+1)) =
          (x-y)*(aeval x (hermite (n+1))*aeval y (hermite (n+1)))+
          (n+1:ℝ)*(aeval x (hermite (n+1))*aeval y (hermite n)-
            aeval x (hermite n)*aeval y (hermite (n+1))) := by
        rw [hermite_eval_recur (n+1) x,hermite_eval_recur (n+1) y]
        simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
        ring
      rw [hnum,Nat.factorial_succ]
      push_cast
      have hn : (n.factorial:ℝ) ≠ 0 := by positivity
      have hs : (n+1:ℝ) ≠ 0 := by positivity
      field_simp
      ring

noncomputable def hermiteKernel (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : ℝ :=
  ∑ k : Fin N, hermiteFunction k.val x * hermiteFunction k.val y

theorem hermiteFunction_pair (k : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    hermiteFunction k x*hermiteFunction k y =
      (Real.exp (-(x^2+y^2)/4)/Real.sqrt (2*Real.pi))*
        (aeval x (hermite k)*aeval y (hermite k)/(k.factorial:ℝ)) := by
  have hn : hermiteNorm k*hermiteNorm k = (k.factorial:ℝ)*Real.sqrt (2*Real.pi) := by
    unfold hermiteNorm
    exact Real.mul_self_sqrt (by positivity)
  have he : Real.exp (-(x^2/4))*Real.exp (-(y^2/4)) = Real.exp (-(x^2+y^2)/4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold hermiteFunction
  rw [div_mul_div_comm,← mul_mul_mul_comm,he,hn]
  ring

theorem hermiteKernel_polynomial (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    hermiteKernel N x y =
      (Real.exp (-(x^2+y^2)/4)/Real.sqrt (2*Real.pi))*hermitePolynomialKernel N x y := by
  unfold hermiteKernel hermitePolynomialKernel
  simp_rw [hermiteFunction_pair]
  rw [← Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => aeval x (hermite k)*aeval y (hermite k)/(k.factorial:ℝ)) N

theorem hermiteKernel_cd_cross (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    (x-y)*hermiteKernel N x y =
      (Real.exp (-(x^2+y^2)/4)/Real.sqrt (2*Real.pi))*
        ((aeval x (hermite N)*aeval y (hermite (N-1))-
          aeval x (hermite (N-1))*aeval y (hermite N))/((N-1).factorial:ℝ)) := by
  rw [hermiteKernel_polynomial,← mul_assoc,mul_comm (x-y) _,mul_assoc,hermitePolynomialKernel_cd]

theorem hermiteKernel_cd (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/)
    (hxy : x ≠ y /- [standing] -/) :
    hermiteKernel N x y =
      (Real.exp (-(x^2+y^2)/4)/Real.sqrt (2*Real.pi))*
        ((aeval x (hermite N)*aeval y (hermite (N-1))-
          aeval x (hermite (N-1))*aeval y (hermite N))/((N-1).factorial:ℝ))/(x-y) := by
  exact (eq_div_iff (sub_ne_zero.mpr hxy)).mpr (by simpa [mul_comm] using hermiteKernel_cd_cross N x y)

theorem hermite_cd_joint_probe :
    ∃ x y : ℝ, x ≠ y ∧ hermiteKernel 3 x y =
      (Real.exp (-(x^2+y^2)/4)/Real.sqrt (2*Real.pi))*
        ((aeval x (hermite 3)*aeval y (hermite 2)-
          aeval x (hermite 2)*aeval y (hermite 3))/(2:ℝ))/(x-y) := by
  refine ⟨0,1,by norm_num,?_⟩
  simpa using hermiteKernel_cd 3 0 1 (by norm_num)

theorem hermiteKernel_trace (N : ℕ /- [definition] -/) :
    (∫ x : ℝ, hermiteKernel N x x) = N := by
  unfold hermiteKernel
  rw [integral_finsetSum Finset.univ (fun k hk => integrable_hermiteFunction_product k.val k.val)]
  simp [hermiteFunction_orthogonality]

theorem hermiteKernel_projection (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    (∫ z : ℝ, hermiteKernel N x z*hermiteKernel N z y) = hermiteKernel N x y := by
  have hid : ∀ z : ℝ, hermiteKernel N x z*hermiteKernel N z y =
      ∑ i : Fin N, ∑ j : Fin N,
        (hermiteFunction i.val x*hermiteFunction j.val y)*
          (hermiteFunction i.val z*hermiteFunction j.val z) := by
    intro z
    unfold hermiteKernel
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hInt : ∀ i j : Fin N, Integrable (fun z : ℝ =>
      (hermiteFunction i.val x*hermiteFunction j.val y)*
        (hermiteFunction i.val z*hermiteFunction j.val z)) := by
    intro i j
    exact (integrable_hermiteFunction_product i.val j.val).const_mul _
  simp_rw [hid]
  rw [integral_finsetSum Finset.univ (fun i hi => integrable_finsetSum _ (fun j hj => hInt i j))]
  unfold hermiteKernel
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j hj => hInt i j)]
  simp_rw [integral_const_mul,hermiteFunction_orthogonality,Fin.val_inj]
  simp

theorem hermiteKernel_symmetric (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : hermiteKernel N x y = hermiteKernel N y x := by
  simp [hermiteKernel,mul_comm]

theorem hermiteKernel_continuous (N : ℕ /- [definition] -/) :
    Continuous (fun p : ℝ × ℝ => hermiteKernel N p.1 p.2) := by
  unfold hermiteKernel
  apply continuous_finset_sum
  intro k hk
  exact ((continuous_hermiteFunction k.val).comp continuous_fst).mul
    ((continuous_hermiteFunction k.val).comp continuous_snd)

theorem hermiteKernel_diagonal_nonnegative (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : 0 ≤ hermiteKernel N x x := by
  exact Finset.sum_nonneg (fun k hk => mul_self_nonneg _)

theorem hermiteKernel_diagonal_positive (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : 0 < hermiteKernel N x x := by
  have h0 : 0 < hermiteFunction 0 x := by
    unfold hermiteFunction
    simp only [hermite_zero,map_one,one_mul]
    exact div_pos (Real.exp_pos _) (hermiteNorm_pos _)
  have hle := Finset.single_le_sum (fun k (hk : k ∈ (Finset.univ : Finset (Fin N))) =>
    mul_self_nonneg (hermiteFunction k.val x)) (Finset.mem_univ (⟨0,hN⟩ : Fin N))
  exact lt_of_lt_of_le (mul_pos h0 h0) hle

theorem hermiteKernel_positive_joint_probe :
    ∃ N : ℕ, 0 < N ∧ (∀ x : ℝ, 0 < hermiteKernel N x x) := by
  exact ⟨3,by norm_num,fun x => hermiteKernel_diagonal_positive 3 x (by norm_num)⟩

theorem hermiteKernel_quadratic (N m : ℕ /- [definition] -/)
    (x c : Fin m → ℝ /- [definition] -/) :
    (∑ i : Fin m, ∑ j : Fin m, c i*c j*hermiteKernel N (x i) (x j)) =
      ∑ k : Fin N, (∑ i : Fin m, c i*hermiteFunction k.val (x i))^2 := by
  simp_rw [hermiteKernel,Finset.mul_sum]
  calc
    _ = ∑ i : Fin m, ∑ k : Fin N, ∑ j : Fin m,
        c i*c j*(hermiteFunction k.val (x i)*hermiteFunction k.val (x j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : Fin N, ∑ i : Fin m, ∑ j : Fin m,
        c i*c j*(hermiteFunction k.val (x i)*hermiteFunction k.val (x j)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_two,Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem hermiteKernel_quadratic_nonnegative (N m : ℕ /- [definition] -/)
    (x c : Fin m → ℝ /- [definition] -/) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, c i*c j*hermiteKernel N (x i) (x j) := by
  rw [hermiteKernel_quadratic]
  exact Finset.sum_nonneg (fun k hk => sq_nonneg _)

end RMTFoundations.TracyWidom.GUEProjection

#print axioms RMTFoundations.TracyWidom.GUEProjection.hermitePolynomialKernel
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermite_eval_recur
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermitePolynomialKernel_cd
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteFunction_pair
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_polynomial
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_cd_cross
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_cd
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermite_cd_joint_probe
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_trace
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_projection
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_symmetric
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_continuous
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_diagonal_nonnegative
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_diagonal_positive
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_positive_joint_probe
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_quadratic
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteKernel_quadratic_nonnegative
