import RMTFoundations.TracyWidom.GUEDensity
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUETruncatedGram
open MeasureTheory Matrix Equiv Finset RMTFoundations.TracyWidom.GUEProjection
open scoped BigOperators

theorem determinant_square_expansion
    (N : ℕ /- [definition] -/)
    (f : Fin N → ℝ → ℝ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    (Matrix.det (fun i j : Fin N => f j (x i)))^2 =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, f (σ i) (x i)*f (τ i) (x i) := by
  change (Matrix.det (Matrix.of (fun i j : Fin N => f j (x i))))^2 = _
  rw [← Matrix.det_transpose (Matrix.of (fun i j : Fin N => f j (x i))),Matrix.det_apply',pow_two]
  dsimp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [Finset.prod_mul_distrib]
  ring

theorem gram_determinant_integrable
    (N : ℕ /- [definition] -/)
    (μ : Measure ℝ /- [definition] -/)
    [hμ : SigmaFinite μ /- [standing] -/]
    (f : Fin N → ℝ → ℝ /- [definition] -/)
    (hi : ∀ i j, Integrable (fun x : ℝ => f i x*f j x) μ /- [standing] -/) :
    Integrable (fun x : Fin N → ℝ => (Matrix.det (fun i j : Fin N => f j (x i)))^2)
      (Measure.pi (fun _ => μ)) := by
  simp_rw [determinant_square_expansion]
  apply integrable_finsetSum
  intro σ hσ
  apply integrable_finsetSum
  intro τ hτ
  exact (Integrable.fintype_prod (fun i => hi (σ i) (τ i))).const_mul _

theorem gram_determinant_integral
    (N : ℕ /- [definition] -/)
    (μ : Measure ℝ /- [definition] -/)
    [hμ : SigmaFinite μ /- [standing] -/]
    (f : Fin N → ℝ → ℝ /- [definition] -/)
    (hi : ∀ i j, Integrable (fun x : ℝ => f i x*f j x) μ /- [standing] -/) :
    (∫ x : Fin N → ℝ, (Matrix.det (fun i j : Fin N => f j (x i)))^2
      ∂Measure.pi (fun _ => μ)) =
      (N.factorial:ℝ)*Matrix.det (fun i j : Fin N => ∫ x : ℝ, f i x*f j x ∂μ) := by
  let G : Matrix (Fin N) (Fin N) ℝ := fun i j => ∫ x : ℝ, f i x*f j x ∂μ
  have hInt : ∀ σ τ : Equiv.Perm (Fin N), Integrable
      (fun x : Fin N → ℝ =>
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, f (σ i) (x i)*f (τ i) (x i))
      (Measure.pi (fun _ => μ)) := by
    intro σ τ
    exact (Integrable.fintype_prod (fun i => hi (σ i) (τ i))).const_mul _
  simp_rw [determinant_square_expansion]
  rw [integral_finsetSum Finset.univ (fun σ hσ => integrable_finsetSum _ (fun τ hτ => hInt σ τ))]
  calc
    _ = ∑ σ : Equiv.Perm (Fin N), G.det := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [integral_finsetSum Finset.univ (fun τ hτ => hInt σ τ)]
      have hprod : ∀ τ : Equiv.Perm (Fin N),
          (∫ x : Fin N → ℝ, ∏ i, f (σ i) (x i)*f (τ i) (x i)
            ∂Measure.pi (fun _ => μ)) = ∏ i, ∫ x : ℝ, f (σ i) x*f (τ i) x ∂μ := by
        intro τ
        exact integral_fintype_prod_eq_prod (fun i (x : ℝ) => f (σ i) x*f (τ i) x)
      simp_rw [integral_const_mul,hprod]
      change (∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, G (σ i) (τ i)) = G.det
      rw [show (∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, G (σ i) (τ i)) =
        ((Equiv.Perm.sign σ:ℤ):ℝ) * (G.submatrix σ id).transpose.det by
          rw [Matrix.det_apply',Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ hτ
          simp only [Matrix.transpose_apply,Matrix.submatrix_apply,id_eq]
          ring]
      rw [Matrix.det_transpose,Matrix.det_permute]
      have hs : ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign σ:ℤ):ℝ)=1 := by
        norm_cast
        simpa only [Units.val_one] using congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
      change ((Equiv.Perm.sign σ:ℤ):ℝ)*(((Equiv.Perm.sign σ:ℤ):ℝ)*G.det)=G.det
      rw [← mul_assoc,hs,one_mul]
    _ = (N.factorial:ℝ)*G.det := by simp [Fintype.card_perm]

theorem gue_truncated_gram_integral
    (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    (∫ x : Fin N → ℝ, gueDensity N x
      ∂Measure.pi (fun _ => (volume : Measure ℝ).restrict (Set.Iic s))) =
      Matrix.det (fun i j : Fin N =>
        ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x*hermiteFunction j.val x) := by
  have hid : gueDensity N = fun x : Fin N → ℝ =>
      (Matrix.det (fun i j : Fin N => hermiteFunction j.val (x i)))^2/(N.factorial:ℝ) := by
    ext x
    rw [gue_density_determinantal,hermite_kernel_det_square]
  rw [hid,integral_div,gram_determinant_integral N _ _
    (fun i j => (integrable_hermiteFunction_product i.val j.val).restrict)]
  field_simp

theorem gue_static_gap_integral
    (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    (∫ x : Fin N → ℝ in {x | ∀ i, x i ≤ s}, gueDensity N x
      ∂Measure.pi (fun _ => (volume : Measure ℝ))) =
      Matrix.det (fun i j : Fin N =>
        ∫ x : ℝ in Set.Iic s, hermiteFunction i.val x*hermiteFunction j.val x) := by
  have hset : {x : Fin N → ℝ | ∀ i, x i ≤ s} =
      Set.univ.pi (fun _ : Fin N => Set.Iic s) := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Iic]
  rw [hset,Measure.restrict_pi_pi]
  exact gue_truncated_gram_integral N s

theorem gram_all_binder_joint_probe :
    ∃ μ : Measure ℝ, SigmaFinite μ ∧ ∃ f : Fin 3 → ℝ → ℝ,
      (∀ i j, Integrable (fun x : ℝ => f i x*f j x) μ) ∧
      (∀ i, ∃ x : ℝ, f i x ≠ 0) ∧
      Integrable (fun x : Fin 3 → ℝ => (Matrix.det (fun i j : Fin 3 => f j (x i)))^2)
        (Measure.pi (fun _ => μ)) ∧
      (∫ x : Fin 3 → ℝ, (Matrix.det (fun i j : Fin 3 => f j (x i)))^2
        ∂Measure.pi (fun _ => μ)) =
        ((3:ℕ).factorial:ℝ)*Matrix.det (fun i j : Fin 3 => ∫ x : ℝ, f i x*f j x ∂μ) := by
  refine ⟨volume,inferInstance,(fun i => hermiteFunction i.val),
    (fun i j => integrable_hermiteFunction_product i.val j.val),?_,
    gram_determinant_integrable 3 volume _
      (fun i j => integrable_hermiteFunction_product i.val j.val),
    gram_determinant_integral 3 volume _
      (fun i j => integrable_hermiteFunction_product i.val j.val)⟩
  intro i
  by_contra h
  have hz : ∀ x : ℝ, hermiteFunction i.val x = 0 := by simpa using h
  have hi := hermiteFunction_orthogonality i.val i.val
  simp [hz] at hi

theorem restricted_hermite_joint_probe :
    ∃ μ : Measure ℝ, μ = (volume : Measure ℝ).restrict (Set.Iic 1) ∧
      SigmaFinite μ ∧ ∃ f : Fin 3 → ℝ → ℝ,
      f = (fun i => hermiteFunction i.val) ∧
      f 0 0 ≠ 0 ∧ (0:ℝ) ≤ 1 ∧
      (∀ i j, Integrable (fun x : ℝ => f i x*f j x) μ) ∧
      (∀ i, ∃ x : ℝ, f i x ≠ 0) ∧
      Integrable (fun x : Fin 3 → ℝ => (Matrix.det (fun i j : Fin 3 => f j (x i)))^2)
        (Measure.pi (fun _ => μ)) ∧
      (∫ x : Fin 3 → ℝ, (Matrix.det (fun i j : Fin 3 => f j (x i)))^2
        ∂Measure.pi (fun _ => μ)) =
        ((3:ℕ).factorial:ℝ)*Matrix.det (fun i j : Fin 3 => ∫ x : ℝ, f i x*f j x ∂μ) ∧
      (∫ x : Fin 3 → ℝ in {x | ∀ i, x i ≤ 1}, gueDensity 3 x
        ∂Measure.pi (fun _ => (volume : Measure ℝ))) =
        Matrix.det (fun i j : Fin 3 =>
          ∫ x : ℝ in Set.Iic 1, hermiteFunction i.val x*hermiteFunction j.val x) := by
  refine ⟨(volume : Measure ℝ).restrict (Set.Iic 1),rfl,inferInstance,
    (fun i => hermiteFunction i.val),rfl,?_,by norm_num,
    (fun i j => (integrable_hermiteFunction_product i.val j.val).restrict),?_,
    gram_determinant_integrable 3 _ _
      (fun i j => (integrable_hermiteFunction_product i.val j.val).restrict),
    gram_determinant_integral 3 _ _
      (fun i j => (integrable_hermiteFunction_product i.val j.val).restrict),
    gue_static_gap_integral 3 1⟩
  · simp [hermiteFunction,Polynomial.hermite_zero,ne_of_gt (hermiteNorm_pos 0)]
  · intro i
    by_contra h
    have hz : ∀ x : ℝ, hermiteFunction i.val x = 0 := by simpa using h
    have hi := hermiteFunction_orthogonality i.val i.val
    simp [hz] at hi

end RMTFoundations.TracyWidom.GUETruncatedGram

#print axioms RMTFoundations.TracyWidom.GUETruncatedGram.determinant_square_expansion
#print axioms RMTFoundations.TracyWidom.GUETruncatedGram.gram_determinant_integrable
#print axioms RMTFoundations.TracyWidom.GUETruncatedGram.gram_determinant_integral
#print axioms RMTFoundations.TracyWidom.GUETruncatedGram.gue_truncated_gram_integral
#print axioms RMTFoundations.TracyWidom.GUETruncatedGram.gram_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.GUETruncatedGram.gue_static_gap_integral
#print axioms RMTFoundations.TracyWidom.GUETruncatedGram.restricted_hermite_joint_probe
