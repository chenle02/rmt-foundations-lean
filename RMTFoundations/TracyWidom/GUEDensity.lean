import RMTFoundations.TracyWidom.GUEHermiteKernel
import RMTFoundations.TracyWidom.GUEAndreief
import Mathlib.LinearAlgebra.Vandermonde
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUEProjection
open MeasureTheory Polynomial Real RMTFoundations.TracyWidom.Andreief
theorem hermite_kernel_det_square (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    (Matrix.det (fun i j : Fin N => hermiteKernel N (x i) (x j))) =
      (Matrix.det (fun i k : Fin N => hermiteFunction k.val (x i)))^2 := by
  let V : Matrix (Fin N) (Fin N) ℝ := fun i k => hermiteFunction k.val (x i)
  have hid : (fun i j : Fin N => hermiteKernel N (x i) (x j)) = V*V.transpose := by
    ext i j
    change (∑ k : Fin N, hermiteFunction k.val (x i)*hermiteFunction k.val (x j)) =
      (∑ k : Fin N, hermiteFunction k.val (x i)*hermiteFunction k.val (x j))
    rfl
  rw [hid,Matrix.det_mul,Matrix.det_transpose,pow_two]

theorem hermite_eval_vandermonde (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    Matrix.det (fun i j : Fin N => aeval (x i) (Polynomial.hermite j.val)) =
      (Matrix.vandermonde x).det := by
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x
    (fun j : Fin N => (Polynomial.hermite j.val).map (Int.castRingHom ℝ))
    (fun j => by rw [Polynomial.natDegree_map_eq_of_injective (f:=Int.castRingHom ℝ) Int.cast_injective _,Polynomial.natDegree_hermite])
    (fun j => (Polynomial.hermite_monic j.val).map _)
  convert h.symm using 1
  congr 1
  ext i j
  simp [Matrix.of,Polynomial.eval_map,Polynomial.aeval_def,algebraMap_int_eq] <;> rfl

theorem hermite_function_det (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    Matrix.det (fun i k : Fin N => hermiteFunction k.val (x i)) =
      (∏ i,Real.exp (-(x i)^2/4))*(Matrix.vandermonde x).det *
        (∏ k : Fin N,(hermiteNorm k.val)⁻¹) := by
  have hid : (fun i k : Fin N => hermiteFunction k.val (x i)) =
      Matrix.of (fun i k : Fin N => Real.exp (-(x i)^2/4) *
        ((hermiteNorm k.val)⁻¹*aeval (x i) (hermite k.val))) := by
    ext i k
    simp only [Matrix.of_apply,hermiteFunction]
    ring
  rw [hid]
  rw [Matrix.det_mul_column (fun i : Fin N => Real.exp (-(x i)^2/4))
    (fun i k : Fin N => (hermiteNorm k.val)⁻¹*aeval (x i) (hermite k.val))]
  change (∏ i : Fin N, Real.exp (-(x i)^2/4)) *
    Matrix.det (Matrix.of (fun i k : Fin N => (hermiteNorm k.val)⁻¹*aeval (x i) (hermite k.val))) = _
  rw [Matrix.det_mul_row (fun k : Fin N => (hermiteNorm k.val)⁻¹)
    (fun i k : Fin N => aeval (x i) (hermite k.val))]
  change (∏ i : Fin N, Real.exp (-(x i)^2/4)) *
    ((∏ k : Fin N, (hermiteNorm k.val)⁻¹)*
      Matrix.det (fun i k : Fin N => aeval (x i) (hermite k.val))) = _
  rw [hermite_eval_vandermonde]
  ring

noncomputable def gueDensity (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) : ℝ :=
  Real.exp (-(∑ i, (x i)^2)/2)*(Matrix.vandermonde x).det^2 /
    ((N.factorial:ℝ)*(∏ k : Fin N, (k.val.factorial:ℝ)*Real.sqrt (2*Real.pi)))

theorem gue_density_determinantal (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    gueDensity N x =
      Matrix.det (fun i j : Fin N => hermiteKernel N (x i) (x j))/(N.factorial:ℝ) := by
  rw [hermite_kernel_det_square,hermite_function_det]
  have he : (∏ i,Real.exp (-(x i)^2/4))^2 = Real.exp (-(∑ i,(x i)^2)/2) := by
    rw [← Real.exp_sum,pow_two,← Real.exp_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    simp_rw [show ∀ t : ℝ, -t^2/4 + -t^2/4 = -t^2/2 by intro t; ring]
    rw [← Finset.sum_div,Finset.sum_neg_distrib]
  have hn : (∏ k : Fin N,(hermiteNorm k.val)⁻¹)^2 =
      (∏ k : Fin N,(k.val.factorial:ℝ)*Real.sqrt (2*Real.pi))⁻¹ := by
    rw [← Finset.prod_pow,← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    rw [inv_pow,hermiteNorm,Real.sq_sqrt (by positivity)]
  rw [mul_pow,mul_pow,he,hn]
  unfold gueDensity
  ring


theorem gue_density_nonnegative (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) : 0 ≤ gueDensity N x := by
  unfold gueDensity
  positivity

theorem gue_density_positive (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/)
    (hx : Function.Injective x /- [standing] -/) : 0 < gueDensity N x := by
  have hv : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hx
  have hp : 0 < (Matrix.vandermonde x).det^2 := sq_pos_of_ne_zero hv
  unfold gueDensity
  exact div_pos (mul_pos (Real.exp_pos _) hp) (mul_pos (by positivity)
    (Finset.prod_pos (fun k hk => mul_pos (by positivity) (by positivity))))

theorem gue_density_joint_probe :
    ∃ x : Fin 3 → ℝ, Function.Injective x ∧ 0 < gueDensity 3 x ∧
      gueDensity 3 x = Matrix.det (fun i j : Fin 3 => hermiteKernel 3 (x i) (x j))/6 := by
  let x : Fin 3 → ℝ := fun i => i.val
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    change (i.val:ℝ) = (j.val:ℝ) at hij
    exact_mod_cast hij
  refine ⟨x,hx,gue_density_positive 3 x hx,?_⟩
  simpa [Nat.factorial] using gue_density_determinantal 3 x

theorem gue_density_integrable (N : ℕ /- [definition] -/) :
    Integrable (gueDensity N) (Measure.pi (fun _ : Fin N => (volume : Measure ℝ))) := by
  have h := orthonormal_determinant_integrable N (fun i => hermiteFunction i.val)
    (fun i j => integrable_hermiteFunction_product i.val j.val)
  have hid : gueDensity N = fun x : Fin N → ℝ =>
      (Matrix.det (fun i j : Fin N => hermiteFunction j.val (x i)))^2/(N.factorial:ℝ) := by
    ext x
    rw [gue_density_determinantal,hermite_kernel_det_square]
  rw [hid]
  exact h.div_const _

theorem gue_density_integral (N : ℕ /- [definition] -/) :
    (∫ x : Fin N → ℝ, gueDensity N x
      ∂Measure.pi (fun _ => (volume : Measure ℝ))) = 1 := by
  have hid : gueDensity N = fun x : Fin N → ℝ =>
      (Matrix.det (fun i j : Fin N => hermiteFunction j.val (x i)))^2/(N.factorial:ℝ) := by
    ext x
    rw [gue_density_determinantal,hermite_kernel_det_square]
  rw [hid,integral_div]
  have h := orthonormal_determinant_integral N (fun i => hermiteFunction i.val)
    (fun i j => integrable_hermiteFunction_product i.val j.val)
    (fun i j => by simpa only [Fin.val_inj] using hermiteFunction_orthogonality i.val j.val)
  rw [h]
  exact div_self (by positivity)

theorem gue_density_all_binder_probe :
    ∃ f : Fin 3 → ℝ → ℝ,
      (∀ i j, Integrable (fun x : ℝ => f i x*f j x)) ∧
      (∀ i j, (∫ x : ℝ, f i x*f j x) = if i=j then 1 else 0) ∧
      (∀ i, ∃ x : ℝ, f i x ≠ 0) ∧
      (∀ σ τ : Equiv.Perm (Fin 3),
        (∫ x : Fin 3 → ℝ, ∏ i, f (σ i) (x i)*f (τ i) (x i)
          ∂Measure.pi (fun _ => (volume : Measure ℝ))) = if σ=τ then 1 else 0) ∧
      (∫ x : Fin 3 → ℝ, gueDensity 3 x
        ∂Measure.pi (fun _ => (volume : Measure ℝ))) = 1 := by
  refine ⟨(fun i => hermiteFunction i.val),
    (fun i j => integrable_hermiteFunction_product i.val j.val),
    (fun i j => by simpa only [Fin.val_inj] using hermiteFunction_orthogonality i.val j.val),?_,
    (fun σ τ => orthogonal_product_integral 3 (fun i => hermiteFunction i.val)
      (fun i j => by simpa only [Fin.val_inj] using hermiteFunction_orthogonality i.val j.val) σ τ),
    gue_density_integral 3⟩
  intro i
  by_contra h
  have hz : ∀ x : ℝ, hermiteFunction i.val x = 0 := by simpa using h
  have hi := hermiteFunction_orthogonality i.val i.val
  simp [hz] at hi


/-- The normalized finite projection ensemble in the standard GUE eigenvalue scale.
This identifies the explicit eigenvalue density; matrix spectral pushforward and edge convergence
are separate statements. -/
theorem gue_projection_determinantal_ensemble (N : ℕ /- [definition] -/) :
    (∀ x : Fin N → ℝ, 0 ≤ gueDensity N x) ∧
    Integrable (gueDensity N) (Measure.pi (fun _ : Fin N => (volume : Measure ℝ))) ∧
    (∫ x : Fin N → ℝ, gueDensity N x ∂Measure.pi (fun _ => (volume : Measure ℝ))) = 1 ∧
    (∀ x : Fin N → ℝ, gueDensity N x =
      Matrix.det (fun i j : Fin N => hermiteKernel N (x i) (x j))/(N.factorial:ℝ)) ∧
    (∀ x y : ℝ, (∫ z : ℝ, hermiteKernel N x z*hermiteKernel N z y) = hermiteKernel N x y) ∧
    (∫ x : ℝ, hermiteKernel N x x) = N := by
  exact ⟨gue_density_nonnegative N,gue_density_integrable N,gue_density_integral N,
    gue_density_determinantal N,hermiteKernel_projection N,hermiteKernel_trace N⟩

end RMTFoundations.TracyWidom.GUEProjection

#print axioms RMTFoundations.TracyWidom.GUEProjection.hermite_kernel_det_square
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermite_eval_vandermonde
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermite_function_det
#print axioms RMTFoundations.TracyWidom.GUEProjection.gueDensity
#print axioms RMTFoundations.TracyWidom.GUEProjection.gue_density_determinantal
#print axioms RMTFoundations.TracyWidom.GUEProjection.gue_density_nonnegative
#print axioms RMTFoundations.TracyWidom.GUEProjection.gue_density_positive
#print axioms RMTFoundations.TracyWidom.GUEProjection.gue_density_joint_probe
#print axioms RMTFoundations.TracyWidom.GUEProjection.gue_density_integrable
#print axioms RMTFoundations.TracyWidom.GUEProjection.gue_density_integral
#print axioms RMTFoundations.TracyWidom.GUEProjection.gue_density_all_binder_probe
#print axioms RMTFoundations.TracyWidom.GUEProjection.gue_projection_determinantal_ensemble
