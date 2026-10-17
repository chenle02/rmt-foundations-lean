import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Andreief
open MeasureTheory Matrix Equiv Finset
open scoped BigOperators

theorem orthogonal_product_integral
    (N : ℕ /- [definition] -/)
    (f : Fin N → ℝ → ℝ /- [definition] -/)
    (ho : ∀ i j, (∫ x : ℝ, f i x*f j x) = if i=j then 1 else 0 /- [standing] -/)
    (σ τ : Equiv.Perm (Fin N) /- [definition] -/) :
    (∫ x : Fin N → ℝ, ∏ i, f (σ i) (x i)*f (τ i) (x i)
      ∂Measure.pi (fun _ => (volume : Measure ℝ))) = if σ=τ then 1 else 0 := by
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => f (σ i) t*f (τ i) t)]
  simp_rw [ho]
  by_cases h : σ=τ
  · subst τ
    simp
  · rw [if_neg h]
    have hex : ∃ i, σ i ≠ τ i := by
      by_contra hno
      apply h
      apply Equiv.ext
      intro i
      exact Classical.not_not.mp (not_exists.mp hno i)
    obtain ⟨i,hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)


theorem orthonormal_determinant_integrable
    (N : ℕ /- [definition] -/)
    (f : Fin N → ℝ → ℝ /- [definition] -/)
    (hi : ∀ i j, Integrable (fun x : ℝ => f i x*f j x) /- [standing] -/) :
    Integrable (fun x : Fin N → ℝ => (Matrix.det (fun i j : Fin N => f j (x i)))^2)
      (Measure.pi (fun _ => (volume : Measure ℝ))) := by
  have hid : ∀ x : Fin N → ℝ, (Matrix.det (fun i j : Fin N => f j (x i)))^2 =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, f (σ i) (x i)*f (τ i) (x i) := by
    intro x
    change (Matrix.det (Matrix.of (fun i j : Fin N => f j (x i))))^2 = _
    rw [← Matrix.det_transpose,Matrix.det_apply',pow_two]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hid]
  apply integrable_finsetSum
  intro σ hσ
  apply integrable_finsetSum
  intro τ hτ
  exact (Integrable.fintype_prod (fun i => hi (σ i) (τ i))).const_mul _

theorem orthonormal_determinant_integral
    (N : ℕ /- [definition] -/)
    (f : Fin N → ℝ → ℝ /- [definition] -/)
    (hi : ∀ i j, Integrable (fun x : ℝ => f i x*f j x) /- [standing] -/)
    (ho : ∀ i j, (∫ x : ℝ, f i x*f j x) = if i=j then 1 else 0 /- [standing] -/) :
    (∫ x : Fin N → ℝ, (Matrix.det (fun i j : Fin N => f j (x i)))^2
      ∂Measure.pi (fun _ => (volume : Measure ℝ))) = N.factorial := by
  have hid : ∀ x : Fin N → ℝ, (Matrix.det (fun i j : Fin N => f j (x i)))^2 =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, f (σ i) (x i)*f (τ i) (x i) := by
    intro x
    change (Matrix.det (Matrix.of (fun i j : Fin N => f j (x i))))^2 = _
    rw [← Matrix.det_transpose,Matrix.det_apply',pow_two]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [Finset.prod_mul_distrib]
    ring
  have hInt : ∀ σ τ : Equiv.Perm (Fin N), Integrable
      (fun x : Fin N → ℝ =>
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, f (σ i) (x i)*f (τ i) (x i))
      (Measure.pi (fun _ => (volume : Measure ℝ))) := by
    intro σ τ
    exact (Integrable.fintype_prod (fun i => hi (σ i) (τ i))).const_mul _
  simp_rw [hid]
  rw [integral_finsetSum Finset.univ (fun σ hσ => integrable_finsetSum _ (fun τ hτ => hInt σ τ))]
  calc
    _ = ∑ σ : Equiv.Perm (Fin N), (1:ℝ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [integral_finsetSum Finset.univ (fun τ hτ => hInt σ τ)]
      simp_rw [integral_const_mul,orthogonal_product_integral N f ho]
      rw [Finset.sum_eq_single σ]
      · simp
        norm_cast
        simpa only [Units.val_one] using congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
      · intro τ hτ hne
        simp [Ne.symm hne]
      · simp
    _ = N.factorial := by simp [Fintype.card_perm]


end RMTFoundations.TracyWidom.Andreief

#print axioms RMTFoundations.TracyWidom.Andreief.orthogonal_product_integral
#print axioms RMTFoundations.TracyWidom.Andreief.orthonormal_determinant_integrable
#print axioms RMTFoundations.TracyWidom.Andreief.orthonormal_determinant_integral
