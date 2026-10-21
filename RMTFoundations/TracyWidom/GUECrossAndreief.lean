import RMTFoundations.TracyWidom.GUEAndreief
import RMTFoundations.TracyWidom.GUEDensity
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUECrossAndreief
open MeasureTheory Matrix Equiv Finset
open scoped BigOperators
open RMTFoundations.TracyWidom.GUEProjection

/-- Entrywise product integrability suffices for absolute integrability of the
full cross-determinant product on the unordered configuration space. -/
theorem cross_determinant_integrable (N : ℕ /- [definition] -/)
    (f g : Fin N → ℝ → ℝ /- [definition] -/)
    (hi : ∀ i j, Integrable (fun x : ℝ => f i x*g j x) /- [standing] -/) :
    Integrable (fun x : Fin N → ℝ =>
      (Matrix.det (fun i j : Fin N => f j (x i))) *
      (Matrix.det (fun i j : Fin N => g j (x i))))
      (Measure.pi (fun _ => (volume : Measure ℝ))) := by
  have hid : ∀ x : Fin N → ℝ,
      (Matrix.det (fun i j : Fin N => f j (x i))) *
      (Matrix.det (fun i j : Fin N => g j (x i))) =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, f (σ i) (x i)*g (τ i) (x i) := by
    intro x
    change (Matrix.det (Matrix.of (fun i j : Fin N => f j (x i)))) *
      (Matrix.det (Matrix.of (fun i j : Fin N => g j (x i)))) = _
    rw [← Matrix.det_transpose (Matrix.of (fun i j : Fin N => f j (x i))), Matrix.det_apply',
      ← Matrix.det_transpose (Matrix.of (fun i j : Fin N => g j (x i))), Matrix.det_apply']
    dsimp only [Matrix.transpose_apply, Matrix.of_apply]
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

/-- Cross-function Andreief identity, with entrywise product integrability.
No orthonormality and no stochastic representation are assumed. -/
theorem cross_determinant_integral (N : ℕ /- [definition] -/)
    (f g : Fin N → ℝ → ℝ /- [definition] -/)
    (hi : ∀ i j, Integrable (fun x : ℝ => f i x*g j x) /- [standing] -/) :
    (∫ x : Fin N → ℝ,
      (Matrix.det (fun i j : Fin N => f j (x i))) *
      (Matrix.det (fun i j : Fin N => g j (x i)))
      ∂Measure.pi (fun _ => (volume : Measure ℝ))) =
      (N.factorial:ℝ) * (Matrix.det (fun i j : Fin N => ∫ x : ℝ, f i x*g j x)) := by
  let H : Matrix (Fin N) (Fin N) ℝ := fun i j => ∫ x : ℝ, f i x*g j x
  have hid : ∀ x : Fin N → ℝ,
      (Matrix.det (fun i j : Fin N => f j (x i))) *
      (Matrix.det (fun i j : Fin N => g j (x i))) =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, f (σ i) (x i)*g (τ i) (x i) := by
    intro x
    change (Matrix.det (Matrix.of (fun i j : Fin N => f j (x i)))) *
      (Matrix.det (Matrix.of (fun i j : Fin N => g j (x i)))) = _
    rw [← Matrix.det_transpose (Matrix.of (fun i j : Fin N => f j (x i))), Matrix.det_apply',
      ← Matrix.det_transpose (Matrix.of (fun i j : Fin N => g j (x i))), Matrix.det_apply']
    dsimp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [Finset.prod_mul_distrib]
    ring
  have hProd : ∀ σ τ : Equiv.Perm (Fin N),
      (∫ x : Fin N → ℝ, ∏ i, f (σ i) (x i)*g (τ i) (x i)
        ∂Measure.pi (fun _ => (volume : Measure ℝ))) = ∏ i, H (σ i) (τ i) := by
    intro σ τ
    rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => f (σ i) t*g (τ i) t)]
  have hInt : ∀ σ τ : Equiv.Perm (Fin N), Integrable
      (fun x : Fin N → ℝ =>
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, f (σ i) (x i)*g (τ i) (x i))
      (Measure.pi (fun _ => (volume : Measure ℝ))) := by
    intro σ τ
    exact (Integrable.fintype_prod (fun i => hi (σ i) (τ i))).const_mul _
  simp_rw [hid]
  rw [integral_finsetSum Finset.univ
    (fun σ hσ => integrable_finsetSum _ (fun τ hτ => hInt σ τ))]
  calc
    _ = ∑ σ : Equiv.Perm (Fin N), H.det := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [integral_finsetSum Finset.univ (fun τ hτ => hInt σ τ)]
      simp_rw [integral_const_mul]
      simp_rw [hProd]
      change (∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ:ℤ):ℝ)*((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, H (σ i) (τ i)) = H.det
      have hdet : (∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign τ:ℤ):ℝ)*
          ∏ i, H (σ i) (τ i)) = (H.submatrix σ id).det := by
        rw [← Matrix.det_transpose, Matrix.det_apply']
        rfl
      calc
        _ = ((Equiv.Perm.sign σ:ℤ):ℝ) *
            (∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign τ:ℤ):ℝ)*
              ∏ i, H (σ i) (τ i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ hτ
          ring
        _ = ((Equiv.Perm.sign σ:ℤ):ℝ) * (H.submatrix σ id).det := by rw [hdet]
        _ = (((Equiv.Perm.sign σ:ℤ):ℝ) * ((Equiv.Perm.sign σ:ℤ):ℝ)) * H.det := by
          rw [Matrix.det_permute]
          ring
        _ = H.det := by
          have hs : ((Equiv.Perm.sign σ:ℤ):ℝ) * ((Equiv.Perm.sign σ:ℤ):ℝ) = 1 := by
            norm_cast
            simpa only [Units.val_one] using
              congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
          rw [hs,one_mul]
    _ = (N.factorial:ℝ) * H.det := by simp [Fintype.card_perm]

theorem cross_Andreief_all_binder_joint_probe :
    ∃ (N : ℕ) (f g : Fin N → ℝ → ℝ),
      N = 3 ∧
      (∀ i j, Integrable (fun x : ℝ => f i x*g j x)) ∧
      (∀ i, ∃ x : ℝ, f i x ≠ 0) ∧ (∀ i, ∃ x : ℝ, g i x ≠ 0) ∧
      Integrable (fun x : Fin N → ℝ =>
        (Matrix.det (fun i j : Fin N => f j (x i))) *
        (Matrix.det (fun i j : Fin N => g j (x i))))
        (Measure.pi (fun _ => (volume : Measure ℝ))) ∧
      (Matrix.det (fun i j : Fin N => ∫ x : ℝ, f i x*g j x)) = 1 ∧
      (∫ x : Fin N → ℝ,
        (Matrix.det (fun i j : Fin N => f j (x i))) *
        (Matrix.det (fun i j : Fin N => g j (x i)))
        ∂Measure.pi (fun _ => (volume : Measure ℝ))) = 6 := by
  obtain ⟨f,hi,ho,hne,_,_⟩ := gue_density_all_binder_probe
  have hm : (fun i j : Fin 3 => ∫ x : ℝ, f i x*f j x) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    simp [ho, Matrix.one_apply]
  refine ⟨3,f,f,rfl,hi,hne,hne,cross_determinant_integrable 3 f f hi,?_,?_⟩
  · rw [hm,Matrix.det_one]
  · rw [cross_determinant_integral 3 f f hi,hm,Matrix.det_one]
    norm_num [Nat.factorial]

end RMTFoundations.TracyWidom.GUECrossAndreief

#print axioms RMTFoundations.TracyWidom.GUECrossAndreief.cross_determinant_integrable
#print axioms RMTFoundations.TracyWidom.GUECrossAndreief.cross_determinant_integral
#print axioms RMTFoundations.TracyWidom.GUECrossAndreief.cross_Andreief_all_binder_joint_probe
