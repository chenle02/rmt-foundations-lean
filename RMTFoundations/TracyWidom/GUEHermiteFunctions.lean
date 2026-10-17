import RMTFoundations.TracyWidom.GUEHermiteFoundations
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Function.L2Space
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUEProjection
open MeasureTheory Polynomial Real
noncomputable def hermiteNorm (n : ℕ /- [definition] -/) : ℝ :=
  Real.sqrt ((n.factorial : ℝ) * Real.sqrt (2 * Real.pi))

noncomputable def hermiteFunction (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  aeval x (hermite n) * Real.exp (-(x^2/4)) / hermiteNorm n

theorem hermiteNorm_pos (n : ℕ /- [definition] -/) : 0 < hermiteNorm n := by
  unfold hermiteNorm
  positivity

theorem hermiteFunction_product (m n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    hermiteFunction m x * hermiteFunction n x =
      (aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x^2/2))) /
        (hermiteNorm m * hermiteNorm n) := by
  have h : Real.exp (-(x^2/4)) * Real.exp (-(x^2/4)) = Real.exp (-(x^2/2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold hermiteFunction
  rw [← h]
  ring

theorem continuous_hermiteFunction (n : ℕ /- [definition] -/) :
    Continuous (hermiteFunction n) := by
  unfold hermiteFunction
  exact ((hermite n).continuous_aeval.mul
    (Real.continuous_exp.comp (((continuous_id.pow 2).div_const 4).neg))).div_const _

theorem integrable_hermiteFunction_product (m n : ℕ /- [definition] -/) :
    Integrable (fun x : ℝ => hermiteFunction m x * hermiteFunction n x) := by
  simp_rw [hermiteFunction_product]
  exact (integrable_aeval_mul_aeval_mul_gaussian (hermite m) (hermite n)).div_const _

theorem hermiteFunction_orthogonality (m n : ℕ /- [definition] -/) :
    (∫ x : ℝ, hermiteFunction m x * hermiteFunction n x) =
      if m=n then 1 else 0 := by
  simp_rw [hermiteFunction_product]
  rw [integral_div,integral_hermite_mul_hermite_mul_gaussian]
  split_ifs with h
  · subst m
    unfold hermiteNorm
    rw [Real.mul_self_sqrt (by positivity)]
    exact div_self (by positivity)
  · simp

theorem hermiteFunction_memLp (n : ℕ /- [definition] -/) :
    MemLp (hermiteFunction n) 2 (volume : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq (continuous_hermiteFunction n).aestronglyMeasurable).2
  simpa [pow_two] using integrable_hermiteFunction_product n n

noncomputable def hermiteVector (n : ℕ /- [definition] -/) :
    Lp ℝ 2 (volume : Measure ℝ) := (hermiteFunction_memLp n).toLp _

theorem hermiteVector_apply_ae (n : ℕ /- [definition] -/) :
    ⇑(hermiteVector n) =ᵐ[volume] hermiteFunction n :=
  MemLp.coeFn_toLp _

theorem hermiteVector_inner (m n : ℕ /- [definition] -/) :
    inner ℝ (hermiteVector m) (hermiteVector n) = if m=n then 1 else 0 := by
  rw [L2.inner_def]
  have hid : (fun x : ℝ => inner ℝ (hermiteVector m x) (hermiteVector n x)) =ᵐ[volume]
      (fun x : ℝ => hermiteFunction m x * hermiteFunction n x) := by
    filter_upwards [hermiteVector_apply_ae m,hermiteVector_apply_ae n] with x hx hy
    simp [hx,hy,RCLike.inner_apply,mul_comm]
  rw [integral_congr_ae hid,hermiteFunction_orthogonality]

theorem hermiteVector_orthonormal : Orthonormal ℝ hermiteVector :=
  orthonormal_iff_ite.mpr hermiteVector_inner

theorem hermiteVector_nonzero (n : ℕ /- [definition] -/) : hermiteVector n ≠ 0 := by
  have h := hermiteVector_orthonormal.norm_eq_one n
  intro hz
  rw [hz,norm_zero] at h
  norm_num at h

theorem hermite_joint_probe :
    ∃ v : ℕ → Lp ℝ 2 (volume : Measure ℝ),
      v=hermiteVector ∧ Orthonormal ℝ v ∧ (∀ n, v n ≠ 0) := by
  exact ⟨hermiteVector,rfl,hermiteVector_orthonormal,hermiteVector_nonzero⟩


end RMTFoundations.TracyWidom.GUEProjection

#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteNorm
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteFunction
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteNorm_pos
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteFunction_product
#print axioms RMTFoundations.TracyWidom.GUEProjection.continuous_hermiteFunction
#print axioms RMTFoundations.TracyWidom.GUEProjection.integrable_hermiteFunction_product
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteFunction_orthogonality
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteFunction_memLp
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteVector
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteVector_apply_ae
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteVector_inner
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteVector_orthonormal
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermiteVector_nonzero
#print axioms RMTFoundations.TracyWidom.GUEProjection.hermite_joint_probe
