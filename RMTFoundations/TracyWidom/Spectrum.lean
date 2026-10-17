import RMTFoundations.TracyWidom.OrderOneBounds
import RMTFoundations.Airy.Spectral


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace Topology
open RMTFoundations.Airy RMTFoundations.Fredholm RMTFoundations.TWOneBounds

theorem hankel_spectrum_subset
    (s : ℝ /- [definition] -/) :
    spectrum ℝ (airyHankelShift s) ⊆ Ioo (-1) 1 := by
  letI : Nontrivial (Lp ℝ 2 halfLineMeasure) :=
    ⟨⟨airyBoundaryVector 0, 0, airyBoundaryVector_ne_zero 0⟩⟩
  intro a ha
  have h := (spectrum.norm_le_norm_of_mem ha).trans_lt (norm_airyHankelShift_lt_one s)
  simpa only [Real.norm_eq_abs, abs_lt, mem_Ioo] using h

theorem kernel_spectrum_subset
    (s : ℝ /- [definition] -/) :
    spectrum ℝ (airyKernelShift s) ⊆ Ico 0 1 := by
  letI : Nontrivial (Lp ℝ 2 halfLineMeasure) :=
    ⟨⟨airyBoundaryVector 0, 0, airyBoundaryVector_ne_zero 0⟩⟩
  have hnorm : ‖airyKernelShift s‖ < 1 := by
    have h := norm_airyHankelShift_lt_one s
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_lt
      (by nlinarith [norm_nonneg (airyHankelShift s)])
  intro a ha
  have h := (spectrum.norm_le_norm_of_mem ha).trans_lt hnorm
  have hu : a < 1 := (abs_lt.mp (by simpa only [Real.norm_eq_abs] using h)).2
  refine ⟨?_, hu⟩
  by_cases hz : a = 0
  · simp [hz]
  have he := ((isTraceClass_airyKernelShift s).isCompactOperator.hasEigenvalue_iff_mem_spectrum hz).mpr ha
  obtain ⟨v, hv, hne⟩ := he.exists_hasEigenvector
  have hev : airyKernelShift s v = a • v := Module.End.mem_eigenspace_iff.mp hv
  have hp := RMTFoundations.Fredholm.airyKernelShift_quadratic_nonneg s v
  rw [hev, inner_smul_right, real_inner_self_eq_norm_sq] at hp
  have hvp : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  exact (mul_nonneg_iff_of_pos_right hvp).mp hp

theorem spectrum_joint_probe :
    ‖shiftedUnitVector 0‖ = 1 ∧ spectrum ℝ (airyHankelShift 0) ⊆ Ioo (-1) 1 ∧
      spectrum ℝ (airyKernelShift 0) ⊆ Ico 0 1 :=
  ⟨shiftedUnitVector_norm 0, hankel_spectrum_subset 0, kernel_spectrum_subset 0⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.hankel_spectrum_subset
#print axioms RMTFoundations.TracyWidom.kernel_spectrum_subset
#print axioms RMTFoundations.TracyWidom.spectrum_joint_probe
