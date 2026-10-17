import RMTFoundations.Airy.Spectral
import RMTFoundations.TracyWidom.OrderOneBounds



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.OrderTwoPositive

open MeasureTheory
open RMTFoundations.Fredholm RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds

/-- The actual Airy-kernel determinant is strictly positive at every real shift.
The spectral family, summability, and strict contraction are obtained from
Airy results; none is a hypothesis of this adapter. -/
theorem TW2R_positive
    (s : ℝ) -- [definition]
    : 0 < TW2R s := by
  obtain ⟨ι, hι, b, a, he, hk, ha, hak, htB, htK, hpB, hpK⟩ := airy_spectral_data s
  letI : Countable ι := hι
  have hupper : ∀ i, (a i)^2 < 1 := by
    intro i
    have hn := real_eigenvalue_norm_le (airyKernelShift s) (b i)
      (b.orthonormal.norm_eq_one i) ((a i)^2) (hk i)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hn
    exact hn.trans_lt (norm_airyKernelShift_lt_one s)
  have hprod : HasProd (fun i => 1 - (a i)^2) (TW2R s) := by
    simpa only [TW2R, TW2, Complex.ofReal_neg, Complex.ofReal_one,
      neg_one_mul, sub_eq_add_neg] using hpK (-1)
  rw [← hprod.tprod_eq]
  exact signed_tprod_pos (fun i => (a i)^2) hak.of_norm hupper

/-- Every adapter binder is realized at zero with a nonzero actual Airy row.
The determinant positivity and contraction hold on this same physical instance. -/
theorem TW2R_positive_joint_probe :
    ∃ s : ℝ, s = 0 ∧ 0 < airyAiReal s ∧ airyBoundaryVector s ≠ 0 ∧
      ‖airyKernelShift s‖ < 1 ∧ 0 < TW2R s ∧ TW2R s ≤ 1 := by
  refine ⟨0, rfl, airyAiReal_zero_pos, airyBoundaryVector_ne_zero 0,
    norm_airyKernelShift_lt_one 0, TW2R_positive 0, ?_⟩
  exact (TW2R_mem_Icc_of_contraction 0 (norm_airyKernelShift_lt_one 0).le).2

end RMTFoundations.TracyWidom.OrderTwoPositive

#print axioms RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive
#print axioms RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive_joint_probe
