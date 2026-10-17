import RMTFoundations.Airy.Spectral
import RMTFoundations.TracyWidom.OrderOneBounds


set_option autoImplicit false

namespace RMTFoundations.TracyWidom.OrderTwoFactorization

open MeasureTheory InnerProductSpace
open scoped Topology
open RMTFoundations.Airy RMTFoundations.Fredholm RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds

/-- The actual plus Hankel determinant in the canonical half-line Hilbert basis. -/
noncomputable def Dplus
    (s : ℝ) -- [definition]
    : ℝ := realOperatorDet (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure))
      (airyHankelShift s) 1

/-- The canonical operator definition is exactly the physical Airy Fredholm series. -/
theorem Dplus_eq_physical
    (s : ℝ) -- [definition]
    : Dplus s =
      (kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y+s)) 1).re := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  have h := congrArg Complex.re (airyHankelFredholm_eq_realOperatorDet b s 1)
  simpa only [Dplus, b, Complex.ofReal_one, Complex.ofReal_re] using h.symm

/-- Changing the countable Hilbert basis does not change the plus determinant. -/
theorem Dplus_eq_realOperatorDet
    {ι : Type*} -- [definition]
    [Countable ι] -- [standing]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) -- [definition]
    (s : ℝ) -- [definition]
    : Dplus s = realOperatorDet b (airyHankelShift s) 1 := by
  rw [Dplus_eq_physical]
  have h := congrArg Complex.re (airyHankelFredholm_eq_realOperatorDet b s 1)
  simpa only [Complex.ofReal_one, Complex.ofReal_re] using h

/-- Exact physical determinant factorization, proved in one simultaneous eigenbasis. -/
theorem TW2R_factorization
    (s : ℝ) -- [definition]
    : TW2R s = TW1R s * Dplus s := by
  obtain ⟨ι, _, b, a, he, hk, ha, ha2, ht, ht2, hp, hq⟩ := airy_spectral_data s
  have hm : HasProd (fun i => 1 - a i) (TW1R s) := by
    simpa [TW1R, TW1, sub_eq_add_neg] using hp (-1)
  have hplus : HasProd (fun i => 1 + a i) (Dplus s) := by
    simpa only [Dplus_eq_physical, one_mul, Complex.ofReal_one] using hp 1
  have hs : HasProd (fun i => 1 - (a i)^2) (TW2R s) := by
    simpa [TW2R, TW2, sub_eq_add_neg] using hq (-1)
  apply hs.unique
  convert hm.mul hplus using 1
  funext i
  ring

/-- Actual left inverse at the plus coupling, with strict contraction discharged. -/
theorem airy_plus_inverse_left
    (s : ℝ) -- [definition]
    (x : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Ring.inverse (1+airyHankelShift s) (x+airyHankelShift s x) = x := by
  have hn : ‖-airyHankelShift s‖ < 1 := by
    simpa only [norm_neg] using norm_airyHankelShift_lt_one s
  simpa only [sub_neg_eq_add, ContinuousLinearMap.neg_apply] using
    contraction_ringInverse_left (-airyHankelShift s) hn x

/-- Actual right inverse at the plus coupling, with strict contraction discharged. -/
theorem airy_plus_inverse_right
    (s : ℝ) -- [definition]
    (x : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Ring.inverse (1+airyHankelShift s) x +
      airyHankelShift s (Ring.inverse (1+airyHankelShift s) x) = x := by
  have hn : ‖-airyHankelShift s‖ < 1 := by
    simpa only [norm_neg] using norm_airyHankelShift_lt_one s
  simpa only [sub_neg_eq_add, ContinuousLinearMap.neg_apply] using
    contraction_ringInverse_right (-airyHankelShift s) hn x

/-- The genuine minus inverse is the even square inverse plus its odd part. -/
theorem airy_minus_inverse_parity
    (s : ℝ) -- [definition]
    (x : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Ring.inverse (1-airyHankelShift s) x =
      Ring.inverse (1-airyKernelShift s) x +
        airyHankelShift s (Ring.inverse (1-airyKernelShift s) x) := by
  exact resolvent_parity_identity (airyHankelShift s)
    (Ring.inverse (1-airyHankelShift s)) (Ring.inverse (1-airyKernelShift s))
    (contraction_ringInverse_left (airyHankelShift s) (norm_airyHankelShift_lt_one s))
    (contraction_ringInverse_right (airyKernelShift s) (norm_airyKernelShift_lt_one s)) x

/-- The genuine plus inverse is the even square inverse minus its odd part. -/
theorem airy_plus_inverse_parity
    (s : ℝ) -- [definition]
    (x : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Ring.inverse (1+airyHankelShift s) x =
      Ring.inverse (1-airyKernelShift s) x -
        airyHankelShift s (Ring.inverse (1-airyKernelShift s) x) := by
  have hl : ∀ y, Ring.inverse (1-(-airyHankelShift s)) (y-(-airyHankelShift s) y) = y := by
    simpa only [sub_neg_eq_add, ContinuousLinearMap.neg_apply] using airy_plus_inverse_left s
  have hr : ∀ y, Ring.inverse (1-airyKernelShift s) y -
      (-airyHankelShift s) ((-airyHankelShift s)
        (Ring.inverse (1-airyKernelShift s) y)) = y := by
    intro y
    simp only [ContinuousLinearMap.neg_apply, map_neg, neg_neg]
    exact contraction_ringInverse_right (airyKernelShift s) (norm_airyKernelShift_lt_one s) y
  simpa only [sub_neg_eq_add, ContinuousLinearMap.neg_apply, sub_eq_add_neg, neg_neg] using
    resolvent_parity_identity (-airyHankelShift s)
      (Ring.inverse (1-(-airyHankelShift s))) (Ring.inverse (1-airyKernelShift s)) hl hr x

/-- The sum of the physical inverses cancels their odd parts. -/
theorem airy_inverse_parity_sum
    (s : ℝ) -- [definition]
    (x : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Ring.inverse (1-airyHankelShift s) x + Ring.inverse (1+airyHankelShift s) x =
      (2 : ℝ) • Ring.inverse (1-airyKernelShift s) x := by
  rw [airy_minus_inverse_parity, airy_plus_inverse_parity, two_smul]
  abel

/-- The quadratic inverse parity used by the physical TW2 product derivative. -/
theorem airy_inverse_quadratic_parity_sum
    (s : ℝ) -- [definition]
    (x : Lp ℝ 2 halfLineMeasure) -- [definition]
    : (inner ℝ x (Ring.inverse (1-airyHankelShift s) x) +
       inner ℝ x (Ring.inverse (1+airyHankelShift s) x)) / 2 =
      inner ℝ x (Ring.inverse (1-airyKernelShift s) x) := by
  rw [airy_minus_inverse_parity, airy_plus_inverse_parity,
    inner_add_right, inner_sub_right]
  ring

/-- All inverse binders, the determinant bridge and factorization coexist at the
actual nonzero Airy row at shift zero. No inverse or product is a premise. -/
theorem factorization_inverse_all_binder_joint_probe
    : ∃ (ι : Type) (_ : Countable ι)
        (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure))
        (x : Lp ℝ 2 halfLineMeasure),
      x = airyBoundaryVector 0 ∧ x ≠ 0 ∧ airyAiReal 0 ≠ 0 ∧
      ‖airyHankelShift 0‖ < 1 ∧ ‖airyKernelShift 0‖ < 1 ∧
      Dplus 0 = realOperatorDet b (airyHankelShift 0) 1 ∧
      TW2R 0 = TW1R 0 * Dplus 0 ∧
      (∀ y, Ring.inverse (1+airyHankelShift 0) (y+airyHankelShift 0 y) = y) ∧
      (∀ y, Ring.inverse (1+airyHankelShift 0) y +
        airyHankelShift 0 (Ring.inverse (1+airyHankelShift 0) y) = y) ∧
      Ring.inverse (1-airyHankelShift 0) x + Ring.inverse (1+airyHankelShift 0) x =
        (2 : ℝ) • Ring.inverse (1-airyKernelShift 0) x ∧
      (inner ℝ x (Ring.inverse (1-airyHankelShift 0) x) +
       inner ℝ x (Ring.inverse (1+airyHankelShift 0) x)) / 2 =
        inner ℝ x (Ring.inverse (1-airyKernelShift 0) x) := by
  obtain ⟨ι, hcount, b, a, he, _⟩ := airy_spectral_data 0
  letI := hcount
  exact ⟨ι, hcount, b, airyBoundaryVector 0, rfl, airyBoundaryVector_ne_zero 0,
    airyAiReal_zero_pos.ne', norm_airyHankelShift_lt_one 0, norm_airyKernelShift_lt_one 0,
    Dplus_eq_realOperatorDet b 0, TW2R_factorization 0,
    airy_plus_inverse_left 0, airy_plus_inverse_right 0,
    airy_inverse_parity_sum 0 (airyBoundaryVector 0),
    airy_inverse_quadratic_parity_sum 0 (airyBoundaryVector 0)⟩

end RMTFoundations.TracyWidom.OrderTwoFactorization

#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.Dplus
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.Dplus_eq_physical
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.Dplus_eq_realOperatorDet
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.TW2R_factorization
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.airy_plus_inverse_left
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.airy_plus_inverse_right
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.airy_minus_inverse_parity
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.airy_plus_inverse_parity
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.airy_inverse_parity_sum
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.airy_inverse_quadratic_parity_sum
#print axioms RMTFoundations.TracyWidom.OrderTwoFactorization.factorization_inverse_all_binder_joint_probe
