import RMTFoundations.Airy.Spectral
import RMTFoundations.TracyWidom.OrderOneBounds


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory InnerProductSpace
open scoped Topology
open RMTFoundations.Airy RMTFoundations.Fredholm RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds

theorem realOperatorDet_square_factorization
    {E ι : Type* /- [definition] -/}
    [NormedAddCommGroup E] /- [standing] -/
    [InnerProductSpace ℝ E] /- [standing] -/
    [CompleteSpace E] /- [standing] -/
    (b : HilbertBasis ι ℝ E /- [definition] -/)
    (T : E →L[ℝ] E /- [definition] -/)
    (hT : IsTraceClass T /- [standing] -/)
    (a : ι → ℝ /- [definition] -/)
    (he : ∀ i, T (b i) = a i • b i /- [standing] -/) :
    realOperatorDet b (T ∘L T) (-1) =
      realOperatorDet b T (-1) * realOperatorDet b T 1 := by
  have hs : IsTraceClass (T ∘L T) := hT.isHilbertSchmidt.isTraceClass_comp hT.isHilbertSchmidt
  have hd : ∀ i, (T ∘L T) (b i) = (a i)^2 • b i := by
    intro i
    simp only [ContinuousLinearMap.comp_apply, he, map_smul, smul_smul, pow_two]
  have hp := (realOperatorDet_diagonal_hasProd b T hT a he (-1)).mul
    (realOperatorDet_diagonal_hasProd b T hT a he 1)
  have hk := realOperatorDet_diagonal_hasProd b (T ∘L T) hs (fun i => (a i)^2) hd (-1)
  apply hk.unique
  convert hp using 1
  funext i
  ring

noncomputable def hankelDetPlus (s : ℝ /- [definition] -/) : ℝ :=
  (kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y+s)) 1).re

theorem TW2R_factorization
    (s : ℝ /- [definition] -/) : TW2R s = TW1R s * hankelDetPlus s := by
  obtain ⟨ι, _, b, a, he, hk, ha, ha2, ht, ht2, hp, hq⟩ := airy_simultaneous_eigenbasis s
  have hm : HasProd (fun i => 1 - a i) (TW1R s) := by
    simpa [TW1R, TW1, sub_eq_add_neg] using hp (-1)
  have hplus : HasProd (fun i => 1 + a i) (hankelDetPlus s) := by
    simpa [hankelDetPlus] using hp 1
  have hs : HasProd (fun i => 1 - (a i)^2) (TW2R s) := by
    simpa [TW2R, TW2, sub_eq_add_neg] using hq (-1)
  apply hs.unique
  convert hm.mul hplus using 1
  funext i
  ring

/-- The same factorization at the original complex-valued Fredholm definitions. -/
theorem TW2_factorization
    (s : ℝ /- [definition] -/) :
    TW2 s = TW1 s * kernelFredholm halfLineMeasure
      (fun x y => airyAiReal (x+y+s)) 1 := by
  have hp : (kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y+s)) 1).im = 0 := by
    rw [show (1:ℂ) = ((1:ℝ):ℂ) by norm_num, kernelFredholm_real_coupling]
    rfl
  apply Complex.ext
  · simpa only [Complex.mul_re, TW1_im_zero, zero_mul, sub_zero,
      TW1R, TW2R, hankelDetPlus] using TW2R_factorization s
  · simp only [Complex.mul_im, TW2_im_zero, TW1_im_zero, hp, mul_zero, zero_mul, add_zero]

/-- The plus factor is the genuine operator determinant in any countable Hilbert basis. -/
theorem hankelDetPlus_eq_realOperatorDet
    {ι : Type* /- [definition] -/}
    [Countable ι] /- [standing] -/
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure) /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    hankelDetPlus s = realOperatorDet b (airyHankelShift s) 1 := by
  have h := airyHankelFredholm_eq_realOperatorDet b s 1
  simpa only [hankelDetPlus, Complex.ofReal_one, Complex.ofReal_re] using congrArg Complex.re h

theorem TW2R_positive
    (s : ℝ /- [definition] -/) : 0 < TW2R s := by
  obtain ⟨ι, _, b, a, he, hk, ha, ha2, ht, ht2, hp, hq⟩ := airy_simultaneous_eigenbasis s
  have hs : HasProd (fun i => 1 - (a i)^2) (TW2R s) := by
    simpa [TW2R, TW2, sub_eq_add_neg] using hq (-1)
  rw [← hs.tprod_eq]
  apply signed_tprod_pos (fun i => (a i)^2) ha2.of_norm
  intro i
  have hn := (real_eigenvalue_norm_le (airyHankelShift s) (b i)
    (b.orthonormal.norm_eq_one i) (a i) (he i)).trans_lt
      (norm_airyHankelShift_lt_one s)
  rw [Real.norm_eq_abs, abs_lt] at hn
  nlinarith [sq_nonneg (a i - 1), sq_nonneg (a i + 1)]

theorem hankelDetPlus_positive
    (s : ℝ /- [definition] -/) : 0 < hankelDetPlus s := by
  have h := TW2R_positive s
  rw [TW2R_factorization] at h
  exact (mul_pos_iff_of_pos_left (TW1R_positive_bounds s).1).mp h

theorem TW2R_le_TW1R_iff
    (s : ℝ /- [definition] -/) : TW2R s ≤ TW1R s ↔ hankelDetPlus s ≤ 1 := by
  rw [TW2R_factorization]
  nth_rw 2 [← mul_one (TW1R s)]
  constructor <;> intro h <;> nlinarith [(TW1R_positive_bounds s).1]

theorem TW1R_le_TW2R_iff
    (s : ℝ /- [definition] -/) : TW1R s ≤ TW2R s ↔ 1 ≤ hankelDetPlus s := by
  rw [TW2R_factorization]
  nth_rw 1 [← mul_one (TW1R s)]
  constructor <;> intro h <;> nlinarith [(TW1R_positive_bounds s).1]

theorem determinant_all_binder_joint_probe :
    ∃ b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2),
    ∃ T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
    ∃ a : ℕ → ℝ,
      IsTraceClass T ∧ (∀ i, T (b i) = a i • b i) ∧ ‖T (b 0)‖ = 2 ∧
      realOperatorDet b (T ∘L T) (-1) =
        realOperatorDet b T (-1) * realOperatorDet b T 1 := by
  obtain ⟨b,T,a,hT,ha,he,hn,_⟩ := real_diagonal_spectral_joint_probe
  exact ⟨b,T,a,hT,he,hn,realOperatorDet_square_factorization b T hT a he⟩

theorem factorization_joint_probe : TW2R 0 = TW1R 0 * hankelDetPlus 0 :=
  TW2R_factorization 0
theorem plus_operator_bridge_all_binder_joint_probe :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)),
      hankelDetPlus 0 = realOperatorDet b (airyHankelShift 0) 1 ∧
      TW2 0 = TW1 0 * kernelFredholm halfLineMeasure
        (fun x y => airyAiReal (x+y)) 1 ∧
      0 < TW2R 0 ∧ 0 < hankelDetPlus 0 ∧ ‖shiftedUnitVector 0‖ = 1 := by
  obtain ⟨ι, hcount, b, a, he, _⟩ := airy_simultaneous_eigenbasis 0
  letI := hcount
  refine ⟨ι, hcount, b, hankelDetPlus_eq_realOperatorDet b 0, ?_,
    TW2R_positive 0, hankelDetPlus_positive 0, shiftedUnitVector_norm 0⟩
  simpa only [add_zero] using TW2_factorization 0

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.realOperatorDet_square_factorization
#print axioms RMTFoundations.TracyWidom.hankelDetPlus
#print axioms RMTFoundations.TracyWidom.TW2R_factorization
#print axioms RMTFoundations.TracyWidom.TW2_factorization
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_eq_realOperatorDet
#print axioms RMTFoundations.TracyWidom.TW2R_positive
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_positive
#print axioms RMTFoundations.TracyWidom.TW2R_le_TW1R_iff
#print axioms RMTFoundations.TracyWidom.TW1R_le_TW2R_iff
#print axioms RMTFoundations.TracyWidom.determinant_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.factorization_joint_probe
#print axioms RMTFoundations.TracyWidom.plus_operator_bridge_all_binder_joint_probe
