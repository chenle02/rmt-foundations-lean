import RMTFoundations.TracyWidom.DetFactor


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory
open RMTFoundations.Airy RMTFoundations.Fredholm RMTFoundations.AiryKernel RMTFoundations.TWOneBounds

/-- The genuine Airy operator supplies every diagonal-basis and trace-class
input to the general determinant multiplicativity API. -/
theorem airy_actual_operator_factorization
    (s : ℝ /- [definition] -/) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure))
      (a : ι → ℝ),
    IsTraceClass (airyHankelShift s) ∧
    (∀ i, airyHankelShift s (b i) = a i • b i) ∧
    realOperatorDet b (airyHankelShift s ∘L airyHankelShift s) (-1) =
      realOperatorDet b (airyHankelShift s) (-1) * realOperatorDet b (airyHankelShift s) 1 ∧
    TW2R s = TW1R s * hankelDetPlus s := by
  obtain ⟨ι,hcount,b,a,he,_⟩ := airy_simultaneous_eigenbasis s
  letI := hcount
  have ht := isTraceClass_airyHankelShift s
  have hf := realOperatorDet_square_factorization b (airyHankelShift s) ht a he
  have hm : TW1R s = realOperatorDet b (airyHankelShift s) (-1) := by
    simpa only [TW1R,TW1,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_re] using
      congrArg Complex.re (airyHankelFredholm_eq_realOperatorDet b s (-1))
  have hk : TW2R s = realOperatorDet b (airyHankelShift s ∘L airyHankelShift s) (-1) := by
    simpa only [TW2R,TW2,airyKernelShift,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_re] using
      congrArg Complex.re (airyKernelFredholm_eq_realOperatorDet b s (-1))
  have hc : TW2R s = TW1R s * hankelDetPlus s := by
    rw [hm,hk,hankelDetPlus_eq_realOperatorDet b s]
    exact hf
  exact ⟨ι,hcount,b,a,ht,he,hf,hc⟩

/-- All generic factorization binders coexist on actual nonzero Airy data. -/
theorem actual_factorization_all_binder_joint_probe :
    airyBoundaryVector (-3) ≠ 0 ∧ ‖shiftedUnitVector (-3)‖ = 1 ∧
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure))
      (a : ι → ℝ), IsTraceClass (airyHankelShift (-3)) ∧
    (∀ i, airyHankelShift (-3) (b i) = a i • b i) ∧
    realOperatorDet b (airyHankelShift (-3) ∘L airyHankelShift (-3)) (-1) =
      realOperatorDet b (airyHankelShift (-3)) (-1) * realOperatorDet b (airyHankelShift (-3)) 1 ∧
    TW2R (-3) = TW1R (-3) * hankelDetPlus (-3) :=
  ⟨airyBoundaryVector_ne_zero (-3),shiftedUnitVector_norm (-3),airy_actual_operator_factorization (-3)⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.airy_actual_operator_factorization
#print axioms RMTFoundations.TracyWidom.actual_factorization_all_binder_joint_probe
