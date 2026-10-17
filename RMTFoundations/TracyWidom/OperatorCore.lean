import RMTFoundations.TracyWidom.OrderOneBounds
import RMTFoundations.Airy.Spectral
import RMTFoundations.Airy.Distribution


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace Topology
open RMTFoundations.Airy RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds

theorem hankel_square_kernel
    (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    (airyHankelShift s ∘L airyHankelShift s) f =ᵐ[halfLineMeasure]
      fun x => ∫ y, airyKernelIntegral (x+s) (y+s) * f y ∂halfLineMeasure :=
  airyKernelShift_apply_ae s f

theorem hankel_selfAdjoint_traceClass_strict
    (s : ℝ /- [definition] -/) :
    IsSelfAdjoint (airyHankelShift s) ∧ IsTraceClass (airyHankelShift s) ∧
      ‖airyHankelShift s‖ < 1 :=
  ⟨isSelfAdjoint_airyHankelShift s, isTraceClass_airyHankelShift s,
    norm_airyHankelShift_lt_one s⟩

theorem kernel_positive_traceClass_strict
    (s : ℝ /- [definition] -/) :
    (∀ f : Lp ℝ 2 halfLineMeasure, 0 ≤ inner ℝ f (airyKernelShift s f)) ∧
      IsTraceClass (airyKernelShift s) ∧ ‖airyKernelShift s‖ < 1 := by
  refine ⟨RMTFoundations.Fredholm.airyKernelShift_quadratic_nonneg s,
    isTraceClass_airyKernelShift s, ?_⟩
  have h := norm_airyHankelShift_lt_one s
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_lt
    (by nlinarith [norm_nonneg (airyHankelShift s)])

theorem hankel_eigenvalue_strict
    {ι : Type* /- [definition] -/}
    (s : ℝ /- [definition] -/)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure) /- [definition] -/)
    (a : ι → ℝ /- [definition] -/)
    (he : ∀ i, airyHankelShift s (b i) = a i • b i /- [standing] -/) :
    ∀ i, -1 < a i ∧ a i < 1 ∧ 0 ≤ (a i)^2 ∧ (a i)^2 < 1 := by
  intro i
  have hn := (real_eigenvalue_norm_le (airyHankelShift s) (b i)
    (b.orthonormal.norm_eq_one i) (a i) (he i)).trans_lt
      (norm_airyHankelShift_lt_one s)
  rw [Real.norm_eq_abs, abs_lt] at hn
  refine ⟨hn.1, hn.2, sq_nonneg _, ?_⟩
  nlinarith [sq_nonneg (a i - 1), sq_nonneg (a i + 1)]

theorem operator_all_binder_joint_probe :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)) (a : ι → ℝ),
      (∀ i, airyHankelShift 0 (b i) = a i • b i) ∧
      (∀ i, -1 < a i ∧ a i < 1 ∧ 0 ≤ (a i)^2 ∧ (a i)^2 < 1) ∧
      ‖shiftedUnitVector 0‖ = 1 ∧
      IsTraceClass (airyHankelShift 0) ∧ ‖airyKernelShift 0‖ < 1 ∧
      ((airyHankelShift 0 ∘L airyHankelShift 0) (shiftedUnitVector 0) =ᵐ[halfLineMeasure]
        fun x => ∫ y, airyKernelIntegral x y * shiftedUnitVector 0 y ∂halfLineMeasure) := by
  obtain ⟨ι, _, b, a, he, _⟩ := airy_simultaneous_eigenbasis 0
  refine ⟨ι, b, a, he, hankel_eigenvalue_strict 0 b a he,
    shiftedUnitVector_norm 0, isTraceClass_airyHankelShift 0,
    (kernel_positive_traceClass_strict 0).2.2, ?_⟩
  simpa only [add_zero] using hankel_square_kernel 0 (shiftedUnitVector 0)
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.hankel_square_kernel
#print axioms RMTFoundations.TracyWidom.hankel_selfAdjoint_traceClass_strict
#print axioms RMTFoundations.TracyWidom.kernel_positive_traceClass_strict
#print axioms RMTFoundations.TracyWidom.hankel_eigenvalue_strict
#print axioms RMTFoundations.TracyWidom.operator_all_binder_joint_probe
