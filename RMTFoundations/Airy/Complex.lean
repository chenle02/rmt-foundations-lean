import Mathlib
import RMTFoundations.Airy.Core

namespace RMTFoundations.AiryComplex

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
open RMTFoundations.Airy

noncomputable def complexHankelKernel (s : ℝ /- [definition] -/) : ℝ × ℝ → ℂ :=
  fun p => (airyHankelShiftKernel s p : ℂ)

theorem complexHankelKernel_memLp (s : ℝ /- [definition] -/) :
    MemLp (complexHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure) :=
  (memLp_airyHankelShiftKernel s).ofReal

noncomputable def complexHankelShift (s : ℝ /- [definition] -/) :
    Lp ℂ 2 halfLineMeasure →L[ℂ] Lp ℂ 2 halfLineMeasure :=
  kernelOperator (complexHankelKernel_memLp s)

theorem complexHankelShift_hilbertSchmidt (s : ℝ /- [definition] -/) :
    IsHilbertSchmidt (complexHankelShift s) :=
  isHilbertSchmidt_kernelOperator (complexHankelKernel_memLp s)

noncomputable def complexKernelShift (s : ℝ /- [definition] -/) :
    Lp ℂ 2 halfLineMeasure →L[ℂ] Lp ℂ 2 halfLineMeasure :=
  complexHankelShift s ∘L complexHankelShift s

theorem complexKernelShift_traceClass (s : ℝ /- [definition] -/) :
    IsTraceClass (complexKernelShift s) :=
  ⟨complexHankelShift s, complexHankelShift s, complexHankelShift_hilbertSchmidt s,
    complexHankelShift_hilbertSchmidt s, rfl⟩

noncomputable def realEmbedding : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℂ 2 halfLineMeasure :=
  (@RCLike.ofRealCLM ℂ _).compLpL 2 halfLineMeasure

theorem realEmbedding_apply_ae (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    realEmbedding f =ᵐ[halfLineMeasure] fun x => (f x : ℂ) :=
  (@RCLike.ofRealCLM ℂ _).coeFn_compLpL f

theorem realEmbedding_norm (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    ‖realEmbedding f‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (realEmbedding f))
    (Lp.aestronglyMeasurable f)
  filter_upwards [realEmbedding_apply_ae f] with x hx
  rw [hx, Complex.norm_real]

/-- The complex Hankel operator is the actual complexification of the real one. -/
theorem complexHankelShift_realEmbedding (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    complexHankelShift s (realEmbedding f) = realEmbedding (airyHankelShift s f) := by
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae (complexHankelKernel_memLp s) (realEmbedding f),
    airyHankelShift_apply_ae s f, realEmbedding_apply_ae (airyHankelShift s f)] with x hc hr he
  rw [he, hr]
  change (kernelOperator (complexHankelKernel_memLp s) (realEmbedding f)) x = _
  rw [hc]
  change (∫ y, complexHankelKernel s (x, y) * (realEmbedding f) y ∂halfLineMeasure) = _
  calc (∫ y, complexHankelKernel s (x, y) * (realEmbedding f) y ∂halfLineMeasure)
      = ∫ y, ((airyAiReal (x + y + s) * f y : ℝ) : ℂ) ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards [realEmbedding_apply_ae f] with y hy
        simp only [complexHankelKernel, airyHankelShiftKernel, hy, Complex.ofReal_mul]
    _ = ((∫ y, airyAiReal (x + y + s) * f y ∂halfLineMeasure : ℝ) : ℂ) := integral_complex_ofReal

theorem complexKernelShift_realEmbedding (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/) :
    complexKernelShift s (realEmbedding f) = realEmbedding (airyKernelShift s f) := by
  simp only [complexKernelShift, airyKernelShift, ContinuousLinearMap.comp_apply]
  rw [complexHankelShift_realEmbedding, complexHankelShift_realEmbedding]

/-- Complexification hypotheses are jointly satisfied on every real shift and
on a nonzero vector of the actual half-line L2 space. -/
theorem complexification_joint_probe (s : ℝ /- [definition] -/) :
    ‖realEmbedding (shiftedUnitVector 0)‖ = 1 ∧
      IsHilbertSchmidt (complexHankelShift s) ∧ IsTraceClass (complexKernelShift s) := by
  rw [realEmbedding_norm, shiftedUnitVector_norm]
  exact ⟨rfl, complexHankelShift_hilbertSchmidt s, complexKernelShift_traceClass s⟩

end RMTFoundations.AiryComplex

#print axioms RMTFoundations.AiryComplex.complexHankelKernel
#print axioms RMTFoundations.AiryComplex.complexHankelKernel_memLp
#print axioms RMTFoundations.AiryComplex.complexHankelShift
#print axioms RMTFoundations.AiryComplex.complexHankelShift_hilbertSchmidt
#print axioms RMTFoundations.AiryComplex.complexKernelShift
#print axioms RMTFoundations.AiryComplex.complexKernelShift_traceClass
#print axioms RMTFoundations.AiryComplex.realEmbedding
#print axioms RMTFoundations.AiryComplex.realEmbedding_apply_ae
#print axioms RMTFoundations.AiryComplex.realEmbedding_norm
#print axioms RMTFoundations.AiryComplex.complexHankelShift_realEmbedding
#print axioms RMTFoundations.AiryComplex.complexKernelShift_realEmbedding
#print axioms RMTFoundations.AiryComplex.complexification_joint_probe
