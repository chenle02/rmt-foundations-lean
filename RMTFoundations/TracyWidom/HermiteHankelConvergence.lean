import RMTFoundations.TracyWidom.SoftEdgeHankelCore
import RMTFoundations.TracyWidom.SoftEdgeTraceProducts
import RMTFoundations.TracyWidom.HermiteAiryAmplitude
import RMTFoundations.TracyWidom.HermiteAdjacentAmplitude
import RMTFoundations.TracyWidom.HermiteUniformTailMass
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HermiteHankelConvergence
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryBounds RMTFoundations.AiryContinuity
open RMTFoundations.TracyWidom.SoftEdgeHankelCore RMTFoundations.TracyWidom.SoftEdgeTraceProducts
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.TracyWidom.HermiteEdgeScale
open RMTFoundations.TracyWidom.HermiteEdgeODE RMTFoundations.TracyWidom.GUEHermite
open RMTFoundations.TracyWidom.HermiteAiryAmplitude RMTFoundations.TracyWidom.HermiteAdjacentAmplitude
open RMTFoundations.TracyWidom.HermiteUniformTail RMTFoundations.TracyWidom.HermiteTailComparison

noncomputable def primaryHankelKernel (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : ℝ × ℝ → ℝ := shiftedKernel (edgeMode (n+2)) s
noncomputable def adjacentHankelKernel (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : ℝ × ℝ → ℝ := shiftedKernel (previousMode (n+2)) s

theorem primary_pointwise (x : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => edgeMode (n+2) x) atTop (𝓝 (airyAiReal x)) := by
  exact (hermite_edge_tendsto x).comp (tendsto_add_atTop_nat 1)
theorem adjacent_pointwise (x : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => previousMode (n+2) x) atTop (𝓝 (airyAiReal x)) := by
  simpa [previousMode,affineMode,edgePoint] using adjacent_edge_tendsto x

theorem primaryHankelKernel_memLp (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : MemLp (primaryHankelKernel n s) 2 quadrantMeasure := by
  obtain ⟨C,hC,hb⟩ := uniform_halfline_tail s
  exact hankel_memLp_of_envelope _ (continuous_iff_continuousAt.mpr
    (fun x => (edgeMode_hasDerivAt (n+2) x).continuousAt)) s C hC.le
    (fun x hx => (hb (n+2) (by omega) x hx).1)
theorem adjacentHankelKernel_memLp (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : MemLp (adjacentHankelKernel n s) 2 quadrantMeasure := by
  obtain ⟨C,hC,hb⟩ := uniform_halfline_tail s
  exact hankel_memLp_of_envelope _ (continuous_iff_continuousAt.mpr
    (fun x => (previousMode_hasDerivAt (n+2) x).continuousAt)) s C hC.le
    (fun x hx => (hb (n+2) (by omega) x hx).2)

/-- L2 convergence of the actual primary Hermite Hankel kernel, at every real cut. -/
theorem primaryHankelKernel_eLpNorm_tendsto (s : ℝ /- [definition] -/) :
    Tendsto (fun n => eLpNorm (primaryHankelKernel n s-airyHankelShiftKernel s) 2 quadrantMeasure)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := uniform_halfline_tail s
  exact hankel_eLpNorm_tendsto (fun n => edgeMode (n+2)) airyAiReal
    (fun n => continuous_iff_continuousAt.mpr (fun x =>
      (edgeMode_hasDerivAt (n+2) x).continuousAt)) continuous_airyAiReal s C hC.le
    (fun n x hx => (hb (n+2) (by omega) x hx).1) primary_pointwise

/-- The neighboring degree is evaluated at the same physical N edge. -/
theorem adjacentHankelKernel_eLpNorm_tendsto (s : ℝ /- [definition] -/) :
    Tendsto (fun n => eLpNorm (adjacentHankelKernel n s-airyHankelShiftKernel s) 2 quadrantMeasure)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := uniform_halfline_tail s
  exact hankel_eLpNorm_tendsto (fun n => previousMode (n+2)) airyAiReal
    (fun n => continuous_iff_continuousAt.mpr (fun x =>
      (previousMode_hasDerivAt (n+2) x).continuousAt)) continuous_airyAiReal s C hC.le
    (fun n x hx => (hb (n+2) (by omega) x hx).2) adjacent_pointwise

noncomputable def primaryHankel (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : AiryOp := kernelOperator (primaryHankelKernel_memLp n s)
noncomputable def adjacentHankel (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : AiryOp := kernelOperator (adjacentHankelKernel_memLp n s)

theorem primaryHankel_isHilbertSchmidt (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : IsHilbertSchmidt (primaryHankel n s) :=
  isHilbertSchmidt_kernelOperator (primaryHankelKernel_memLp n s)
theorem adjacentHankel_isHilbertSchmidt (n : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : IsHilbertSchmidt (adjacentHankel n s) :=
  isHilbertSchmidt_kernelOperator (adjacentHankelKernel_memLp n s)

/-- The genuine primary Hermite Hankel operators converge in Hilbert-Schmidt norm. -/
theorem primaryHankel_hs_tendsto (s : ℝ /- [definition] -/) :
    Tendsto (fun n => hsENorm (primaryHankel n s-airyHankelShift s)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (primaryHankelKernel_eLpNorm_tendsto s) (Eventually.of_forall fun _ => zero_le)
  exact Eventually.of_forall fun n => hs_kernel_error_le _ _
    (primaryHankelKernel_memLp n s) (memLp_airyHankelShiftKernel s)

/-- The actual adjacent operators converge in the same Hilbert-Schmidt norm. -/
theorem adjacentHankel_hs_tendsto (s : ℝ /- [definition] -/) :
    Tendsto (fun n => hsENorm (adjacentHankel n s-airyHankelShift s)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (adjacentHankelKernel_eLpNorm_tendsto s) (Eventually.of_forall fun _ => zero_le)
  exact Eventually.of_forall fun n => hs_kernel_error_le _ _
    (adjacentHankelKernel_memLp n s) (memLp_airyHankelShiftKernel s)

/-- The literal mixed products converge in trace norm to the physical Airy kernel. -/
theorem mixed_hankel_trace_tendsto (s : ℝ /- [definition] -/) :
    Tendsto (fun n => traceENorm (primaryHankel n s ∘L adjacentHankel n s-airyKernelShift s))
      atTop (𝓝 0) ∧
    Tendsto (fun n => traceENorm (adjacentHankel n s ∘L primaryHankel n s-airyKernelShift s))
      atTop (𝓝 0) := by
  have hH : hsENorm (airyHankelShift s) ≠ ⊤ := isHilbertSchmidt_airyHankelShift s
  exact ⟨trace_product_tendsto_of_hs (fun n => primaryHankel n s)
      (fun n => adjacentHankel n s) (airyHankelShift s) (airyHankelShift s)
      hH hH (primaryHankel_hs_tendsto s) (adjacentHankel_hs_tendsto s),
    trace_product_tendsto_of_hs (fun n => adjacentHankel n s)
      (fun n => primaryHankel n s) (airyHankelShift s) (airyHankelShift s)
      hH hH (adjacentHankel_hs_tendsto s) (primaryHankel_hs_tendsto s)⟩

/-- Every analytic input of the dominated-convergence and trace-product roots is
supplied by terms on one genuine growing Hermite family, with a negative cut. -/
theorem complete_hankel_joint_probe :
    airyAiReal 0 ≠ 0 ∧
    (∀ n : ℕ, 0 < hermiteDensity (n+2) (fun i => (i.val : ℝ))) ∧
    Continuous airyAiReal ∧
    (∀ n : ℕ, Continuous (edgeMode (n+2)) ∧ Continuous (previousMode (n+2))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x : ℝ, -1 ≤ x →
      |edgeMode (n+2) x| ≤ C*Real.exp (-(1/2:ℝ)*(x-(-1))) ∧
      |previousMode (n+2) x| ≤ C*Real.exp (-(1/2:ℝ)*(x-(-1)))) ∧
    (∀ x : ℝ, Tendsto (fun n => edgeMode (n+2) x) atTop (𝓝 (airyAiReal x)) ∧
      Tendsto (fun n => previousMode (n+2) x) atTop (𝓝 (airyAiReal x))) ∧
    (∀ n : ℕ, MemLp (primaryHankelKernel n (-1)) 2 quadrantMeasure ∧
      MemLp (adjacentHankelKernel n (-1)) 2 quadrantMeasure ∧
      IsHilbertSchmidt (primaryHankel n (-1)) ∧ IsHilbertSchmidt (adjacentHankel n (-1))) ∧
    MemLp (airyHankelShiftKernel (-1)) 2 quadrantMeasure ∧
    Tendsto (fun n => eLpNorm (primaryHankelKernel n (-1)-airyHankelShiftKernel (-1))
      2 quadrantMeasure) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (adjacentHankelKernel n (-1)-airyHankelShiftKernel (-1))
      2 quadrantMeasure) atTop (𝓝 0) ∧
    hsENorm (airyHankelShift (-1)) ≠ ⊤ ∧
    Tendsto (fun n => hsENorm (primaryHankel n (-1)-airyHankelShift (-1))) atTop (𝓝 0) ∧
    Tendsto (fun n => hsENorm (adjacentHankel n (-1)-airyHankelShift (-1))) atTop (𝓝 0) ∧
    Tendsto (fun n => traceENorm
      (primaryHankel n (-1) ∘L adjacentHankel n (-1)-airyKernelShift (-1))) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := uniform_halfline_tail (-1)
  refine ⟨airyAiReal_zero_pos.ne',fun n => hermite_density_all_binder_joint_probe.2 (n+1),
    continuous_airyAiReal,fun n => ⟨continuous_iff_continuousAt.mpr (fun x =>
      (edgeMode_hasDerivAt (n+2) x).continuousAt),continuous_iff_continuousAt.mpr (fun x =>
      (previousMode_hasDerivAt (n+2) x).continuousAt)⟩,
    ⟨C,hC,fun n x hx => hb (n+2) (by omega) x hx⟩,
    fun x => ⟨primary_pointwise x,adjacent_pointwise x⟩,
    fun n => ⟨primaryHankelKernel_memLp n (-1),adjacentHankelKernel_memLp n (-1),
      primaryHankel_isHilbertSchmidt n (-1),adjacentHankel_isHilbertSchmidt n (-1)⟩,
    memLp_airyHankelShiftKernel (-1),primaryHankelKernel_eLpNorm_tendsto (-1),
    adjacentHankelKernel_eLpNorm_tendsto (-1),isHilbertSchmidt_airyHankelShift (-1),
    primaryHankel_hs_tendsto (-1),
    adjacentHankel_hs_tendsto (-1),(mixed_hankel_trace_tendsto (-1)).1⟩

end RMTFoundations.TracyWidom.HermiteHankelConvergence

#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.primaryHankelKernel
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.adjacentHankelKernel
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.primary_pointwise
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.adjacent_pointwise
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.primaryHankelKernel_memLp
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.adjacentHankelKernel_memLp
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.primaryHankelKernel_eLpNorm_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.adjacentHankelKernel_eLpNorm_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.primaryHankel
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.adjacentHankel
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.primaryHankel_isHilbertSchmidt
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.adjacentHankel_isHilbertSchmidt
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.primaryHankel_hs_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.adjacentHankel_hs_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.mixed_hankel_trace_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteHankelConvergence.complete_hankel_joint_probe
