import RMTFoundations.TracyWidom.HermiteKernelIntegral
import RMTFoundations.TracyWidom.HermiteHankelConvergence
import RMTFoundations.Airy.KernelDeterminant
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HermiteKernelLimit
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TracyWidom.HermiteKernelIntegral RMTFoundations.TracyWidom.HermiteHankelConvergence
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.TracyWidom.HermiteTailComparison
open RMTFoundations.TracyWidom.HermiteUniformTail RMTFoundations.TracyWidom.HermiteEdgeKernel RMTFoundations.TracyWidom.GUEHermite

/-- Uniform domination of the exact adjacent-mode convolution on the full half-line. -/
theorem adjacentPair_shift_uniform_bound (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ x y u : ℝ,
      0 ≤ x → 0 ≤ y → 0 ≤ u →
      |adjacentPair N (x+s) (y+s) u| ≤
        (2*C^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y))*Real.exp (-u) := by
  obtain ⟨C,hC,hb⟩ := uniform_halfline_tail s
  refine ⟨C,hC,?_⟩
  intro N hN x y u hx hy hu
  have hxp := hb N hN (x+s+u) (by linarith)
  have hyp := hb N hN (y+s+u) (by linarith)
  have he (v : ℝ) : C*Real.exp (-(1/2:ℝ)*(v+s+u-s)) =
      C*Real.exp (-(1/2:ℝ)*v)*Real.exp (-(1/2:ℝ)*u) := by
    rw [show -(1/2:ℝ)*(v+s+u-s) = -(1/2:ℝ)*v+(-(1/2:ℝ)*u) by ring,Real.exp_add]
    ring
  rw [he x] at hxp
  rw [he y] at hyp
  have h1 := mul_le_mul hxp.1 hyp.2 (abs_nonneg _) (by positivity)
  have h2 := mul_le_mul hxp.2 hyp.1 (abs_nonneg _) (by positivity)
  have he2 : (C*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*u))*
      (C*Real.exp (-(1/2:ℝ)*y)*Real.exp (-(1/2:ℝ)*u)) =
      C^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y)*Real.exp (-u) := by
    rw [show -u = -(1/2:ℝ)*u+(-(1/2:ℝ)*u) by ring,Real.exp_add]
    ring
  unfold adjacentPair
  calc _ ≤ |edgeMode N (x+s+u)*previousMode N (y+s+u)|+
      |previousMode N (x+s+u)*edgeMode N (y+s+u)| := abs_add_le _ _
    _ ≤ 2*((C*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*u))*
      (C*Real.exp (-(1/2:ℝ)*y)*Real.exp (-(1/2:ℝ)*u))) := by
        rw [abs_mul,abs_mul]
        linarith
    _ = _ := by rw [he2];ring

/-- Exact finite-N scaled Hermite projection converges pointwise to the Airy product kernel. -/
theorem scaledKernel_shift_tendsto
    (s x y : ℝ /- [definition] -/)
    (hx : 0 ≤ x /- [standing] -/)
    (hy : 0 ≤ y /- [standing] -/) :
    Tendsto (fun n : ℕ => scaledKernel (n+2) (x+s) (y+s))
      atTop (𝓝 (airyKernelIntegral (x+s) (y+s))) := by
  obtain ⟨C,hC,hb⟩ := adjacentPair_shift_uniform_bound s
  have hi : Integrable (fun u : ℝ =>
      (2*C^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y))*Real.exp (-u)) halfLineMeasure := by
    simpa only [neg_one_mul] using
      (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul
        (2*C^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y))
  have hl (u : ℝ) : Tendsto (fun n : ℕ => adjacentPair (n+2) (x+s) (y+s) u)
      atTop (𝓝 (2*(airyAiReal (x+s+u)*airyAiReal (y+s+u)))) := by
    have h1 := (primary_pointwise (x+s+u)).mul (adjacent_pointwise (y+s+u))
    have h2 := (adjacent_pointwise (x+s+u)).mul (primary_pointwise (y+s+u))
    convert h1.add h2 using 1
    · rfl
    · ring
  have ht : Tendsto (fun n : ℕ => ∫ u, adjacentPair (n+2) (x+s) (y+s) u ∂halfLineMeasure)
      atTop (𝓝 (∫ u, 2*(airyAiReal (x+s+u)*airyAiReal (y+s+u)) ∂halfLineMeasure)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun u => (2*C^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y))*Real.exp (-u))
    · exact Eventually.of_forall fun n => (adjacentPair_integrable (n+2) (by omega) (x+s) (y+s)).aestronglyMeasurable
    · apply Eventually.of_forall
      intro n
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro u hu
      simpa only [Real.norm_eq_abs] using hb (n+2) (by omega) x y u hx hy hu.le
    · exact hi
    · exact ae_of_all _ hl
  have ht' := ht.const_mul (1/2:ℝ)
  rw [integral_const_mul] at ht'
  have he : (1/2:ℝ)*(2*∫ u, airyAiReal (x+s+u)*airyAiReal (y+s+u) ∂halfLineMeasure) =
      airyKernelIntegral (x+s) (y+s) := by
    unfold airyKernelIntegral halfLineMeasure
    ring
  rw [he] at ht'
  exact ht'.congr (fun n => (scaledKernel_eq_adjacent_integral (n+2) (by omega) (x+s) (y+s)).symm)

/-- Pointwise convergence and every DCT binder hold on nonzero Hermite source data. -/
theorem kernel_pointwise_complete_joint_probe :
    airyAiReal 0 ≠ 0 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 ∧
    (∀ n : ℕ, 0 < hermiteDensity (n+2) (fun i => (i.val : ℝ))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x y u : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ u →
      |adjacentPair (n+2) (x-1) (y-1) u| ≤
        (2*C^2*Real.exp (-(1/2:ℝ)*x)*Real.exp (-(1/2:ℝ)*y))*Real.exp (-u)) ∧
    (∀ n : ℕ, Integrable (adjacentPair (n+2) (-1) 0) halfLineMeasure ∧
      scaledKernel (n+2) (-1) 0 = (1/2:ℝ)*∫ u, adjacentPair (n+2) (-1) 0 u ∂halfLineMeasure) ∧
    Tendsto (fun n : ℕ => scaledKernel (n+2) (-1) 0) atTop (𝓝 (airyKernelIntegral (-1) 0)) := by
  obtain ⟨C,hC,hb⟩ := adjacentPair_shift_uniform_bound (-1)
  refine ⟨airyAiReal_zero_pos.ne',by norm_num,by norm_num,
    fun n => hermite_density_all_binder_joint_probe.2 (n+1),⟨C,hC,?_⟩,
    fun n => ⟨adjacentPair_integrable (n+2) (by omega) (-1) 0,
      scaledKernel_eq_adjacent_integral (n+2) (by omega) (-1) 0⟩,?_⟩
  · intro n x y u hx hy hu
    simpa only [sub_eq_add_neg] using hb (n+2) (by omega) x y u hx hy hu
  · simpa using scaledKernel_shift_tendsto (-1) 0 1 (by norm_num) (by norm_num)

end RMTFoundations.TracyWidom.HermiteKernelLimit

#print axioms RMTFoundations.TracyWidom.HermiteKernelLimit.adjacentPair_shift_uniform_bound
#print axioms RMTFoundations.TracyWidom.HermiteKernelLimit.scaledKernel_shift_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteKernelLimit.kernel_pointwise_complete_joint_probe
