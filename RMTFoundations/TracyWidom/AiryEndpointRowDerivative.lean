import RMTFoundations.TracyWidom.AiryBoundaryContinuity
import RMTFoundations.TracyWidom.VectorWeakToNorm
import RMTFoundations.Airy.HankelFactorization



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.AiryEndpointRowDerivative

open MeasureTheory Filter Set InnerProductSpace
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.AiryBoundaryContinuity

/-- The actual L² endpoint row of the physical Airy square kernel. -/
noncomputable def airyEndpointRow
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure := airyHankelShift s (airyBoundaryVector s)

/-- The norm derivative candidate is the genuine Airy endpoint rank-one row. -/
noncomputable def airyEndpointRowDerivative
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure := (-airyAiReal s) • airyBoundaryVector s

theorem airyEndpointRow_apply_ae
    (s : ℝ) -- [definition]
    : airyEndpointRow s =ᵐ[halfLineMeasure] fun x => airyKernelIntegral (x+s) s :=
  airyBoundaryVector_hankel_apply_ae s

theorem airyEndpointRow_pairing
    (v : Lp ℝ 2 halfLineMeasure) -- [definition]
    (s : ℝ) -- [definition]
    : inner ℝ v (airyEndpointRow s) =
      ∫ x, airyKernelIntegral (x+s) s * v x ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [airyEndpointRow_apply_ae s] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]

theorem airyEndpointRowDerivative_pairing
    (v : Lp ℝ 2 halfLineMeasure) -- [definition]
    (s : ℝ) -- [definition]
    : inner ℝ v (airyEndpointRowDerivative s) =
      ∫ x, (-airyAiReal (x+s)*airyAiReal s)*v x ∂halfLineMeasure := by
  rw [airyEndpointRowDerivative, inner_smul_right, L2.inner_def]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [airyBoundaryVector_apply_ae s] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  rw [add_comm s x]
  ring

/-- Airy exponential bounds give a genuine common rank-one derivative envelope. -/
theorem airyEndpointRowDerivative_local_bound
    (s : ℝ) -- [definition]
    : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Metric.ball s 1, ∀ x : ℝ, 0 ≤ x →
      |-airyAiReal (x+t)*airyAiReal t| ≤ C*Real.exp (-x) := by
  obtain ⟨C,hC,hb⟩ := Ai_kernel_exp_bound_uniform (s-1)
  refine ⟨C^2, sq_pos_of_pos hC, ?_⟩
  intro t ht x hx
  have ht' : s-1 ≤ t := by
    have h : |t-s| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
    linarith [(abs_lt.mp h).1]
  have hax : |airyAiReal (x+t)| ≤ C*Real.exp (-x) := by
    simpa only [add_zero, neg_zero, Real.exp_zero, mul_one] using hb t x 0 ht' hx le_rfl
  have hat : |airyAiReal t| ≤ C := by
    simpa only [zero_add, neg_zero, Real.exp_zero, mul_one] using hb t 0 0 ht' le_rfl le_rfl
  calc
    |-airyAiReal (x+t)*airyAiReal t| = |airyAiReal (x+t)| * |airyAiReal t| := by
      rw [abs_mul, abs_neg]
    _ ≤ (C*Real.exp (-x))*C :=
      mul_le_mul hax hat (abs_nonneg _) (by positivity)
    _ = C^2*Real.exp (-x) := by ring

/-- Genuine scalar pairing derivative for every L² test vector. -/
theorem airyEndpointRow_pairing_hasDerivAt
    (v : Lp ℝ 2 halfLineMeasure) -- [definition]
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => inner ℝ v (airyEndpointRow t))
      (inner ℝ v (airyEndpointRowDerivative s)) s := by
  obtain ⟨C,hC,hb⟩ := airyEndpointRowDerivative_local_bound s
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun x => airyKernelIntegral (x+t) t * v x) halfLineMeasure := by
    have hc : Continuous (fun x : ℝ => airyKernelIntegral (x+t) t) := by
      simpa only [Function.comp_def, Pi.add_apply, id_eq] using
        K_Ai_continuous.comp ((continuous_id.add continuous_const).prodMk continuous_const)
    exact hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable v)
  have hdmeas : AEStronglyMeasurable
      (fun x => (-airyAiReal (x+s)*airyAiReal s)*v x) halfLineMeasure :=
    (((continuous_airyAiReal.comp (continuous_id.add continuous_const)).neg.mul
      continuous_const).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v))
  have hi : Integrable (fun x => airyKernelIntegral (x+s) s*v x) halfLineMeasure := by
    have hh := (Lp.memLp (airyEndpointRow s)).integrable_mul (Lp.memLp v)
    apply hh.congr
    filter_upwards [airyEndpointRow_apply_ae s] with x hx
    simp only [Pi.mul_apply]
    rw [hx]
  have hmajor : Integrable (fun x : ℝ => C*Real.exp (-x)*|v x|) halfLineMeasure := by
    have hh := ((memLp_halfline_exp_rate (-1) (by norm_num)).integrable_mul
      (Lp.memLp v).norm).const_mul C
    simpa only [Real.norm_eq_abs, Pi.mul_apply, neg_one_mul, mul_assoc] using hh
  have hbound : ∀ᵐ x ∂halfLineMeasure, ∀ t ∈ Metric.ball s 1,
      ‖(-airyAiReal (x+t)*airyAiReal t)*v x‖ ≤ C*Real.exp (-x)*|v x| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro t ht
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_right (hb t ht x hx.le) (abs_nonneg (v x))
  have hdiff : ∀ᵐ x ∂halfLineMeasure, ∀ t ∈ Metric.ball s 1,
      HasDerivAt (fun r => airyKernelIntegral (x+r) r*v x)
        ((-airyAiReal (x+t)*airyAiReal t)*v x) t := by
    apply ae_of_all
    intro x t _
    simpa only [zero_add] using
      (hasDerivAt_airyKernelIntegral_simultaneous_shift x 0 t).mul_const (v x)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1)) (Eventually.of_forall hmeas)
    hi hdmeas hbound hmajor hdiff).2
  simpa only [airyEndpointRow_pairing, airyEndpointRowDerivative_pairing] using h

/-- The physical candidate derivative is norm continuous, as an actual scalar times actual row. -/
theorem airyEndpointRowDerivative_continuous : Continuous airyEndpointRowDerivative := by
  exact continuous_airyAiReal.neg.smul airyBoundaryVector_continuous

/-- Actual endpoint-row norm derivative; no endpoint differentiability premise. -/
theorem hasDerivAt_airyEndpointRow
    (s : ℝ) -- [definition]
    : HasDerivAt airyEndpointRow ((-airyAiReal s) • airyBoundaryVector s) s :=
  RMTFoundations.TracyWidom.hasDerivAt_vector_of_pairings airyEndpointRow
    airyEndpointRowDerivative airyEndpointRowDerivative_continuous
    airyEndpointRow_pairing_hasDerivAt s

theorem airyEndpointRowDerivative_zero_ne : airyEndpointRowDerivative 0 ≠ 0 := by
  rw [airyEndpointRowDerivative]
  exact smul_ne_zero (neg_ne_zero.mpr airyAiReal_zero_pos.ne') (airyBoundaryVector_ne_zero 0)

/-- All weak-to-norm binders coexist on the genuine nonzero shift-zero derivative row. -/
theorem airyEndpointRow_derivative_all_binder_joint_probe :
    Continuous airyEndpointRowDerivative ∧
      (∀ (v : Lp ℝ 2 halfLineMeasure) (s : ℝ),
        HasDerivAt (fun t => inner ℝ v (airyEndpointRow t))
          (inner ℝ v (airyEndpointRowDerivative s)) s) ∧
      (∀ s : ℝ, HasDerivAt airyEndpointRow ((-airyAiReal s) • airyBoundaryVector s) s) ∧
      airyBoundaryVector 0 ≠ 0 ∧ airyEndpointRowDerivative 0 ≠ 0 ∧ 0 < airyAiReal 0 ∧
      (airyEndpointRow 0 =ᵐ[halfLineMeasure] fun x => airyKernelIntegral x 0) := by
  refine ⟨airyEndpointRowDerivative_continuous, airyEndpointRow_pairing_hasDerivAt,
    hasDerivAt_airyEndpointRow, airyBoundaryVector_ne_zero 0,
    airyEndpointRowDerivative_zero_ne, airyAiReal_zero_pos, ?_⟩
  simpa only [add_zero] using airyEndpointRow_apply_ae 0

end RMTFoundations.TracyWidom.AiryEndpointRowDerivative

#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRow
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRowDerivative
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRow_apply_ae
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRow_pairing
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRowDerivative_pairing
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRowDerivative_local_bound
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRow_pairing_hasDerivAt
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRowDerivative_continuous
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.hasDerivAt_airyEndpointRow
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRowDerivative_zero_ne
#print axioms RMTFoundations.TracyWidom.AiryEndpointRowDerivative.airyEndpointRow_derivative_all_binder_joint_probe
