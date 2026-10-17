import RMTFoundations.TracyWidom.AiryBoundaryContinuity
import RMTFoundations.TracyWidom.VectorWeakToNorm
import RMTFoundations.Airy.HankelFactorization



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.AiryBoundaryDerivative

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.AiryBoundaryContinuity

/-- One exponential majorant works for all shifts in a neighborhood. -/
theorem airyDerivative_local_bound
    (s : ℝ) -- [definition]
    : ∃ D : ℝ, 0 < D ∧ ∀ t ∈ Metric.ball s 1, ∀ x : ℝ, 0 ≤ x →
      |deriv airyAiReal (t+x)| ≤ D * Real.exp (-(1/2:ℝ)*x) := by
  obtain ⟨C,hC,hb⟩ := airy_deriv_halfline_exp_bound (s-1)
  refine ⟨C*Real.exp (-(s-1)/2), by positivity, ?_⟩
  intro t ht x hx
  have ht' : s-1 < t := by
    have h : |t-s| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
    linarith [(abs_lt.mp h).1]
  have he : Real.exp (-(t+x)/2) ≤ Real.exp (-(s-1)/2) * Real.exp (-(1/2:ℝ)*x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  exact (hb (t+x) (by linarith)).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hC.le)

/-- The translated physical Airy derivative is a genuine half-line L² function. -/
theorem memLp_airyDerivative
    (s : ℝ) -- [definition]
    : MemLp (fun x : ℝ => deriv airyAiReal (s+x)) 2 halfLineMeasure := by
  obtain ⟨D,hD,hb⟩ := airyDerivative_local_bound s
  apply ((memLp_halfline_exp_rate (-(1/2:ℝ)) (by norm_num)).const_mul D).mono'
    (continuous_deriv_airyAiReal.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [Real.norm_eq_abs, Function.comp_def, Pi.add_apply, id_eq] using hb s (Metric.mem_ball_self (by norm_num)) x hx.le

/-- The norm derivative candidate is the class of the actual translated Ai′. -/
noncomputable def airyBoundaryDerivative
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure := (memLp_airyDerivative s).toLp _

theorem airyBoundaryDerivative_apply_ae
    (s : ℝ) -- [definition]
    : airyBoundaryDerivative s =ᵐ[halfLineMeasure] fun x => deriv airyAiReal (s+x) :=
  (memLp_airyDerivative s).coeFn_toLp

/-- L² distance is an integral of squared differences of the physical functions. -/
theorem airyBoundaryDerivative_norm_sub_sq
    (s t : ℝ) -- [definition]
    : ‖airyBoundaryDerivative t - airyBoundaryDerivative s‖^2 =
      ∫ x, (deriv airyAiReal (t+x)-deriv airyAiReal (s+x))^2 ∂halfLineMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (airyBoundaryDerivative t) (airyBoundaryDerivative s),
    airyBoundaryDerivative_apply_ae s, airyBoundaryDerivative_apply_ae t] with x hx hs ht
  rw [hx]
  simp only [Pi.sub_apply]
  rw [hs, ht]
  simp only [Real.inner_apply, pow_two]

/-- Dominated convergence proves norm continuity of the physical derivative family. -/
theorem airyBoundaryDerivative_continuous : Continuous airyBoundaryDerivative := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨D,hD,hb⟩ := airyDerivative_local_bound s
  have hs : s ∈ Metric.ball s 1 := Metric.mem_ball_self (by norm_num)
  have hi : Integrable (fun x : ℝ => (2*D)^2 * Real.exp (-x)) halfLineMeasure := by
    simpa only [neg_one_mul] using
      (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul ((2*D)^2)
  have hl : Tendsto (fun t : ℝ => ∫ x,
      (deriv airyAiReal (t+x)-deriv airyAiReal (s+x))^2 ∂halfLineMeasure)
      (𝓝 s) (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => ∫ x,
        (deriv airyAiReal (t+x)-deriv airyAiReal (s+x))^2 ∂halfLineMeasure)
        (𝓝 s) (𝓝 (∫ x, (0:ℝ) ∂halfLineMeasure)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => (2*D)^2 * Real.exp (-x))
      · exact Eventually.of_forall fun t =>
          (((continuous_deriv_airyAiReal.comp (continuous_const.add continuous_id)).sub
            (continuous_deriv_airyAiReal.comp (continuous_const.add continuous_id))).pow 2).aestronglyMeasurable
      · filter_upwards [Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1)] with t ht
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have h1 := hb t ht x hx.le
        have h2 := hb s hs x hx.le
        have ht1 : |deriv airyAiReal (t+x)-deriv airyAiReal (s+x)| ≤
            |deriv airyAiReal (t+x)|+|deriv airyAiReal (s+x)| := by
          simpa only [Real.norm_eq_abs] using
            norm_sub_le (deriv airyAiReal (t+x)) (deriv airyAiReal (s+x))
        have hle : |deriv airyAiReal (t+x)-deriv airyAiReal (s+x)| ≤
            2*D*Real.exp (-(1/2:ℝ)*x) := by linarith
        have hpow := pow_le_pow_left₀ (abs_nonneg _) hle 2
        have he : (Real.exp (-(1/2:ℝ)*x))^2 = Real.exp (-x) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        simpa only [Real.norm_eq_abs, abs_sq, mul_pow, sq_abs, he] using hpow
      · exact hi
      · apply ae_of_all
        intro x
        have hc : Continuous (fun t : ℝ =>
            (deriv airyAiReal (t+x)-deriv airyAiReal (s+x))^2) :=
          ((continuous_deriv_airyAiReal.comp (continuous_id.add continuous_const)).sub continuous_const).pow 2
        simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using hc.tendsto s
    simpa using hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun t => ‖airyBoundaryDerivative t-airyBoundaryDerivative s‖^2) (𝓝 s) (𝓝 0) := by
    simpa only [airyBoundaryDerivative_norm_sub_sq] using hl
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- Arbitrary L² test vectors pair with the actual Airy function integral. -/
theorem airyBoundaryVector_pairing
    (v : Lp ℝ 2 halfLineMeasure) -- [definition]
    (s : ℝ) -- [definition]
    : inner ℝ v (airyBoundaryVector s) =
      ∫ x, airyAiReal (s+x)*v x ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [airyBoundaryVector_apply_ae s] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]

/-- Arbitrary L² test vectors pair with the actual Airy derivative integral. -/
theorem airyBoundaryDerivative_pairing
    (v : Lp ℝ 2 halfLineMeasure) -- [definition]
    (s : ℝ) -- [definition]
    : inner ℝ v (airyBoundaryDerivative s) =
      ∫ x, deriv airyAiReal (s+x)*v x ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [airyBoundaryDerivative_apply_ae s] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]

/-- Genuine weak derivative, proved for every L² test vector by dominated differentiation. -/
theorem airyBoundaryVector_pairing_hasDerivAt
    (v : Lp ℝ 2 halfLineMeasure) -- [definition]
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => inner ℝ v (airyBoundaryVector t))
      (inner ℝ v (airyBoundaryDerivative s)) s := by
  obtain ⟨D,hD,hb⟩ := airyDerivative_local_bound s
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun x => airyAiReal (t+x)*v x) halfLineMeasure :=
    (continuous_airyAiReal.comp (continuous_const.add continuous_id)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable v)
  have hdmeas : AEStronglyMeasurable
      (fun x => deriv airyAiReal (s+x)*v x) halfLineMeasure :=
    (continuous_deriv_airyAiReal.comp (continuous_const.add continuous_id)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable v)
  have hi : Integrable (fun x => airyAiReal (s+x)*v x) halfLineMeasure := by
    have hh := (Lp.memLp (airyBoundaryVector s)).integrable_mul (Lp.memLp v)
    apply hh.congr
    filter_upwards [airyBoundaryVector_apply_ae s] with x hx
    simp only [Pi.mul_apply]
    rw [hx]
  have hmajor : Integrable (fun x : ℝ => D*Real.exp (-(1/2:ℝ)*x)*|v x|) halfLineMeasure := by
    have hh := ((memLp_halfline_exp_rate (-(1/2:ℝ)) (by norm_num)).integrable_mul
      (Lp.memLp v).norm).const_mul D
    simpa only [Real.norm_eq_abs, Pi.mul_apply, mul_assoc] using hh
  have hbound : ∀ᵐ x ∂halfLineMeasure, ∀ t ∈ Metric.ball s 1,
      ‖deriv airyAiReal (t+x)*v x‖ ≤ D*Real.exp (-(1/2:ℝ)*x)*|v x| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro t ht
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_right (hb t ht x hx.le) (abs_nonneg (v x))
  have hdiff : ∀ᵐ x ∂halfLineMeasure, ∀ t ∈ Metric.ball s 1,
      HasDerivAt (fun t => airyAiReal (t+x)*v x) (deriv airyAiReal (t+x)*v x) t := by
    apply ae_of_all
    intro x t _
    simpa only [Function.comp_def, mul_one, id_eq] using!
      ((hasDerivAt_airyAiReal' (t+x)).comp t ((hasDerivAt_id t).add_const x)).mul_const (v x)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1)) (Eventually.of_forall hmeas)
    hi hdmeas hbound hmajor hdiff).2
  simpa only [airyBoundaryVector_pairing, airyBoundaryDerivative_pairing] using h

/-- Actual norm derivative of the Airy boundary vector; no physical regularity premise. -/
theorem hasDerivAt_airyBoundaryVector
    (s : ℝ) -- [definition]
    : HasDerivAt airyBoundaryVector (airyBoundaryDerivative s) s :=
  RMTFoundations.TracyWidom.hasDerivAt_vector_of_pairings airyBoundaryVector
    airyBoundaryDerivative airyBoundaryDerivative_continuous
    airyBoundaryVector_pairing_hasDerivAt s

/-- The differentiated physical energy gives a useful scalar pairing identity. -/
theorem airyBoundaryVector_derivative_pairing
    (s : ℝ) -- [definition]
    : 2 * inner ℝ (airyBoundaryVector s) (airyBoundaryDerivative s) =
      -(airyAiReal s)^2 := by
  have hd := hasDerivAt_airyBoundaryVector s
  have h := hd.inner ℝ hd
  simp only [airyBoundaryVector_inner_self] at h
  have he := h.unique (hasDerivAt_airyEnergy s)
  rw [real_inner_comm (airyBoundaryVector s) (airyBoundaryDerivative s)] at he
  linarith

/-- Physical Ai′ gives a nonzero L² derivative at the nondegenerate shift zero. -/
theorem airyBoundaryDerivative_zero_ne : airyBoundaryDerivative 0 ≠ 0 := by
  intro hz
  have h := airyBoundaryVector_derivative_pairing 0
  rw [hz, inner_zero_right, mul_zero] at h
  have hp := sq_pos_of_pos airyAiReal_zero_pos
  linarith

/-- Every physical binder is realized simultaneously, with nonzero boundary row and derivative. -/
theorem airyBoundary_derivative_joint_probe :
    Continuous airyBoundaryDerivative ∧
      (∀ (v : Lp ℝ 2 halfLineMeasure) (s : ℝ),
        HasDerivAt (fun t => inner ℝ v (airyBoundaryVector t))
          (inner ℝ v (airyBoundaryDerivative s)) s) ∧
      (∀ s : ℝ, HasDerivAt airyBoundaryVector (airyBoundaryDerivative s) s) ∧
      airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧ 0 < airyAiReal 0 ∧
      (airyBoundaryDerivative 0 =ᵐ[halfLineMeasure] fun x => deriv airyAiReal x) ∧
      2 * inner ℝ (airyBoundaryVector 0) (airyBoundaryDerivative 0) = -(airyAiReal 0)^2 := by
  refine ⟨airyBoundaryDerivative_continuous, airyBoundaryVector_pairing_hasDerivAt,
    hasDerivAt_airyBoundaryVector, airyBoundaryVector_ne_zero 0,
    airyBoundaryDerivative_zero_ne, airyAiReal_zero_pos, ?_,
    airyBoundaryVector_derivative_pairing 0⟩
  simpa only [zero_add] using airyBoundaryDerivative_apply_ae 0

end RMTFoundations.TracyWidom.AiryBoundaryDerivative

#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryDerivative
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyDerivative_local_bound
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.memLp_airyDerivative
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryDerivative_apply_ae
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryDerivative_norm_sub_sq
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryDerivative_continuous
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryVector_pairing
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryDerivative_pairing
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryVector_pairing_hasDerivAt
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.hasDerivAt_airyBoundaryVector
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryVector_derivative_pairing
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundaryDerivative_zero_ne
#print axioms RMTFoundations.TracyWidom.AiryBoundaryDerivative.airyBoundary_derivative_joint_probe
