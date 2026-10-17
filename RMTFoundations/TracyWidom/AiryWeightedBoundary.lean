import RMTFoundations.TracyWidom.OrderOneMonotone


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.AiryWeightedBoundary
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds

/-- Polynomial weight is absorbed by a slower exponential, uniformly near each shift. -/
theorem weightedAi_local_bound
    (s : ℝ) -- [definition]
    : ∃ D : ℝ, 0 < D ∧ ∀ t ∈ Metric.ball s 1, ∀ x : ℝ, 0 ≤ x →
      |(t+x)*airyAiReal (t+x)| ≤ D * Real.exp (-(1/2:ℝ)*x) := by
  obtain ⟨C,hC,hb⟩ := airyAiReal_abs_le_exp'
  let A : ℝ := |s|+1
  let E : ℝ := Real.exp (-(s-1))
  refine ⟨C*E*(A+2), by dsimp [A,E]; positivity, ?_⟩
  intro t ht x hx
  have hab : |t-s| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using ht
  have hl : s-1 < t := by linarith [(abs_lt.mp hab).1]
  have htabs : |t| ≤ A := by
    have h := abs_add_le (t-s) s
    have he : t-s+s=t := by ring
    rw [he] at h
    dsimp [A]
    linarith
  have habs : |t+x| ≤ A+x := by
    have h := abs_add_le t x
    rw [abs_of_nonneg hx] at h
    linarith
  have hshift : Real.exp (-(t+x)) ≤ E*Real.exp (-x) := by
    dsimp [E]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hAi : |airyAiReal (t+x)| ≤ C*E*Real.exp (-x) := by
    exact (hb (t+x)).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hshift hC.le)
  have hpoly : A+x ≤ (A+2)*Real.exp (x/2) := by
    have h1 := Real.one_le_exp (by linarith : 0 ≤ x/2)
    have h2 := Real.add_one_le_exp (x/2)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hA
    nlinarith
  calc
    |(t+x)*airyAiReal (t+x)| = |t+x| *|airyAiReal (t+x)| := abs_mul _ _
    _ ≤ (A+x)*(C*E*Real.exp (-x)) :=
      mul_le_mul habs hAi (abs_nonneg _) (by dsimp [A]; positivity)
    _ = C*E*((A+x)*Real.exp (-x)) := by ring
    _ ≤ C*E*((A+2)*Real.exp (x/2)*Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le) (by dsimp [E]; positivity)
    _ = C*E*(A+2)*Real.exp (-(1/2:ℝ)*x) := by
      rw [mul_assoc (A+2),← Real.exp_add]
      rw [show x/2 + -x = -(1/2:ℝ)*x by ring]
      ring

/-- The translated weighted physical Airy row is a genuine half-line L² function. -/
theorem memLp_airyWeighted
    (s : ℝ) -- [definition]
    : MemLp (fun x : ℝ => (s+x)*airyAiReal (s+x)) 2 halfLineMeasure := by
  obtain ⟨D,hD,hb⟩ := weightedAi_local_bound s
  apply ((memLp_halfline_exp_rate (-(1/2:ℝ)) (by norm_num)).const_mul D).mono'
    ((continuous_const.add continuous_id).mul (continuous_airyAiReal.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [Real.norm_eq_abs, Function.comp_def, Pi.add_apply, Pi.mul_apply, id_eq] using hb s (Metric.mem_ball_self (by norm_num)) x hx.le

/-- The Airy ODE source is the class of the actual translated x Ai. -/
noncomputable def airyBoundaryODEVector
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure := (memLp_airyWeighted s).toLp _

theorem airyBoundaryODEVector_apply_ae
    (s : ℝ) -- [definition]
    : airyBoundaryODEVector s =ᵐ[halfLineMeasure] fun x => (s+x)*airyAiReal (s+x) :=
  (memLp_airyWeighted s).coeFn_toLp

/-- L² distance is an integral of squared differences of the physical functions. -/
theorem airyBoundaryODEVector_norm_sub_sq
    (s t : ℝ) -- [definition]
    : ‖airyBoundaryODEVector t - airyBoundaryODEVector s‖^2 =
      ∫ x, ((t+x)*airyAiReal (t+x)-(s+x)*airyAiReal (s+x))^2 ∂halfLineMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (airyBoundaryODEVector t) (airyBoundaryODEVector s),
    airyBoundaryODEVector_apply_ae s, airyBoundaryODEVector_apply_ae t] with x hx hs ht
  rw [hx]
  simp only [Pi.sub_apply]
  rw [hs, ht]
  simp only [Real.inner_apply, pow_two]

/-- Dominated convergence proves norm continuity of the physical weighted-row family. -/
theorem airyBoundaryODEVector_continuous : Continuous airyBoundaryODEVector := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨D,hD,hb⟩ := weightedAi_local_bound s
  have hs : s ∈ Metric.ball s 1 := Metric.mem_ball_self (by norm_num)
  have hi : Integrable (fun x : ℝ => (2*D)^2 * Real.exp (-x)) halfLineMeasure := by
    simpa only [neg_one_mul] using
      (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul ((2*D)^2)
  have hl : Tendsto (fun t : ℝ => ∫ x,
      ((t+x)*airyAiReal (t+x)-(s+x)*airyAiReal (s+x))^2 ∂halfLineMeasure)
      (𝓝 s) (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => ∫ x,
        ((t+x)*airyAiReal (t+x)-(s+x)*airyAiReal (s+x))^2 ∂halfLineMeasure)
        (𝓝 s) (𝓝 (∫ x, (0:ℝ) ∂halfLineMeasure)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => (2*D)^2 * Real.exp (-x))
      · exact Eventually.of_forall fun t =>
          ((((continuous_const.add continuous_id).mul (continuous_airyAiReal.comp (continuous_const.add continuous_id))).sub
            ((continuous_const.add continuous_id).mul (continuous_airyAiReal.comp (continuous_const.add continuous_id)))).pow 2).aestronglyMeasurable
      · filter_upwards [Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1)] with t ht
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have h1 := hb t ht x hx.le
        have h2 := hb s hs x hx.le
        have ht1 : |(t+x)*airyAiReal (t+x)-(s+x)*airyAiReal (s+x)| ≤
            |(t+x)*airyAiReal (t+x)|+|(s+x)*airyAiReal (s+x)| := by
          simpa only [Real.norm_eq_abs] using
            norm_sub_le ((t+x)*airyAiReal (t+x)) ((s+x)*airyAiReal (s+x))
        have hle : |(t+x)*airyAiReal (t+x)-(s+x)*airyAiReal (s+x)| ≤
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
            ((t+x)*airyAiReal (t+x)-(s+x)*airyAiReal (s+x))^2) :=
          (((continuous_id.add continuous_const).mul (continuous_airyAiReal.comp (continuous_id.add continuous_const))).sub continuous_const).pow 2
        simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using hc.tendsto s
    simpa using hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun t => ‖airyBoundaryODEVector t-airyBoundaryODEVector s‖^2) (𝓝 s) (𝓝 0) := by
    simpa only [airyBoundaryODEVector_norm_sub_sq] using hl
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h


theorem airyBoundaryODEVector_pairing
    (v : Lp ℝ 2 halfLineMeasure) -- [definition]
    (s : ℝ) -- [definition]
    : inner ℝ v (airyBoundaryODEVector s) =
      ∫ x, ((s+x)*airyAiReal (s+x))*v x ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [airyBoundaryODEVector_apply_ae s] with x hx
  simp only [hx,RCLike.inner_apply,conj_trivial]

/-- A physical positive-shift instance has a nonzero weighted row. -/
theorem airyBoundaryODEVector_one_ne : airyBoundaryODEVector 1 ≠ 0 := by
  have hmono : inner ℝ (airyBoundaryVector 1) (airyBoundaryVector 1) ≤
      inner ℝ (airyBoundaryVector 1) (airyBoundaryODEVector 1) := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_mono_ae (L2.integrable_inner (𝕜 := ℝ) _ _)
      (L2.integrable_inner (𝕜 := ℝ) _ _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      airyBoundaryVector_apply_ae 1,airyBoundaryODEVector_apply_ae 1] with x hx ha hc
    simp only [ha,hc,RCLike.inner_apply,conj_trivial]
    nlinarith [mul_nonneg hx.le (sq_nonneg (airyAiReal (1+x)))]
  intro hz
  rw [hz,inner_zero_right,airyBoundaryVector_inner_self] at hmono
  exact (airyEnergy_pos 1).not_ge hmono

/-- All weighted-row binders are jointly realized by the genuine nonzero shift-one row. -/
theorem airy_weighted_boundary_joint_probe :
    Continuous airyBoundaryODEVector ∧
      MemLp (fun x : ℝ => (1+x)*airyAiReal (1+x)) 2 halfLineMeasure ∧
      airyBoundaryVector 1 ≠ 0 ∧ airyBoundaryODEVector 1 ≠ 0 ∧
      (airyBoundaryODEVector 1 =ᵐ[halfLineMeasure] fun x => (1+x)*airyAiReal (1+x)) ∧
      (∀ v : Lp ℝ 2 halfLineMeasure,
        inner ℝ v (airyBoundaryODEVector 1) =
          ∫ x, ((1+x)*airyAiReal (1+x))*v x ∂halfLineMeasure) :=
  ⟨airyBoundaryODEVector_continuous,memLp_airyWeighted 1,
    airyBoundaryVector_ne_zero 1,airyBoundaryODEVector_one_ne,
    airyBoundaryODEVector_apply_ae 1,fun v => airyBoundaryODEVector_pairing v 1⟩

end RMTFoundations.TracyWidom.AiryWeightedBoundary
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.weightedAi_local_bound
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.memLp_airyWeighted
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector_apply_ae
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector_norm_sub_sq
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector_continuous
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector_pairing
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.airyBoundaryODEVector_one_ne
#print axioms RMTFoundations.TracyWidom.AiryWeightedBoundary.airy_weighted_boundary_joint_probe
