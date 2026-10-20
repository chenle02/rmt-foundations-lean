import RMTFoundations.TracyWidom.Airy2Operator
import RMTFoundations.Airy.HankelFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm

/-- Equal division of the physical time weight between two spectral Airy factors. -/
noncomputable def spectralFactorKernel
    (s d b : ℝ /- [definition] -/) : ℝ × ℝ → ℝ :=
  fun p => Real.exp (-(d/2)*p.2)*airyAiReal (p.1+s+b*p.2)

/-- Measurability for either sign of the spectral coordinate. -/
theorem spectralFactorKernel_measurable
    (s d b : ℝ /- [definition] -/) :
    Measurable (spectralFactorKernel s d b) := by
  unfold spectralFactorKernel
  have hm := measurable_airyAiReal
  fun_prop

/-- Every physical factor has exponential decay in both half-line coordinates. -/
theorem spectralFactorKernel_bound
    (s d b C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/)
    (p : ℝ × ℝ /- [definition] -/)
    (hu : 0 ≤ p.2 /- [standing] -/) :
    |spectralFactorKernel s d b p| ≤
      (C*Real.exp (-a*s))*(Real.exp (-a*p.1)*Real.exp (-a*p.2)) := by
  rw [spectralFactorKernel,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(d/2)*p.2)*|airyAiReal (p.1+s+b*p.2)|
      ≤ Real.exp (-(d/2)*p.2)*(C*Real.exp (-a*(p.1+s+b*p.2))) :=
        mul_le_mul_of_nonneg_left (hAi _) (Real.exp_nonneg _)
    _ = (C*Real.exp (-a*s))*(Real.exp (-a*p.1)*Real.exp (-(d/2+a*b)*p.2)) := by
      rw [show -a*(p.1+s+b*p.2) = -a*s + (-a*p.1 + -a*b*p.2) by ring,
        show -(d/2+a*b)*p.2 = -(d/2)*p.2 + -a*b*p.2 by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact Real.exp_le_exp.mpr (by nlinarith)
      · positivity

/-- The two genuine spectral factors are Hilbert--Schmidt kernels, including the backward branch. -/
theorem spectralFactorKernel_memLp
    (s d b C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/) :
    MemLp (spectralFactorKernel s d b) 2 (halfLineMeasure.prod halfLineMeasure) := by
  apply ((memLp_halfline_exp_pair_rate (-a) (-a) (by linarith) (by linarith)).const_smul
    (C*Real.exp (-a*s))).of_le (spectralFactorKernel_measurable s d b).aestronglyMeasurable
  filter_upwards [RMTFoundations.AiryBounds.ae_positive_quadrant] with p hp
  simpa only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (C*Real.exp (-a*s))*(Real.exp (-a*p.1)*Real.exp (-a*p.2)))]
    using spectralFactorKernel_bound s d b C a hC hAi hdec p hp.2.le

/-- Both physical branches have the same jointly selected envelope constants. -/
theorem spectralFactor_parameters
    (t r : ℝ /- [definition] -/) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      (∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z)) ∧
      (r ≤ t → a ≤ (t-r)/2+a*1) ∧
      (t < r → a ≤ (r-t)/2+a*(-1)) := by
  let times : Fin 2 → ℝ := fun i => if i=0 then t else r
  obtain ⟨a,ha,ha1,hgap⟩ := finiteTime_positive_rate 2 times
  obtain ⟨C,hC,hAi⟩ := Ai_slow_exponential_envelope
  refine ⟨C,a,hC,ha,hAi a ha.le ha1,?_,?_⟩
  · intro h; linarith
  · intro h
    have hg := hgap 0 1 (by simpa [times] using h)
    simp only [times] at hg
    norm_num at hg
    linarith

/-- Nonzero Airy data and a genuine backward time gap satisfy all factor hypotheses jointly. -/
theorem spectral_factors_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      (∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z)) ∧
      a ≤ (1:ℝ)/2+a*(-1) ∧
      MemLp (spectralFactorKernel (-1) 1 (-1)) 2 (halfLineMeasure.prod halfLineMeasure) ∧
      MemLp (spectralFactorKernel 1 1 (-1)) 2 (halfLineMeasure.prod halfLineMeasure) := by
  obtain ⟨C,a,hC,ha,hAi,_,hb⟩ := spectralFactor_parameters 0 1
  have hdec := hb (by norm_num)
  refine ⟨airyAiReal_zero_pos.ne',C,a,hC,ha,hAi,?_,
    spectralFactorKernel_memLp (-1) 1 (-1) C a hC.le ha hAi (by simpa using hdec),
    spectralFactorKernel_memLp 1 1 (-1) C a hC.le ha hAi (by simpa using hdec)⟩
  simpa using hdec

/-- Every spectral row has a genuine L2 representative. -/
theorem spectralFactorKernel_row_memLp
    (s d b C a x : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/) :
    MemLp (fun u => star (spectralFactorKernel s d b (x,u))) 2 halfLineMeasure := by
  simp only [star_trivial]
  apply ((memLp_halfline_exp_rate (-a) (by linarith)).const_smul
    ((C*Real.exp (-a*s))*Real.exp (-a*x))).of_le
    (((spectralFactorKernel_measurable s d b).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change |spectralFactorKernel s d b (x,u)| ≤
    |((C*Real.exp (-a*s))*Real.exp (-a*x))*Real.exp (-a*u)|
  rw [abs_of_nonneg (show 0 ≤ ((C*Real.exp (-a*s))*Real.exp (-a*x))*Real.exp (-a*u) by positivity)]
  simpa only [mul_assoc] using spectralFactorKernel_bound s d b C a hC hAi hdec (x,u) hu.le

/-- The unsigned branch kernel, before the essential backward minus sign. -/
noncomputable def spectralBlockKernel
    (s v d b : ℝ /- [definition] -/) : ℝ × ℝ → ℝ := fun p =>
      ∫ u, Real.exp (-d*u)*airyAiReal (p.1+s+b*u)*airyAiReal (p.2+v+b*u)
        ∂halfLineMeasure

/-- The convolution identity splits the original weight exactly, without changing the branch. -/
theorem spectralBlockKernel_eq_convolution
    (s v d b x y : ℝ /- [definition] -/) :
    spectralBlockKernel s v d b (x,y) =
      ∫ u, spectralFactorKernel s d b (x,u)*spectralFactorKernel v d b (y,u)
        ∂halfLineMeasure := by
  unfold spectralBlockKernel spectralFactorKernel
  congr 1
  funext u
  have he : Real.exp (-(d/2)*u)*Real.exp (-(d/2)*u) = Real.exp (-d*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-d*u)*airyAiReal (x+s+b*u)*airyAiReal (y+v+b*u)
      = (Real.exp (-(d/2)*u)*Real.exp (-(d/2)*u))*
          airyAiReal (x+s+b*u)*airyAiReal (y+v+b*u) := by rw [he]
    _ = _ := by ring

/-- The unsigned branch is jointly measurable. -/
theorem spectralBlockKernel_measurable
    (s v d b : ℝ /- [definition] -/) :
    Measurable (spectralBlockKernel s v d b) := by
  have h : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      Real.exp (-d*p.2)*airyAiReal (p.1.1+s+b*p.2)*airyAiReal (p.1.2+v+b*p.2)) := by
    have hm := measurable_airyAiReal
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- The original spectral integral has a product exponential envelope. -/
theorem spectralBlockKernel_bound
    (s v d b C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/)
    (p : ℝ × ℝ /- [definition] -/) :
    |spectralBlockKernel s v d b p| ≤
      (C^2*Real.exp (-a*s)*Real.exp (-a*v)*
        ∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure)*
        (Real.exp (-a*p.1)*Real.exp (-a*p.2)) := by
  have hi : Integrable (fun u : ℝ => Real.exp (-(2*a)*u)) halfLineMeasure :=
    integrableOn_exp_mul_Ioi (by linarith : -(2*a)<0) 0
  have hb : ∀ᵐ u ∂halfLineMeasure,
      |Real.exp (-d*u)*airyAiReal (p.1+s+b*u)*airyAiReal (p.2+v+b*u)| ≤
        C^2*Real.exp (-a*((p.1+s)+(p.2+v)))*Real.exp (-(2*a)*u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact weighted_integrand_spatial_envelope C a d b (p.1+s) (p.2+v) u
      hC hAi hu.le (by linarith)
  have hm : AEStronglyMeasurable (fun u : ℝ =>
      Real.exp (-d*u)*airyAiReal (p.1+s+b*u)*airyAiReal (p.2+v+b*u)) halfLineMeasure := by
    have hm := measurable_airyAiReal
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hint := (hi.const_mul (C^2*Real.exp (-a*((p.1+s)+(p.2+v))))).mono' hm
    (by simpa only [Real.norm_eq_abs] using hb)
  unfold spectralBlockKernel
  calc |∫ u, Real.exp (-d*u)*airyAiReal (p.1+s+b*u)*airyAiReal (p.2+v+b*u) ∂halfLineMeasure|
      ≤ ∫ u, |Real.exp (-d*u)*airyAiReal (p.1+s+b*u)*airyAiReal (p.2+v+b*u)| ∂halfLineMeasure :=
        by
          simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
            (fun u => Real.exp (-d*u)*airyAiReal (p.1+s+b*u)*airyAiReal (p.2+v+b*u))
            (μ := halfLineMeasure))
    _ ≤ ∫ u, C^2*Real.exp (-a*((p.1+s)+(p.2+v)))*Real.exp (-(2*a)*u) ∂halfLineMeasure :=
      integral_mono_ae hint.norm (hi.const_mul _) hb
    _ = _ := by
      rw [integral_const_mul,
        show -a*((p.1+s)+(p.2+v)) = -a*s + (-a*v + (-a*p.1 + -a*p.2)) by ring]
      simp only [Real.exp_add]
      ring

/-- Square integrability of the actual unsigned branch kernel. -/
theorem spectralBlockKernel_memLp
    (s v d b C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/) :
    MemLp (spectralBlockKernel s v d b) 2 (halfLineMeasure.prod halfLineMeasure) := by
  let D := C^2*Real.exp (-a*s)*Real.exp (-a*v)*∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure
  have hD : 0 ≤ D := by dsimp [D]; exact mul_nonneg (by positivity) (integral_nonneg (fun _ => Real.exp_nonneg _))
  apply ((memLp_halfline_exp_pair_rate (-a) (-a) (by linarith) (by linarith)).const_smul D).of_le
    (spectralBlockKernel_measurable s v d b).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  simpa only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ D*(Real.exp (-a*p.1)*Real.exp (-a*p.2)))]
    using spectralBlockKernel_bound s v d b C a hC ha hAi hdec p

/-- Every physical convolution row has a genuine L2 representative. -/
theorem spectralBlockKernel_row_memLp
    (s v d b C a x : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/) :
    MemLp (fun y => star (spectralBlockKernel s v d b (x,y))) 2 halfLineMeasure := by
  let D := C^2*Real.exp (-a*s)*Real.exp (-a*v)*∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure
  have hD : 0 ≤ D := by dsimp [D]; exact mul_nonneg (by positivity) (integral_nonneg (fun _ => Real.exp_nonneg _))
  simp only [star_trivial]
  apply ((memLp_halfline_exp_rate (-a) (by linarith)).const_smul (D*Real.exp (-a*x))).of_le
    (((spectralBlockKernel_measurable s v d b).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro y
  change |spectralBlockKernel s v d b (x,y)| ≤ |(D*Real.exp (-a*x))*Real.exp (-a*y)|
  rw [abs_of_nonneg (show 0 ≤ (D*Real.exp (-a*x))*Real.exp (-a*y) by positivity)]
  simpa only [D,mul_assoc] using spectralBlockKernel_bound s v d b C a hC ha hAi hdec (x,y)

/-- The second HS factor sends each first-factor row to the actual branch-kernel row. -/
theorem spectralBlockKernel_factor_row
    (s v d b C a x : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/) :
    kernelOperator (spectralFactorKernel_memLp v d b C a hC ha hAi hdec)
      (sliceLp halfLineMeasure (spectralFactorKernel s d b) x) =
      sliceLp halfLineMeasure (spectralBlockKernel s v d b) x := by
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae (spectralFactorKernel_memLp v d b C a hC ha hAi hdec)
    (sliceLp halfLineMeasure (spectralFactorKernel s d b) x),
    sliceLp_apply_ae (spectralBlockKernel_row_memLp s v d b C a x hC ha hAi hdec)] with y hy hk
  rw [hy,hk]
  change (∫ u, spectralFactorKernel v d b (y,u)*
    (sliceLp halfLineMeasure (spectralFactorKernel s d b) x) u ∂halfLineMeasure) = _
  rw [star_trivial,spectralBlockKernel_eq_convolution]
  apply integral_congr_ae
  filter_upwards [sliceLp_apply_ae (spectralFactorKernel_row_memLp s d b C a x hC ha hAi hdec)] with u hu
  simp only [hu,star_trivial,mul_comm]

/-- Identity of actual bounded operators, proved through genuine L2 rows and the adjoint. -/
theorem spectralBlockOperator_factorization
    (s v d b C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/) :
    kernelOperator (spectralBlockKernel_memLp s v d b C a hC ha hAi hdec) =
      kernelOperator (spectralFactorKernel_memLp s d b C a hC ha hAi hdec) ∘L
        (kernelOperator (spectralFactorKernel_memLp v d b C a hC ha hAi hdec)).adjoint := by
  let A := kernelOperator (spectralFactorKernel_memLp s d b C a hC ha hAi hdec)
  let B := kernelOperator (spectralFactorKernel_memLp v d b C a hC ha hAi hdec)
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_eval_inner_ae (spectralBlockKernel_memLp s v d b C a hC ha hAi hdec) f,
    kernelOperator_eval_inner_ae (spectralFactorKernel_memLp s d b C a hC ha hAi hdec) (B.adjoint f)] with x hk hA
  change _ = A (B.adjoint f) x
  change (A (B.adjoint f)) x = inner ℝ (sliceLp halfLineMeasure (spectralFactorKernel s d b) x) (B.adjoint f) at hA
  rw [hk,hA,B.adjoint_inner_right,
    spectralBlockKernel_factor_row s v d b C a x hC ha hAi hdec]

/-- Trace class is proved for the actual unsigned branch integral operator. -/
theorem spectralBlockOperator_isTraceClass
    (s v d b C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/) :
    IsTraceClass (kernelOperator (spectralBlockKernel_memLp s v d b C a hC ha hAi hdec)) := by
  rw [spectralBlockOperator_factorization s v d b C a hC ha hAi hdec]
  exact (isHilbertSchmidt_kernelOperator (spectralFactorKernel_memLp s d b C a hC ha hAi hdec)).isTraceClass_comp
    (isHilbertSchmidt_kernelOperator (spectralFactorKernel_memLp v d b C a hC ha hAi hdec)).adjoint

/-- A negative HS product is still trace class; the physical backward sign is retained. -/
theorem neg_spectralBlockOperator_isTraceClass
    (s v d b C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hdec : a ≤ d/2+a*b /- [standing] -/) :
    IsTraceClass (-kernelOperator (spectralBlockKernel_memLp s v d b C a hC ha hAi hdec)) := by
  rw [spectralBlockOperator_factorization s v d b C a hC ha hAi hdec]
  let A := kernelOperator (spectralFactorKernel_memLp s d b C a hC ha hAi hdec)
  let B := kernelOperator (spectralFactorKernel_memLp v d b C a hC ha hAi hdec)
  have he : -(A ∘L B.adjoint) = (-A) ∘L B.adjoint := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [he]
  exact (isHilbertSchmidt_kernelOperator (spectralFactorKernel_memLp s d b C a hC ha hAi hdec)).neg.isTraceClass_comp
    (isHilbertSchmidt_kernelOperator (spectralFactorKernel_memLp v d b C a hC ha hAi hdec)).adjoint

/-- The original later-time physical block is exactly the unsigned forward spectral kernel. -/
theorem physical_block_forward
    (t r s v : ℝ /- [definition] -/)
    (h : r ≤ t /- [standing] -/) :
    (fun p : ℝ × ℝ => extendedAiryKernel t r (p.1+s) (p.2+v)) =
      spectralBlockKernel s v (t-r) 1 := by
  funext p
  simp only [extendedAiryKernel,h,if_true,spectralBlockKernel,halfLineMeasure,one_mul]

/-- The original earlier-time physical block is exactly the negative backward spectral kernel. -/
theorem physical_block_backward
    (t r s v : ℝ /- [definition] -/)
    (h : t < r /- [standing] -/) :
    (fun p : ℝ × ℝ => extendedAiryKernel t r (p.1+s) (p.2+v)) =
      -spectralBlockKernel s v (r-t) (-1) := by
  funext p
  simp only [extendedAiryKernel,not_le.mpr h,if_false,spectralBlockKernel,
    halfLineMeasure,neg_one_mul,Pi.neg_apply,sub_eq_add_neg]

/-- Kernel operators preserve an exact pointwise kernel identity. -/
theorem halfline_kernelOperator_congr
    (K L : ℝ × ℝ → ℝ /- [definition] -/)
    (hK : MemLp K 2 (halfLineMeasure.prod halfLineMeasure) /- [standing] -/)
    (hL : MemLp L 2 (halfLineMeasure.prod halfLineMeasure) /- [standing] -/)
    (he : K = L /- [standing] -/) :
    kernelOperator hK = kernelOperator hL := by
  subst L
  rfl

/-- Negation of the actual kernel gives negation of its actual integral operator. -/
theorem halfline_kernelOperator_neg
    (K : ℝ × ℝ → ℝ /- [definition] -/)
    (hK : MemLp K 2 (halfLineMeasure.prod halfLineMeasure) /- [standing] -/) :
    kernelOperator hK.neg = -kernelOperator hK := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae hK.neg f,kernelOperator_apply_ae hK f,
    Lp.coeFn_neg ((kernelOperator hK) f)] with x hn hk hneg
  change ((kernelOperator hK.neg) f) x = (-(kernelOperator hK f)) x
  rw [hn,hneg]
  simp only [Pi.neg_apply]
  rw [hk]
  change (∫ y, (-K) (x,y)*f y ∂halfLineMeasure) =
    -(∫ y, K (x,y)*f y ∂halfLineMeasure)
  simp only [Pi.neg_apply,neg_mul,integral_neg]

/-- Every original physical time block is square integrable at all real cuts. -/
theorem physical_block_memLp
    (t r s v : ℝ /- [definition] -/) :
    MemLp (fun p : ℝ × ℝ => extendedAiryKernel t r (p.1+s) (p.2+v)) 2
      (halfLineMeasure.prod halfLineMeasure) := by
  obtain ⟨C,a,hC,ha,hAi,hf,hb⟩ := spectralFactor_parameters t r
  by_cases h : r ≤ t
  · rw [physical_block_forward t r s v h]
    exact spectralBlockKernel_memLp s v (t-r) 1 C a hC.le ha hAi (hf h)
  · rw [physical_block_backward t r s v (lt_of_not_ge h)]
    exact (spectralBlockKernel_memLp s v (r-t) (-1) C a hC.le ha hAi (hb (lt_of_not_ge h))).neg

/-- Trace class is unconditional for each physical time block at the caller's cuts. -/
theorem physical_block_isTraceClass
    (t r s v : ℝ /- [definition] -/) :
    IsTraceClass (kernelOperator (physical_block_memLp t r s v)) := by
  obtain ⟨C,a,hC,ha,hAi,hf,hb⟩ := spectralFactor_parameters t r
  by_cases h : r ≤ t
  · rw [halfline_kernelOperator_congr _ _ (physical_block_memLp t r s v)
      (spectralBlockKernel_memLp s v (t-r) 1 C a hC.le ha hAi (hf h))
      (physical_block_forward t r s v h)]
    exact spectralBlockOperator_isTraceClass s v (t-r) 1 C a hC.le ha hAi (hf h)
  · have ht : t < r := lt_of_not_ge h
    rw [halfline_kernelOperator_congr _ _ (physical_block_memLp t r s v)
      (spectralBlockKernel_memLp s v (r-t) (-1) C a hC.le ha hAi (hb ht)).neg
      (physical_block_backward t r s v ht),halfline_kernelOperator_neg]
    exact neg_spectralBlockOperator_isTraceClass s v (r-t) (-1) C a hC.le ha hAi (hb ht)

/-- Nonzero physical data exercise backward, forward and equal-time trace-class conclusions jointly. -/
theorem physical_block_traceClass_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧
      IsTraceClass (kernelOperator (physical_block_memLp 0 1 (-1) 1)) ∧
      IsTraceClass (kernelOperator (physical_block_memLp 1 0 (-1) 1)) ∧
      IsTraceClass (kernelOperator (physical_block_memLp 0 0 (-1) 1)) := by
  exact ⟨airyAiReal_zero_pos.ne',physical_block_isTraceClass _ _ _ _,
    physical_block_isTraceClass _ _ _ _,physical_block_isTraceClass _ _ _ _⟩


end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.spectralFactorKernel
#print axioms RMTFoundations.TracyWidom.Airy2.spectralFactorKernel_measurable
#print axioms RMTFoundations.TracyWidom.Airy2.spectralFactorKernel_bound
#print axioms RMTFoundations.TracyWidom.Airy2.spectralFactorKernel_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.spectralFactor_parameters
#print axioms RMTFoundations.TracyWidom.Airy2.spectral_factors_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.spectralFactorKernel_row_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockKernel
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockKernel_eq_convolution
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockKernel_measurable
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockKernel_bound
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockKernel_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockKernel_row_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockKernel_factor_row
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockOperator_factorization
#print axioms RMTFoundations.TracyWidom.Airy2.spectralBlockOperator_isTraceClass
#print axioms RMTFoundations.TracyWidom.Airy2.neg_spectralBlockOperator_isTraceClass
#print axioms RMTFoundations.TracyWidom.Airy2.physical_block_forward
#print axioms RMTFoundations.TracyWidom.Airy2.physical_block_backward
#print axioms RMTFoundations.TracyWidom.Airy2.halfline_kernelOperator_congr
#print axioms RMTFoundations.TracyWidom.Airy2.halfline_kernelOperator_neg
#print axioms RMTFoundations.TracyWidom.Airy2.physical_block_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.physical_block_isTraceClass
#print axioms RMTFoundations.TracyWidom.Airy2.physical_block_traceClass_all_binder_joint_probe
