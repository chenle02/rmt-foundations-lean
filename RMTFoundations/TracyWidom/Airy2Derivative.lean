import RMTFoundations.TracyWidom.Airy2Operator
import RMTFoundations.Airy.HankelFactorization
import RMTFoundations.Airy.Damping
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm

/-- The  polynomial derivative bound supplies arbitrarily slow exponential envelopes. -/
theorem Ai_deriv_slow_exponential_envelope
    (a : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/)
    (ha1 : a ≤ 1/2 /- [standing] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |deriv airyAiReal x| ≤ C*Real.exp (-a*x) := by
  obtain ⟨M,hM,hpoly⟩ := airyAiReal_deriv_polynomial_bound
  obtain ⟨P,hP,hpos⟩ := airy_deriv_halfline_exp_bound 0
  let D : ℝ := M*(1+2/a^2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨max D P,hD.trans_le (le_max_left _ _),?_⟩
  intro x
  by_cases hx : 0 ≤ x
  · calc |deriv airyAiReal x| ≤ P*Real.exp (-x/2) := hpos x hx
      _ ≤ max D P*Real.exp (-a*x) :=
        mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr (by nlinarith))
          (Real.exp_nonneg _) (hP.le.trans (le_max_right _ _))
  · have hax : 0 ≤ -a*x := by nlinarith
    have he := Real.pow_div_factorial_le_exp (-a*x) hax 2
    norm_num at he
    have hs : x^2 ≤ (2/a^2)*Real.exp (-a*x) := by
      calc x^2 = (2/a^2)*((-a*x)^2/2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [neg_mul,neg_sq] using he) (by positivity)
    have h1 : 1 ≤ Real.exp (-a*x) := Real.one_le_exp_iff.mpr hax
    calc |deriv airyAiReal x| ≤ M*(1+|x|^2) := hpoly x
      _ ≤ D*Real.exp (-a*x) := by
        rw [sq_abs]
        dsimp [D]
        nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hs)]
      _ ≤ max D P*Real.exp (-a*x) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)

/-- A common envelope simultaneously controls the genuine Ai and Ai-prime. -/
theorem Ai_and_deriv_envelope
    (a : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/)
    (ha1 : a ≤ 1/2 /- [standing] -/) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, |airyAiReal x| ≤ C*Real.exp (-a*x)) ∧
      (∀ x : ℝ, |deriv airyAiReal x| ≤ C*Real.exp (-a*x)) := by
  obtain ⟨C,hC,hAi⟩ := Ai_slow_exponential_envelope
  obtain ⟨D,hD,hder⟩ := Ai_deriv_slow_exponential_envelope a ha ha1
  refine ⟨max C D,hC.trans_le (le_max_left _ _),?_,?_⟩
  · intro x
    exact (hAi a ha.le (by linarith) x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  · intro x
    exact (hder x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))

/-- Slow derivative bounds are instantiated on nonzero physical Airy data at a real backward gap. -/
theorem derivative_envelope_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, |airyAiReal x| ≤ C*Real.exp (-(1/8:ℝ)*x)) ∧
      (∀ x : ℝ, |deriv airyAiReal x| ≤ C*Real.exp (-(1/8:ℝ)*x)) := by
  exact ⟨airyAiReal_zero_pos.ne',Ai_and_deriv_envelope (1/8) (by norm_num) (by norm_num)⟩

/-- One product estimate applies to the physical Ai/Ai-prime spectral integrand. -/
theorem weighted_derivative_integrand_spatial_envelope
    (C a d b x y u : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hDer : ∀ z : ℝ, |deriv airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hu : 0 ≤ u /- [standing] -/)
    (hdec : 2*a ≤ d+2*a*b /- [standing] -/) :
    |Real.exp (-d*u)*airyAiReal (x+b*u)*deriv airyAiReal (y+b*u)| ≤
      C^2*Real.exp (-a*(x+y))*Real.exp (-(2*a)*u) := by
  simp only [abs_mul,abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-d*u) * |airyAiReal (x+b*u)| * |deriv airyAiReal (y+b*u)|
      ≤ Real.exp (-d*u)*(C*Real.exp (-a*(x+b*u)))*(C*Real.exp (-a*(y+b*u))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hAi _) (Real.exp_nonneg _)) (hDer _)
          (abs_nonneg _) (mul_nonneg (Real.exp_nonneg _) (by positivity))
    _ = C^2*Real.exp (-a*(x+y))*Real.exp (-(d+2*a*b)*u) := by
      rw [show -(d+2*a*b)*u = -d*u + (-a*b*u + -a*b*u) by ring,
        show -a*(x+b*u) = -a*x + -a*b*u by ring,
        show -a*(y+b*u) = -a*y + -a*b*u by ring,
        show -a*(x+y) = -a*x + -a*y by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

/-- The literal y-derivative integrand of both physical branches, with their original signs. -/
noncomputable def extendedAiryDerivativeIntegrand
    (t r x y u : ℝ /- [definition] -/) : ℝ :=
  if r ≤ t then Real.exp (-(t-r)*u)*airyAiReal (x+u)*deriv airyAiReal (y+u)
  else -Real.exp (-(r-t)*u)*airyAiReal (x-u)*deriv airyAiReal (y-u)

/-- A physical derivative envelope uses the genuine finite-time gap. -/
theorem extendedAiryDerivativeIntegrand_bound
    (C a t r x y u : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hDer : ∀ z : ℝ, |deriv airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hu : 0 ≤ u /- [standing] -/)
    (hgap : t < r → 4*a ≤ r-t /- [standing] -/) :
    |extendedAiryDerivativeIntegrand t r x y u| ≤
      C^2*Real.exp (-a*(x+y))*Real.exp (-(2*a)*u) := by
  by_cases h : r ≤ t
  · simpa only [extendedAiryDerivativeIntegrand,if_pos h,one_mul] using
      weighted_derivative_integrand_spatial_envelope C a (t-r) 1 x y u hC hAi hDer hu (by linarith)
  · have hg := hgap (lt_of_not_ge h)
    simpa only [extendedAiryDerivativeIntegrand,if_neg h,neg_mul,abs_neg,neg_one_mul,one_mul,sub_eq_add_neg] using
      weighted_derivative_integrand_spatial_envelope C a (r-t) (-1) x y u hC hAi hDer hu (by linarith)

/-- Actual spectral formula for the y derivative; no regularity premise is built into the object. -/
noncomputable def extendedAiryYDerivative
    (t r x y : ℝ /- [definition] -/) : ℝ :=
    ∫ u, extendedAiryDerivativeIntegrand t r x y u ∂halfLineMeasure

/-- The derivative spectral formula is absolutely integrable. -/
theorem extendedAiryDerivativeIntegrand_integrable
    (C a t r x y : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hDer : ∀ z : ℝ, |deriv airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hgap : t < r → 4*a ≤ r-t /- [standing] -/) :
    Integrable (extendedAiryDerivativeIntegrand t r x y) halfLineMeasure := by
  have hi : Integrable (fun u : ℝ => Real.exp (-(2*a)*u)) halfLineMeasure :=
    integrableOn_exp_mul_Ioi (by linarith : -(2*a)<0) 0
  apply (hi.const_mul (C^2*Real.exp (-a*(x+y)))).mono'
  · have hm := measurable_airyAiReal
    have hd := continuous_deriv_airyAiReal.measurable
    unfold extendedAiryDerivativeIntegrand
    split_ifs <;> apply Measurable.aestronglyMeasurable <;> fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [Real.norm_eq_abs] using
      extendedAiryDerivativeIntegrand_bound C a t r x y u hC ha hAi hDer hu.le hgap

/-- Differentiation under the spectral integral is justified by physical domination on a neighborhood. -/
theorem extendedAiryKernel_hasDerivAt_y_of_envelope
    (C a t r x y : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hDer : ∀ z : ℝ, |deriv airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hgap : t < r → 4*a ≤ r-t /- [standing] -/) :
    HasDerivAt (fun v : ℝ => extendedAiryKernel t r x v) (extendedAiryYDerivative t r x y) y := by
  have hmeas : ∀ v : ℝ, AEStronglyMeasurable (extendedAiryIntegrand t r x v) halfLineMeasure := by
    intro v
    have hm := measurable_airyAiReal
    unfold extendedAiryIntegrand
    split_ifs <;> apply Measurable.aestronglyMeasurable <;> fun_prop
  have hdmeas : AEStronglyMeasurable (extendedAiryDerivativeIntegrand t r x y) halfLineMeasure :=
    (extendedAiryDerivativeIntegrand_integrable C a t r x y hC ha hAi hDer hgap).aestronglyMeasurable
  have hmajor : Integrable (fun u : ℝ => C^2*Real.exp (-a*(x+(y-1)))*Real.exp (-(2*a)*u)) halfLineMeasure :=
    (integrableOn_exp_mul_Ioi (by linarith : -(2*a)<0) 0).const_mul _
  have hb : ∀ᵐ u ∂halfLineMeasure, ∀ v ∈ Metric.ball y 1,
      ‖extendedAiryDerivativeIntegrand t r x v u‖ ≤
        C^2*Real.exp (-a*(x+(y-1)))*Real.exp (-(2*a)*u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro v hv
    have hv' : y-1 ≤ v := by
      have hh : |v-y|<1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hv
      linarith [(abs_lt.mp hh).1]
    rw [Real.norm_eq_abs]
    exact (extendedAiryDerivativeIntegrand_bound C a t r x v u hC ha hAi hDer hu.le hgap).trans
      (by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        apply Real.exp_le_exp.mpr
        nlinarith)
  have hdiff : ∀ᵐ u ∂halfLineMeasure, ∀ v ∈ Metric.ball y 1,
      HasDerivAt (fun v => extendedAiryIntegrand t r x v u)
        (extendedAiryDerivativeIntegrand t r x v u) v := by
    apply ae_of_all
    intro u v _
    by_cases h : r ≤ t
    · simp only [extendedAiryIntegrand,extendedAiryDerivativeIntegrand,if_pos h]
      simpa only [Function.comp_def,id_eq,mul_one] using
        ((hasDerivAt_airyAiReal' (v+u)).comp v ((hasDerivAt_id v).add_const u)).const_mul
          (Real.exp (-(t-r)*u)*airyAiReal (x+u))
    · simp only [extendedAiryIntegrand,extendedAiryDerivativeIntegrand,if_neg h]
      simpa only [Function.comp_def,id_eq,mul_one,neg_mul] using
        ((hasDerivAt_airyAiReal' (v-u)).comp v ((hasDerivAt_id v).sub_const u)).const_mul
          (-Real.exp (-(r-t)*u)*airyAiReal (x-u))
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds y (by norm_num : (0:ℝ)<1)) (Eventually.of_forall hmeas)
    (extendedAiryIntegrand_integrable t r x y) hdmeas hb hmajor hdiff).2
  have he : (fun v : ℝ => extendedAiryKernel t r x v) =
      (fun v : ℝ => ∫ u, extendedAiryIntegrand t r x v u ∂halfLineMeasure) :=
    funext (fun v => extendedAiryKernel_eq_integral t r x v)
  rw [he]
  exact hd

/-- The actual derivative kernel has the same physical spatial decay as the original kernel. -/
theorem extendedAiryYDerivative_bound
    (C a t r x y : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hAi : ∀ z : ℝ, |airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hDer : ∀ z : ℝ, |deriv airyAiReal z| ≤ C*Real.exp (-a*z) /- [standing] -/)
    (hgap : t < r → 4*a ≤ r-t /- [standing] -/) :
    |extendedAiryYDerivative t r x y| ≤
      (C^2*∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure)*Real.exp (-a*x)*Real.exp (-a*y) := by
  have he : Integrable (fun u : ℝ => Real.exp (-(2*a)*u)) halfLineMeasure :=
    integrableOn_exp_mul_Ioi (by linarith : -(2*a)<0) 0
  unfold extendedAiryYDerivative
  calc |∫ u, extendedAiryDerivativeIntegrand t r x y u ∂halfLineMeasure|
      ≤ ∫ u, |extendedAiryDerivativeIntegrand t r x y u| ∂halfLineMeasure :=
        by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (extendedAiryDerivativeIntegrand t r x y)
    _ ≤ ∫ u, C^2*Real.exp (-a*(x+y))*Real.exp (-(2*a)*u) ∂halfLineMeasure := by
      apply integral_mono_ae
        (extendedAiryDerivativeIntegrand_integrable C a t r x y hC ha hAi hDer hgap).norm (he.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact extendedAiryDerivativeIntegrand_bound C a t r x y u hC ha hAi hDer hu.le hgap
    _ = _ := by
      rw [integral_const_mul,show -a*(x+y) = -a*x + -a*y by ring,Real.exp_add]
      ring


end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.Ai_deriv_slow_exponential_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.Ai_and_deriv_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.derivative_envelope_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.weighted_derivative_integrand_spatial_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryDerivativeIntegrand
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryDerivativeIntegrand_bound
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryYDerivative
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryDerivativeIntegrand_integrable
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_hasDerivAt_y_of_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryYDerivative_bound
