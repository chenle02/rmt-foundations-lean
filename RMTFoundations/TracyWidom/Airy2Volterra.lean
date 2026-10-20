import RMTFoundations.TracyWidom.Airy2Operator
import RMTFoundations.Airy.HankelFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm

/-- The actual finite time-space measure is sigma finite. -/
instance timeSpaceMeasure_sigmaFinite
    (m : ℕ /- [definition] -/) : SigmaFinite (timeSpaceMeasure m) := by
  unfold timeSpaceMeasure
  infer_instance

/-- The spatial coordinate is positive almost everywhere on the actual union of time slices. -/
theorem timeSpace_positive_ae
    (m : ℕ /- [definition] -/) :
    ∀ᵐ p ∂timeSpaceMeasure m, 0 < p.2 := by
  unfold timeSpaceMeasure
  exact (Measure.ae_prod_iff_ae_ae (p := fun z : Fin m × ℝ => 0 < z.2) (by measurability)).mpr
    (Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioi))

/-- Arbitrary positive spatial exponential rates give actual L2 functions on time-space. -/
theorem timeSpace_exp_memLp
    (m : ℕ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/) :
    MemLp (fun p : TimeSpace m => Real.exp (-a*p.2)) 2 (timeSpaceMeasure m) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [add_zero] using timeSpace_exponential_square_integrable m (fun _ => 0) a ha

/-- Measurable product-exponential kernel domination gives square integrability on time-space. -/
theorem timeSpace_kernel_memLp_of_envelope
    (m : ℕ /- [definition] -/)
    (K : TimeSpace m × TimeSpace m → ℝ /- [definition] -/)
    (C a b : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hb : 0 < b /- [standing] -/)
    (hm : Measurable K /- [standing] -/)
    (hbound : ∀ p q, 0 ≤ p.2 → 0 ≤ q.2 →
      |K (p,q)| ≤ C*Real.exp (-a*p.2)*Real.exp (-b*q.2) /- [standing] -/) :
    MemLp K 2 ((timeSpaceMeasure m).prod (timeSpaceMeasure m)) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  have hi := ((timeSpace_exp_memLp m a ha).integrable_sq.mul_prod
    (timeSpace_exp_memLp m b hb).integrable_sq).const_mul (C^2)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply hi.mono' (hm.pow_const 2).aestronglyMeasurable
  have hp : ∀ᵐ z ∂(timeSpaceMeasure m).prod (timeSpaceMeasure m), 0 < z.1.2 ∧ 0 < z.2.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [timeSpace_positive_ae m] with p hp
    filter_upwards [timeSpace_positive_ae m] with q hq
    exact ⟨hp,hq⟩
  filter_upwards [hp] with z hz
  have h := pow_le_pow_left₀ (abs_nonneg _) (hbound z.1 z.2 hz.1.le hz.2.le) 2
  simpa only [Real.norm_of_nonneg (sq_nonneg _),sq_abs,mul_pow,mul_assoc] using h

/-- The common transposed Volterra kernel preserves labels and retains a decaying weight. -/
noncomputable def timeSpaceVolterraKernel
    (m : ℕ /- [definition] -/)
    (a : ℝ /- [definition] -/) : TimeSpace m × TimeSpace m → ℝ := fun z =>
    if z.1.1=z.2.1 ∧ 0 ≤ z.1.2 ∧ z.1.2<z.2.2 then Real.exp (-(a/2)*z.2.2) else 0

/-- Joint measurability of the label-preserving Volterra factor. -/
theorem timeSpaceVolterraKernel_measurable
    (m : ℕ /- [definition] -/)
    (a : ℝ /- [definition] -/) :
    Measurable (timeSpaceVolterraKernel m a) := by
  unfold timeSpaceVolterraKernel
  apply Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The common Volterra factor is square integrable in both coordinates. -/
theorem timeSpaceVolterraKernel_memLp
    (m : ℕ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/) :
    MemLp (timeSpaceVolterraKernel m a) 2 ((timeSpaceMeasure m).prod (timeSpaceMeasure m)) := by
  apply timeSpace_kernel_memLp_of_envelope m _ 1 (a/4) (a/4) (by norm_num)
    (by linarith) (by linarith) (timeSpaceVolterraKernel_measurable m a)
  intro p q hp hq
  unfold timeSpaceVolterraKernel
  split_ifs with h
  · rw [abs_of_pos (Real.exp_pos _),one_mul,← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [h.2.2])
  · simp only [abs_zero]
    positivity

/-- Every common Volterra row has a genuine L2 representative. -/
theorem timeSpaceVolterraKernel_row_memLp
    (m : ℕ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/)
    (q : TimeSpace m /- [definition] -/) :
    MemLp (fun t => star (timeSpaceVolterraKernel m a (q,t))) 2 (timeSpaceMeasure m) := by
  simp only [star_trivial]
  apply (timeSpace_exp_memLp m (a/2) (by linarith)).of_le
    (((timeSpaceVolterraKernel_measurable m a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  change |timeSpaceVolterraKernel m a (q,t)| ≤ |Real.exp (-(a/2)*t.2)|
  unfold timeSpaceVolterraKernel
  split_ifs
  · rfl
  · rw [abs_zero,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_nonneg _

/-- The derivative factor uses the same Volterra weight for every time block. -/
noncomputable def timeSpaceDerivativeFactorKernel
    (m : ℕ /- [definition] -/)
    (D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/) : TimeSpace m × TimeSpace m → ℝ := fun z =>
    -D z.1 z.2*Real.exp ((a/2)*z.2.2)

/-- The physical derivative envelope makes the common first factor square integrable. -/
theorem timeSpaceDerivativeFactorKernel_memLp
    (m : ℕ /- [definition] -/)
    (D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hm : Measurable (Function.uncurry D) /- [standing] -/)
    (hbound : ∀ p q, |D p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/) :
    MemLp (timeSpaceDerivativeFactorKernel m D a) 2
      ((timeSpaceMeasure m).prod (timeSpaceMeasure m)) := by
  apply timeSpace_kernel_memLp_of_envelope m _ C a (a/2) hC ha (by linarith)
  · unfold timeSpaceDerivativeFactorKernel
    exact hm.neg.mul (by fun_prop)
  · intro p q _ _
    change |-D p q*Real.exp ((a/2)*q.2)| ≤ _
    rw [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_right (hbound p q) (Real.exp_nonneg ((a/2)*q.2))
    have he : Real.exp (-a*q.2)*Real.exp ((a/2)*q.2) = Real.exp (-(a/2)*q.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc |D p q| *Real.exp ((a/2)*q.2)
        ≤ (C*Real.exp (-a*p.2)*Real.exp (-a*q.2))*Real.exp ((a/2)*q.2) := h
      _ = _ := by rw [mul_assoc (C*Real.exp (-a*p.2)),he]

/-- Every derivative-factor row has a genuine L2 representative. -/
theorem timeSpaceDerivativeFactorKernel_row_memLp
    (m : ℕ /- [definition] -/)
    (D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hm : Measurable (Function.uncurry D) /- [standing] -/)
    (hbound : ∀ p q, |D p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (p : TimeSpace m /- [definition] -/) :
    MemLp (fun t => star (timeSpaceDerivativeFactorKernel m D a (p,t))) 2 (timeSpaceMeasure m) := by
  simp only [star_trivial]
  apply ((timeSpace_exp_memLp m (a/2) (by linarith)).const_smul (C*Real.exp (-a*p.2))).of_le
  · apply Measurable.aestronglyMeasurable
    unfold timeSpaceDerivativeFactorKernel
    exact ((hm.comp (measurable_const.prodMk measurable_id)).neg).mul (by fun_prop)
  · apply Eventually.of_forall
    intro t
    change |-D p t*Real.exp ((a/2)*t.2)| ≤ |(C*Real.exp (-a*p.2))*Real.exp (-(a/2)*t.2)|
    rw [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _),abs_of_nonneg (show 0 ≤ (C*Real.exp (-a*p.2))*Real.exp (-(a/2)*t.2) by positivity)]
    have h := mul_le_mul_of_nonneg_right (hbound p t) (Real.exp_nonneg ((a/2)*t.2))
    have he : Real.exp (-a*t.2)*Real.exp ((a/2)*t.2) = Real.exp (-(a/2)*t.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc |D p t| *Real.exp ((a/2)*t.2)
        ≤ (C*Real.exp (-a*p.2)*Real.exp (-a*t.2))*Real.exp ((a/2)*t.2) := h
      _ = _ := by rw [mul_assoc (C*Real.exp (-a*p.2)),he]

/-- Exponential domination supplies every original-kernel L2 row. -/
theorem timeSpace_kernel_row_memLp_of_envelope
    (m : ℕ /- [definition] -/)
    (K : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hm : Measurable (Function.uncurry K) /- [standing] -/)
    (hbound : ∀ p q, |K p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (p : TimeSpace m /- [definition] -/) :
    MemLp (fun q => star (K p q)) 2 (timeSpaceMeasure m) := by
  simp only [star_trivial]
  apply ((timeSpace_exp_memLp m a ha).const_smul (C*Real.exp (-a*p.2))).of_le
    ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro q
  change |K p q| ≤ |(C*Real.exp (-a*p.2))*Real.exp (-a*q.2)|
  rw [abs_of_nonneg (show 0 ≤ (C*Real.exp (-a*p.2))*Real.exp (-a*q.2) by positivity)]
  exact hbound p q

/-- FTC recovers each original kernel row from its actual decaying spatial derivative. -/
theorem timeSpace_derivative_tail
    (m : ℕ /- [definition] -/)
    (K D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hmD : Measurable (Function.uncurry D) /- [standing] -/)
    (hK : ∀ p q, |K p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hD : ∀ p q, |D p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hder : ∀ p j y, HasDerivAt (fun u : ℝ => K p (j,u)) (D p (j,y)) y /- [standing] -/)
    (p : TimeSpace m /- [definition] -/)
    (j : Fin m /- [definition] -/)
    (y : ℝ /- [definition] -/) :
    (∫ u in Ioi y, -D p (j,u)) = K p (j,y) := by
  have hi : IntegrableOn (fun u : ℝ => D p (j,u)) (Ioi y) := by
    apply ((integrableOn_exp_mul_Ioi (by linarith : -a<0) y).const_mul (C*Real.exp (-a*p.2))).mono'
    · exact (hmD.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    · apply Eventually.of_forall
      intro u
      simpa only [Real.norm_eq_abs] using hD p (j,u)
  have hl : Tendsto (fun u : ℝ => K p (j,u)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hK p (j,u)))
    have he : Tendsto (fun u : ℝ => Real.exp (-a*u)) atTop (𝓝 0) := by
      simpa only [neg_mul,Function.comp_def,id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.Tendsto.const_mul_atTop ha tendsto_id)
    simpa only [mul_zero] using he.const_mul (C*Real.exp (-a*p.2))
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hder p j y).continuousAt.continuousWithinAt) (fun u _ => hder p j u) hi hl
  rw [integral_neg,hh]
  ring

/-- Label-preserving common Volterra convolution recovers every time block at once. -/
theorem timeSpace_derivative_volterra_convolution
    (m : ℕ /- [definition] -/)
    (K D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hmD : Measurable (Function.uncurry D) /- [standing] -/)
    (hK : ∀ p q, |K p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hD : ∀ p q, |D p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hder : ∀ p j y, HasDerivAt (fun u : ℝ => K p (j,u)) (D p (j,y)) y /- [standing] -/)
    (p q : TimeSpace m /- [definition] -/)
    (hq : 0 ≤ q.2 /- [standing] -/) :
    (∫ t, timeSpaceVolterraKernel m a (q,t)*timeSpaceDerivativeFactorKernel m D a (p,t)
      ∂timeSpaceMeasure m) = K p q := by
  classical
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  have hv := timeSpaceVolterraKernel_row_memLp m a ha q
  have hd := timeSpaceDerivativeFactorKernel_row_memLp m D C a hC ha hmD hD p
  simp only [star_trivial] at hv hd
  have hi : Integrable (fun t => timeSpaceVolterraKernel m a (q,t)*timeSpaceDerivativeFactorKernel m D a (p,t))
      (timeSpaceMeasure m) := by
    exact (hv.integrable_mul hd).congr (Eventually.of_forall (fun t => rfl))
  change (∫ t, timeSpaceVolterraKernel m a (q,t)*timeSpaceDerivativeFactorKernel m D a (p,t)
    ∂Measure.count.prod halfLineMeasure) = _
  rw [integral_prod _ hi,integral_count]
  have hsum : (∑ i : Fin m, ∫ u, timeSpaceVolterraKernel m a (q,(i,u))*
      timeSpaceDerivativeFactorKernel m D a (p,(i,u)) ∂halfLineMeasure) =
      ∫ u, timeSpaceVolterraKernel m a (q,(q.1,u))*
        timeSpaceDerivativeFactorKernel m D a (p,(q.1,u)) ∂halfLineMeasure := by
    apply Finset.sum_eq_single q.1
    · intro i _ hi
      simp only [timeSpaceVolterraKernel,hi.symm,false_and,if_false,zero_mul,integral_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hsum]
  have he : (fun u => timeSpaceVolterraKernel m a (q,(q.1,u))*
      timeSpaceDerivativeFactorKernel m D a (p,(q.1,u))) =ᵐ[halfLineMeasure]
      (Ioi q.2).indicator (fun u => -D p (q.1,u)) := by
    apply Eventually.of_forall
    intro u
    by_cases hu : q.2<u
    · simp only [timeSpaceVolterraKernel,timeSpaceDerivativeFactorKernel,
        hq,hu,and_self,and_true,true_and,if_true,
        indicator_of_mem (show u ∈ Ioi q.2 from hu)]
      rw [mul_comm, mul_assoc,← Real.exp_add]
      simp only [show (a/2)*u + -(a/2)*u = 0 by ring,Real.exp_zero,mul_one]
    · simp [timeSpaceVolterraKernel,hu,indicator_of_notMem (show u ∉ Ioi q.2 from hu)]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioi]
  have hm : halfLineMeasure.restrict (Ioi q.2) = volume.restrict (Ioi q.2) :=
    Measure.restrict_restrict_of_subset (by intro u hu; exact lt_of_le_of_lt hq hu)
  rw [hm]
  exact timeSpace_derivative_tail m K D C a hC ha hmD hK hD hder p q.1 q.2

/-- The common Volterra operator sends derivative-factor rows to original physical rows. -/
theorem timeSpace_volterra_factor_row
    (m : ℕ /- [definition] -/)
    (K D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hmK : Measurable (Function.uncurry K) /- [standing] -/)
    (hmD : Measurable (Function.uncurry D) /- [standing] -/)
    (hK : ∀ p q, |K p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hD : ∀ p q, |D p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hder : ∀ p j y, HasDerivAt (fun u : ℝ => K p (j,u)) (D p (j,y)) y /- [standing] -/)
    (p : TimeSpace m /- [definition] -/) :
    kernelOperator (timeSpaceVolterraKernel_memLp m a ha)
      (sliceLp (timeSpaceMeasure m) (timeSpaceDerivativeFactorKernel m D a) p) =
      sliceLp (timeSpaceMeasure m) (Function.uncurry K) p := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae (timeSpaceVolterraKernel_memLp m a ha)
    (sliceLp (timeSpaceMeasure m) (timeSpaceDerivativeFactorKernel m D a) p),
    sliceLp_apply_ae (K := Function.uncurry K) (x := p) (timeSpace_kernel_row_memLp_of_envelope m K C a hC ha hmK hK p),
    timeSpace_positive_ae m] with q hv hk hq
  rw [hv,hk]
  change (∫ t, timeSpaceVolterraKernel m a (q,t)*
    (sliceLp (timeSpaceMeasure m) (timeSpaceDerivativeFactorKernel m D a) p) t ∂timeSpaceMeasure m) = _
  simp only [star_trivial,Function.uncurry]
  have he : (∫ t, timeSpaceVolterraKernel m a (q,t)*
      (sliceLp (timeSpaceMeasure m) (timeSpaceDerivativeFactorKernel m D a) p) t ∂timeSpaceMeasure m) =
      ∫ t, timeSpaceVolterraKernel m a (q,t)*timeSpaceDerivativeFactorKernel m D a (p,t) ∂timeSpaceMeasure m := by
    apply integral_congr_ae
    filter_upwards [sliceLp_apply_ae (timeSpaceDerivativeFactorKernel_row_memLp m D C a hC ha hmD hD p)] with t ht
    simp only [ht,star_trivial]
  rw [he]
  exact timeSpace_derivative_volterra_convolution m K D C a hC ha hmD hK hD hder p q hq.le

/-- One common Hilbert--Schmidt factorization gives trace class on the full time-space domain. -/
theorem timeSpace_kernel_isTraceClass_of_derivative_envelope
    (m : ℕ /- [definition] -/)
    (K D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hmK : Measurable (Function.uncurry K) /- [standing] -/)
    (hmD : Measurable (Function.uncurry D) /- [standing] -/)
    (hK : ∀ p q, |K p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hD : ∀ p q, |D p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hder : ∀ p j y, HasDerivAt (fun u : ℝ => K p (j,u)) (D p (j,y)) y /- [standing] -/) :
    IsTraceClass (kernelOperator (timeSpace_kernel_memLp_of_envelope m (Function.uncurry K) C a a hC ha ha hmK
      (fun p q _ _ => hK p q))) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  let A := kernelOperator (timeSpaceDerivativeFactorKernel_memLp m D C a hC ha hmD hD)
  let B := kernelOperator (timeSpaceVolterraKernel_memLp m a ha)
  refine ⟨A,B.adjoint,isHilbertSchmidt_kernelOperator _,(isHilbertSchmidt_kernelOperator _).adjoint,?_⟩
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_eval_inner_ae (timeSpace_kernel_memLp_of_envelope m (Function.uncurry K) C a a hC ha ha hmK
    (fun p q _ _ => hK p q)) f,
    kernelOperator_eval_inner_ae (timeSpaceDerivativeFactorKernel_memLp m D C a hC ha hmD hD) (B.adjoint f)] with p hk hA
  change _ = A (B.adjoint f) p
  change (A (B.adjoint f)) p = inner ℝ
    (sliceLp (timeSpaceMeasure m) (timeSpaceDerivativeFactorKernel m D a) p) (B.adjoint f) at hA
  rw [hk,hA,B.adjoint_inner_right,timeSpace_volterra_factor_row m K D C a hC ha hmK hmD hK hD hder]

/-- One common physical factorization, with no probability hypothesis. -/
theorem timeSpace_kernel_eq_derivative_volterra
    (m : ℕ /- [definition] -/)
    (K D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hmK : Measurable (Function.uncurry K) /- [standing] -/)
    (hmD : Measurable (Function.uncurry D) /- [standing] -/)
    (hK : ∀ p q, |K p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hD : ∀ p q, |D p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hder : ∀ p j y, HasDerivAt (fun u : ℝ => K p (j,u)) (D p (j,y)) y /- [standing] -/) :
    kernelOperator (timeSpace_kernel_memLp_of_envelope m (Function.uncurry K) C a a hC ha ha hmK
      (fun p q _ _ => hK p q)) =
      kernelOperator (timeSpaceDerivativeFactorKernel_memLp m D C a hC ha hmD hD) ∘L
        (kernelOperator (timeSpaceVolterraKernel_memLp m a ha)).adjoint := by
  let A := kernelOperator (timeSpaceDerivativeFactorKernel_memLp m D C a hC ha hmD hD)
  let B := kernelOperator (timeSpaceVolterraKernel_memLp m a ha)
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_eval_inner_ae (timeSpace_kernel_memLp_of_envelope m (Function.uncurry K) C a a hC ha ha hmK
    (fun p q _ _ => hK p q)) f,
    kernelOperator_eval_inner_ae (timeSpaceDerivativeFactorKernel_memLp m D C a hC ha hmD hD) (B.adjoint f)] with p hk hA
  change _ = A (B.adjoint f) p
  change (A (B.adjoint f)) p = inner ℝ
    (sliceLp (timeSpaceMeasure m) (timeSpaceDerivativeFactorKernel m D a) p) (B.adjoint f) at hA
  rw [hk,hA,B.adjoint_inner_right,timeSpace_volterra_factor_row m K D C a hC ha hmK hmD hK hD hder]


/-- The absolutely convergent physical Fredholm series is the actual full trace-class operator determinant. -/
theorem timeSpace_kernelFredholm_eq_realOperatorDet
    {ι : Type* /- [definition] -/}
    [Countable ι /- [standing] -/]
    (m : ℕ /- [definition] -/)
    (K D : TimeSpace m → TimeSpace m → ℝ /- [definition] -/)
    (C a : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hmK : Measurable (Function.uncurry K) /- [standing] -/)
    (hmD : Measurable (Function.uncurry D) /- [standing] -/)
    (hK : ∀ p q, |K p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hD : ∀ p q, |D p q| ≤ C*Real.exp (-a*p.2)*Real.exp (-a*q.2) /- [standing] -/)
    (hder : ∀ p j y, HasDerivAt (fun u : ℝ => K p (j,u)) (D p (j,y)) y /- [standing] -/)
    (b : HilbertBasis ι ℝ (TimeSpaceL2 m) /- [definition] -/)
    (z : ℝ /- [definition] -/) :
    kernelFredholm (timeSpaceMeasure m) K (z : ℂ) =
      (realOperatorDet b (kernelOperator (timeSpace_kernel_memLp_of_envelope m
        (Function.uncurry K) C a a hC ha ha hmK (fun p q _ _ => hK p q))) z : ℂ) := by
  let A := kernelOperator (timeSpaceDerivativeFactorKernel_memLp m D C a hC ha hmD hD)
  let V := kernelOperator (timeSpaceVolterraKernel_memLp m a ha)
  have hA := summable_norm_sq_apply_basis
    (isHilbertSchmidt_kernelOperator (timeSpaceDerivativeFactorKernel_memLp m D C a hC ha hmD hD)) b
  have hV := summable_norm_sq_apply_basis
    (isHilbertSchmidt_kernelOperator (timeSpaceVolterraKernel_memLp m a ha)).adjoint b
  have h := kernelFredholm_convolution_eq_of_integral_factors (timeSpaceMeasure m) b A V.adjoint hA hV
    (fun p u => timeSpaceDerivativeFactorKernel m D a (p,u))
    (fun u q => timeSpaceVolterraKernel m a (q,u))
    (sliceLp (timeSpaceMeasure m) (timeSpaceDerivativeFactorKernel m D a))
    (sliceLp (timeSpaceMeasure m) (timeSpaceVolterraKernel m a))
    {p | 0 < p.2} (timeSpace_positive_ae m)
    (fun p _ => by
      simpa only [star_trivial] using (sliceLp_apply_ae
        (K := timeSpaceDerivativeFactorKernel m D a) (x := p)
        (timeSpaceDerivativeFactorKernel_row_memLp m D C a hC ha hmD hD p)))
    (fun q _ => by
      simpa only [star_trivial] using (sliceLp_apply_ae
        (K := timeSpaceVolterraKernel m a) (x := q)
        (timeSpaceVolterraKernel_row_memLp m a ha q)))
    (kernelOperator_apply_ae (timeSpaceDerivativeFactorKernel_memLp m D C a hC ha hmD hD))
    (by
      intro f
      filter_upwards [kernelOperator_apply_ae (timeSpaceVolterraKernel_memLp m a ha) f] with q hq
      simpa only [ContinuousLinearMap.adjoint_adjoint,V,kernelIntegralFun] using hq) z
  have hk := kernelFredholm_congr_on_full_measure (timeSpaceMeasure m)
    (fun p q => ∫ u, timeSpaceDerivativeFactorKernel m D a (p,u)*timeSpaceVolterraKernel m a (q,u)
      ∂timeSpaceMeasure m) K {p | 0 < p.2} (timeSpace_positive_ae m)
    (fun p _ q hq => by
      simpa only [mul_comm] using timeSpace_derivative_volterra_convolution m K D C a hC ha hmD hK hD hder p q hq.le)
    (z : ℂ)
  rw [← timeSpace_kernel_eq_derivative_volterra m K D C a hC ha hmK hmD hK hD hder] at h
  exact hk.symm.trans h


end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceMeasure_sigmaFinite
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_positive_ae
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_exp_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_kernel_memLp_of_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceVolterraKernel
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceVolterraKernel_measurable
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceVolterraKernel_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceVolterraKernel_row_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceDerivativeFactorKernel
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceDerivativeFactorKernel_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpaceDerivativeFactorKernel_row_memLp
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_kernel_row_memLp_of_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_derivative_tail
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_derivative_volterra_convolution
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_volterra_factor_row
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_kernel_isTraceClass_of_derivative_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_kernel_eq_derivative_volterra
#print axioms RMTFoundations.TracyWidom.Airy2.timeSpace_kernelFredholm_eq_realOperatorDet
