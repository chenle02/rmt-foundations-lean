import RMTFoundations.Airy.FredholmBridge

namespace RMTFoundations.Fredholm

open MeasureTheory Filter Topology Set
open scoped Classical ENNReal
open RMTFoundations.Airy RMTFoundations.AiryKernel

/-- The Airy energy identity gives a uniform derivative bound on the full real line. -/
theorem airy_deriv_exp_bound
    : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      |deriv airyAiReal x| ≤ C * (1 + Real.exp (-x)) * Real.exp (-x / 2) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  refine ⟨C, hCpos, fun x => ?_⟩
  have hint : (∫ t, (airyAiReal (x + t)) ^ 2 ∂halfLineMeasure) ≤
      (C * Real.exp (-x)) ^ 2 := by
    have hb : ∀ t, (airyAiReal (x + t)) ^ 2 ≤
        (C * Real.exp (-x)) ^ 2 * (Real.exp (-t)) ^ 2 := by
      intro t
      have h := pow_le_pow_left₀ (abs_nonneg _) (hC (x + t)) 2
      simpa only [sq_abs, neg_add, Real.exp_add, mul_pow, mul_assoc] using h
    have hi := integral_mono_ae (integrable_airyAiReal_sq_comp_add_Ioi x)
      (RMTFoundations.AiryBounds.integrable_exp_square.const_mul ((C * Real.exp (-x)) ^ 2))
      (Eventually.of_forall hb)
    rw [integral_const_mul] at hi
    exact hi.trans (mul_le_of_le_one_right (sq_nonneg _) integral_exp_square_le_one)
  have htwist : x * (airyAiReal x) ^ 2 ≤ C ^ 2 * Real.exp (-x) := by
    by_cases hx : 0 ≤ x
    · have hs := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hC x) 2) hx
      rw [sq_abs, mul_pow, exp_neg_sq] at hs
      have h1 : x ≤ Real.exp x := (by linarith : x ≤ x + 1).trans (Real.add_one_le_exp x)
      calc x * (airyAiReal x) ^ 2 ≤ C ^ 2 * (x * Real.exp (-(2 * x))) := by nlinarith [hs]
        _ ≤ C ^ 2 * (Real.exp x * Real.exp (-(2 * x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (sq_nonneg _)
        _ = C ^ 2 * Real.exp (-x) := by rw [← Real.exp_add]; (congr 2; ring)
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx) (sq_nonneg _)).trans (by positivity)
  have he : (deriv airyAiReal x) ^ 2 ≤
      C ^ 2 * ((Real.exp (-x)) ^ 2 + Real.exp (-x)) := by
    have henergy := airyAiReal_sq_integral x
    change (∫ t, (airyAiReal (x + t)) ^ 2 ∂halfLineMeasure) = _ at henergy
    rw [mul_pow] at hint
    nlinarith
  have hexp : (Real.exp (-x / 2)) ^ 2 = Real.exp (-x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hrhs : (C * (1 + Real.exp (-x)) * Real.exp (-x / 2)) ^ 2 ≥
      C ^ 2 * ((Real.exp (-x)) ^ 2 + Real.exp (-x)) := by
    rw [mul_pow, hexp]
    nlinarith [sq_nonneg C, Real.exp_pos (-x), mul_nonneg (sq_nonneg C) (sq_nonneg (Real.exp (-x))),
      mul_nonneg (sq_nonneg C) (pow_nonneg (Real.exp_pos (-x)).le 3)]
  have hnonneg : 0 ≤ C * (1 + Real.exp (-x)) * Real.exp (-x / 2) := by positivity
  have habs : |deriv airyAiReal x| ^ 2 = (deriv airyAiReal x) ^ 2 := sq_abs _
  nlinarith [abs_nonneg (deriv airyAiReal x)]

/-- The derivative has an exponential bound on every fixed lower half-line. -/
theorem airy_deriv_halfline_exp_bound
    (a : ℝ /- [definition] -/ )
    : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, a ≤ x →
      |deriv airyAiReal x| ≤ C * Real.exp (-x / 2) := by
  obtain ⟨C,hC,hb⟩ := airy_deriv_exp_bound
  refine ⟨C * (1 + Real.exp (-a)), by positivity, fun x hx => ?_⟩
  exact (hb x).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) (Real.exp_le_exp.mpr (neg_le_neg hx))) hC.le)
    (Real.exp_pos _).le)

/-- The derivative of a translated Ai is absolutely integrable on every right half-line. -/
theorem integrable_airy_deriv_shift_Ioi
    (u a : ℝ /- [definition] -/ )
    : IntegrableOn (fun t => deriv airyAiReal (u + t)) (Ioi a) := by
  obtain ⟨C,hC,hb⟩ := airy_deriv_halfline_exp_bound (u + a)
  have hmajor : IntegrableOn (fun t => C * Real.exp (-u / 2) * Real.exp (-(1 / 2 : ℝ) * t)) (Ioi a) :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) a).const_mul _
  apply hmajor.mono' (continuous_deriv_airyAiReal.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have h := hb (u + t) (by linarith [show a < t from ht])
  have he : -t / 2 = -(1 / 2 : ℝ) * t := by ring
  simpa only [Real.norm_eq_abs, Function.comp_def, Pi.add_apply, id_eq, neg_add, add_div, Real.exp_add, mul_assoc, he] using h

/-- FTC identifies the weighted Volterra convolution with the actual Airy Hankel kernel. -/
theorem airy_integral_neg_deriv_tail
    (u a : ℝ /- [definition] -/ )
    : (∫ t in Ioi a, -deriv airyAiReal (u + t)) = airyAiReal (u + a) := by
  have hd (t : ℝ) : HasDerivAt (fun t => airyAiReal (u + t)) (deriv airyAiReal (u + t)) t := by
    have h := (hasDerivAt_airyAiReal' (u + t)).comp t
      ((hasDerivAt_const t u).add (hasDerivAt_id' t))
    exact h.congr_deriv (by ring)
  have hlim : Tendsto (fun t => airyAiReal (u + t)) atTop (𝓝 0) := by
    obtain ⟨C,hC,hb⟩ := airyAiReal_abs_le_exp'
    apply squeeze_zero_norm' (Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hb (u + t)))
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_atTop_add_const_left atTop u tendsto_id)).const_mul C
    simpa only [mul_zero, Function.comp_def, id_eq] using h
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hd a).continuousAt.continuousWithinAt) (fun t _ => hd t)
    (integrable_airy_deriv_shift_Ioi u a) hlim
  rw [integral_neg, h]
  ring

/-- Exponential weights of every negative rate lie in the actual half-line L2 space. -/
theorem memLp_halfline_exp_rate
    (a : ℝ /- [definition] -/ )
    (ha : a < 0 /- [standing] -/ )
    : MemLp (fun t : ℝ => Real.exp (a * t)) 2 halfLineMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  have he : (fun t : ℝ => (Real.exp (a * t)) ^ 2) =
      (fun t => Real.exp ((2 * a) * t)) := by
    funext t
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact integrableOn_exp_mul_Ioi (by linarith : 2 * a < 0) 0

/-- The separable product of two exponential weights is a Hilbert--Schmidt kernel. -/
theorem memLp_halfline_exp_pair_rate
    (a d : ℝ /- [definition] -/ )
    (ha : a < 0 /- [standing] -/ )
    (hd : d < 0 /- [standing] -/ )
    : MemLp (fun p : ℝ × ℝ => Real.exp (a * p.1) * Real.exp (d * p.2))
      2 (halfLineMeasure.prod halfLineMeasure) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  exact ((memLp_halfline_exp_rate a ha).integrable_sq.mul_prod
    (memLp_halfline_exp_rate d hd).integrable_sq).congr
    (Eventually.of_forall (fun p => (mul_pow _ _ 2).symm))

/-- Weighted derivative kernel. Cutoffs outside the measure's support fix representatives. -/
noncomputable def airyDerivativeFactorKernel
    (s : ℝ /- [definition] -/ )
    : ℝ × ℝ → ℝ := fun p => if 0 ≤ p.1 ∧ 0 ≤ p.2 then
      -deriv airyAiReal (p.1 + p.2 + s) * Real.exp (p.2 / 4) else 0

/-- Weighted Volterra kernel, with the transpose convention matching B-adjoint. -/
noncomputable def airyVolterraFactorKernel : ℝ × ℝ → ℝ := fun p =>
  if 0 ≤ p.1 ∧ p.1 < p.2 then Real.exp (-p.2 / 4) else 0

theorem measurable_airyDerivativeFactorKernel
    (s : ℝ /- [definition] -/ )
    : Measurable (airyDerivativeFactorKernel s) := by
  unfold airyDerivativeFactorKernel
  apply Measurable.ite (by measurability)
    (((continuous_deriv_airyAiReal.measurable.comp
      ((measurable_fst.add measurable_snd).add_const s)).neg).mul (by fun_prop))
    measurable_const

theorem measurable_airyVolterraFactorKernel
    : Measurable airyVolterraFactorKernel := by
  unfold airyVolterraFactorKernel
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- A derivative factor bound at every level, including every negative level. -/
theorem airyDerivativeFactorKernel_bound
    (s : ℝ /- [definition] -/ )
    : ∃ D : ℝ, 0 < D ∧ ∀ p : ℝ × ℝ,
      |airyDerivativeFactorKernel s p| ≤
        D * (Real.exp (-(1 / 2 : ℝ) * p.1) * Real.exp (-(1 / 4 : ℝ) * p.2)) := by
  obtain ⟨C,hC,hb⟩ := airy_deriv_halfline_exp_bound s
  refine ⟨C * Real.exp (-s / 2), by positivity, fun p => ?_⟩
  by_cases hp : 0 ≤ p.1 ∧ 0 ≤ p.2
  · rw [airyDerivativeFactorKernel, if_pos hp, abs_mul, abs_neg,
      abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_right (hb (p.1 + p.2 + s) (by linarith [hp.1,hp.2]))
      (Real.exp_pos (p.2 / 4)).le
    calc
      _ ≤ C * Real.exp (-(p.1 + p.2 + s) / 2) * Real.exp (p.2 / 4) := h
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        have he : -(p.1 + p.2 + s) / 2 + p.2 / 4 =
            -s / 2 + (-(1 / 2 : ℝ) * p.1 + -(1 / 4 : ℝ) * p.2) := by ring
        rw [he, Real.exp_add, Real.exp_add]
        ring
  · rw [airyDerivativeFactorKernel, if_neg hp, abs_zero]
    positivity

/-- Volterra's cutoff supplies exponential product domination. -/
theorem airyVolterraFactorKernel_bound
    (p : ℝ × ℝ /- [definition] -/ )
    : |airyVolterraFactorKernel p| ≤
      Real.exp (-(1 / 8 : ℝ) * p.1) * Real.exp (-(1 / 8 : ℝ) * p.2) := by
  by_cases hp : 0 ≤ p.1 ∧ p.1 < p.2
  · rw [airyVolterraFactorKernel, if_pos hp, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hp.2]
  · rw [airyVolterraFactorKernel, if_neg hp, abs_zero]
    positivity

theorem memLp_airyDerivativeFactorKernel
    (s : ℝ /- [definition] -/ )
    : MemLp (airyDerivativeFactorKernel s) 2 (halfLineMeasure.prod halfLineMeasure) := by
  obtain ⟨D,hD,hb⟩ := airyDerivativeFactorKernel_bound s
  apply ((memLp_halfline_exp_pair_rate (-(1 / 2)) (-(1 / 4)) (by norm_num) (by norm_num)).const_smul D).of_le
    (measurable_airyDerivativeFactorKernel s).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by positivity :
    0 < D * (Real.exp (-(1 / 2 : ℝ) * p.1) * Real.exp (-(1 / 4 : ℝ) * p.2)))] using hb p

theorem memLp_airyVolterraFactorKernel
    : MemLp airyVolterraFactorKernel 2 (halfLineMeasure.prod halfLineMeasure) := by
  apply (memLp_halfline_exp_pair_rate (-(1 / 8)) (-(1 / 8)) (by norm_num) (by norm_num)).of_le
    measurable_airyVolterraFactorKernel.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  simpa only [Real.norm_eq_abs, abs_of_pos (by positivity :
    0 < Real.exp (-(1 / 8 : ℝ) * p.1) * Real.exp (-(1 / 8 : ℝ) * p.2))] using
    airyVolterraFactorKernel_bound p

/-- Every weighted derivative row has an actual L2 representative. -/
theorem memLp_airyDerivativeFactorRow
    (s x : ℝ /- [definition] -/ )
    : MemLp (fun t => star (airyDerivativeFactorKernel s (x, t))) 2 halfLineMeasure := by
  simp only [star_trivial]
  obtain ⟨D,hD,hb⟩ := airyDerivativeFactorKernel_bound s
  apply ((memLp_halfline_exp_rate (-(1 / 4)) (by norm_num)).const_smul
    (D * Real.exp (-(1 / 2 : ℝ) * x))).of_le
    (((measurable_airyDerivativeFactorKernel s).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < (D * Real.exp (-(1 / 2 : ℝ) * x)) *
    Real.exp (-(1 / 4 : ℝ) * t))]
  simpa only [mul_assoc,Function.comp_def,id_eq] using hb (x,t)

/-- Every weighted Volterra row has an actual L2 representative. -/
theorem memLp_airyVolterraFactorRow
    (y : ℝ /- [definition] -/ )
    : MemLp (fun t => star (airyVolterraFactorKernel (y,t))) 2 halfLineMeasure := by
  simp only [star_trivial]
  apply ((memLp_halfline_exp_rate (-(1 / 8)) (by norm_num)).const_smul
    (Real.exp (-(1 / 8 : ℝ) * y))).of_le
    ((measurable_airyVolterraFactorKernel.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  simpa only [star_trivial, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,Function.comp_def,id_eq,
    abs_of_pos (by positivity : 0 < Real.exp (-(1 / 8 : ℝ) * y) *
      Real.exp (-(1 / 8 : ℝ) * t))] using airyVolterraFactorKernel_bound (y,t)

/-- The two genuine HS factor kernels convolve to the physical Hankel kernel
on a common full-measure half-line, including all of its diagonals. -/
theorem airyDerivative_volterra_convolution
    (s x y : ℝ /- [definition] -/ )
    (hx : 0 ≤ x /- [standing] -/ )
    (hy : 0 ≤ y /- [standing] -/ )
    : (∫ t, airyDerivativeFactorKernel s (x,t) * airyVolterraFactorKernel (y,t)
        ∂halfLineMeasure) = airyAiReal (x + y + s) := by
  have he : (fun t => airyDerivativeFactorKernel s (x,t) * airyVolterraFactorKernel (y,t))
      =ᵐ[halfLineMeasure] (Ioi y).indicator (fun t => -deriv airyAiReal (x + t + s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases hyt : y < t
    · rw [airyDerivativeFactorKernel,
        if_pos (show 0 ≤ x ∧ 0 ≤ t from ⟨hx,ht.le⟩),
        airyVolterraFactorKernel, if_pos (show 0 ≤ y ∧ y < t from ⟨hy,hyt⟩),
        indicator_of_mem (show t ∈ Ioi y from hyt), mul_assoc, ← Real.exp_add]
      have he : t / 4 + -t / 4 = 0 := by ring
      rw [he,Real.exp_zero,mul_one]
    · simp only [airyVolterraFactorKernel, if_neg (by tauto : ¬(0 ≤ y ∧ y < t)), mul_zero,
        indicator_of_notMem (show t ∉ Ioi y from hyt)]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioi]
  have hm : halfLineMeasure.restrict (Ioi y) = volume.restrict (Ioi y) :=
    Measure.restrict_restrict_of_subset (by intro t ht; exact lt_of_le_of_lt hy ht)
  rw [hm]
  simpa only [add_assoc, add_left_comm, add_comm] using airy_integral_neg_deriv_tail (x+s) y

noncomputable def airyDerivativeFactor
    (s : ℝ /- [definition] -/ )
    : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
  kernelOperator (memLp_airyDerivativeFactorKernel s)

noncomputable def airyVolterraFactor
    : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
  kernelOperator memLp_airyVolterraFactorKernel

/-- The weighted Volterra operator maps each derivative row to the physical Airy row. -/
theorem airyVolterraFactor_derivative_row
    (s x : ℝ /- [definition] -/ )
    (hx : 0 ≤ x /- [standing] -/ )
    : airyVolterraFactor (sliceLp halfLineMeasure (airyDerivativeFactorKernel s) x) =
      sliceLp halfLineMeasure (airyHankelShiftKernel s) x := by
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae memLp_airyVolterraFactorKernel
    (sliceLp halfLineMeasure (airyDerivativeFactorKernel s) x),
    sliceLp_apply_ae (memLp_airyHankelShiftSlice s x),
    ae_restrict_mem measurableSet_Ioi] with y hy hrow hpos
  change (airyVolterraFactor _) y = _ at hy
  rw [hy, hrow]
  change (∫ t, airyVolterraFactorKernel (y,t) *
    (sliceLp halfLineMeasure (airyDerivativeFactorKernel s) x) t ∂halfLineMeasure) = _
  have he : (∫ t, airyVolterraFactorKernel (y,t) *
      (sliceLp halfLineMeasure (airyDerivativeFactorKernel s) x) t ∂halfLineMeasure) =
      ∫ t, airyDerivativeFactorKernel s (x,t) * airyVolterraFactorKernel (y,t) ∂halfLineMeasure := by
    apply integral_congr_ae
    filter_upwards [sliceLp_apply_ae (memLp_airyDerivativeFactorRow s x)] with t ht
    simp only [ht, star_trivial, mul_comm]
  rw [he, airyDerivative_volterra_convolution s x y hx hpos.le]
  simp only [star_trivial, airyHankelShiftKernel]

/-- The actual Airy Hankel operator, not merely a scalar kernel, factors as two
Hilbert--Schmidt maps. This handles TW1 without a norm-disk restriction. -/
theorem airyHankelShift_eq_derivative_volterra
    (s : ℝ /- [definition] -/ )
    : airyHankelShift s = airyDerivativeFactor s ∘L airyVolterraFactor.adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_eval_inner_ae (memLp_airyHankelShiftKernel s) f,
    kernelOperator_eval_inner_ae (memLp_airyDerivativeFactorKernel s) (airyVolterraFactor.adjoint f),
    ae_restrict_mem measurableSet_Ioi] with x hH hA hx
  change (airyHankelShift s f) x = (airyDerivativeFactor s (airyVolterraFactor.adjoint f)) x
  change (airyHankelShift s f) x =
    inner ℝ (sliceLp halfLineMeasure (airyHankelShiftKernel s) x) f at hH
  change (airyDerivativeFactor s (airyVolterraFactor.adjoint f)) x =
    inner ℝ (sliceLp halfLineMeasure (airyDerivativeFactorKernel s) x)
      (airyVolterraFactor.adjoint f) at hA
  rw [hH,hA,airyVolterraFactor.adjoint_inner_right,
    airyVolterraFactor_derivative_row s x hx.le]

/-- The Airy Hankel operator is trace class at every real level. -/
theorem isTraceClass_airyHankelShift
    (s : ℝ /- [definition] -/ )
    : IsTraceClass (airyHankelShift s) := by
  exact ⟨airyDerivativeFactor s, airyVolterraFactor.adjoint,
    isHilbertSchmidt_kernelOperator (memLp_airyDerivativeFactorKernel s),
    (isHilbertSchmidt_kernelOperator memLp_airyVolterraFactorKernel).adjoint,
    airyHankelShift_eq_derivative_volterra s⟩

/-- The whole Fredholm series of the actual Airy Hankel kernel equals its
trace-class operator determinant, at every real coupling and level. -/
theorem airyHankelFredholm_eq_realOperatorDet
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s z : ℝ /- [definition] -/ )
    : kernelFredholm halfLineMeasure (fun x y => airyAiReal (x + y + s)) (z : ℂ) =
      (realOperatorDet b (airyHankelShift s) z : ℂ) := by
  have hA := summable_norm_sq_apply_basis
    (isHilbertSchmidt_kernelOperator (memLp_airyDerivativeFactorKernel s)) b
  have hB := summable_norm_sq_apply_basis
    (isHilbertSchmidt_kernelOperator memLp_airyVolterraFactorKernel).adjoint b
  have h := kernelFredholm_convolution_eq_of_integral_factors halfLineMeasure b
    (airyDerivativeFactor s) airyVolterraFactor.adjoint hA hB
    (fun x t => airyDerivativeFactorKernel s (x,t))
    (fun t y => airyVolterraFactorKernel (y,t))
    (sliceLp halfLineMeasure (airyDerivativeFactorKernel s))
    (sliceLp halfLineMeasure airyVolterraFactorKernel)
    (Ioi 0) (ae_restrict_mem measurableSet_Ioi)
    (fun x _ => by simpa only [star_trivial] using sliceLp_apply_ae (memLp_airyDerivativeFactorRow s x))
    (fun y _ => by simpa only [star_trivial] using sliceLp_apply_ae (memLp_airyVolterraFactorRow y))
    (kernelOperator_apply_ae (memLp_airyDerivativeFactorKernel s))
    (by
      intro f
      filter_upwards [kernelOperator_apply_ae memLp_airyVolterraFactorKernel f] with y hy
      simpa only [ContinuousLinearMap.adjoint_adjoint,airyVolterraFactor,kernelIntegralFun] using hy) z
  have hk := kernelFredholm_congr_on_full_measure halfLineMeasure
    (fun x y => ∫ t, airyDerivativeFactorKernel s (x,t) * airyVolterraFactorKernel (y,t) ∂halfLineMeasure)
    (fun x y => airyAiReal (x+y+s)) (Ioi 0) (ae_restrict_mem measurableSet_Ioi)
    (fun x hx y hy => airyDerivative_volterra_convolution s x y hx.le hy.le) (z : ℂ)
  rw [← airyHankelShift_eq_derivative_volterra s] at h
  exact hk.symm.trans h

/-- TW1 is the operator determinant of the actual trace-class Hankel map at -1. -/
theorem TW1_eq_realOperatorDet
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : TW1 s = (realOperatorDet b (airyHankelShift s) (-1) : ℂ) := by
  simpa only [TW1, Complex.ofReal_neg, Complex.ofReal_one] using
    airyHankelFredholm_eq_realOperatorDet b s (-1)

/-- The real-valued TW1 definition is its actual Hankel operator determinant. -/
theorem TW1R_eq_realOperatorDet
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : TW1R s = realOperatorDet b (airyHankelShift s) (-1) := by
  rw [TW1R,TW1_eq_realOperatorDet b s,Complex.ofReal_re]

noncomputable def airyOperatorTW1
    (s : ℝ /- [definition] -/ )
    : ℝ := realOperatorDet (canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure))
      (airyHankelShift s) (-1)

theorem TW1_eq_airyOperatorTW1
    (s : ℝ /- [definition] -/ )
    : TW1 s = (airyOperatorTW1 s : ℂ) := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  exact TW1_eq_realOperatorDet b s

theorem TW1R_eq_airyOperatorTW1
    (s : ℝ /- [definition] -/ )
    : TW1R s = airyOperatorTW1 s := by
  rw [TW1R,TW1_eq_airyOperatorTW1 s,Complex.ofReal_re]

/-- The physical Hankel determinant is independent of the index type of its basis. -/
theorem airyHankel_realOperatorDet_basis_independent
    {ι κ : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (c : HilbertBasis κ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s z : ℝ /- [definition] -/ )
    : realOperatorDet b (airyHankelShift s) z = realOperatorDet c (airyHankelShift s) z := by
  letI := airyL2_basis_countable b
  letI := airyL2_basis_countable c
  apply Complex.ofReal_injective
  exact (airyHankelFredholm_eq_realOperatorDet b s z).symm.trans
    (airyHankelFredholm_eq_realOperatorDet c s z)

/-- The actual Hankel determinant is analytic at every real coupling. -/
theorem airyHankel_realOperatorDet_entire
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : AnalyticOnNhd ℝ (realOperatorDet b (airyHankelShift s)) Set.univ := by
  exact realOperatorDet_entire b _ ⟨airyDerivativeFactor s,airyVolterraFactor.adjoint,
    airyHankelShift_eq_derivative_volterra s,
    summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator (memLp_airyDerivativeFactorKernel s)) b,
    summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator memLp_airyVolterraFactorKernel).adjoint b⟩

/-- Continuity of the Hankel determinant for all real levels and couplings. -/
theorem airyHankel_realOperatorDet_continuous_coupling
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : Continuous (fun s => realOperatorDet b (airyHankelShift s) z) := by
  letI := airyL2_basis_countable b
  have he : (fun s => kernelFredholm halfLineMeasure (B_fredholmKernel s) (z : ℂ)) =
      (fun s => (realOperatorDet b (airyHankelShift s) z : ℂ)) := by
    funext s
    exact (B_fredholm_physical s (z : ℂ)).trans
      (airyHankelFredholm_eq_realOperatorDet b s z)
  have hc := B_fredholm_continuous (z : ℂ)
  rw [he] at hc
  simpa only [Function.comp_def,Complex.ofReal_re] using Complex.continuous_re.comp hc

/-- The physical TW1R is the limit of ordinary finite matrix compression determinants. -/
theorem TW1R_finite_compressions_tendsto
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : Tendsto (fun t : Finset ι => Matrix.det ((1 : Matrix t t ℝ) -
        Matrix.of (fun i j : t => inner ℝ (b i) (airyHankelShift s (b j)))))
      atTop (𝓝 (TW1R s)) := by
  letI := airyL2_basis_countable b
  rw [TW1R_eq_realOperatorDet b s]
  simpa only [neg_one_smul,sub_eq_add_neg] using
    realOperatorDet_matrix_det_tendsto b _
      ⟨airyDerivativeFactor s,airyVolterraFactor.adjoint,airyHankelShift_eq_derivative_volterra s,
        summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator (memLp_airyDerivativeFactorKernel s)) b,
        summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator memLp_airyVolterraFactorKernel).adjoint b⟩ (-1)

/-- Simultaneous actual-data witness for both nonzero kernels and HS factors,
operator composition, and the TW1 determinant identity. -/
theorem airy_hankel_factorization_joint_probe
    : airyDerivativeFactorKernel 0 (0,0) ≠ 0 ∧ airyVolterraFactorKernel (0,1) ≠ 0 ∧
      IsHilbertSchmidt (airyDerivativeFactor 0) ∧ IsHilbertSchmidt airyVolterraFactor.adjoint ∧
      airyHankelShift 0 = airyDerivativeFactor 0 ∘L airyVolterraFactor.adjoint ∧
      IsTraceClass (airyHankelShift 0) ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      TW1 0 = (airyOperatorTW1 0 : ℂ) := by
  refine ⟨?_,?_,isHilbertSchmidt_kernelOperator (memLp_airyDerivativeFactorKernel 0),
    (isHilbertSchmidt_kernelOperator memLp_airyVolterraFactorKernel).adjoint,
    airyHankelShift_eq_derivative_volterra 0,isTraceClass_airyHankelShift 0,
    shiftedUnitVector_norm 0,TW1_eq_airyOperatorTW1 0⟩
  · simpa only [airyDerivativeFactorKernel, add_zero, zero_div,
      Real.exp_zero, mul_one, neg_ne_zero, if_pos (by norm_num : 0 ≤ (0 : ℝ) ∧ 0 ≤ (0 : ℝ))]
      using deriv_airyAiReal_zero_neg.ne
  · simp only [airyVolterraFactorKernel, if_pos (by norm_num : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) < 1)]
    exact (Real.exp_pos _).ne'


end RMTFoundations.Fredholm

#print axioms RMTFoundations.Fredholm.airy_deriv_exp_bound
#print axioms RMTFoundations.Fredholm.airy_deriv_halfline_exp_bound
#print axioms RMTFoundations.Fredholm.integrable_airy_deriv_shift_Ioi
#print axioms RMTFoundations.Fredholm.airy_integral_neg_deriv_tail
#print axioms RMTFoundations.Fredholm.memLp_halfline_exp_rate
#print axioms RMTFoundations.Fredholm.memLp_halfline_exp_pair_rate
#print axioms RMTFoundations.Fredholm.airyDerivativeFactorKernel
#print axioms RMTFoundations.Fredholm.airyVolterraFactorKernel
#print axioms RMTFoundations.Fredholm.measurable_airyDerivativeFactorKernel
#print axioms RMTFoundations.Fredholm.measurable_airyVolterraFactorKernel
#print axioms RMTFoundations.Fredholm.airyDerivativeFactorKernel_bound
#print axioms RMTFoundations.Fredholm.airyVolterraFactorKernel_bound
#print axioms RMTFoundations.Fredholm.memLp_airyDerivativeFactorKernel
#print axioms RMTFoundations.Fredholm.memLp_airyVolterraFactorKernel
#print axioms RMTFoundations.Fredholm.memLp_airyDerivativeFactorRow
#print axioms RMTFoundations.Fredholm.memLp_airyVolterraFactorRow
#print axioms RMTFoundations.Fredholm.airyDerivative_volterra_convolution
#print axioms RMTFoundations.Fredholm.airyDerivativeFactor
#print axioms RMTFoundations.Fredholm.airyVolterraFactor
#print axioms RMTFoundations.Fredholm.airyVolterraFactor_derivative_row
#print axioms RMTFoundations.Fredholm.airyHankelShift_eq_derivative_volterra
#print axioms RMTFoundations.Fredholm.isTraceClass_airyHankelShift
#print axioms RMTFoundations.Fredholm.airyHankelFredholm_eq_realOperatorDet
#print axioms RMTFoundations.Fredholm.TW1_eq_realOperatorDet
#print axioms RMTFoundations.Fredholm.TW1R_eq_realOperatorDet
#print axioms RMTFoundations.Fredholm.airyOperatorTW1
#print axioms RMTFoundations.Fredholm.TW1_eq_airyOperatorTW1
#print axioms RMTFoundations.Fredholm.TW1R_eq_airyOperatorTW1
#print axioms RMTFoundations.Fredholm.airyHankel_realOperatorDet_basis_independent
#print axioms RMTFoundations.Fredholm.airyHankel_realOperatorDet_entire
#print axioms RMTFoundations.Fredholm.airyHankel_realOperatorDet_continuous_coupling
#print axioms RMTFoundations.Fredholm.TW1R_finite_compressions_tendsto
#print axioms RMTFoundations.Fredholm.airy_hankel_factorization_joint_probe
