import Mathlib



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom

open MeasureTheory Filter Set
open scoped Topology

/-- A nonnegative decreasing slope is controlled by the primitive on the last half interval. -/
theorem primitive_half_interval_bound
    (g u : ℝ → ℝ) -- [definition]
    (hu : Continuous u) -- [standing]
    (hgu : ∀ t, HasDerivAt g (u t) t) -- [standing]
    (hpos : ∀ t, 0 ≤ u t) -- [standing]
    (hanti : Antitone u) -- [standing]
    (t : ℝ) -- [definition]
    (ht : 0 ≤ t) -- [standing]
    : 0 ≤ t*u t ∧ t*u t ≤ 2*(g t-g (t/2)) := by
  have hle : t/2 ≤ t := by linarith
  have hconst : IntervalIntegrable (fun _ : ℝ => u t) volume (t/2) t := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on hle hconst
    (hu.intervalIntegrable (t/2) t) (fun x hx => hanti hx.2)
  have hftc : (∫ x in (t/2)..t, u x) = g t-g (t/2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hgu x)
      (hu.intervalIntegrable (t/2) t)
  rw [intervalIntegral.integral_const, hftc] at hm
  simp only [smul_eq_mul] at hm
  exact ⟨mul_nonneg ht (hpos t), by nlinarith⟩

/-- Concavity and a finite zero right limit force the weighted slope to vanish. -/
theorem primitive_weighted_slope_tendsto_zero
    (g u : ℝ → ℝ) -- [definition]
    (hu : Continuous u) -- [standing]
    (hgu : ∀ t, HasDerivAt g (u t) t) -- [standing]
    (hpos : ∀ t, 0 ≤ u t) -- [standing]
    (hanti : Antitone u) -- [standing]
    (hg : Tendsto g atTop (𝓝 0)) -- [standing]
    : Tendsto (fun t => t*u t) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun t : ℝ => t/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (2*b)] with t ht
    linarith
  have hupper : Tendsto (fun t => 2*(g t-g (t/2))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, mul_zero] using (hg.sub (hg.comp hhalf)).const_mul 2
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (primitive_half_interval_bound g u hu hgu hpos hanti t ht).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (primitive_half_interval_bound g u hu hgu hpos hanti t ht).2

/-- The unweighted decreasing slope also tends to zero. -/
theorem primitive_slope_tendsto_zero
    (g u : ℝ → ℝ) -- [definition]
    (hu : Continuous u) -- [standing]
    (hgu : ∀ t, HasDerivAt g (u t) t) -- [standing]
    (hpos : ∀ t, 0 ≤ u t) -- [standing]
    (hanti : Antitone u) -- [standing]
    (hg : Tendsto g atTop (𝓝 0)) -- [standing]
    : Tendsto u atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall hpos) _
    (primitive_weighted_slope_tendsto_zero g u hu hgu hpos hanti hg)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ht (hpos t)

/-- A fixed-origin correction does not change the vanishing weighted slope. -/
theorem primitive_shifted_weighted_slope_tendsto_zero
    (g u : ℝ → ℝ) -- [definition]
    (hu : Continuous u) -- [standing]
    (hgu : ∀ t, HasDerivAt g (u t) t) -- [standing]
    (hpos : ∀ t, 0 ≤ u t) -- [standing]
    (hanti : Antitone u) -- [standing]
    (hg : Tendsto g atTop (𝓝 0)) -- [standing]
    (s : ℝ) -- [definition]
    : Tendsto (fun t => (t-s)*u t) atTop (𝓝 0) := by
  have ht := primitive_weighted_slope_tendsto_zero g u hu hgu hpos hanti hg
  have hz := primitive_slope_tendsto_zero g u hu hgu hpos hanti hg
  simpa only [sub_mul, mul_zero, sub_zero] using ht.sub (hz.const_mul s)

/-- The weighted square primitive has the genuine algebraic derivative. -/
theorem hasDerivAt_weighted_square_primitive
    (g u q : ℝ → ℝ) -- [definition]
    (hgu : ∀ t, HasDerivAt g (u t) t) -- [standing]
    (huq : ∀ t, HasDerivAt u (-(q t)^2) t) -- [standing]
    (s t : ℝ) -- [definition]
    : HasDerivAt (fun x => g x-(x-s)*u x) ((t-s)*(q t)^2) t := by
  convert! (hgu t).sub (((hasDerivAt_id t).sub_const s).mul (huq t)) using 1
  simp only [id_eq]
  ring

/-- Finite concave primitive limit gives both genuine square tail integrals,
without a quantitative decay or square-integrability premise. -/
theorem primitive_square_tail_integrals
    (g u q : ℝ → ℝ) -- [definition]
    (hu : Continuous u) -- [standing]
    (hgu : ∀ t, HasDerivAt g (u t) t) -- [standing]
    (hpos : ∀ t, 0 ≤ u t) -- [standing]
    (hanti : Antitone u) -- [standing]
    (hg : Tendsto g atTop (𝓝 0)) -- [standing]
    (huq : ∀ t, HasDerivAt u (-(q t)^2) t) -- [standing]
    (s : ℝ) -- [definition]
    : IntegrableOn (fun t => (q t)^2) (Ioi s) ∧
      (∫ t in Ioi s, (q t)^2) = u s ∧
      IntegrableOn (fun t => (t-s)*(q t)^2) (Ioi s) ∧
      (∫ t in Ioi s, (t-s)*(q t)^2) = -g s := by
  have hz := primitive_slope_tendsto_zero g u hu hgu hpos hanti hg
  have hzn : Tendsto (fun t => -u t) atTop (𝓝 0) := by
    simpa only [neg_zero] using hz.neg
  have hn (t : ℝ) : HasDerivAt (fun x => -u x) ((q t)^2) t := by
    simpa only [Pi.neg_apply, neg_neg] using (huq t).fun_neg
  have hnp : ∀ t ∈ Ioi s, 0 ≤ (q t)^2 := fun t _ => sq_nonneg (q t)
  have hi := integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hn t) hnp hzn
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => hn t) hnp hzn
  have hw := primitive_shifted_weighted_slope_tendsto_zero g u hu hgu hpos hanti hg s
  have hzw : Tendsto (fun t => g t-(t-s)*u t) atTop (𝓝 0) := by
    simpa only [sub_zero] using hg.sub hw
  have hwd := hasDerivAt_weighted_square_primitive g u q hgu huq s
  have hwp : ∀ t ∈ Ioi s, 0 ≤ (t-s)*(q t)^2 :=
    fun t ht => mul_nonneg (sub_pos.mpr ht).le (sq_nonneg (q t))
  have hwi := integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hwd t) hwp hzw
  have hwe := integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => hwd t) hwp hzw
  refine ⟨hi, ?_, hwi, ?_⟩
  · simpa only [zero_sub, neg_neg] using he
  · simpa only [sub_self, zero_mul, sub_zero, zero_sub] using hwe

/-- The nonconstant exponential primitive jointly satisfies every generic binder,
with g(0)=-1 and u(0)=q(0)=1 and both tail integrals equal to one. -/
theorem concave_primitive_tail_all_binder_joint_probe :
    ∃ g u q : ℝ → ℝ,
      Continuous u ∧ (∀ t, HasDerivAt g (u t) t) ∧
      (∀ t, 0 ≤ u t) ∧ Antitone u ∧ Tendsto g atTop (𝓝 0) ∧
      (∀ t, HasDerivAt u (-(q t)^2) t) ∧
      g 0 = -1 ∧ u 0 = 1 ∧ q 0 = 1 ∧
      Tendsto (fun t => t*u t) atTop (𝓝 0) ∧ Tendsto u atTop (𝓝 0) ∧
      IntegrableOn (fun t => (q t)^2) (Ioi 0) ∧
      (∫ t in Ioi 0, (q t)^2) = 1 ∧
      IntegrableOn (fun t => t*(q t)^2) (Ioi 0) ∧
      (∫ t in Ioi 0, t*(q t)^2) = 1 := by
  let g : ℝ → ℝ := fun t => -Real.exp (-t)
  let u : ℝ → ℝ := fun t => Real.exp (-t)
  let q : ℝ → ℝ := fun t => Real.exp (-t/2)
  have hdu (t : ℝ) : HasDerivAt u (-u t) t := by
    convert! (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg using 1 <;> simp [u]
  have hdg (t : ℝ) : HasDerivAt g (u t) t := by
    simpa only [g, u, Pi.neg_apply, neg_neg] using (hdu t).fun_neg
  have hq (t : ℝ) : (q t)^2 = u t := by
    dsimp [q,u]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hduq (t : ℝ) : HasDerivAt u (-(q t)^2) t := by
    rw [hq]
    exact hdu t
  have hcu : Continuous u := Real.continuous_exp.comp continuous_neg
  have hp (t : ℝ) : 0 ≤ u t := (Real.exp_pos _).le
  have ha : Antitone u := by
    intro a b hab
    exact Real.exp_le_exp.mpr (neg_le_neg hab)
  have hg : Tendsto g atTop (𝓝 0) := by
    simpa only [g, neg_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.neg
  have ht := primitive_square_tail_integrals g u q hcu hdg hp ha hg hduq 0
  refine ⟨g,u,q,hcu,hdg,hp,ha,hg,hduq, ?_, ?_, ?_,
    primitive_weighted_slope_tendsto_zero g u hcu hdg hp ha hg,
    primitive_slope_tendsto_zero g u hcu hdg hp ha hg, ht.1, ?_, ?_, ?_⟩
  · norm_num [g]
  · norm_num [u]
  · norm_num [q]
  · simpa only [u, neg_zero, Real.exp_zero] using ht.2.1
  · simpa only [sub_zero] using ht.2.2.1
  · simpa only [sub_zero, g, neg_zero, Real.exp_zero, neg_neg] using ht.2.2.2

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.primitive_half_interval_bound
#print axioms RMTFoundations.TracyWidom.primitive_weighted_slope_tendsto_zero
#print axioms RMTFoundations.TracyWidom.primitive_slope_tendsto_zero
#print axioms RMTFoundations.TracyWidom.primitive_shifted_weighted_slope_tendsto_zero
#print axioms RMTFoundations.TracyWidom.hasDerivAt_weighted_square_primitive
#print axioms RMTFoundations.TracyWidom.primitive_square_tail_integrals
#print axioms RMTFoundations.TracyWidom.concave_primitive_tail_all_binder_joint_probe
