import RMTFoundations.Measure.FreeConvolution
import RMTFoundations.Measure.EdgeDensity

/-!
# Shared Marchenko–Pastur probability law

The law is constructed from a tilted semicircle.
The aspect ratio is y; the raw covariance law has mean one.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RMTFoundations.MarchenkoPastur
open MeasureTheory ProbabilityTheory Filter Topology Set
open RMTFoundations.FreeConvolution
open RMTFoundations.Stieltjes (stieltjes)

/-- Scalar covariance parameters at aspect ratio y and mean one. -/
def shift (y : ℝ 
     /- [definition] -/ ) : ℝ := 1+y

def radius (y : ℝ 
     /- [definition] -/ ) : ℝ := scEdge y

theorem radius_pos (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (_hlt : y < 1 
     /- [standing] -/ ) : 0 < radius y := scEdge_pos (by linarith)

theorem radius_sq (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (_hlt : y < 1 
     /- [standing] -/ ) : radius y ^ 2 = 4*y := by
  rw [radius, scEdge_sq (by linarith : 0 < y)]

theorem shift_gap (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : 0 < shift y-radius y := by
  have hr := radius_pos y hy hlt
  have hsq := radius_sq y hy hlt
  have hs : 0 < shift y := by unfold shift; linarith
  have hdiff : radius y ^ 2 < shift y ^ 2 := by
    unfold shift
    nlinarith [sq_pos_of_pos (by linarith : 0 < 1-y)]
  nlinarith

/-- The resolvent of the semicircle at a strictly negative real point has
no pole on its actual support. This is an integral, not a density assumption. -/
theorem inverse_shift_integrable (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : Integrable (fun t : ℝ => 1/(t+shift y)) (semicircle (y)) := by
  haveI := semicircle_prob (by linarith : 0 < y)
  apply Integrable.of_bound (measurable_const.div (measurable_id.add measurable_const)).aestronglyMeasurable ((shift y-radius y)⁻¹)
  filter_upwards [ae_mem (semicircle_supported (by linarith : 0 < y))] with t ht
  have hgap := shift_gap y hy hlt
  have hden : shift y-radius y ≤ t+shift y := by have hh : -radius y ≤ t := ht.1; linarith
  change ‖(1/(t+shift y) : ℝ)‖ ≤ (shift y-radius y)⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hgap.trans_le hden)), one_div]
  exact inv_anti₀ hgap hden

/-- Real boundary evaluation of the semicircle transform via dominated
convergence on its genuine compact support. -/
theorem inverse_shift_boundary (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : Tendsto (fun n : ℕ => stieltjes (semicircle (y))
      ((-shift y : ℝ) + (1/((n : ℝ)+1) : ℝ)*Complex.I)) atTop
      (𝓝 ((∫ t : ℝ, 1/(t+shift y) ∂(semicircle (y)) : ℝ) : ℂ)) := by
  haveI := semicircle_prob (by linarith : 0 < y)
  have hgap := shift_gap y hy hlt
  have hlim : Tendsto (fun n : ℕ => (1/((n : ℝ)+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hz : ∀ n : ℕ, 0 < ((-shift y : ℝ) +
      (1/((n : ℝ)+1) : ℝ)*Complex.I : ℂ).im := fun n => by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      using (show (0 : ℝ) < 1/((n : ℝ)+1) by positivity)
  have hreal : ((∫ t : ℝ, 1/(t+shift y) ∂(semicircle (y)) : ℝ) : ℂ) =
      ∫ t : ℝ, ((t+shift y : ℝ) : ℂ)⁻¹ ∂(semicircle (y)) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    simp
  rw [hreal]
  apply tendsto_integral_of_dominated_convergence (fun _ => (shift y-radius y)⁻¹)
  · intro n
    exact (continuous_inv_sub (hz n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [ae_mem (semicircle_supported (by linarith : 0 < y))] with t ht
    have hden : shift y-radius y ≤ t+shift y := by
      have hh : -radius y ≤ t := ht.1
      linarith
    have he := re_le_norm_sub
      ((-shift y : ℝ) + (1/((n : ℝ)+1) : ℝ)*Complex.I : ℂ) t
    have hp : 0 < t+shift y := hgap.trans_le hden
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, sub_neg_eq_add] at he
    rw [abs_of_pos hp] at he
    rw [norm_inv]
    exact inv_anti₀ hgap (hden.trans he)
  · filter_upwards [ae_mem (semicircle_supported (by linarith : 0 < y))] with t ht
    have hp : 0 < t+shift y := by
      have hh : -radius y ≤ t := ht.1
      linarith
    have hn : (t : ℂ)-((-shift y : ℝ) : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr hp.ne' : ((t+shift y : ℝ) : ℂ) ≠ 0)
    have hzc : Tendsto (fun n : ℕ => ((-shift y : ℝ) : ℂ)+
        (1/((n : ℝ)+1) : ℝ)*Complex.I) atTop (𝓝 ((-shift y : ℝ) : ℂ)) := by
      simpa using (tendsto_const_nhds.add
        (((Complex.continuous_ofReal.tendsto 0).comp hlim).mul_const Complex.I))
    have hh := (tendsto_const_nhds.sub hzc).inv₀ hn
    simpa [stieltjes] using hh

/-- The branch on the negative real side selects the smaller quadratic root. -/
theorem left_transform_bound (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (n : ℕ 
     /- [definition] -/ ) : (stieltjes (semicircle (y))
      ((-shift y : ℝ) + (1/((n : ℝ)+1) : ℝ)*Complex.I)).re ≤ shift y/(2*y) := by
  let z : ℂ := (-shift y : ℝ) + (1/((n : ℝ)+1) : ℝ)*Complex.I
  have hz : 0 < z.im := by
    simpa only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      using (show (0 : ℝ) < 1/((n : ℝ)+1) by positivity)
  let u : ℂ := csqrt (rad (y) z)
  have hu := csqrt_sq (rad (y) z)
  have zre : z.re = -shift y := by
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have zim : z.im = 1/((n : ℝ)+1) := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  have him : 2*u.re*u.im = 2*shift y/((n : ℝ)+1) := by
    have h := congrArg Complex.im hu
    change (u^2).im = (rad (y) z).im at h
    have hrad : (rad (y) z).im = -(2*z.re*z.im) := by
      unfold rad
      norm_num [pow_two, Complex.mul_im]
      ring
    have husq : (u^2).im = 2*u.re*u.im := by simp [pow_two, Complex.mul_im]; ring
    rw [husq, hrad, zre, zim] at h
    rw [h]
    ring
  have ha : 0 ≤ u.re := re_sq_nonneg _
  have hb : 0 < shift y := by unfold shift; linarith
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hp : 0 < 2*shift y/((n : ℝ)+1) := by positivity
  have hui : 0 ≤ u.im := by nlinarith
  rw [stieltjes_semicircle (by linarith : 0 < y) hz]
  have he : (gsc (y) z).re = (shift y-u.im)/(2*y) := by
    unfold gsc
    rw [show (2 : ℂ)*(y : ℝ) = ((2*y : ℝ) : ℂ) by push_cast; ring,
      Complex.div_ofReal_re]
    change ((-z+Complex.I*u).re)/(2*y) = (shift y-u.im)/(2*y)
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zre, neg_neg]
    rfl
  rw [he, div_le_iff₀ (by linarith : 0 < 2*y)]
  rw [div_mul_cancel₀ _ (by linarith : 2*y ≠ 0)]
  linarith

/-- Exact normalization of the tilted semicircle: this is the scalar MP
probability/density normalization, proved without an analytic hypothesis. -/
theorem inverse_shift_integral (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : ∫ t : ℝ, 1/(t+shift y) ∂(semicircle (y)) = 1 := by
  let q : ℝ := ∫ t : ℝ, 1/(t+shift y) ∂(semicircle (y))
  let z : ℕ → ℂ := fun n => (-shift y : ℝ)+(1/((n : ℝ)+1) : ℝ)*Complex.I
  let S : ℕ → ℂ := fun n => stieltjes (semicircle (y)) (z n)
  have ht : Tendsto S atTop (𝓝 (q : ℂ)) := inverse_shift_boundary y hy hlt
  have hz : Tendsto z atTop (𝓝 ((-shift y : ℝ) : ℂ)) := by
    have h := ((Complex.continuous_ofReal.tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat).mul_const Complex.I
    simpa [z] using tendsto_const_nhds.add h
  have hb : q ≤ shift y/(2*y) := le_of_tendsto (Complex.continuous_re.tendsto (q : ℂ) |>.comp ht)
    (Eventually.of_forall (left_transform_bound y hy hlt))
  have hp : Tendsto (fun n => (y : ℝ)*(S n)^2+(z n)*(S n)+1) atTop
      (𝓝 ((y : ℝ)*(q : ℂ)^2+((-shift y : ℝ) : ℂ)*(q : ℂ)+1)) :=
    ((tendsto_const_nhds.mul (ht.pow 2)).add (hz.mul ht)).add tendsto_const_nhds
  have hzero : Tendsto (fun n => (y : ℝ)*(S n)^2+(z n)*(S n)+1) atTop (𝓝 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)) using 1
    funext n
    have hzn : 0 < (z n).im := by
      simpa only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
        using (show (0 : ℝ) < 1/((n : ℝ)+1) by positivity)
    dsimp only [S]
    rw [stieltjes_semicircle (by linarith : 0 < y) hzn]
    exact gsc_quad (by linarith : 0 < y) (z n)
  have he := congrArg Complex.re (tendsto_nhds_unique hp hzero)
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at he
  have hquad : y*q^2-shift y*q+1 = 0 := by
    nlinarith [he]
  have hfac : (q-1)*(y*q-1) = 0 := by unfold shift at hquad; nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · have hq : y*q = 1 := by linarith
    have hh := (le_div_iff₀ (by positivity : 0 < 2*y)).mp hb
    unfold shift at hh
    nlinarith

/-- Weighting the existing semicircle produces the raw scalar MP law. -/
def tilt (y : ℝ 
     /- [definition] -/ ) : Measure ℝ := (semicircle (y)).withDensity
      (fun t => ENNReal.ofReal (1/(t+shift y)))

/-- Centered MP law at aspect ratio y, translated by its mean one. -/
def law (y : ℝ 
     /- [definition] -/ ) : Measure ℝ := (tilt y).map (fun t => t+y)

def density (y x : ℝ 
     /- [definition] -/ ) : ℝ := 1/(x+1)*scDens (y) (x-y)

theorem tilt_prob (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : IsProbabilityMeasure (tilt y) := by
  haveI := semicircle_prob (by linarith : 0 < y)
  have hi := inverse_shift_integrable y hy hlt
  have hn : ∀ᵐ t ∂(semicircle (y)), 0 ≤ 1/(t+shift y) := by
    filter_upwards [ae_mem (semicircle_supported (by linarith : 0 < y))] with t ht
    have hgap := shift_gap y hy hlt
    have hh : -radius y ≤ t := ht.1
    apply div_nonneg (by norm_num)
    linarith
  constructor
  rw [tilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn]
  rw [inverse_shift_integral y hy hlt, ENNReal.ofReal_one]

theorem law_prob (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : IsProbabilityMeasure (law y) := by
  haveI := tilt_prob y hy hlt
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

/-- Exact translation of a Lebesgue density; no density hypothesis is added. -/
theorem translate_density (f : ℝ → ENNReal 
     /- [definition] -/ ) (h : ℝ 
     /- [standing] -/ ) : (volume.withDensity f).map (fun t : ℝ => t+h) =
      volume.withDensity (fun x : ℝ => f (x-h)) := by
  ext s hs
  have hy : Measurable (fun t : ℝ => t+h) := by fun_prop
  rw [Measure.map_apply hy hs, withDensity_apply _ (hs.preimage hy),
    withDensity_apply _ hs, ← lintegral_indicator (hs.preimage hy),
    ← lintegral_indicator hs]
  have he : (∫⁻ t : ℝ, ((fun t : ℝ => t+h) ⁻¹' s).indicator f t) =
      ∫⁻ t : ℝ, s.indicator (fun x : ℝ => f (x-h)) (t+h) := by
    apply lintegral_congr
    intro t
    by_cases ht : t+h ∈ s <;> simp [Set.indicator, ht]
  rw [he, lintegral_add_right_eq_self]

theorem law_density (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (_hlt : y < 1 
     /- [standing] -/ ) : law y = volume.withDensity (fun x => ENNReal.ofReal (density y x)) := by
  have hf : Measurable (fun t => ENNReal.ofReal (scDens (y) t)) := by
    exact ENNReal.measurable_ofReal.comp (continuous_scDens (y)).measurable
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (1/(t+shift y))) := by
    exact ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.add measurable_const))
  rw [law, tilt, semicircle_eq_withDensity (by linarith : 0 < y),
    ← withDensity_mul volume hf hw, translate_density]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (scDens_nonneg (by linarith : 0 < y) _)]
  congr 1
  unfold density shift
  rw [show x-y+(1+y) = x+1 by ring]
  ring

theorem density_nonneg (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (x : ℝ 
     /- [definition] -/ ) : 0 ≤ density y x := by
  unfold density
  by_cases hx : |x-y| < radius y
  · have hgap := shift_gap y hy hlt
    have hl := (abs_lt.mp hx).1
    apply mul_nonneg
    · apply div_nonneg (by norm_num)
      unfold shift at hgap
      linarith
    · exact scDens_nonneg (by linarith : 0 < y) _
  · rw [scDens_eq_zero (by linarith : 0 < y) (le_of_not_gt hx), mul_zero]

theorem law_centered (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : ∫ x : ℝ, x ∂(law y) = 0 := by
  haveI := semicircle_prob (by linarith : 0 < y)
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (1/(t+shift y))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.add measurable_const))
  rw [law, integral_map (by fun_prop) (by fun_prop), tilt,
    integral_withDensity_eq_integral_toReal_smul hw (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun t : ℝ => (ENNReal.ofReal (1/(t+shift y))).toReal • (t+y)) =ᵐ[semicircle (y)]
      (fun t => 1-1/(t+shift y)) := by
    filter_upwards [ae_mem (semicircle_supported (by linarith : 0 < y))] with t ht
    have hgap := shift_gap y hy hlt
    have hh : -radius y ≤ t := ht.1
    have hp : 0 < t+shift y := by linarith
    rw [ENNReal.toReal_ofReal (div_nonneg (by norm_num) hp.le), smul_eq_mul]
    field_simp [hp.ne']
    unfold shift
    ring
  rw [integral_congr_ae he,
    integral_sub (integrable_const _) (inverse_shift_integrable y hy hlt),
    integral_const, probReal_univ, one_smul, inverse_shift_integral y hy hlt]
  norm_num

theorem tilt_supported (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (_hlt : y < 1 
     /- [standing] -/ ) : SupportedIn (tilt y) (radius y) :=
  withDensity_absolutelyContinuous _ _ (semicircle_supported (by linarith : 0 < y))

theorem law_supported (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : SupportedIn (law y) (radius y+y) := by
  unfold SupportedIn law
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  apply measure_mono_null _ (tilt_supported y hy hlt)
  intro t ht
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc] at ht ⊢
  intro hh
  apply ht
  constructor <;> linarith [hh.1, hh.2]

theorem semicircle_ac_tilt (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : semicircle (y) ≪ tilt y := by
  apply withDensity_absolutelyContinuous'
  · exact (ENNReal.measurable_ofReal.comp
      (measurable_const.div (measurable_id.add measurable_const))).aemeasurable
  · filter_upwards [ae_mem (semicircle_supported (by linarith : 0 < y))] with t ht
    have hh : -radius y ≤ t := ht.1
    have hgap := shift_gap y hy hlt
    have hp : 0 < t+shift y := by linarith
    exact (ENNReal.ofReal_pos.mpr (div_pos (by norm_num : (0 : ℝ) < 1) hp)).ne'

/-- The endpoint is tied to the genuine MP measure, with positive mass below it. -/
theorem law_rightEndpoint (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : rightEndpoint (law y) = radius y+y := by
  haveI := law_prob y hy hlt
  haveI := semicircle_prob (by linarith : 0 < y)
  refine le_antisymm (rightEndpoint_le (law_supported y hy hlt)) ?_
  by_contra h
  have hedge : rightEndpoint (law y) < radius y+y := lt_of_not_ge h
  have hnull := measure_Ioi_rightEndpoint (law_supported y hy hlt)
  have he : (fun t : ℝ => t+y) ⁻¹' Ioi (rightEndpoint (law y)) =
      Ioi (rightEndpoint (law y)-y) := by ext t; simp only [mem_preimage, mem_Ioi]; constructor <;> intro h <;> linarith
  change ((tilt y).map (fun t : ℝ => t+y)) (Ioi (rightEndpoint (law y))) = 0 at hnull
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi, he] at hnull
  have hsnull := semicircle_ac_tilt y hy hlt hnull
  have hspos := measure_Ioi_pos_of_lt (semicircle_supported (by linarith : 0 < y))
    (x := rightEndpoint (law y)-y) (by
      rw [rightEndpoint_semicircle (by linarith : 0 < y)]
      change rightEndpoint (law y)-y < radius y
      linarith)
  rw [hsnull] at hspos
  exact (lt_irrefl (0 : ENNReal)) hspos

/-- The Stieltjes transform of the centered MP probability measure. -/
theorem law_transform (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (z : ℂ 
     /- [definition] -/ ) (hz : 0 < z.im 
     /- [standing] -/ ) : stieltjes (law y) z =
      (gsc y (z-y)-1)/(z+1) := by
  haveI := semicircle_prob (by linarith : 0 < y)
  have hzshift : 0 < (z-y).im := by simpa using hz
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (1/(t+shift y))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.add measurable_const))
  unfold stieltjes
  rw [law, integral_map (by fun_prop) (by
    exact (continuous_inv_sub hz).aestronglyMeasurable), tilt,
    integral_withDensity_eq_integral_toReal_smul hw (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hzm : z+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at hi
    exact hz.ne' hi
  have he : (fun t : ℝ => (ENNReal.ofReal (1/(t+shift y))).toReal •
      ((t+y : ℝ)-z)⁻¹) =ᵐ[semicircle (y)]
      (fun t => (((t : ℂ)-(z-y))⁻¹-
        ((1/(t+shift y) : ℝ) : ℂ))/(z+1)) := by
    filter_upwards [ae_mem (semicircle_supported (by linarith : 0 < y))] with t ht
    have hh : -radius y ≤ t := ht.1
    have hgap := shift_gap y hy hlt
    have hp : 0 < t+shift y := by linarith
    rw [ENNReal.toReal_ofReal (div_nonneg (by norm_num) hp.le), Complex.real_smul]
    have hn := Complex.ofReal_ne_zero.mpr hp.ne'
    have htz := sub_ne hzshift t
    have htz2 : (t+y : ℝ)-z ≠ 0 := by
      convert htz using 1
      push_cast
      ring
    have hcast : ((t+shift y : ℝ) : ℂ) = (t : ℂ)+1+(y : ℂ) := by
      unfold shift; push_cast; ring
    have harg : ((t+y : ℝ) : ℂ)-z = (t : ℂ)-(z-y) := by push_cast; ring
    push_cast only [Complex.ofReal_div, Complex.ofReal_one]
    rw [hcast] at hn
    rw [harg, hcast]
    generalize ha : (t : ℂ)-(z-y) = a
    generalize hb : (t : ℂ)+1+(y : ℂ) = b
    generalize hc : z+1 = c
    have hanz : a ≠ 0 := by rw [← ha]; exact htz
    have hbnz : b ≠ 0 := by rw [← hb]; exact hn
    have hcnz : c ≠ 0 := by rw [← hc]; exact hzm
    have hab : b-a = c := by rw [← ha, ← hb, ← hc]; ring
    field_simp [hanz, hbnz, hcnz]
    linear_combination -hab
  have hi1 : Integrable (fun t : ℝ => ((t : ℂ)-(z-y))⁻¹) (semicircle (y)) :=
    integrable_inv_sub _ hzshift
  have hi2 : Integrable (fun t : ℝ => ((1/(t+shift y) : ℝ) : ℂ)) (semicircle (y)) :=
    (inverse_shift_integrable y hy hlt).ofReal
  rw [integral_congr_ae he, integral_div, integral_sub hi1 hi2,
    integral_complex_ofReal,
    inverse_shift_integral y hy hlt]
  have hs := stieltjes_semicircle (by linarith : 0 < y) hzshift
  unfold stieltjes at hs
  rw [hs]
  simp only [Complex.ofReal_one]

/-- The MP transform satisfies its centered covariance quadratic. -/
theorem law_transform_quadratic (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (z : ℂ 
     /- [definition] -/ ) (hz : 0 < z.im 
     /- [standing] -/ ) : (y : ℂ)*(z+1)*(stieltjes (law y) z)^2+
      (z+y)*stieltjes (law y) z+1 = 0 := by
  have hq := gsc_quad (by linarith : 0 < y) (z-y)
  have hzm : z+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at hi
    exact hz.ne' hi
  rw [law_transform y hy hlt z hz]
  generalize gsc (y) (z-y) = G at hq ⊢
  field_simp [hzm]
  linear_combination hq

theorem law_transform_im_pos (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (z : ℂ 
     /- [definition] -/ ) (hz : 0 < z.im 
     /- [standing] -/ ) : 0 < (stieltjes (law y) z).im := by
  haveI := law_prob y hy hlt
  exact im_stieltjes_pos _ (law_supported y hy hlt) hz



/-- Lower endpoint in covariance units. -/
def lower (y : ℝ 
     /- [definition] -/ ) : ℝ := (1-Real.sqrt y)^2

/-- Upper endpoint in covariance units. -/
def upper (y : ℝ 
     /- [definition] -/ ) : ℝ := (1+Real.sqrt y)^2

/-- Uncentered Marchenko–Pastur law, with mean one. -/
def mpMeasure (y : ℝ 
     /- [definition] -/ ) : Measure ℝ := (law y).map (fun x : ℝ => x+1)

/-- Explicit covariance density, zero outside the MP interval. -/
def mpDensity (y x : ℝ 
     /- [definition] -/ ) : ℝ := if x ∈ Icc (lower y) (upper y) then
      Real.sqrt ((upper y-x)*(x-lower y))/(2*Real.pi*y*x) else 0

theorem endpoints (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (_hlt : y < 1 
     /- [standing] -/ ) : lower y = shift y-radius y ∧ upper y = shift y+radius y := by
  have hs := Real.sq_sqrt hy.le
  unfold lower upper shift radius scEdge
  constructor <;> nlinarith

theorem lower_pos (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : 0 < lower y := by
  rw [(endpoints y hy hlt).1]
  exact shift_gap y hy hlt

theorem mpDensity_identification (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (x : ℝ 
     /- [definition] -/ ) : mpDensity y x = density y (x-1) := by
  have he := endpoints y hy hlt
  have hr := radius_pos y hy hlt
  have hs := radius_sq y hy hlt
  have hp : (upper y-x)*(x-lower y) = 4*y-(x-shift y)^2 := by
    rw [he.1,he.2]
    nlinarith [hs]
  unfold mpDensity density scDens
  rw [show x-1-y = x-shift y by unfold shift; ring,
    show x-1+1 = x by ring]
  by_cases hx : x ∈ Icc (lower y) (upper y)
  · rw [if_pos hx,hp]
    ring
  · rw [if_neg hx]
    have hh : 4*y-(x-shift y)^2 ≤ 0 := by
      simp only [mem_Icc,not_and_or,not_le] at hx
      rw [he.1,he.2] at hx
      rcases hx with hx | hx
      · nlinarith [sq_nonneg (x-shift y+radius y)]
      · nlinarith [sq_nonneg (x-shift y-radius y)]
    rw [Real.sqrt_eq_zero'.mpr hh]
    simp

theorem mpMeasure_density (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : mpMeasure y = volume.withDensity (fun x => ENNReal.ofReal (mpDensity y x)) := by
  rw [mpMeasure,law_density y hy hlt,translate_density]
  congr 1
  funext x
  rw [mpDensity_identification y hy hlt x]

theorem mpMeasure_prob (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : IsProbabilityMeasure (mpMeasure y) := by
  haveI := law_prob y hy hlt
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

theorem mpMeasure_mass (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : mpMeasure y univ = 1 := by
  haveI := mpMeasure_prob y hy hlt
  exact measure_univ

theorem law_ac (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : law y ≪ volume := by
  rw [law_density y hy hlt]
  exact withDensity_absolutelyContinuous _ _

theorem mpMeasure_ac (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : mpMeasure y ≪ volume := by
  rw [mpMeasure_density y hy hlt]
  exact withDensity_absolutelyContinuous _ _

theorem mpMeasure_supported (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : mpMeasure y (Icc (lower y) (upper y))ᶜ = 0 := by
  rw [mpMeasure,law,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  apply measure_mono_null _ (tilt_supported y hy hlt)
  intro t ht
  rw [(endpoints y hy hlt).1,(endpoints y hy hlt).2] at ht
  simp only [mem_preimage,Function.comp_def,mem_compl_iff,mem_Icc] at ht ⊢
  intro hh
  unfold shift at ht
  exact ht ⟨by linarith [hh.1],by linarith [hh.2]⟩

theorem law_supported_exact (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : law y (Icc (lower y-1) (upper y-1))ᶜ = 0 := by
  rw [law,Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  apply measure_mono_null _ (tilt_supported y hy hlt)
  intro t ht
  rw [(endpoints y hy hlt).1,(endpoints y hy hlt).2] at ht
  simp only [mem_preimage,mem_compl_iff,mem_Icc] at ht ⊢
  intro hh
  unfold shift at ht
  exact ht ⟨by linarith [hh.1],by linarith [hh.2]⟩

theorem mpMeasure_mean (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : ∫ x : ℝ, x ∂(mpMeasure y) = 1 := by
  haveI := law_prob y hy hlt
  rw [mpMeasure,integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_id (law_supported y hy hlt)) (integrable_const 1),
    law_centered y hy hlt]
  simp

theorem centered_mpMeasure (y : ℝ 
     /- [definition] -/ ) : (mpMeasure y).map (fun x : ℝ => x-1) = law y := by
  rw [mpMeasure,Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ => x-1) ∘ (fun x : ℝ => x+1) = id := by
    funext x
    simp
  rw [he]
  exact Measure.map_id

theorem law_endpoint (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : rightEndpoint (law y) = upper y-1 := by
  rw [law_rightEndpoint y hy hlt,(endpoints y hy hlt).2]
  unfold shift
  ring

theorem mpMeasure_transform (y : ℝ 
     /- [definition] -/ ) (_hy : 0 < y 
     /- [standing] -/ ) (_hlt : y < 1 
     /- [standing] -/ ) (z : ℂ 
     /- [definition] -/ ) (hz : 0 < z.im 
     /- [standing] -/ ) : stieltjes (mpMeasure y) z = stieltjes (law y) (z-1) := by
  unfold stieltjes
  rw [mpMeasure,integral_map (by fun_prop)
    (continuous_inv_sub hz).aestronglyMeasurable]
  congr 1
  funext x
  congr 1
  push_cast
  ring

theorem mpMeasure_transform_quadratic (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (z : ℂ 
     /- [definition] -/ ) (hz : 0 < z.im 
     /- [standing] -/ ) : (y : ℂ)*z*(stieltjes (mpMeasure y) z)^2+
      (z+y-1)*stieltjes (mpMeasure y) z+1 = 0 := by
  rw [mpMeasure_transform y hy hlt z hz]
  have h := law_transform_quadratic y hy hlt (z-1) (by simpa using hz)
  convert h using 1
  ring

/-- Positive explicit lower square-root coefficient. -/
def edgeLower (y : ℝ 
     /- [definition] -/ ) : ℝ := Real.sqrt (radius y)/(2*Real.pi*y*(shift y+radius y))

/-- Positive explicit upper square-root coefficient. -/
def edgeUpper (y : ℝ 
     /- [definition] -/ ) : ℝ := scCoef y/(shift y)

theorem edge_constants_pos (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : 0 < edgeLower y ∧ 0 < edgeUpper y ∧ 0 < radius y/2 := by
  have hr := radius_pos y hy hlt
  have hs : 0 < shift y := by unfold shift; positivity
  have he : 0 < scEdge y := hr
  unfold edgeLower edgeUpper scCoef
  constructor
  · positivity
  · constructor <;> positivity

/-- Square-root density bounds at the right endpoint on a positive fixed window. -/
theorem law_edge_bounds (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : RMTFoundations.EdgeDensity.EdgeDensityBounds (density y)
      (rightEndpoint (law y)) (1/2) (edgeLower y) (edgeUpper y) (radius y/2) := by
  intro x hx
  rw [law_rightEndpoint y hy hlt] at hx ⊢
  have hr := radius_pos y hy hlt
  have hs : 0 < shift y := by unfold shift; positivity
  have hxi : x-y ∈ Ioo 0 (scEdge y) := by
    change x-y ∈ Ioo 0 (radius y)
    constructor <;> linarith [hx.1,hx.2]
  have hsc := sc_density_bounds hy hxi
  have hxpos : 0 < x+1 := by unfold shift at hs; linarith [hx.1]
  have hxl : shift y ≤ x+1 := by unfold shift; linarith [hx.1]
  have hxu : x+1 ≤ shift y+radius y := by unfold shift; linarith [hx.2]
  have ht : 0 ≤ radius y+y-x := by linarith [hx.2]
  have he : scEdge y-(x-y) = radius y+y-x := by unfold radius; ring
  rw [he] at hsc
  rw [density,one_div_mul_eq_div,← Real.sqrt_eq_rpow]
  constructor
  · calc edgeLower y*Real.sqrt (radius y+y-x) =
        (Real.sqrt (radius y)/(2*Real.pi*y)*Real.sqrt (radius y+y-x))/(shift y+radius y) := by
          unfold edgeLower
          field_simp [Real.pi_ne_zero,hy.ne',(add_pos hs hr).ne']
      _ ≤ (Real.sqrt (radius y)/(2*Real.pi*y)*Real.sqrt (radius y+y-x))/(x+1) :=
          div_le_div_of_nonneg_left (by positivity) hxpos hxu
      _ ≤ scDens y (x-y)/(x+1) := div_le_div_of_nonneg_right hsc.1 hxpos.le
  · calc scDens y (x-y)/(x+1) ≤ (scCoef y*Real.sqrt (radius y+y-x))/(x+1) :=
          div_le_div_of_nonneg_right hsc.2 hxpos.le
      _ ≤ (scCoef y*Real.sqrt (radius y+y-x))/(shift y) :=
          div_le_div_of_nonneg_left (by unfold scCoef; positivity) hs hxl
      _ = edgeUpper y*Real.sqrt (radius y+y-x) := by unfold edgeUpper; ring

/-- Nondegenerate mass strictly to the right of the mean of the centered law. -/
theorem law_right_mass_pos (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : 0 < law y (Ioi y) := by
  haveI := law_prob y hy hlt
  apply measure_Ioi_pos_of_lt (law_supported y hy hlt)
  rw [law_rightEndpoint y hy hlt]
  linarith [radius_pos y hy hlt]

/-- Probability, support, centering and edge bounds hold together at aspect ratio 1/2. -/
theorem mp_joint_probe :
    (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 ∧
    IsProbabilityMeasure (mpMeasure (1/2)) ∧
    mpMeasure (1/2) univ = 1 ∧
    mpMeasure (1/2) = volume.withDensity (fun x => ENNReal.ofReal (mpDensity (1/2) x)) ∧
    mpMeasure (1/2) ≪ volume ∧ law (1/2) ≪ volume ∧
    mpMeasure (1/2) (Icc (lower (1/2)) (upper (1/2)))ᶜ = 0 ∧
    (∫ x : ℝ, x ∂mpMeasure (1/2)) = 1 ∧
    (mpMeasure (1/2)).map (fun x : ℝ => x-1) = law (1/2) ∧
    (∫ x : ℝ, x ∂law (1/2)) = 0 ∧
    0 < law (1/2) (Ioi (1/2)) ∧
    0 < edgeLower (1/2) ∧ 0 < edgeUpper (1/2) ∧ 0 < radius (1/2)/2 ∧
    RMTFoundations.EdgeDensity.EdgeDensityBounds (density (1/2))
      (rightEndpoint (law (1/2))) (1/2) (edgeLower (1/2)) (edgeUpper (1/2)) (radius (1/2)/2) ∧
    (∀ z : ℂ, 0 < z.im →
      (1/2 : ℂ)*z*(stieltjes (mpMeasure (1/2)) z)^2+
        (z+(1/2 : ℝ)-1)*stieltjes (mpMeasure (1/2)) z+1 = 0) := by
  have hp := edge_constants_pos (1/2) (by norm_num) (by norm_num)
  exact ⟨by norm_num,by norm_num,mpMeasure_prob _ (by norm_num) (by norm_num),
    mpMeasure_mass _ (by norm_num) (by norm_num),mpMeasure_density _ (by norm_num) (by norm_num),
    mpMeasure_ac _ (by norm_num) (by norm_num),law_ac _ (by norm_num) (by norm_num),
    mpMeasure_supported _ (by norm_num) (by norm_num),mpMeasure_mean _ (by norm_num) (by norm_num),
    centered_mpMeasure _,law_centered _ (by norm_num) (by norm_num),
    law_right_mass_pos _ (by norm_num) (by norm_num),hp.1,hp.2.1,hp.2.2,
    law_edge_bounds _ (by norm_num) (by norm_num),
    fun z hz => by simpa using mpMeasure_transform_quadratic (1/2) (by norm_num) (by norm_num) z hz⟩


theorem mpDensity_nonneg (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (x : ℝ 
     /- [definition] -/ ) : 0 ≤ mpDensity y x := by
  rw [mpDensity_identification y hy hlt]
  exact density_nonneg y hy hlt (x-1)

theorem law_density_centered (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : law y = volume.withDensity (fun x => ENNReal.ofReal (mpDensity y (x+1))) := by
  rw [law_density y hy hlt]
  congr 1
  funext x
  rw [mpDensity_identification y hy hlt]
  simp

theorem mpMeasure_supported_bound (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : SupportedIn (mpMeasure y) (upper y) := by
  apply measure_mono_null _ (mpMeasure_supported y hy hlt)
  intro x hx
  simp only [mem_compl_iff,mem_Icc] at hx ⊢
  intro hh
  have hl := lower_pos y hy hlt
  have hu : 0 < upper y := by
    rw [(endpoints y hy hlt).2]
    have := radius_pos y hy hlt
    unfold shift
    linarith
  exact hx ⟨by linarith [hh.1],hh.2⟩

theorem mpMeasure_integrable (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : Integrable (fun x : ℝ => x) (mpMeasure y) := by
  haveI := mpMeasure_prob y hy hlt
  exact integrable_id (mpMeasure_supported_bound y hy hlt)

theorem mpMeasure_endpoint (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : rightEndpoint (mpMeasure y) = upper y := by
  haveI := mpMeasure_prob y hy hlt
  haveI := law_prob y hy hlt
  have hs := mpMeasure_supported_bound y hy hlt
  refine le_antisymm (rightEndpoint_le hs) ?_
  by_contra h
  have he : rightEndpoint (mpMeasure y) < upper y := lt_of_not_ge h
  have hn := measure_Ioi_rightEndpoint hs
  change (law y).map (fun x : ℝ => x+1) (Ioi (rightEndpoint (mpMeasure y))) = 0 at hn
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at hn
  have hset : (fun x : ℝ => x+1) ⁻¹' Ioi (rightEndpoint (mpMeasure y)) =
      Ioi (rightEndpoint (mpMeasure y)-1) := by
    ext x
    simp only [mem_preimage,mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [hset] at hn
  have hp := measure_Ioi_pos_of_lt (law_supported y hy hlt)
    (x := rightEndpoint (mpMeasure y)-1) (by rw [law_endpoint y hy hlt]; linarith)
  rw [hn] at hp
  exact (lt_irrefl (0 : ENNReal)) hp

theorem compact_joint_probe :
    IsCompact (Icc (lower (1/2)) (upper (1/2))) ∧
    IsCompact (Icc (lower (1/2)-1) (upper (1/2)-1)) ∧
    law (1/2) (Icc (lower (1/2)-1) (upper (1/2)-1))ᶜ = 0 ∧
    Integrable (fun x : ℝ => x) (mpMeasure (1/2)) ∧
    rightEndpoint (mpMeasure (1/2)) = upper (1/2) ∧
    rightEndpoint (law (1/2)) = upper (1/2)-1 ∧
    law (1/2) = volume.withDensity (fun x => ENNReal.ofReal (mpDensity (1/2) (x+1))) :=
  ⟨isCompact_Icc,isCompact_Icc,law_supported_exact _ (by norm_num) (by norm_num),
    mpMeasure_integrable _ (by norm_num) (by norm_num),
    mpMeasure_endpoint _ (by norm_num) (by norm_num),law_endpoint _ (by norm_num) (by norm_num),
    law_density_centered _ (by norm_num) (by norm_num)⟩


/-- An upper square-root coefficient strictly greater than the lower coefficient. -/
def clauseUpper (y : ℝ 
     /- [definition] -/ ) : ℝ := edgeUpper y+edgeLower y+1

theorem clause_constants (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : 0 < edgeLower y ∧ edgeLower y < clauseUpper y ∧ 0 < radius y/2 := by
  have hp := edge_constants_pos y hy hlt
  unfold clauseUpper
  exact ⟨hp.1,by linarith [hp.2.1],hp.2.2⟩

/-- Existence of an edge exponent in (-1, 1), witnessed by exponent 1/2. -/
theorem law_clause_i (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : ∃ t ∈ Ioo (-1 : ℝ) 1,
      RMTFoundations.EdgeDensity.EdgeDensityBounds (density y)
        (rightEndpoint (law y)) t (edgeLower y) (clauseUpper y) (radius y/2) := by
  refine ⟨1/2,by norm_num,?_⟩
  intro x hx
  have h := law_edge_bounds y hy hlt x hx
  have hp := (edge_constants_pos y hy hlt).1
  have hc : edgeUpper y ≤ clauseUpper y := by unfold clauseUpper; linarith
  exact ⟨h.1,h.2.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith [hx.2]) _))⟩

/-- At aspect ratio 1/2, the centered probability law has compact support and
square-root edge bounds with strictly ordered positive coefficients. -/
theorem s_side_joint_probe :
    IsProbabilityMeasure (law (1/2)) ∧
    law (1/2) = volume.withDensity (fun x => ENNReal.ofReal (density (1/2) x)) ∧
    (∫ x : ℝ, x ∂law (1/2)) = 0 ∧
    (∃ R : ℝ, law (1/2) (Icc (-R) R)ᶜ = 0) ∧
    law (1/2) (Ioi (rightEndpoint (law (1/2)))) = 0 ∧
    (0 < edgeLower (1/2) ∧ edgeLower (1/2) < clauseUpper (1/2)) ∧
    0 < radius (1/2)/2 ∧
    (∃ t ∈ Ioo (-1 : ℝ) 1,
      RMTFoundations.EdgeDensity.EdgeDensityBounds (density (1/2))
        (rightEndpoint (law (1/2))) t (edgeLower (1/2)) (clauseUpper (1/2)) (radius (1/2)/2)) := by
  haveI := law_prob (1/2) (by norm_num) (by norm_num)
  have hs := law_supported (1/2) (by norm_num) (by norm_num)
  have hc := clause_constants (1/2) (by norm_num) (by norm_num)
  exact ⟨inferInstance,law_density _ (by norm_num) (by norm_num),
    law_centered _ (by norm_num) (by norm_num),⟨radius (1/2)+1/2,hs⟩,
    measure_Ioi_rightEndpoint hs,⟨hc.1,hc.2.1⟩,hc.2.2,
    law_clause_i _ (by norm_num) (by norm_num)⟩

/-- All-binder transform probe with an explicitly positive imaginary part. -/
theorem transform_joint_probe : (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 ∧
    0 < Complex.I.im ∧
    (1/2 : ℂ)*(Complex.I+1)*(stieltjes (law (1/2)) Complex.I)^2+
      (Complex.I+(1/2 : ℝ))*stieltjes (law (1/2)) Complex.I+1 = 0 ∧
    (1/2 : ℂ)*Complex.I*(stieltjes (mpMeasure (1/2)) Complex.I)^2+
      (Complex.I+(1/2 : ℝ)-1)*stieltjes (mpMeasure (1/2)) Complex.I+1 = 0 :=
  ⟨by norm_num,by norm_num,by norm_num,
    by simpa using law_transform_quadratic (1/2) (by norm_num) (by norm_num) Complex.I (by norm_num),
    by simpa using mpMeasure_transform_quadratic (1/2) (by norm_num) (by norm_num) Complex.I (by norm_num)⟩


theorem law_compact (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : ∃ R : ℝ, law y (Icc (-R) R)ᶜ = 0 :=
  ⟨radius y+y,law_supported y hy hlt⟩

theorem law_top (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : law y (Ioi (rightEndpoint (law y))) = 0 := by
  haveI := law_prob y hy hlt
  exact measure_Ioi_rightEndpoint (law_supported y hy hlt)

/-- At aspect ratio 1/2, the law is a translated tilted semicircle. -/
theorem fixed_half_construction : law (1/2) =
    ((semicircle (1/2)).withDensity
      (fun t : ℝ => ENNReal.ofReal (1/(t+3/2)))).map (fun t : ℝ => t+1/2) := by
  unfold law tilt shift
  norm_num

/-- Explicit centered density at aspect ratio 1/2. -/
theorem fixed_half_density (x : ℝ 
     /- [definition] -/ ) : density (1/2) x = 1/(x+1)*scDens (1/2) (x-1/2) := rfl

end RMTFoundations.MarchenkoPastur

#print axioms RMTFoundations.MarchenkoPastur.shift
#print axioms RMTFoundations.MarchenkoPastur.radius
#print axioms RMTFoundations.MarchenkoPastur.radius_pos
#print axioms RMTFoundations.MarchenkoPastur.radius_sq
#print axioms RMTFoundations.MarchenkoPastur.shift_gap
#print axioms RMTFoundations.MarchenkoPastur.inverse_shift_integrable
#print axioms RMTFoundations.MarchenkoPastur.inverse_shift_boundary
#print axioms RMTFoundations.MarchenkoPastur.left_transform_bound
#print axioms RMTFoundations.MarchenkoPastur.inverse_shift_integral
#print axioms RMTFoundations.MarchenkoPastur.tilt
#print axioms RMTFoundations.MarchenkoPastur.law
#print axioms RMTFoundations.MarchenkoPastur.density
#print axioms RMTFoundations.MarchenkoPastur.tilt_prob
#print axioms RMTFoundations.MarchenkoPastur.law_prob
#print axioms RMTFoundations.MarchenkoPastur.translate_density
#print axioms RMTFoundations.MarchenkoPastur.law_density
#print axioms RMTFoundations.MarchenkoPastur.density_nonneg
#print axioms RMTFoundations.MarchenkoPastur.law_centered
#print axioms RMTFoundations.MarchenkoPastur.tilt_supported
#print axioms RMTFoundations.MarchenkoPastur.law_supported
#print axioms RMTFoundations.MarchenkoPastur.semicircle_ac_tilt
#print axioms RMTFoundations.MarchenkoPastur.law_rightEndpoint
#print axioms RMTFoundations.MarchenkoPastur.law_transform
#print axioms RMTFoundations.MarchenkoPastur.law_transform_quadratic
#print axioms RMTFoundations.MarchenkoPastur.law_transform_im_pos
#print axioms RMTFoundations.MarchenkoPastur.lower
#print axioms RMTFoundations.MarchenkoPastur.upper
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure
#print axioms RMTFoundations.MarchenkoPastur.mpDensity
#print axioms RMTFoundations.MarchenkoPastur.endpoints
#print axioms RMTFoundations.MarchenkoPastur.lower_pos
#print axioms RMTFoundations.MarchenkoPastur.mpDensity_identification
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_density
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_prob
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_mass
#print axioms RMTFoundations.MarchenkoPastur.law_ac
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_ac
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_supported
#print axioms RMTFoundations.MarchenkoPastur.law_supported_exact
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_mean
#print axioms RMTFoundations.MarchenkoPastur.centered_mpMeasure
#print axioms RMTFoundations.MarchenkoPastur.law_endpoint
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_transform
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_transform_quadratic
#print axioms RMTFoundations.MarchenkoPastur.edgeLower
#print axioms RMTFoundations.MarchenkoPastur.edgeUpper
#print axioms RMTFoundations.MarchenkoPastur.edge_constants_pos
#print axioms RMTFoundations.MarchenkoPastur.law_edge_bounds
#print axioms RMTFoundations.MarchenkoPastur.law_right_mass_pos
#print axioms RMTFoundations.MarchenkoPastur.mp_joint_probe
#print axioms RMTFoundations.MarchenkoPastur.mpDensity_nonneg
#print axioms RMTFoundations.MarchenkoPastur.law_density_centered
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_supported_bound
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_integrable
#print axioms RMTFoundations.MarchenkoPastur.mpMeasure_endpoint
#print axioms RMTFoundations.MarchenkoPastur.compact_joint_probe
#print axioms RMTFoundations.MarchenkoPastur.clauseUpper
#print axioms RMTFoundations.MarchenkoPastur.clause_constants
#print axioms RMTFoundations.MarchenkoPastur.law_clause_i
#print axioms RMTFoundations.MarchenkoPastur.s_side_joint_probe
#print axioms RMTFoundations.MarchenkoPastur.transform_joint_probe
#print axioms RMTFoundations.MarchenkoPastur.law_compact
#print axioms RMTFoundations.MarchenkoPastur.law_top
#print axioms RMTFoundations.MarchenkoPastur.fixed_half_construction
#print axioms RMTFoundations.MarchenkoPastur.fixed_half_density
