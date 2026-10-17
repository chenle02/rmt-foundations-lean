import Mathlib
import RMTFoundations.Airy.Damping
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryDerivativeAsymptotics
open MeasureTheory Set Filter Asymptotics
open RMTFoundations.Airy
open scoped Topology Asymptotics

/-- The extra hyperbolic-cosine weight has the same Gaussian leading term. -/
theorem weighted_schlaefli_isEquivalent :
    (fun z : ℝ => ∫ t in Ioi 0, Real.cosh t *
      (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))) ~[atTop]
      fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  apply schlaefli_master_isEquivalent (fun _ t => Real.cosh t) (C := 1) zero_le_one
  · intro z
    exact Real.continuous_cosh
  · intro z t ht
    exact (Real.cosh_pos t).le
  · intro z hz t ht
    simpa only [one_mul, abs_of_nonneg ht] using cosh_le_exp_abs t
  · intro t ht
    have h := (Real.continuous_cosh.tendsto 0).comp (tendsto_div_sqrt_atTop t)
    simpa [Function.comp_def] using h

/-- Derivative asymptotics are obtained from the genuine differentiated Schläfli integral. -/
theorem deriv_schlaefli_isEquivalent :
    deriv schlaefliK13 ~[atTop]
      fun z => -(Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z)) := by
  have he : deriv schlaefliK13 =ᶠ[atTop]
      fun z => -(∫ t in Ioi 0, Real.cosh t *
        (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))) := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    rw [(hasDerivAt_schlaefliK13 hz).2.deriv, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    ring
  exact he.isEquivalent.trans weighted_schlaefli_isEquivalent.neg


/-- The derivative is linked to the same genuine Bessel construction as Ai. -/
theorem airy_deriv_bessel (x : ℝ /- [definition] -/)
    (hx : 0 < x /- [standing] -/) :
    deriv airyAiReal x = airyBesselY1 x / Real.pi := by
  have he : (fun y => airyBesselY y / Real.pi) =ᶠ[𝓝 x] airyAiReal := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact (airyAiReal_eq_airyBesselY_div_pi hy).symm
  exact ((hasDerivAt_airyBesselY hx).div_const Real.pi).congr_of_eventuallyEq he.symm |>.deriv


noncomputable def saddle (x : ℝ /- [definition] -/) : ℝ := (2/3) * x ^ (3/2 : ℝ)
noncomputable def besselLead (z : ℝ /- [definition] -/) : ℝ :=
  Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z)

/-- The normalized derivative separates a vanishing correction and the true derivative ratio. -/
theorem airy_deriv_ratio (x : ℝ /- [definition] -/)
    (hx : 0 < x /- [standing] -/) :
    deriv airyAiReal x / (-(Real.sqrt 3)⁻¹ * x * besselLead (saddle x) / Real.pi) =
      (-(1/2) * x ^ (-3/2 : ℝ)) * (schlaefliK13 (saddle x) / besselLead (saddle x)) +
      deriv schlaefliK13 (saddle x) / (-besselLead (saddle x)) := by
  rw [airy_deriv_bessel x hx, airyBesselY1]
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hl : Real.sqrt (Real.pi / (2 * saddle x)) ≠ 0 := by unfold saddle; positivity
  have hp : x ^ (-3/2 : ℝ) * x = x ^ (-1/2 : ℝ) := by
    rw [← Real.rpow_add_one hx.ne']
    norm_num
  rw [← hp]
  unfold besselLead saddle
  field_simp [hx.ne', hs, hl, Real.exp_ne_zero, Real.pi_ne_zero]
  ring

/-- The Airy derivative has its exact classical leading term. -/
theorem airy_deriv_isEquivalent :
    deriv airyAiReal ~[atTop] fun x =>
      -(1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) *
        Real.exp (-(2/3) * x ^ (3/2 : ℝ)) := by
  have hg : Tendsto saddle atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2/3)).2
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/2))
  have hn : ∀ᶠ z : ℝ in atTop, besselLead z ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    unfold besselLead
    positivity
  have hK : Tendsto (fun z => schlaefliK13 z / besselLead z) atTop (𝓝 1) := by
    exact (isEquivalent_iff_tendsto_one hn).mp schlaefliK13_isEquivalent
  have hKp : Tendsto (fun z => deriv schlaefliK13 z / (-besselLead z)) atTop (𝓝 1) := by
    exact (isEquivalent_iff_tendsto_one (hn.mono fun z hz => neg_ne_zero.mpr hz)).mp
      deriv_schlaefli_isEquivalent
  have h0 : Tendsto (fun x : ℝ => -(1/2) * x ^ (-3/2 : ℝ)) atTop (𝓝 0) := by
    simpa only [show -(3/2 : ℝ) = (-3/2 : ℝ) from by ring, mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/2)).const_mul (-(1/2) : ℝ)
  have he : deriv airyAiReal ~[atTop] fun x =>
      -(Real.sqrt 3)⁻¹ * x * besselLead (saddle x) / Real.pi := by
    apply isEquivalent_of_tendsto_one
    have ht := (h0.mul (hK.comp hg)).add (hKp.comp hg)
    simp only [zero_mul, zero_add] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (airy_deriv_ratio x hx).symm
  refine he.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hp : x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have hc : (Real.sqrt 3)⁻¹ * x * Real.sqrt (Real.pi / (2 * saddle x)) / Real.pi =
      (1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) := by
    calc
      _ = ((1 / Real.pi) * Real.sqrt (x / 3) *
          Real.sqrt (Real.pi / (2 * saddle x))) * x ^ (1/2 : ℝ) := by
        rw [sqrt_div_three hx.le]
        rw [show (1 / Real.pi) * ((Real.sqrt 3)⁻¹ * x ^ (1/2 : ℝ)) *
            Real.sqrt (Real.pi / (2 * saddle x)) * x ^ (1/2 : ℝ) =
            (Real.sqrt 3)⁻¹ * (x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ)) *
              Real.sqrt (Real.pi / (2 * saddle x)) / Real.pi from by ring, hp]
      _ = ((1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ)) * x ^ (1/2 : ℝ) := by
        rw [show saddle x = (2/3) * x ^ (3/2 : ℝ) from rfl, airyAiReal_prefactor hx]
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hx]
        norm_num
  unfold besselLead
  rw [show -(Real.sqrt 3)⁻¹ * x * (Real.sqrt (Real.pi / (2 * saddle x)) *
      Real.exp (-saddle x)) / Real.pi =
      -((Real.sqrt 3)⁻¹ * x * Real.sqrt (Real.pi / (2 * saddle x)) / Real.pi) *
        Real.exp (-saddle x) from by ring, hc]
  unfold saddle
  rw [neg_mul]
  ring

/-- The positive-argument hypotheses occur on a genuine positive Airy solution. -/
theorem airy_positive_joint_probe :
    ∃ x : ℝ, 0 < x ∧ 0 < airyAiReal x ∧
      HasDerivAt airyAiReal (deriv airyAiReal x) x ∧
      HasDerivAt (deriv airyAiReal) (x * airyAiReal x) x := by
  exact ⟨1, zero_lt_one, airyAiReal_pos_of_nonneg zero_le_one,
    hasDerivAt_airyAiReal' 1, hasDerivAt_deriv_airyAiReal' 1⟩

end RMTFoundations.TracyWidom.AiryDerivativeAsymptotics

#print axioms RMTFoundations.TracyWidom.AiryDerivativeAsymptotics.weighted_schlaefli_isEquivalent
#print axioms RMTFoundations.TracyWidom.AiryDerivativeAsymptotics.deriv_schlaefli_isEquivalent
#print axioms RMTFoundations.TracyWidom.AiryDerivativeAsymptotics.airy_deriv_bessel
#print axioms RMTFoundations.TracyWidom.AiryDerivativeAsymptotics.saddle
#print axioms RMTFoundations.TracyWidom.AiryDerivativeAsymptotics.besselLead
#print axioms RMTFoundations.TracyWidom.AiryDerivativeAsymptotics.airy_deriv_ratio
#print axioms RMTFoundations.TracyWidom.AiryDerivativeAsymptotics.airy_deriv_isEquivalent
#print axioms RMTFoundations.TracyWidom.AiryDerivativeAsymptotics.airy_positive_joint_probe
