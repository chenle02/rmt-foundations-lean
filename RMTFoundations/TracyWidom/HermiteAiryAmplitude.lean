import RMTFoundations.TracyWidom.HermiteCircleCauchy
import RMTFoundations.TracyWidom.HermiteEdgeNormalization
import RMTFoundations.TracyWidom.HermiteEdgeReduction
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteAiryAmplitude
open Complex Filter Topology MeasureTheory
open RMTFoundations.TracyWidom.HermiteCauchy RMTFoundations.TracyWidom.HermiteCubicSaddle
open RMTFoundations.TracyWidom.HermiteCircleEnvelope RMTFoundations.TracyWidom.HermiteCircleCoordinate
open RMTFoundations.TracyWidom.HermiteCircleDominated RMTFoundations.TracyWidom.HermiteCircleCauchy
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.HermiteEdgeReduction
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeNormalization
open RMTFoundations.Airy

lemma sqrt_power_exponential (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    (Real.sqrt N)^N = Real.exp ((N : ℝ)/2*Real.log N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have he := Real.exp_log (pow_pos hs N)
  rw [Real.log_pow,Real.log_sqrt hn.le] at he
  convert he.symm using 1 <;> ring

/-- Exact finite external factor at the same literal Cauchy radius and Hermite normalizer. -/
lemma circle_external_factor (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    edgeAmplitude N*gaussianWeight (edgePoint N x)*hermiteNormalizer N*(N.factorial : ℝ)*
      saddleScale N*Real.exp (3*(N : ℝ)/2+Real.sqrt N*edgeScale N*x)/(Real.sqrt N)^N =
        saddlePrefactor N x := by
  rw [sqrt_power_exponential N hN]
  unfold edgeAmplitude saddlePrefactor saddleScale gaussianWeight
  simp_rw [Real.exp_sub,Real.exp_add]
  ring

lemma cut_circle_integrable (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hsmall : saddleScale N ≤ 1/2 /- [standing] -/)
    (hx : |x| *saddleScale N ≤ 1 /- [standing] -/) : Integrable (cutCircle N x) := by
  have hg : Integrable (fun t : ℝ => Real.exp (|x|+4/3)*Real.exp (-1/Real.pi^2*t^2)) := by
    simpa only [neg_div] using (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1/Real.pi^2)).const_mul (Real.exp (|x|+4/3))
  apply hg.mono' (cut_circle_aestronglyMeasurable N x)
  apply ae_of_all
  intro t
  unfold cutCircle
  split_ifs with ht
  · exact circle_phase_gaussian N hN x t hsmall hx ht
  · simp only [norm_zero]
    positivity

/-- The actual normalized Hermite function is the finite rescaled-circle integral.
Every source and scalar normalizer is literal; there is no assumed PR formula. -/
theorem edge_mode_circle_integral (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hsmall : saddleScale N ≤ 1/2 /- [standing] -/)
    (hx : |x| *saddleScale N ≤ 1 /- [standing] -/) :
    edgeMode N x = saddlePrefactor N x*((1/(2*Real.pi))*∫ t : ℝ, (cutCircle N x t).re) := by
  have hr : 0 < circleRadius N 1 := by
    unfold circleRadius
    exact mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) (by linarith)
  have hc := hermite_mode_cauchy N (edgePoint N x) (circleRadius N 1) hr
  rw [circle_integral_scaled N hN x hsmall,← cut_circle_integral_interval N hN x] at hc
  have hs : (Real.sqrt N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hN)))
  have hp : (2*(Real.pi : ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have he : (edgeMode N x : ℂ) =
      ((saddlePrefactor N x/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ, cutCircle N x t := by
    change ((edgeAmplitude N*hermiteMode N (edgePoint N x) : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul,hc]
    rw [← circle_external_factor N hN x]
    push_cast
    field_simp <;> ring
  have hre := congrArg Complex.re he
  simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] at hre
  have hi : (∫ t : ℝ, cutCircle N x t).re = ∫ t : ℝ, (cutCircle N x t).re :=
    (integral_re (cut_circle_integrable N hN x hsmall hx)).symm
  rw [hi] at hre
  convert hre using 1 <;> ring

/-- Actual Plancherel--Rotach edge amplitude, at each real point, with no imported input. -/
theorem hermite_edge_tendsto (x : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => edgeMode (n+1) x) atTop (𝓝 (airyAiReal x)) := by
  have hf : Tendsto (fun n : ℕ => saddlePrefactor (n+1) x) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [saddle_prefactor_locally_uniform |x| (abs_nonneg x) ε hε] with n hn
    simpa only [Real.dist_eq] using hn x (le_refl |x|)
  have hh := hf.mul (cut_circle_integral_tendsto x)
  simp only [one_mul] at hh
  apply hh.congr'
  have hs := saddle_scale_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hx : Tendsto (fun n : ℕ => |x| *saddleScale (n+1)) atTop (𝓝 0) := by
    simpa using saddle_scale_tendsto.const_mul |x|
  filter_upwards [hs,hx.eventually (gt_mem_nhds zero_lt_one)] with n hn hnx
  exact (edge_mode_circle_integral (n+1) (by omega) x hn.le hnx.le).symm

/-- Complete actual-source joint example: growing N, its exact mode and Ai limit,
with every finite readiness condition derived at that same source. -/
theorem airy_amplitude_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, 0 < edgeAmplitude (n+1) ∧ 0 < edgeScale (n+1)) ∧
    (∀ᶠ n : ℕ in atTop, saddleScale (n+1) ≤ 1/2 ∧
      |(1 : ℝ)| *saddleScale (n+1) ≤ 1 ∧
      edgeMode (n+1) 1 = saddlePrefactor (n+1) 1*
        ((1/(2*Real.pi))*∫ t : ℝ, (cutCircle (n+1) 1 t).re)) ∧
    Tendsto (fun n : ℕ => edgeMode (n+1) 1) atTop (𝓝 (airyAiReal 1)) ∧
    0 < airyAiReal 1 := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,fun n =>
    ⟨by unfold edgeAmplitude; positivity,edgeScale_pos _ (by omega)⟩,?_,
    hermite_edge_tendsto 1,airyAiReal_pos_of_nonneg zero_le_one⟩
  have hs := saddle_scale_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs] with n hn
  have hx : |(1 : ℝ)| *saddleScale (n+1) ≤ 1 := by norm_num; linarith
  exact ⟨hn.le,hx,edge_mode_circle_integral _ (by omega) 1 hn.le hx⟩
end RMTFoundations.TracyWidom.HermiteAiryAmplitude

#print axioms RMTFoundations.TracyWidom.HermiteAiryAmplitude.sqrt_power_exponential
#print axioms RMTFoundations.TracyWidom.HermiteAiryAmplitude.circle_external_factor
#print axioms RMTFoundations.TracyWidom.HermiteAiryAmplitude.cut_circle_integrable
#print axioms RMTFoundations.TracyWidom.HermiteAiryAmplitude.edge_mode_circle_integral
#print axioms RMTFoundations.TracyWidom.HermiteAiryAmplitude.hermite_edge_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteAiryAmplitude.airy_amplitude_joint_probe
