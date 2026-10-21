import RMTFoundations.TracyWidom.HermiteCircleCoordinate
import RMTFoundations.TracyWidom.HermiteAiryContour
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteCircleDominated
open Complex Filter Topology MeasureTheory
open RMTFoundations.TracyWidom.HermiteCauchy RMTFoundations.TracyWidom.HermiteCubicSaddle
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.HermiteSaddleSource
open RMTFoundations.TracyWidom.HermiteCircleEnvelope RMTFoundations.TracyWidom.HermiteCircleCoordinate
open RMTFoundations.TracyWidom.HermiteAiryContour RMTFoundations.Airy

lemma circle_denominator (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β t : ℝ /- [definition] -/) :
    1+(saddleScale N : ℂ)*circleCoordinate N β t =
      ((1-β*saddleScale N : ℝ) : ℂ)*Complex.exp ((saddleScale N : ℂ)*Complex.I*t) := by
  have hd : (saddleScale N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (saddle_scale_pos N hN))
  unfold circleCoordinate
  rw [mul_div_cancel₀ _ hd]
  ring

lemma circle_denominator_norm (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β t : ℝ /- [definition] -/)
    (hsmall : β*saddleScale N ≤ 1/2 /- [standing] -/) :
    ‖1+(saddleScale N : ℂ)*circleCoordinate N β t‖ = 1-β*saddleScale N := by
  rw [circle_denominator N hN, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith),
    Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

/-- Exact generating-source factorization; its finite radius is never replaced by a limit. -/
lemma circle_generating_factorization (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β x t : ℝ /- [definition] -/)
    (hsmall : β*saddleScale N ≤ 1/2 /- [standing] -/) :
    circleGenerating (edgePoint N x) (circleRadius N β) (saddleScale N*t) =
      Complex.exp (3*(N : ℂ)/2+(Real.sqrt N : ℂ)*(edgeScale N : ℂ)*x)*
      Complex.exp (saddlePhase N x (circleCoordinate N β t))*
      (1+(saddleScale N : ℂ)*circleCoordinate N β t)^N := by
  have hw : 1+(saddleScale N : ℂ)*circleCoordinate N β t ≠ 0 := by
    rw [circle_denominator N hN]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) (Complex.exp_ne_zero _)
  have hp : Complex.exp ((N : ℂ)*Complex.log (1+(saddleScale N : ℂ)*circleCoordinate N β t)) =
      (1+(saddleScale N : ℂ)*circleCoordinate N β t)^N := by
    rw [Complex.exp_nat_mul,Complex.exp_log hw]
  rw [circleGenerating,← circle_coordinate_source N hN,generating,generating_saddle_exponent N hN,
    ← hp,← Complex.exp_add,← Complex.exp_add]
  congr 1
  unfold saddlePhase
  push_cast
  ring

lemma circle_phase_norm_ratio (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β x t : ℝ /- [definition] -/)
    (hsmall : β*saddleScale N ≤ 1/2 /- [standing] -/) :
    ‖Complex.exp (saddlePhase N x (circleCoordinate N β t))‖ /
      ‖Complex.exp (saddlePhase N x (-(β : ℂ)))‖ =
      ‖circleGenerating (edgePoint N x) (circleRadius N β) (saddleScale N*t)‖ /
        ‖circleGenerating (edgePoint N x) (circleRadius N β) 0‖ := by
  have h0 := circle_generating_factorization N hN β x 0 hsmall
  simp only [mul_zero,circle_coordinate_zero N hN] at h0
  rw [circle_generating_factorization N hN β x t hsmall,h0]
  simp only [norm_mul,norm_pow]
  rw [circle_denominator_norm N hN β t hsmall]
  have hn0 : ‖1+(saddleScale N : ℂ)*(-(β : ℂ))‖ = 1-β*saddleScale N := by
    simpa only [circle_coordinate_zero N hN] using circle_denominator_norm N hN β 0 hsmall
  rw [hn0]
  have hc : ‖Complex.exp (3*(N : ℂ)/2+(Real.sqrt N : ℂ)*(edgeScale N : ℂ)*x)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
  have hr : (1-β*saddleScale N)^N ≠ 0 := pow_ne_zero _ (by linarith)
  field_simp

lemma circle_center_bound (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hsmall : saddleScale N ≤ 1/2 /- [standing] -/) :
    ‖Complex.exp (saddlePhase N x (-1))‖ ≤ Real.exp (|x|+4/3) := by
  have he := saddle_phase_compact_error N hN 1 zero_le_one (by simpa using hsmall) x (-1)
    (by norm_num)
  have hr := Complex.re_le_norm (saddlePhase N x (-1)-((x : ℂ)*(-1)-(-1 : ℂ)^3/3))
  have hreal : (saddlePhase N x (-1)-((x : ℂ)*(-1)-(-1 : ℂ)^3/3)).re =
      (saddlePhase N x (-1)).re+x-1/3 := by
    have hc : (x : ℂ)*(-1)-(-1 : ℂ)^3/3 = ((-x+1/3 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hc,Complex.sub_re,Complex.ofReal_re]
    ring
  rw [hreal] at hr
  simp only [one_pow,mul_one] at he
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  nlinarith [neg_le_abs x]

/-- Uniform Gaussian domination of the actual moving Cauchy source on its full finite domain. -/
theorem circle_phase_gaussian (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x t : ℝ /- [definition] -/)
    (hsmall : saddleScale N ≤ 1/2 /- [standing] -/)
    (hx : |x| *saddleScale N ≤ 1 /- [standing] -/)
    (ht : |saddleScale N*t| ≤ Real.pi /- [standing] -/) :
    ‖Complex.exp (saddlePhase N x (circleCoordinate N 1 t))‖ ≤
      Real.exp (|x|+4/3)*Real.exp (-1/Real.pi^2*t^2) := by
  have hg := circle_edge_generating_gaussian N hN 1 x t zero_lt_one (by simpa using hsmall) hx ht
  rw [← circle_phase_norm_ratio N hN 1 x t (by simpa using hsmall)] at hg
  simp only [Complex.ofReal_one,neg_neg,mul_one] at hg
  have hc : 0 < ‖Complex.exp (saddlePhase N x (-1))‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hh := (div_le_iff₀ hc).mp hg
  have he := circle_center_bound N hN x hsmall
  norm_num at hh
  calc
    _ ≤ Real.exp (-1/Real.pi^2*t^2)*‖Complex.exp (saddlePhase N x (-1))‖ := hh
    _ ≤ Real.exp (-1/Real.pi^2*t^2)*Real.exp (|x|+4/3) :=
      mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- Extend the finite rescaled-circle integrand by zero outside its actual angle domain. -/
noncomputable def cutCircle (N : ℕ /- [definition] -/)
    (x t : ℝ /- [definition] -/) : ℂ :=
  if |saddleScale N*t| ≤ Real.pi then
    Complex.exp (saddlePhase N x (circleCoordinate N 1 t)) else 0

lemma cut_circle_tendsto (x t : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => cutCircle (n+1) x t) atTop (𝓝 (verticalIntegrand 1 x t)) := by
  apply (circle_exp_tendsto 1 x t).congr'
  filter_upwards [circle_domain_exhausts t] with n hn
  simp only [cutCircle,if_pos hn.le]

lemma cut_circle_aestronglyMeasurable (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : AEStronglyMeasurable (cutCircle N x) := by
  have hm : Measurable (fun t : ℝ => Complex.exp (saddlePhase N x (circleCoordinate N 1 t))) := by
    unfold circleCoordinate saddlePhase
    fun_prop
  have hs : MeasurableSet {t : ℝ | |saddleScale N*t| ≤ Real.pi} := by
    exact measurableSet_le (by fun_prop) measurable_const
  exact (hm.piecewise hs measurable_const).aestronglyMeasurable

lemma cut_circle_eventual_bound (x : ℝ /- [definition] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, ‖cutCircle (n+1) x t‖ ≤
      Real.exp (|x|+4/3)*Real.exp (-1/Real.pi^2*t^2) := by
  have hs := saddle_scale_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hx : Tendsto (fun n : ℕ => |x| *saddleScale (n+1)) atTop (𝓝 0) := by
    simpa using saddle_scale_tendsto.const_mul |x|
  filter_upwards [hs,hx.eventually (gt_mem_nhds zero_lt_one)] with n hn hnx t
  unfold cutCircle
  split_ifs with ht
  · exact circle_phase_gaussian (n+1) (by omega) x t hn.le hnx.le ht
  · simp only [norm_zero]
    positivity

/-- The integral limit uses the literal finite circle, a proved bound and the genuine Ai. -/
theorem cut_circle_integral_tendsto (x : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => (1/(2*Real.pi))*∫ t : ℝ, (cutCircle (n+1) x t).re)
      atTop (𝓝 (airyAiReal x)) := by
  have hg : Integrable (fun t : ℝ =>
      Real.exp (|x|+4/3)*Real.exp (-1/Real.pi^2*t^2)) := by
    simpa only [neg_div] using (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1/Real.pi^2)).const_mul (Real.exp (|x|+4/3))
  have hh := tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => Real.exp (|x|+4/3)*Real.exp (-1/Real.pi^2*t^2))
    (Filter.Eventually.of_forall (fun n : ℕ => (cut_circle_aestronglyMeasurable (n+1) x).re))
    (by
      filter_upwards [cut_circle_eventual_bound x] with n hn
      exact ae_of_all _ (fun t => le_trans (by simpa using Complex.abs_re_le_norm (cutCircle (n+1) x t)) (hn t)))
    hg (ae_of_all _ (fun t => (Complex.continuous_re.tendsto _).comp (cut_circle_tendsto x t)))
  have hmul := hh.const_mul (1/(2*Real.pi))
  rw [← airy_vertical_integral 1 x zero_lt_one] at hmul
  exact hmul

/-- All finite domination premises and the actual limit are instantiated together. -/
theorem circle_dominated_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ᶠ n : ℕ in atTop, 0 < saddleScale (n+1) ∧ saddleScale (n+1) ≤ 1/2 ∧
      ∀ t : ℝ, ‖cutCircle (n+1) 1 t‖ ≤ Real.exp (1+4/3)*Real.exp (-1/Real.pi^2*t^2)) ∧
    Tendsto (fun n : ℕ => (1/(2*Real.pi))*∫ t : ℝ, (cutCircle (n+1) 1 t).re)
      atTop (𝓝 (airyAiReal 1)) ∧ 0 < airyAiReal 1 := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,?_,cut_circle_integral_tendsto 1,
    airyAiReal_pos_of_nonneg zero_le_one⟩
  have hs := saddle_scale_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs,cut_circle_eventual_bound 1] with n hn hb
  exact ⟨saddle_scale_pos _ (by omega),hn.le,by simpa using hb⟩
end RMTFoundations.TracyWidom.HermiteCircleDominated

#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.circle_denominator
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.circle_denominator_norm
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.circle_generating_factorization
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.circle_phase_norm_ratio
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.circle_center_bound
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.circle_phase_gaussian
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.cutCircle
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.cut_circle_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.cut_circle_aestronglyMeasurable
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.cut_circle_eventual_bound
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.cut_circle_integral_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteCircleDominated.circle_dominated_joint_probe
