import RMTFoundations.TracyWidom.HermiteCircleDominated
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteCircleCauchy
open Complex MeasureTheory
open RMTFoundations.TracyWidom.HermiteCauchy RMTFoundations.TracyWidom.HermiteCubicSaddle
open RMTFoundations.TracyWidom.HermiteSaddleSource RMTFoundations.TracyWidom.HermiteCircleEnvelope
open RMTFoundations.TracyWidom.HermiteCircleCoordinate RMTFoundations.TracyWidom.HermiteCircleDominated
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.GUEHermite

lemma circle_integral_centered (f : ℂ → ℂ /- [definition] -/)
    (r : ℝ /- [definition] -/) :
    circleIntegral f 0 r = ∫ θ : ℝ in -Real.pi..Real.pi,
      circleMap 0 r θ*Complex.I*f (circleMap 0 r θ) := by
  rw [circleIntegral]
  simp only [deriv_circleMap,smul_eq_mul]
  have hp : Function.Periodic (fun θ : ℝ => circleMap 0 r θ*Complex.I*f (circleMap 0 r θ))
      (2*Real.pi) := by
    intro θ
    dsimp only
    rw [periodic_circleMap 0 r θ]
  convert hp.intervalIntegral_add_eq 0 (-Real.pi) using 1 <;> ring

noncomputable def angularIntegrand (N : ℕ /- [definition] -/)
    (x θ : ℝ /- [definition] -/) : ℂ :=
  let z := circleMap 0 (circleRadius N 1) θ
  z*Complex.I*((1/z^(N+1))*generating (edgePoint N x) z)

/-- The actual circle Jacobian cancels exactly the finite saddle denominator. -/
theorem angular_scaled_identity (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x t : ℝ /- [definition] -/)
    (hsmall : saddleScale N ≤ 1/2 /- [standing] -/) :
    angularIntegrand N x (saddleScale N*t) =
      (Complex.I*Complex.exp (3*(N : ℂ)/2+(Real.sqrt N : ℂ)*(edgeScale N : ℂ)*x)/
        (Real.sqrt N : ℂ)^N)*Complex.exp (saddlePhase N x (circleCoordinate N 1 t)) := by
  have hw : 1+(saddleScale N : ℂ)*circleCoordinate N 1 t ≠ 0 := by
    rw [circle_denominator N hN]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by simp; linarith)) (Complex.exp_ne_zero _)
  have hr : (Real.sqrt N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hN)))
  have hz : circleMap 0 (circleRadius N 1) (saddleScale N*t) =
      saddleCoordinate N (circleCoordinate N 1 t) := by
    simpa only [circleMap,zero_add] using (circle_coordinate_source N hN 1 t).symm
  unfold angularIntegrand
  dsimp only
  rw [hz,hermite_integrand_saddle_nonzero N hN x (circleCoordinate N 1 t) hw,
    saddleCoordinate,pow_succ]
  field_simp

/-- Literal finite rescaled-circle representation before the scalar external normalizer. -/
theorem circle_integral_scaled (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hsmall : saddleScale N ≤ 1/2 /- [standing] -/) :
    circleIntegral (fun z : ℂ => (1/z^(N+1))*generating (edgePoint N x) z) 0 (circleRadius N 1) =
      (saddleScale N : ℂ)*
      (Complex.I*Complex.exp (3*(N : ℂ)/2+(Real.sqrt N : ℂ)*(edgeScale N : ℂ)*x)/
        (Real.sqrt N : ℂ)^N)*
      ∫ t : ℝ in -Real.pi/saddleScale N..Real.pi/saddleScale N,
        Complex.exp (saddlePhase N x (circleCoordinate N 1 t)) := by
  rw [circle_integral_centered]
  change (∫ θ : ℝ in -Real.pi..Real.pi, angularIntegrand N x θ) = _
  have hd : saddleScale N ≠ 0 := ne_of_gt (saddle_scale_pos N hN)
  have ha : saddleScale N*(-Real.pi/saddleScale N) = -Real.pi := by field_simp
  have hb : saddleScale N*(Real.pi/saddleScale N) = Real.pi := by field_simp
  have hc := intervalIntegral.smul_integral_comp_mul_left (angularIntegrand N x) (saddleScale N)
    (a := -Real.pi/saddleScale N) (b := Real.pi/saddleScale N)
  rw [ha,hb] at hc
  rw [← hc]
  simp_rw [angular_scaled_identity N hN x _ hsmall]
  rw [intervalIntegral.integral_const_mul,Complex.real_smul]
  ring

lemma cut_circle_integral_interval (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    (∫ t : ℝ, cutCircle N x t) =
      ∫ t : ℝ in -Real.pi/saddleScale N..Real.pi/saddleScale N,
        Complex.exp (saddlePhase N x (circleCoordinate N 1 t)) := by
  have hd := saddle_scale_pos N hN
  have he : {t : ℝ | |saddleScale N*t| ≤ Real.pi} =
      Set.Icc (-Real.pi/saddleScale N) (Real.pi/saddleScale N) := by
    ext t
    simp only [Set.mem_setOf_eq,Set.mem_Icc,abs_le]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨(div_le_iff₀ hd).mpr (by nlinarith),(le_div_iff₀ hd).mpr (by nlinarith)⟩
    · rintro ⟨h1,h2⟩
      have hh1 := (div_le_iff₀ hd).mp h1
      have hh2 := (le_div_iff₀ hd).mp h2
      constructor <;> nlinarith
  have hf : cutCircle N x = {t : ℝ | |saddleScale N*t| ≤ Real.pi}.indicator
      (fun t : ℝ => Complex.exp (saddlePhase N x (circleCoordinate N 1 t))) := by
    funext t
    simp only [cutCircle,Set.indicator_apply]
    rfl
  rw [hf,he,integral_indicator measurableSet_Icc,
    intervalIntegral.integral_of_le (show -Real.pi/saddleScale N ≤ Real.pi/saddleScale N from
      div_le_div_of_nonneg_right (by linarith [Real.pi_pos]) hd.le),
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

theorem circle_cauchy_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, 0 < saddleScale (n+1) ∧
      (∫ t : ℝ, cutCircle (n+1) 1 t) =
        ∫ t : ℝ in -Real.pi/saddleScale (n+1)..Real.pi/saddleScale (n+1),
          Complex.exp (saddlePhase (n+1) 1 (circleCoordinate (n+1) 1 t))) ∧
    (∀ᶠ n : ℕ in Filter.atTop, saddleScale (n+1) ≤ 1/2 ∧
      circleIntegral (fun z : ℂ => (1/z^(n+1+1))*generating (edgePoint (n+1) 1) z)
        0 (circleRadius (n+1) 1) =
        (saddleScale (n+1) : ℂ)*
        (Complex.I*Complex.exp (3*((n+1 : ℕ) : ℂ)/2+
          (Real.sqrt (n+1 : ℕ) : ℂ)*(edgeScale (n+1) : ℂ))/(Real.sqrt (n+1 : ℕ) : ℂ)^(n+1))*
        ∫ t : ℝ, cutCircle (n+1) 1 t) := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,fun n =>
    ⟨saddle_scale_pos _ (by omega),cut_circle_integral_interval _ (by omega) 1⟩,?_⟩
  have hs := saddle_scale_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs] with n hn
  refine ⟨hn.le,?_⟩
  rw [circle_integral_scaled _ (by omega) 1 hn.le,← cut_circle_integral_interval _ (by omega) 1]
  simp
end RMTFoundations.TracyWidom.HermiteCircleCauchy

#print axioms RMTFoundations.TracyWidom.HermiteCircleCauchy.circle_integral_centered
#print axioms RMTFoundations.TracyWidom.HermiteCircleCauchy.angularIntegrand
#print axioms RMTFoundations.TracyWidom.HermiteCircleCauchy.angular_scaled_identity
#print axioms RMTFoundations.TracyWidom.HermiteCircleCauchy.circle_integral_scaled
#print axioms RMTFoundations.TracyWidom.HermiteCircleCauchy.cut_circle_integral_interval
#print axioms RMTFoundations.TracyWidom.HermiteCircleCauchy.circle_cauchy_joint_probe
