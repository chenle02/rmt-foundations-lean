import RMTFoundations.TracyWidom.HermiteCauchy
import RMTFoundations.TracyWidom.HermiteSaddleSource
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteCircleEnvelope
open Complex Filter Topology
open RMTFoundations.TracyWidom.HermiteCauchy RMTFoundations.TracyWidom.HermiteCubicSaddle
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.HermiteSaddleSource

noncomputable def circleExponent (y r θ : ℝ /- [definition] -/) : ℝ :=
  y*r*Real.cos θ-r^2/2*Real.cos (2*θ)

lemma circle_decay_identity (y r θ : ℝ /- [definition] -/) :
    circleExponent y r θ-circleExponent y r 0 =
      -r^2*(1-Real.cos θ)^2-r*(y-2*r)*(1-Real.cos θ) := by
  simp only [circleExponent,Real.cos_zero,Real.cos_two_mul]
  ring

/-- Source-dependent, finite Gaussian angular estimate on the entire circle.
The coefficient premise is a scalar radius/gap inequality, not an assumed tail bound. -/
theorem circle_gaussian_exponent (y r d c t : ℝ /- [definition] -/)
    (hc : 0 ≤ c /- [standing] -/)
    (hgap : 0 ≤ r*(y-2*r) /- [standing] -/)
    (hcoef : c ≤ r*(y-2*r)*d^2 /- [standing] -/)
    (hangle : |d*t| ≤ Real.pi /- [standing] -/) :
    circleExponent y r (d*t)-circleExponent y r 0 ≤ -2*c/Real.pi^2*t^2 := by
  have hcos := Real.cos_le_one_sub_mul_cos_sq hangle
  have hq : 2/Real.pi^2*(d*t)^2 ≤ 1-Real.cos (d*t) := by linarith
  have hm := mul_le_mul_of_nonneg_left hq hgap
  have hp : 0 ≤ 2/Real.pi^2*t^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right hcoef hp
  have heq : r*(y-2*r)*(2/Real.pi^2*(d*t)^2) =
      r*(y-2*r)*d^2*(2/Real.pi^2*t^2) := by ring
  rw [heq] at hm
  have hh2 : 2*c/Real.pi^2*t^2 ≤ r*(y-2*r)*(1-Real.cos (d*t)) := by
    calc
      _ = c*(2/Real.pi^2*t^2) := by ring
      _ ≤ _ := le_trans hh hm
  have hneg : 0 ≤ r^2*(1-Real.cos (d*t))^2 := by positivity
  calc
    _ ≤ -(r*(y-2*r)*(1-Real.cos (d*t))) := by
      rw [circle_decay_identity]
      nlinarith only [hneg]
    _ ≤ -(2*c/Real.pi^2*t^2) := neg_le_neg hh2
    _ = _ := by ring

noncomputable def circleGenerating (y r θ : ℝ /- [definition] -/) : ℂ :=
  generating y ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))

lemma circle_generating_norm (y r θ : ℝ /- [definition] -/) :
    ‖circleGenerating y r θ‖ = Real.exp (circleExponent y r θ) := by
  have htr := Real.sin_sq_add_cos_sq θ
  unfold circleGenerating generating
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin,pow_two]
  simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,add_zero,zero_add,sub_zero,mul_one]
  unfold circleExponent
  rw [Real.cos_two_mul]
  have hscaled : r^2*(Real.sin θ^2+Real.cos θ^2) = r^2 := by rw [htr]; ring
  nlinarith [hscaled]

lemma circle_generating_ratio (y r θ : ℝ /- [definition] -/) :
    ‖circleGenerating y r θ‖/‖circleGenerating y r 0‖ =
      Real.exp (circleExponent y r θ-circleExponent y r 0) := by
  rw [circle_generating_norm,circle_generating_norm,Real.exp_sub]

/-- The finite normalized generating source itself satisfies the angular Gaussian bound. -/
theorem circle_generating_gaussian (y r d c t : ℝ /- [definition] -/)
    (hc : 0 ≤ c /- [standing] -/)
    (hgap : 0 ≤ r*(y-2*r) /- [standing] -/)
    (hcoef : c ≤ r*(y-2*r)*d^2 /- [standing] -/)
    (hangle : |d*t| ≤ Real.pi /- [standing] -/) :
    ‖circleGenerating y r (d*t)‖/‖circleGenerating y r 0‖ ≤
      Real.exp (-2*c/Real.pi^2*t^2) := by
  rw [circle_generating_ratio]
  exact Real.exp_le_exp.mpr (circle_gaussian_exponent y r d c t hc hgap hcoef hangle)

/-- All scalar premises of the full-circle envelope are supplied on an unbounded
nonzero-radius source, with uniform coefficient c=1 and exhausting angle window. -/
theorem circle_envelope_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, let r : ℝ := n+1
      let d : ℝ := 1/r
      0 < r ∧ 0 < d ∧ 0 ≤ r*(3*r-2*r) ∧ 1 ≤ r*(3*r-2*r)*d^2 ∧
      ∀ t : ℝ, |d*t| ≤ Real.pi →
        ‖circleGenerating (3*r) r (d*t)‖/‖circleGenerating (3*r) r 0‖ ≤
          Real.exp (-2/Real.pi^2*t^2)) := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,?_⟩
  intro n
  dsimp only
  have hr : (0 : ℝ) < n+1 := by positivity
  have hg : 0 ≤ (n+1 : ℝ)*(3*(n+1)-2*(n+1)) := by nlinarith
  have hc : (1 : ℝ) ≤ (n+1)*(3*(n+1)-2*(n+1))*(1/(n+1))^2 := by
    have hne := ne_of_gt hr
    field_simp
    nlinarith
  refine ⟨hr,by positivity,hg,hc,?_⟩
  intro t ht
  simpa only [mul_one] using circle_generating_gaussian (3*(n+1)) (n+1) (1/(n+1)) 1 t
    zero_le_one hg hc ht

lemma edge_scale_saddle_identity (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    edgeScale N = Real.sqrt N*(saddleScale N)^2 := by
  have hs : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hd := saddle_scale_pos N hN
  apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt hr) (ne_of_gt hd))
  calc
    Real.sqrt N*saddleScale N*edgeScale N = 1 := by
      convert sqrt_scale_saddle_scale N hN using 1 <;> ring
    _ = Real.sqrt N*saddleScale N*(Real.sqrt N*(saddleScale N)^2) := by
      calc
        1 = (N : ℝ)*(saddleScale N)^3 := (saddle_scale_cube N hN).symm
        _ = (Real.sqrt N)^2*(saddleScale N)^3 := by rw [hs]
        _ = _ := by ring

noncomputable def circleRadius (N : ℕ /- [definition] -/)
    (β : ℝ /- [definition] -/) : ℝ :=
  Real.sqrt N*(1-β*saddleScale N)

lemma circle_radial_coefficient (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β x : ℝ /- [definition] -/) :
    circleRadius N β*(edgePoint N x-2*circleRadius N β)*(saddleScale N)^2 =
      (1-β*saddleScale N)*(2*β+saddleScale N*x) := by
  have hs : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hc := saddle_scale_cube N hN
  unfold circleRadius edgePoint
  rw [edge_scale_saddle_identity N hN]
  calc
    _ = (Real.sqrt N)^2*(saddleScale N)^3*
        ((1-β*saddleScale N)*(2*β+saddleScale N*x)) := by ring
    _ = _ := by rw [hs,hc,one_mul]

/-- Uniform radial coefficient for the literal source on every bounded edge window.
The positive radius and gap are derived from finite scalar smallness conditions. -/
theorem circle_edge_coefficient_bound (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/)
    (hsmall : β*saddleScale N ≤ 1/2 /- [standing] -/)
    (hx : |x| *saddleScale N ≤ β /- [standing] -/) :
    0 < circleRadius N β ∧
      0 ≤ circleRadius N β*(edgePoint N x-2*circleRadius N β) ∧
      β/2 ≤ circleRadius N β*(edgePoint N x-2*circleRadius N β)*(saddleScale N)^2 := by
  have hd := saddle_scale_pos N hN
  have hr : 0 < circleRadius N β := by
    unfold circleRadius
    exact mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) (by linarith)
  have hneg := neg_abs_le x
  have hmx := mul_le_mul_of_nonneg_left hneg hd.le
  have ha : 1/2 ≤ 1-β*saddleScale N := by linarith
  have hb : β ≤ 2*β+saddleScale N*x := by nlinarith
  have hprod := mul_le_mul ha hb hβ.le (by linarith : 0 ≤ 1-β*saddleScale N)
  have hcoeff : β/2 ≤ circleRadius N β*(edgePoint N x-2*circleRadius N β)*(saddleScale N)^2 := by
    rw [circle_radial_coefficient N hN]
    nlinarith
  have hg : 0 ≤ circleRadius N β*(edgePoint N x-2*circleRadius N β) := by
    have hmul : 0 < circleRadius N β*(edgePoint N x-2*circleRadius N β)*(saddleScale N)^2 :=
      lt_of_lt_of_le (by linarith) hcoeff
    exact (pos_of_mul_pos_left hmul (sq_nonneg _)).le
  exact ⟨hr,hg,hcoeff⟩

/-- Genuine Hermite source, full finite circle and uniform Gaussian angular envelope. -/
theorem circle_edge_generating_gaussian (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (β x t : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/)
    (hsmall : β*saddleScale N ≤ 1/2 /- [standing] -/)
    (hx : |x| *saddleScale N ≤ β /- [standing] -/)
    (hangle : |saddleScale N*t| ≤ Real.pi /- [standing] -/) :
    ‖circleGenerating (edgePoint N x) (circleRadius N β) (saddleScale N*t)‖/
        ‖circleGenerating (edgePoint N x) (circleRadius N β) 0‖ ≤
      Real.exp (-β/Real.pi^2*t^2) := by
  have h := circle_edge_coefficient_bound N hN β x hβ hsmall hx
  have hb := circle_generating_gaussian (edgePoint N x) (circleRadius N β)
    (saddleScale N) (β/2) t (by linarith) h.2.1 h.2.2 hangle
  convert hb using 1 <;> ring

/-- Complete literal edge-source example with fixed β=1, every bounded x-window,
positive radii, exhausting angle domains, and no assumed analytic bound. -/
theorem circle_edge_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ᶠ n : ℕ in atTop,
      0 < circleRadius (n+1) 1 ∧ 1*saddleScale (n+1) ≤ 1/2 ∧
      ∀ x t : ℝ, |x| ≤ R → |saddleScale (n+1)*t| ≤ Real.pi →
        |x| *saddleScale (n+1) ≤ 1 ∧
        ‖circleGenerating (edgePoint (n+1) x) (circleRadius (n+1) 1) (saddleScale (n+1)*t)‖/
          ‖circleGenerating (edgePoint (n+1) x) (circleRadius (n+1) 1) 0‖ ≤
            Real.exp (-1/Real.pi^2*t^2)) := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,?_⟩
  intro R hR
  have hs : ∀ᶠ n : ℕ in atTop, saddleScale (n+1) < 1/2 :=
    saddle_scale_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have ht : Tendsto (fun n : ℕ => saddleScale (n+1)*R) atTop (𝓝 0) := by
    simpa using saddle_scale_tendsto.mul_const R
  have hb := ht.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hs,hb] with n hn hnr
  have hsmall : 1*saddleScale (n+1) ≤ 1/2 := by linarith
  have hr := (circle_edge_coefficient_bound (n+1) (by omega) 1 0 zero_lt_one hsmall
    (by simp)).1
  refine ⟨hr,hsmall,?_⟩
  intro x t hx hθ
  have hxx : |x| *saddleScale (n+1) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hx (saddle_scale_pos (n+1) (by omega)).le
    nlinarith
  exact ⟨hxx,circle_edge_generating_gaussian (n+1) (by omega) 1 x t zero_lt_one hsmall hxx hθ⟩

end RMTFoundations.TracyWidom.HermiteCircleEnvelope

#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circleExponent
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_decay_identity
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_gaussian_exponent
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circleGenerating
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_generating_norm
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_generating_ratio
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_generating_gaussian
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_envelope_joint_probe
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.edge_scale_saddle_identity
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circleRadius
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_radial_coefficient
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_edge_coefficient_bound
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_edge_generating_gaussian
#print axioms RMTFoundations.TracyWidom.HermiteCircleEnvelope.circle_edge_joint_probe
