import RMTFoundations.TracyWidom.HermiteCauchy
import RMTFoundations.TracyWidom.HermiteCubicSaddle
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteSaddleSource
open Complex Filter Topology
open RMTFoundations.TracyWidom.HermiteCauchy RMTFoundations.TracyWidom.HermiteCubicSaddle
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.GUEHermite

noncomputable def saddleCoordinate (N : ℕ /- [definition] -/)
    (u : ℂ /- [definition] -/) : ℂ :=
  (Real.sqrt N : ℂ)*(1+(saddleScale N : ℂ)*u)

lemma sqrt_scale_saddle_scale (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    Real.sqrt N*edgeScale N*saddleScale N = 1 := by
  have he : saddleScale N = (edgeScale N)^2 := (edgeScale_square N).symm
  rw [he]
  convert sqrt_mul_edgeScale_cube N hN using 1 <;> ring

/-- Exact exponent of the literal Hermite generating function at the coalescing saddle. -/
lemma generating_saddle_exponent (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (u : ℂ /- [definition] -/) :
    (edgePoint N x : ℂ)*saddleCoordinate N u-(saddleCoordinate N u)^2/2 =
      (3*(N : ℝ)/2+Real.sqrt N*edgeScale N*x : ℂ)+
      (N : ℂ)*((saddleScale N : ℂ)*u-((saddleScale N : ℂ)*u)^2/2)+(x : ℂ)*u := by
  have hs : (Real.sqrt N : ℂ)^2 = (N : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hc : (Real.sqrt N : ℂ)*(edgeScale N : ℂ)*(saddleScale N : ℂ) = 1 := by
    exact_mod_cast sqrt_scale_saddle_scale N hN
  unfold edgePoint saddleCoordinate
  push_cast
  calc
    _ = (Real.sqrt N : ℂ)^2*(3/2+(saddleScale N : ℂ)*u-
          ((saddleScale N : ℂ)*u)^2/2)+
        (Real.sqrt N : ℂ)*(edgeScale N : ℂ)*(x : ℂ)+
        ((Real.sqrt N : ℂ)*(edgeScale N : ℂ)*(saddleScale N : ℂ))*(x : ℂ)*u := by ring
    _ = _ := by rw [hs,hc]; ring

/-- The actual Cauchy integrand equals the cubic-phase integrand with the exact
finite denominator correction. No contour deformation or limit is assumed. -/
theorem hermite_integrand_saddle_nonzero (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (u : ℂ /- [definition] -/)
    (hsource : 1+(saddleScale N : ℂ)*u ≠ 0 /- [standing] -/) :
    (1/(saddleCoordinate N u)^(N+1))*generating (edgePoint N x) (saddleCoordinate N u) =
      Complex.exp (3*(N : ℂ)/2+(Real.sqrt N : ℂ)*(edgeScale N : ℂ)*x)*
      Complex.exp (saddlePhase N x u)/
        ((Real.sqrt N : ℂ)^(N+1)*(1+(saddleScale N : ℂ)*u)) := by
  have hw := hsource
  have hr : (Real.sqrt N : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hN)))
  have hp : Complex.exp ((N : ℂ)*Complex.log (1+(saddleScale N : ℂ)*u)) =
      (1+(saddleScale N : ℂ)*u)^N := by
    rw [Complex.exp_nat_mul,Complex.exp_log hw]
  have hg : generating (edgePoint N x) (saddleCoordinate N u) =
      Complex.exp (3*(N : ℂ)/2+(Real.sqrt N : ℂ)*(edgeScale N : ℂ)*x)*
      Complex.exp (saddlePhase N x u)*(1+(saddleScale N : ℂ)*u)^N := by
    rw [generating,generating_saddle_exponent N hN,← hp,← Complex.exp_add,← Complex.exp_add]
    congr 1
    unfold saddlePhase
    push_cast
    ring
  rw [hg,saddleCoordinate,mul_pow,pow_succ]
  field_simp [hr,hw]
  rw [pow_succ]
  ring

/-- The previously compiled local source statement, preserved literally. -/
theorem hermite_integrand_saddle (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (u : ℂ /- [definition] -/)
    (hu : ‖(saddleScale N : ℂ)*u‖ < 1 /- [standing] -/) :
    (1/(saddleCoordinate N u)^(N+1))*generating (edgePoint N x) (saddleCoordinate N u) =
      Complex.exp (3*(N : ℂ)/2+(Real.sqrt N : ℂ)*(edgeScale N : ℂ)*x)*
      Complex.exp (saddlePhase N x u)/
        ((Real.sqrt N : ℂ)^(N+1)*(1+(saddleScale N : ℂ)*u)) := by
  exact hermite_integrand_saddle_nonzero N hN x u
    (Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hu))

/-- A complete growing actual-source example, including the literal normalized
Hermite contour, its rescaled integrand and the proved compact cubic limit. -/
theorem saddle_source_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, 0 < Real.sqrt (n+1 : ℕ) ∧
      (hermiteMode (n+1) (edgePoint (n+1) 1) : ℂ) =
        (gaussianWeight (edgePoint (n+1) 1)*hermiteNormalizer (n+1)*((n+1).factorial : ℝ) : ℂ)/
          (2*Real.pi*Complex.I)*circleIntegral
            (fun z : ℂ => (1/z^(n+1+1))*generating (edgePoint (n+1) 1) z)
            0 (Real.sqrt (n+1 : ℕ))) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, let u : ℂ := Complex.I/4
      u ≠ 0 ∧ ‖(saddleScale (n+1) : ℂ)*u‖ < 1 ∧
      (1/(saddleCoordinate (n+1) u)^(n+1+1))*
        generating (edgePoint (n+1) 1) (saddleCoordinate (n+1) u) =
          Complex.exp (3*(n+1 : ℂ)/2+(Real.sqrt (n+1 : ℕ) : ℂ)*(edgeScale (n+1) : ℂ))*
            Complex.exp (saddlePhase (n+1) 1 u)/
              ((Real.sqrt (n+1 : ℕ) : ℂ)^(n+1+1)*(1+(saddleScale (n+1) : ℂ)*u)) ∧
      ‖saddlePhase (n+1) 1 u-(u-u^3/3)‖ < ε) := by
  refine ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,?_,?_⟩
  · intro n
    have hr : 0 < Real.sqrt (n+1 : ℕ) := by positivity
    exact ⟨hr,hermite_mode_cauchy (n+1) (edgePoint (n+1) 1) _ hr⟩
  · intro ε hε
    have hs : ∀ᶠ n : ℕ in atTop, saddleScale (n+1) < 1 :=
      saddle_scale_tendsto.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [hs,saddle_phase_locally_uniform 1 zero_le_one ε hε] with n hn he
    dsimp only
    have hu : ‖(Complex.I/4 : ℂ)‖ ≤ 1 := by norm_num [norm_div]
    have hb : ‖(saddleScale (n+1) : ℂ)*(Complex.I/4)‖ < 1 := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (saddle_scale_pos _ (by omega)).le]
      have hm : saddleScale (n+1)*‖(Complex.I/4 : ℂ)‖ ≤ saddleScale (n+1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (saddle_scale_pos (n+1) (by omega)).le
      exact hm.trans_lt hn
    refine ⟨div_ne_zero Complex.I_ne_zero (by norm_num),hb,?_,?_⟩
    · simpa using hermite_integrand_saddle (n+1) (by omega) 1 (Complex.I/4) hb
    · simpa using he 1 (Complex.I/4) hu
end RMTFoundations.TracyWidom.HermiteSaddleSource

#print axioms RMTFoundations.TracyWidom.HermiteSaddleSource.saddleCoordinate
#print axioms RMTFoundations.TracyWidom.HermiteSaddleSource.sqrt_scale_saddle_scale
#print axioms RMTFoundations.TracyWidom.HermiteSaddleSource.generating_saddle_exponent
#print axioms RMTFoundations.TracyWidom.HermiteSaddleSource.hermite_integrand_saddle_nonzero
#print axioms RMTFoundations.TracyWidom.HermiteSaddleSource.hermite_integrand_saddle
#print axioms RMTFoundations.TracyWidom.HermiteSaddleSource.saddle_source_joint_probe
