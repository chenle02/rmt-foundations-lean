import RMTFoundations.Airy.Bounds
import RMTFoundations.Airy.HankelFactorization
import RMTFoundations.Airy.Continuity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.SoftEdgeHankelCore
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.Airy RMTFoundations.AiryBounds
open RMTFoundations.Fredholm RMTFoundations.AiryContinuity

/-- A half-line exponential bound controls the genuine Hankel kernel in L2. -/
theorem hankel_memLp_of_envelope
    (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (s C : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hb : ∀ x : ℝ, s ≤ x → |f x| ≤ C*Real.exp (-(1/2:ℝ)*(x-s)) /- [standing] -/) :
    MemLp (shiftedKernel f s) 2 quadrantMeasure := by
  apply ((memLp_halfline_exp_pair_rate (-(1/2:ℝ)) (-(1/2:ℝ))
    (by norm_num) (by norm_num)).const_smul C).of_le
    ((continuous_shiftedKernel f hf s).aestronglyMeasurable)
  filter_upwards [ae_positive_quadrant] with p hp
  change |f (p.1+p.2+s)| ≤ |C*(Real.exp (-(1/2:ℝ)*p.1)*Real.exp (-(1/2:ℝ)*p.2))|
  rw [abs_mul,abs_of_nonneg hC,abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  have hh := hb (p.1+p.2+s) (by linarith)
  convert hh using 1
  rw [← Real.exp_add]
  congr 1
  ring

/-- The common envelope passes to the pointwise limit without an extra bound premise. -/
theorem limit_envelope
    (f : ℕ → ℝ → ℝ /- [definition] -/)
    (g : ℝ → ℝ /- [definition] -/)
    (s C : ℝ /- [definition] -/)
    (hb : ∀ n x, s ≤ x → |f n x| ≤ C*Real.exp (-(1/2:ℝ)*(x-s)) /- [standing] -/)
    (hl : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) /- [standing] -/) :
    ∀ x : ℝ, s ≤ x → |g x| ≤ C*Real.exp (-(1/2:ℝ)*(x-s)) := by
  intro x hx
  exact le_of_tendsto ((hl x).abs) (Eventually.of_forall fun n => hb n x hx)

/-- Pointwise convergence and the actual uniform tail envelope imply L2 convergence.
The integration domain is the full shifted quadrant, not a compact truncation. -/
theorem hankel_eLpNorm_tendsto
    (f : ℕ → ℝ → ℝ /- [definition] -/)
    (g : ℝ → ℝ /- [definition] -/)
    (hf : ∀ n, Continuous (f n) /- [standing] -/)
    (hg : Continuous g /- [standing] -/)
    (s C : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hb : ∀ n x, s ≤ x → |f n x| ≤ C*Real.exp (-(1/2:ℝ)*(x-s)) /- [standing] -/)
    (hl : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) /- [standing] -/) :
    Tendsto (fun n => eLpNorm (shiftedKernel (f n) s-shiftedKernel g s) 2 quadrantMeasure)
      atTop (𝓝 0) := by
  let E : ℝ × ℝ → ℝ := fun p =>
    (2*C)*(Real.exp (-(1/2:ℝ)*p.1)*Real.exp (-(1/2:ℝ)*p.2))
  let B : ℝ × ℝ → ℝ := fun p => (E p)^2
  let F : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal ((shiftedKernel (f n) s p-shiftedKernel g s p)^2)
  have hB : Integrable B quadrantMeasure :=
    (((memLp_halfline_exp_pair_rate (-(1/2:ℝ)) (-(1/2:ℝ))
      (by norm_num) (by norm_num)).const_smul (2*C)).integrable_sq)
  have hfin : (∫⁻ p, ENNReal.ofReal (B p) ∂quadrantMeasure) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg (E p))).mp
      hB.hasFiniteIntegral).ne
  have hmeas : ∀ᶠ n : ℕ in atTop, Measurable (F n) := by
    apply Eventually.of_forall
    intro n
    exact ENNReal.measurable_ofReal.comp
      (((continuous_shiftedKernel (f n) (hf n) s).sub
        (continuous_shiftedKernel g hg s)).pow 2).measurable
  have hgb := limit_envelope f g s C hb hl
  have hdom : ∀ᶠ n : ℕ in atTop, ∀ᵐ p ∂quadrantMeasure,
      F n p ≤ ENNReal.ofReal (B p) := by
    apply Eventually.of_forall
    intro n
    filter_upwards [ae_positive_quadrant] with p hp
    apply ENNReal.ofReal_le_ofReal
    have hfn := hb n (p.1+p.2+s) (by linarith)
    have hgn := hgb (p.1+p.2+s) (by linarith)
    have he : C*Real.exp (-(1/2:ℝ)*(p.1+p.2+s-s)) =
        C*(Real.exp (-(1/2:ℝ)*p.1)*Real.exp (-(1/2:ℝ)*p.2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at hfn hgn
    have hab := abs_sub (f n (p.1+p.2+s)) (g (p.1+p.2+s))
    have hE : 0 ≤ E p := by dsimp [E]; positivity
    dsimp [F,B,E,shiftedKernel]
    nlinarith [sq_abs (f n (p.1+p.2+s)-g (p.1+p.2+s)),
      abs_nonneg (f n (p.1+p.2+s)-g (p.1+p.2+s))]
  have hlim : ∀ᵐ p ∂quadrantMeasure,
      Tendsto (fun n => F n p) atTop (𝓝 0) := by
    apply ae_of_all
    intro p
    have hh := ((hl (p.1+p.2+s)).sub_const (g (p.1+p.2+s))).pow 2
    simpa [F,shiftedKernel,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have ht := tendsto_lintegral_filter_of_dominated_convergence
    (μ := quadrantMeasure) (f := fun _ => 0) (fun p => ENNReal.ofReal (B p))
    hmeas hdom hfin hlim
  have ht' : Tendsto (fun n => (∫⁻ p, F n p ∂quadrantMeasure) ^ (1/2:ℝ))
      atTop (𝓝 0) := by simpa using ht.ennrpow_const (1/2:ℝ)
  have heq : ∀ n, eLpNorm (shiftedKernel (f n) s-shiftedKernel g s) 2 quadrantMeasure =
      (∫⁻ p, F n p ∂quadrantMeasure) ^ (1/2:ℝ) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (((continuous_shiftedKernel (f n) (hf n) s).sub
        (continuous_shiftedKernel g hg s)).aestronglyMeasurable)]
    norm_num
    congr 1
    apply lintegral_congr
    intro p
    simp only [F]
    rw [← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg _)]
    congr 1
    rw [Real.norm_eq_abs,sq_abs]
  exact ht'.congr (fun n => (heq n).symm)

/-- The operator HS error is bounded by the L2 error of the literal kernels. -/
theorem hs_kernel_error_le
    (K L : ℝ × ℝ → ℝ /- [definition] -/)
    (hK : MemLp K 2 quadrantMeasure /- [standing] -/)
    (hL : MemLp L 2 quadrantMeasure /- [standing] -/) :
    hsENorm (kernelOperator hK-kernelOperator hL) ≤ eLpNorm (K-L) 2 quadrantMeasure := by
  have hh := hsENorm_kernelOperator_le (hK.sub hL)
  rw [kernelOperator_sub K L hK hL] at hh
  exact hh

end RMTFoundations.TracyWidom.SoftEdgeHankelCore

#print axioms RMTFoundations.TracyWidom.SoftEdgeHankelCore.hankel_memLp_of_envelope
#print axioms RMTFoundations.TracyWidom.SoftEdgeHankelCore.limit_envelope
#print axioms RMTFoundations.TracyWidom.SoftEdgeHankelCore.hankel_eLpNorm_tendsto
#print axioms RMTFoundations.TracyWidom.SoftEdgeHankelCore.hs_kernel_error_le
