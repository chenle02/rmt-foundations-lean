import Challenge.Reference.Airy.Consequences
import Challenge.Reference.Airy.Contraction
import Challenge.Reference.Airy.HankelFactorization

set_option autoImplicit false
universe u
namespace RMTFoundations.TWOneBounds
open MeasureTheory Set Filter
open scoped Topology ENNReal InnerProductSpace BigOperators
open RMTFoundations.Fredholm RMTFoundations.Airy RMTFoundations.AiryBounds RMTFoundations.AiryKernel

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false


open MeasureTheory FourierTransform RMTFoundations.Airy
open Set Filter Complex
open scoped InnerProductSpace InnerProduct TemperedDistribution
open scoped SchwartzMap ENNReal Topology ContDiff

open FourierTransform LineDeriv
open scoped SchwartzMap TemperedDistribution
open Asymptotics
open scoped Asymptotics
open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open Filter

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

open FourierTransform
open scoped SchwartzMap

open RMTFoundations.Airy
open Set

set_option autoImplicit false
/-- The third-order primitive energy. This is not an event predicate. -/
noncomputable def tailEnergy
    (f f1 f2 : ℝ → ℝ /- [definition] -/ )
    (x : ℝ /- [definition] -/ )
    : ℝ := f x * f2 x - (f1 x) ^ 2 / 2 - x * (f x) ^ 2 / 2

theorem hasDerivAt_tailEnergy
    (f f1 f2 : ℝ → ℝ /- [definition] -/ )
    (h1 : ∀ x, HasDerivAt f (f1 x) x /- [standing] -/ )
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x /- [standing] -/ )
    (h3 : ∀ x, HasDerivAt f2 (x * f1 x) x /- [standing] -/ )
    (x : ℝ /- [definition] -/ )
    : HasDerivAt (tailEnergy f f1 f2) (-(f x) ^ 2 / 2) x := by
  convert! ((h1 x).mul (h3 x)).sub (((h2 x).pow 2).div_const 2) |>.sub
    (((hasDerivAt_id x).mul ((h1 x).pow 2)).div_const 2) using 1 <;>
    (try simp only [tailEnergy, Pi.pow_apply, id_eq]) <;> ring

/-- An energy tending to zero and dissipating f² forbids a zero of f,
provided f is positive on the nonnegative half-line. -/
theorem positive_of_tail_energy
    (f E : ℝ → ℝ /- [definition] -/ )
    (hc : Continuous f /- [standing] -/ )
    (hE : ∀ x, HasDerivAt E (-(f x) ^ 2 / 2) x /- [standing] -/ )
    (hlim : Tendsto E atTop (𝓝 0)  /- [standing] -/ )
    (hz : ∀ x, f x = 0 → E x ≤ 0 /- [standing] -/ )
    (hp : ∀ x, 0 ≤ x → 0 < f x /- [standing] -/ )
    : ∀ x, 0 < f x := by
  have hm : Antitone E := antitone_of_hasDerivAt_nonpos hE (fun x => by
    dsimp
    nlinarith [sq_nonneg (f x)])
  have hn : ∀ x, 0 ≤ E x := hm.le_of_tendsto hlim
  have hfne : ∀ a, f a ≠ 0 := by
    intro a hfa
    have hea : E a = 0 := le_antisymm (hz a hfa) (hn a)
    have hez : ∀ y, a ≤ y → E y = 0 := by
      intro y hay
      exact le_antisymm (by simpa [hea] using hm hay) (hn y)
    let b := max a 0 + 1
    have hab : a < b := by dsimp [b]; linarith [le_max_left a 0]
    have hb : 0 ≤ b := by dsimp [b]; linarith [le_max_right a 0]
    have heq : E =ᶠ[𝓝 b] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hab] with y hy
      exact hez y hy.le
    have hd0 : HasDerivAt E 0 b :=
      (hasDerivAt_const b (0 : ℝ)).congr_of_eventuallyEq heq
    have hsq : -(f b) ^ 2 / 2 = 0 := (hE b).unique hd0
    have hfb : f b = 0 := by nlinarith [sq_nonneg (f b)]
    exact (hp b hb).ne' hfb
  intro a
  by_contra hpa
  have hna : f a ≤ 0 := le_of_not_gt hpa
  let b := max a 0 + 1
  have hab : a ≤ b := by dsimp [b]; linarith [le_max_left a 0]
  have hb : 0 ≤ b := by dsimp [b]; linarith [le_max_right a 0]
  obtain ⟨c, _, hfc⟩ := intermediate_value_Icc hab hc.continuousOn
    (show (0 : ℝ) ∈ Icc (f a) (f b) from ⟨hna, (hp b hb).le⟩)
  exact hfne c hfc

theorem positive_of_third_order_ode
    (f f1 f2 : ℝ → ℝ /- [definition] -/ )
    (h1 : ∀ x, HasDerivAt f (f1 x) x /- [standing] -/ )
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x /- [standing] -/ )
    (h3 : ∀ x, HasDerivAt f2 (x * f1 x) x /- [standing] -/ )
    (hlim : Tendsto (tailEnergy f f1 f2) atTop (𝓝 0)  /- [standing] -/ )
    (hp : ∀ x, 0 ≤ x → 0 < f x /- [standing] -/ )
    : ∀ x, 0 < f x := by
  have hc : Continuous f := (show Differentiable ℝ f from fun x => (h1 x).differentiableAt).continuous
  apply positive_of_tail_energy f (tailEnergy f f1 f2) hc
    (hasDerivAt_tailEnergy f f1 f2 h1 h2 h3) hlim
  · intro x hx
    dsimp [tailEnergy]
    rw [hx]
    nlinarith [sq_nonneg (f1 x)]
  · exact hp


/-- Ordinary absolutely convergent upper tail, with Lebesgue measure. -/
noncomputable def airyTailIntegral
    (f : ℝ → ℝ /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : ℝ := ∫ x in Ioi s, f x

theorem exp_bound_integrable_Ioi
    (f : ℝ → ℝ /- [definition] -/ )
    (hc : Continuous f /- [standing] -/ )
    (hb : ∀ a, ∃ C : ℝ, 0 < C ∧ ∀ x, a ≤ x → |f x| ≤ C * Real.exp (-x)  /- [standing] -/ )
    (a : ℝ /- [definition] -/ )
    : IntegrableOn f (Ioi a) := by
  obtain ⟨C, _, hC⟩ := hb a
  apply ((integrableOn_exp_neg_Ioi a).const_mul C).mono' hc.aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro x hx
  simpa only [Real.norm_eq_abs] using hC x hx.le

theorem hasDerivAt_airyTailIntegral
    (f : ℝ → ℝ /- [definition] -/ )
    (hc : Continuous f /- [standing] -/ )
    (hi : ∀ a, IntegrableOn f (Ioi a)  /- [standing] -/ )
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (airyTailIntegral f) (-f s) s := by
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 s) hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt).const_sub (airyTailIntegral f 0)
  convert! hd using 1
  funext a
  have he := intervalIntegral.integral_interval_add_Ioi (hi 0) (hi a)
  dsimp [airyTailIntegral]
  linarith

theorem airyTailIntegral_abs_le
    (f : ℝ → ℝ /- [definition] -/ )
    (hi : ∀ a, IntegrableOn f (Ioi a)  /- [standing] -/ )
    (C a : ℝ /- [definition] -/ )
    (hb : ∀ x, a ≤ x → |f x| ≤ C * Real.exp (-x)  /- [standing] -/ )
    : |airyTailIntegral f a| ≤ C * Real.exp (-a) := by
  calc
    |airyTailIntegral f a| ≤ ∫ x in Ioi a, |f x| := by
      simpa only [airyTailIntegral, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := volume.restrict (Ioi a)) f
    _ ≤ ∫ x in Ioi a, C * Real.exp (-x) := by
      apply integral_mono_ae (hi a).norm ((integrableOn_exp_neg_Ioi a).const_mul C)
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      exact fun x hx => hb x hx.le
    _ = C * Real.exp (-a) := by rw [integral_const_mul, integral_exp_neg_Ioi]

theorem airyTailIntegral_pos_of_nonneg
    (f : ℝ → ℝ /- [definition] -/ )
    (hi : ∀ a, IntegrableOn f (Ioi a)  /- [standing] -/ )
    (hp : ∀ x, 0 ≤ x → 0 < f x /- [standing] -/ )
    (a : ℝ /- [definition] -/ )
    (ha : 0 ≤ a /- [standing] -/ )
    : 0 < airyTailIntegral f a := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi a)] f := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    exact fun x hx => (hp x (ha.trans hx.le)).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn (hi a)).mpr
  have he : Function.support f ∩ Ioi a = Ioi a := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, Function.mem_support]
    exact ⟨fun h => h.2, fun hx => ⟨(hp x (ha.trans hx.le)).ne', hx⟩⟩
  rw [he]
  simp

/-- x exp(-x) is bounded by a slower exponential. -/
theorem linear_exp_bound
    (x : ℝ /- [definition] -/ )
    (hx : 0 ≤ x /- [standing] -/ )
    : x * Real.exp (-x) ≤ 2 * Real.exp (-(1 / 2 : ℝ) * x) := by
  have h : x ≤ 2 * Real.exp (x / 2) := by
    nlinarith [Real.add_one_le_exp (x / 2)]
  calc
    x * Real.exp (-x) ≤ (2 * Real.exp (x / 2)) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 2 * Real.exp (-(1 / 2 : ℝ) * x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem linear_mul_exp_bound_integrable
    (f : ℝ → ℝ /- [definition] -/ )
    (hc : Continuous f /- [standing] -/ )
    (C : ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (hb : ∀ x, 0 ≤ x → |f x| ≤ C * Real.exp (-x)  /- [standing] -/ )
    : IntegrableOn (fun x => x * f x) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).const_mul (C * 2)).mono'
    (continuous_id.mul hc).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro x hx
  dsimp only [Pi.mul_apply, id_eq]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx]
  calc
    x * |f x| ≤ x * (C * Real.exp (-x)) := mul_le_mul_of_nonneg_left (hb x hx.le) hx.le
    _ = C * (x * Real.exp (-x)) := by ring
    _ ≤ C * (2 * Real.exp (-(1 / 2 : ℝ) * x)) :=
      mul_le_mul_of_nonneg_left (linear_exp_bound x hx.le) hC
    _ = (C * 2) * Real.exp (-(1 / 2 : ℝ) * x) := by ring

theorem airyTailIntegral_weighted_tendsto
    (f : ℝ → ℝ /- [definition] -/ )
    (hi : ∀ a, IntegrableOn f (Ioi a)  /- [standing] -/ )
    (C : ℝ /- [definition] -/ )
    (hb : ∀ x, 0 ≤ x → |f x| ≤ C * Real.exp (-x)  /- [standing] -/ )
    : Tendsto (fun x => x * airyTailIntegral f x) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x : ℝ => C * (x * Real.exp (-x)))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
    calc
      x * |airyTailIntegral f x| ≤ x * (C * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left (airyTailIntegral_abs_le f hi C x
          (fun t ht => hb t (hx.trans ht))) hx
      _ = C * (x * Real.exp (-x)) := by ring
  · simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul C

/-- Global sign of the genuine primitive is derived from the Airy ODE and decay.
No primitive sign hypothesis on negative arguments is used. -/
theorem decaying_airy_tail_pos
    (f f1 : ℝ → ℝ /- [definition] -/ )
    (h1 : ∀ x, HasDerivAt f (f1 x) x /- [standing] -/ )
    (h2 : ∀ x, HasDerivAt f1 (x * f x) x /- [standing] -/ )
    (hp : ∀ x, 0 ≤ x → 0 < f x /- [standing] -/ )
    (hb : ∀ a, ∃ C : ℝ, 0 < C ∧ ∀ x, a ≤ x → |f x| ≤ C * Real.exp (-x)  /- [standing] -/ )
    : ∀ s, 0 < airyTailIntegral f s := by
  have hc : Continuous f := (show Differentiable ℝ f from fun x => (h1 x).differentiableAt).continuous
  have hi := exp_bound_integrable_Ioi f hc hb
  obtain ⟨C, hC, hbound⟩ := hb 0
  have hft : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ => C * Real.exp (-x))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simpa only [Real.norm_eq_abs] using hbound x hx
    · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  have hf1t : Tendsto f1 atTop (𝓝 (limUnder atTop f1)) :=
    tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun x _ => h2 x) (linear_mul_exp_bound_integrable f hc C hC.le hbound)
  have ht : Tendsto (airyTailIntegral f) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hwt := airyTailIntegral_weighted_tendsto f hi C hbound
  have hd1 : ∀ x, HasDerivAt (airyTailIntegral f) (-f x) x := hasDerivAt_airyTailIntegral f hc hi
  have hd2 : ∀ x, HasDerivAt (fun t => -f t) (-f1 x) x := fun x => (h1 x).neg
  have hd3 : ∀ x, HasDerivAt (fun t => -f1 t) (x * (-f x)) x := by
    intro x
    convert! (h2 x).neg using 1 <;> simp only [mul_neg]
  have he : Tendsto (tailEnergy (airyTailIntegral f) (fun x => -f x) (fun x => -f1 x))
      atTop (𝓝 0) := by
    have hprod := ht.mul hf1t.neg
    have hsq := hft.neg.pow 2
    have hw := hwt.mul ht
    have h := (hprod.sub (hsq.div_const 2)).sub (hw.div_const 2)
    have heq : tailEnergy (airyTailIntegral f) (fun x => -f x) (fun x => -f1 x) =
        fun x => airyTailIntegral f x * -f1 x - (-f x) ^ 2 / 2 -
          x * airyTailIntegral f x * airyTailIntegral f x / 2 := by
      funext x
      dsimp only [tailEnergy]
      ring
    rw [heq]
    simpa using h
  exact positive_of_third_order_ode (airyTailIntegral f) (fun x => -f x) (fun x => -f1 x)
    hd1 hd2 hd3 he (airyTailIntegral_pos_of_nonneg f hi hp)

/-- Translation of a Lebesgue half-line integral, with no implicit measure. -/
theorem halfline_translate_integral
    (f : ℝ → ℝ /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : (∫ x in Ioi (0 : ℝ), f (x + s)) = airyTailIntegral f s := by
  rw [airyTailIntegral, ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  have h := integral_add_right_eq_self (μ := volume) ((Ioi s).indicator f) s
  convert h using 1
  apply integral_congr_ae
  filter_upwards with x
  have he : x + s ∈ Ioi s ↔ x ∈ Ioi (0 : ℝ) := by
    simp only [mem_Ioi]
    constructor <;> intro hx <;> linarith
  simp only [indicator_apply, he]

/-- Physical Airy Hankel diagonal normalization, before any spectral trace theorem. -/
theorem halfline_diagonal_integral
    (f : ℝ → ℝ /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : (∫ x in Ioi (0 : ℝ), f (x + x + s)) = airyTailIntegral f s / 2 := by
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => f (u + s)) 0
    (b := 2) (by norm_num)
  simp only [mul_zero, smul_eq_mul] at h
  rw [halfline_translate_integral f s] at h
  convert h using 1 <;> congr 1
  · funext x
    congr 1
    ring
  · ring

/-- The upper tail of the exact RMTFoundations.Airy.airyAiReal constructed in the TWC source is positive
for every real shift. No asymptotic or negative-half-line sign input is assumed. -/
theorem airy_tail_positive
    (s : ℝ /- [definition] -/ )
    : 0 < airyTailIntegral RMTFoundations.Airy.airyAiReal s := by
  exact decaying_airy_tail_pos RMTFoundations.Airy.airyAiReal (deriv RMTFoundations.Airy.airyAiReal) Ai_ODE_joint_probe.1
    Ai_ODE_joint_probe.2.1 (fun x hx => airyAiReal_pos_of_nonneg hx) Ai_halfline_exp_bound s

/-- Physical diagonal normalization. Identifying this with a spectral trace
requires the determinant-function bridge, rather than a new trace hypothesis. -/
theorem B_diagonal_integral_eq_half_tail
    (s : ℝ /- [definition] -/ )
    : (∫ x, RMTFoundations.Airy.airyAiReal (x + x + s) ∂ RMTFoundations.Airy.halfLineMeasure) = airyTailIntegral RMTFoundations.Airy.airyAiReal s / 2 :=
  halfline_diagonal_integral RMTFoundations.Airy.airyAiReal s

theorem B_diagonal_integral_positive
    (s : ℝ /- [definition] -/ )
    : 0 < ∫ x, RMTFoundations.Airy.airyAiReal (x + x + s) ∂ RMTFoundations.Airy.halfLineMeasure := by
  rw [B_diagonal_integral_eq_half_tail]
  exact div_pos (airy_tail_positive s) (by norm_num)

/-- All the ODE, regularity, decay, and positive-half-line premises hold jointly
on the actual nonzero, sign-changing Airy solution. -/
theorem airy_tail_analytic_joint_probe :
    ∃ f f1 : ℝ → ℝ,
      (∀ x, HasDerivAt f (f1 x) x) ∧
      (∀ x, HasDerivAt f1 (x * f x) x) ∧
      (∀ x, 0 ≤ x → 0 < f x) ∧
      (∀ a, ∃ C : ℝ, 0 < C ∧ ∀ x, a ≤ x → |f x| ≤ C * Real.exp (-x)) ∧
      0 < f 0 ∧ (∃ x, f x < 0) ∧ (∀ s, 0 < airyTailIntegral f s) := by
  refine ⟨RMTFoundations.Airy.airyAiReal, deriv RMTFoundations.Airy.airyAiReal, Ai_ODE_joint_probe.1, Ai_ODE_joint_probe.2.1,
    fun x hx => airyAiReal_pos_of_nonneg hx, Ai_halfline_exp_bound,
    airyAiReal_zero_pos, ?_, airy_tail_positive⟩
  obtain ⟨x, _, hx⟩ := Ai_negative_witness
  exact ⟨x, hx⟩




open Filter Set
open scoped Topology BigOperators

noncomputable def spectralCoeff
    (lam : ℕ → ℝ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℝ := ∑' s : {s : Finset ℕ // s.card = n}, ∏ i ∈ s.val, lam i

theorem spectral_finset_summable
    (lam : ℕ → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Summable (fun s : Finset ℕ => (∏ i ∈ s, lam i) * z ^ s.card) := by
  have hm := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (norm_nonneg (lam i))) (hs.norm.mul_left ‖z‖)
  have hn : Summable (fun s : Finset ℕ => ‖(∏ i ∈ s, lam i) * z ^ s.card‖) := by
    convert hm using 1
    funext s
    rw [norm_mul, norm_pow, norm_prod, Finset.prod_mul_distrib, Finset.prod_const]
    ring
  exact hn.of_norm

theorem spectralCoeff_hasSum
    (lam : ℕ → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : HasSum (fun n => spectralCoeff lam n * z ^ n) (∏' i, (1 + z * lam i)) := by
  have hp : HasSum (fun s : Finset ℕ => ∏ i ∈ s, z * lam i) (∏' i, (1 + z * lam i)) := by
    have hss : Summable (fun s : Finset ℕ => ∏ i ∈ s, z * lam i) := by
      simpa only [Finset.prod_mul_distrib, Finset.prod_const, mul_comm] using
        spectral_finset_summable lam hs z
    rw [tprod_one_add hss]
    exact hss.hasSum
  have hgroup := hp.tsum_fiberwise Finset.card
  refine hgroup.congr_fun (fun n => ?_)
  rw [spectralCoeff, ← tsum_mul_right]
  apply tsum_congr
  intro s
  rw [Finset.prod_mul_distrib, Finset.prod_const, s.property]
  ring

theorem spectralCoeff_radius_top
    (lam : ℕ → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    : (FormalMultilinearSeries.ofScalars ℝ (spectralCoeff lam)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  have h := (spectralCoeff_hasSum lam hs (R : ℝ)).summable.norm
  simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
    Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg] using h

theorem spectralCoeff_one
    (lam : ℕ → ℝ /- [definition] -/ )
    : spectralCoeff lam 1 = ∑' i, lam i := by
  classical
  let e : ℕ ≃ {s : Finset ℕ // s.card = 1} := Equiv.ofBijective
    (fun i => ⟨{i}, Finset.card_singleton i⟩) (by
      constructor
      · intro i j hij
        have he := congrArg Subtype.val hij
        simpa using he
      · intro s
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp s.property
        exact ⟨i, Subtype.ext hi.symm⟩)
  have h := e.tsum_eq (fun s => ∏ i ∈ s.val, lam i)
  simpa [spectralCoeff, e] using h.symm

/-- Equality of the whole determinant function identifies the trace coefficient.
This does not assume the eigenvalue sum equals a kernel diagonal integral. -/
theorem trace_coefficient_of_product_bridge
    (c : ℕ → ℝ /- [definition] -/ )
    (hc : ∀ R : NNReal, Summable (fun n => ‖c n‖ * (R : ℝ) ^ n)  /- [standing] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    (hbridge : ∀ z : ℝ, (∑' n, c n * z ^ n) = ∏' i, (1 + z * lam i)  /- [standing] -/ )
    : c 1 = ∑' i, lam i := by
  let p := FormalMultilinearSeries.ofScalars ℝ c
  let q := FormalMultilinearSeries.ofScalars ℝ (spectralCoeff lam)
  have hrp : p.radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
    intro R
    simpa only [p, FormalMultilinearSeries.ofScalars_norm] using hc R
  have hrq : q.radius = ⊤ := spectralCoeff_radius_top lam hs
  have hp := p.hasFPowerSeriesOnBall (by rw [hrp]; exact ENNReal.zero_lt_top)
  have hq := q.hasFPowerSeriesOnBall (by rw [hrq]; exact ENNReal.zero_lt_top)
  have heq : p.sum = q.sum := by
    funext z
    rw [show p.sum z = ∑' n, c n * z ^ n from FormalMultilinearSeries.ofScalars_sum_eq c z,
      show q.sum z = ∑' n, spectralCoeff lam n * z ^ n from
        FormalMultilinearSeries.ofScalars_sum_eq (spectralCoeff lam) z,
      (spectralCoeff_hasSum lam hs z).tsum_eq, hbridge z]
  have hseries : p = q := by
    rw [heq] at hp
    exact hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hq.hasFPowerSeriesAt
  have hcoeff : c = spectralCoeff lam := FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ hseries
  rw [hcoeff, spectralCoeff_one]

/-- Logarithmic proof of the signed infinite-product upper bound. -/
theorem signed_tprod_le_exp_trace
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (hsum : Summable lam /- [standing] -/ )
    (hupper : ∀ i, lam i < 1 /- [standing] -/ )
    : (∏' i, (1 - lam i)) ≤ Real.exp (-(∑' i, lam i)) := by
  have hpos : ∀ i, 0 < 1 - lam i := fun i => sub_pos.mpr (hupper i)
  have hlog : Summable (fun i => Real.log (1 - lam i)) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hsum.neg
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  apply Real.exp_le_exp.mpr
  calc
    (∑' i, Real.log (1 - lam i)) ≤ ∑' i, -lam i := by
      apply hlog.tsum_le_tsum _ hsum.neg
      intro i
      have h := Real.log_le_sub_one_of_pos (hpos i)
      linarith
    _ = -(∑' i, lam i) := tsum_neg

theorem signed_tprod_le_one
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (hsum : Summable lam /- [standing] -/ )
    (hupper : ∀ i, lam i < 1 /- [standing] -/ )
    (htrace : 0 ≤ ∑' i, lam i /- [standing] -/ )
    : (∏' i, (1 - lam i)) ≤ 1 := by
  apply (signed_tprod_le_exp_trace lam hsum hupper).trans
  simpa using (Real.exp_le_exp.mpr (neg_nonpos.mpr htrace))

/-- Every infinite-product premise holds simultaneously, with mixed signs and
strictly positive trace on an infinite index set. -/
theorem signed_tprod_joint_probe :
    ∃ lam : ℕ → ℝ,
      Summable lam ∧ (∀ i, lam i < 1) ∧ 0 < ∑' i, lam i ∧
      (∃ i, lam i < 0) ∧ (∏' i, (1 - lam i)) = 5 / 8 := by
  let lam : ℕ → ℝ := fun i => if i = 0 then 1 / 2 else if i = 1 then -1 / 4 else 0
  have hz : ∀ i ∉ ({0, 1} : Finset ℕ), lam i = 0 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [lam, hi.1, hi.2]
  have hs : Summable lam := summable_of_ne_finset_zero hz
  have hu : ∀ i, lam i < 1 := by
    intro i
    simp only [lam]
    split_ifs <;> norm_num
  have ht : (∑' i, lam i) = 1 / 4 := by
    rw [tsum_eq_sum hz]
    norm_num [lam]
  have hp : (∏' i, (1 - lam i)) = 5 / 8 := by
    rw [tprod_eq_prod (s := {0, 1})]
    · norm_num [lam]
    · intro i hi
      rw [hz i hi]
      norm_num
  exact ⟨lam, hs, hu, by rw [ht]; norm_num, ⟨1, by norm_num [lam]⟩, hp⟩

/-- Generic determinant upper bound, with the trace sign placed on its proved
first coefficient rather than postulated on an unrelated eigenvalue list. -/
theorem series_le_one_of_product_bridge
    (c : ℕ → ℝ /- [definition] -/ )
    (hc : ∀ R : NNReal, Summable (fun n => ‖c n‖ * (R : ℝ) ^ n)  /- [standing] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    (hu : ∀ i, lam i < 1 /- [standing] -/ )
    (hbridge : ∀ z : ℝ, (∑' n, c n * z ^ n) = ∏' i, (1 + z * lam i)  /- [standing] -/ )
    (hc1 : 0 ≤ c 1 /- [standing] -/ )
    : (∑' n, c n * (-1 : ℝ) ^ n) ≤ 1 := by
  have ht : 0 ≤ ∑' i, lam i := by
    rw [← trace_coefficient_of_product_bridge c hc lam hs hbridge]
    exact hc1
  rw [hbridge (-1)]
  simp only [neg_one_mul, ← sub_eq_add_neg]
  exact signed_tprod_le_one lam hs hu ht

/-- Every premise of the coefficient-trace and upper-bound theorems is jointly
satisfiable, with an infinite index set, mixed signs, positive trace and D(-1)=5/8. -/
theorem determinant_bridge_joint_probe :
    ∃ (c : ℕ → ℝ) (lam : ℕ → ℝ),
      (∀ R : NNReal, Summable (fun n => ‖c n‖ * (R : ℝ) ^ n)) ∧
      Summable lam ∧ (∀ i, lam i < 1) ∧
      (∀ z : ℝ, (∑' n, c n * z ^ n) = ∏' i, (1 + z * lam i)) ∧
      0 < c 1 ∧ (∃ i, lam i < 0) ∧
      (∑' n, c n * (-1 : ℝ) ^ n) = 5 / 8 := by
  obtain ⟨lam, hs, hu, ht, hn, hprod⟩ := signed_tprod_joint_probe
  let c := spectralCoeff lam
  have hc : ∀ R : NNReal, Summable (fun n => ‖c n‖ * (R : ℝ) ^ n) := by
    intro R
    have h := (spectralCoeff_hasSum lam hs (R : ℝ)).summable.norm
    simpa only [c, norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg R.coe_nonneg] using h
  have hb : ∀ z : ℝ, (∑' n, c n * z ^ n) = ∏' i, (1 + z * lam i) :=
    fun z => (spectralCoeff_hasSum lam hs z).tsum_eq
  have hc1 : 0 < c 1 := by
    dsimp [c]
    rw [spectralCoeff_one]
    exact ht
  refine ⟨c, lam, hc, hs, hu, hb, hc1, hn, ?_⟩
  calc
    (∑' n, c n * (-1 : ℝ) ^ n) = ∏' i, (1 - lam i) := by
      simpa only [neg_one_mul, sub_eq_add_neg] using hb (-1)
    _ = 5 / 8 := hprod

/-- Equality only at the physical coupling does not identify the trace.
This is a counterinstance to a generic bridge weakening, not to the Airy kernel. -/
theorem single_coupling_does_not_identify_trace :
    ∃ c lam : ℕ → ℝ,
      (∀ R : NNReal, Summable (fun n => ‖c n‖ * (R : ℝ) ^ n)) ∧
      Summable lam ∧ (∀ i, |lam i| < 1) ∧
      (∑' n, c n * (-1 : ℝ) ^ n) = (∏' i, (1 - lam i)) ∧
      c 1 ≠ ∑' i, lam i := by
  let c : ℕ → ℝ := fun n => if n = 0 ∨ n = 1 ∨ n = 2 then 1 else 0
  let lam : ℕ → ℝ := fun _ => 0
  have hz : ∀ n ∉ ({0, 1, 2} : Finset ℕ), c n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [c, hn]
  refine ⟨c, lam, ?_, ?_, ?_, ?_, ?_⟩
  · intro R
    exact summable_of_ne_finset_zero (s := {0, 1, 2}) (fun n hn => by rw [hz n hn]; simp)
  · exact summable_zero
  · intro i
    norm_num [lam]
  · rw [tsum_eq_sum (s := {0, 1, 2}) (fun n hn => by rw [hz n hn]; simp)]
    norm_num [c, lam]
  · norm_num [c, lam]


/-- The first Fredholm coefficient is the ordinary diagonal integral. -/
theorem kernelCoefficient_one
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/ )
    : kernelCoefficient μ k 1 = ∫ x, k x x ∂μ := by
  unfold kernelCoefficient kernelMinor
  simp only [Nat.factorial_one, Nat.cast_one, div_one, Matrix.det_unique]
  exact (measurePreserving_funUnique μ (Fin 1)).integral_comp' (fun x => k x x)

/-- A genuine eigenvector supplies the upper spectral bound from the operator norm. -/
theorem eigenvalue_lt_one_of_norm
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [NormedSpace ℝ E /- [definition] -/ ]
    (T : E →L[ℝ] E /- [definition] -/ )
    (lam : ℝ /- [definition] -/ )
    (v : E /- [definition] -/ )
    (hv : v ≠ 0 /- [standing] -/ )
    (he : T v = lam • v /- [standing] -/ )
    (hn : ‖T‖ < 1 /- [standing] -/ )
    : lam < 1 := by
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h : |lam| * ‖v‖ ≤ ‖T‖ * ‖v‖ := by
    simpa only [he, norm_smul, Real.norm_eq_abs] using T.le_opNorm v
  have hl : |lam| ≤ ‖T‖ := le_of_mul_le_mul_right h hp
  exact (le_abs_self lam).trans_lt (hl.trans_lt hn)

theorem eigenvalue_norm_joint_probe :
    ∃ (T : ℝ →L[ℝ] ℝ) (lam v : ℝ),
      v ≠ 0 ∧ T v = lam • v ∧ ‖T‖ < 1 ∧ lam < 0 := by
  refine ⟨(-1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ, -1 / 2, 1, ?_, ?_, ?_, ?_⟩
  · norm_num
  · simp
  · simp [norm_smul]
    norm_num
  · norm_num

/-- Explicit joint inhabitant for every derivative and boundary premise of the
energy lemmas: the actual Airy tail, with a strictly positive value at zero. -/
theorem airy_tail_energy_joint_probe :
    ∃ f f1 f2 : ℝ → ℝ,
      (∀ x, HasDerivAt f (f1 x) x) ∧
      (∀ x, HasDerivAt f1 (f2 x) x) ∧
      (∀ x, HasDerivAt f2 (x * f1 x) x) ∧
      Tendsto (tailEnergy f f1 f2) atTop (𝓝 0) ∧
      (∀ x, 0 ≤ x → 0 < f x) ∧ 0 < f 0 ∧
      Continuous f ∧
      (∀ x, HasDerivAt (tailEnergy f f1 f2) (-(f x) ^ 2 / 2) x) ∧
      (∀ x, f x = 0 → tailEnergy f f1 f2 x ≤ 0) := by
  let f := airyTailIntegral RMTFoundations.Airy.airyAiReal
  let f1 : ℝ → ℝ := fun x => -RMTFoundations.Airy.airyAiReal x
  let f2 : ℝ → ℝ := fun x => -deriv RMTFoundations.Airy.airyAiReal x
  have hi := exp_bound_integrable_Ioi RMTFoundations.Airy.airyAiReal Ai_continuous Ai_halfline_exp_bound
  have h1 : ∀ x, HasDerivAt f (f1 x) x := hasDerivAt_airyTailIntegral RMTFoundations.Airy.airyAiReal Ai_continuous hi
  have h2 : ∀ x, HasDerivAt f1 (f2 x) x := fun x => (Ai_ODE_joint_probe.1 x).neg
  have h3 : ∀ x, HasDerivAt f2 (x * f1 x) x := by
    intro x
    convert! (Ai_ODE_joint_probe.2.1 x).neg using 1 <;> simp only [f1, f2, mul_neg]
  have hp : ∀ x, 0 ≤ x → 0 < f x := airyTailIntegral_pos_of_nonneg RMTFoundations.Airy.airyAiReal hi
    (fun x hx => airyAiReal_pos_of_nonneg hx)
  obtain ⟨C, hC, hbound⟩ := Ai_halfline_exp_bound 0
  have hAt : Tendsto RMTFoundations.Airy.airyAiReal atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ => C * Real.exp (-x))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simpa only [Real.norm_eq_abs] using hbound x hx
    · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  have hA1t : Tendsto (deriv RMTFoundations.Airy.airyAiReal) atTop (𝓝 (limUnder atTop (deriv RMTFoundations.Airy.airyAiReal))) :=
    tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun x _ => Ai_ODE_joint_probe.2.1 x)
      (linear_mul_exp_bound_integrable RMTFoundations.Airy.airyAiReal Ai_continuous C hC.le hbound)
  have ht : Tendsto f atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  have hwt := airyTailIntegral_weighted_tendsto RMTFoundations.Airy.airyAiReal hi C hbound
  have he : Tendsto (tailEnergy f f1 f2) atTop (𝓝 0) := by
    have hprod := ht.mul hA1t.neg
    have hsq := hAt.neg.pow 2
    have hw := hwt.mul ht
    have h := (hprod.sub (hsq.div_const 2)).sub (hw.div_const 2)
    have heq : tailEnergy f f1 f2 = fun x =>
        f x * -deriv RMTFoundations.Airy.airyAiReal x - (-RMTFoundations.Airy.airyAiReal x) ^ 2 / 2 - x * f x * f x / 2 := by
      funext x
      dsimp only [tailEnergy, f1, f2]
      ring
    rw [heq]
    simpa only [f, zero_mul, mul_zero, neg_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, sub_zero] using h
  refine ⟨f, f1, f2, h1, h2, h3, he, hp, hp 0 le_rfl,
    (show Differentiable ℝ f from fun x => (h1 x).differentiableAt).continuous,
    hasDerivAt_tailEnergy f f1 f2 h1 h2 h3, ?_⟩
  intro x hx
  dsimp only [tailEnergy]
  rw [hx]
  nlinarith [sq_nonneg (f1 x)]

/-- The spectral trace is identified by the determinant-function bridge.
The diagonal trace is a proved conclusion, not an additional premise. -/
theorem B_spectral_trace_of_product_bridge
    (s : ℝ /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hsum : Summable lam /- [standing] -/ )
    (hbridge : ∀ z : ℝ,
      (kernelFredholm RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s)) (z : ℂ)).re =
        ∏' i, (1 + z * lam i)  /- [standing] -/ )
    : (∑' i, lam i) = (∫ x, RMTFoundations.Airy.airyAiReal (x + x + s) ∂ RMTFoundations.Airy.halfLineMeasure) := by
  have hc : ∀ R : NNReal, Summable (fun n =>
      ‖kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s)) n‖ * (R : ℝ) ^ n) := by
    intro R
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg R.coe_nonneg] using B_physical_fredholm_absolute s ((R : ℝ) : ℂ)
  have hb : ∀ z : ℝ,
      (∑' n, kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s)) n * z ^ n) =
        ∏' i, (1 + z * lam i) := by
    intro z
    simpa only [kernelFredholm_real_coupling, Complex.ofReal_re] using hbridge z
  have h := trace_coefficient_of_product_bridge
    (kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s))) hc lam hsum hb
  rw [kernelCoefficient_one] at h
  exact h.symm

/-- Upper bound under the exact all-coupling product bridge for an absolutely
summable real eigenvalue enumeration of the physical operator and a strict
operator contraction. Every remaining premise is displayed; no trace sign,
Airy-tail sign, determinant bound, or monotonicity is assumed. -/
theorem TW1R_le_one_of_eigenvalue_product_bridge
    (s : ℝ /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (v : ℕ → Lp ℝ 2 RMTFoundations.Airy.halfLineMeasure /- [definition] -/ )
    (hsum : Summable lam /- [standing] -/ )
    (hv : ∀ i, v i ≠ 0 /- [standing] -/ )
    (heigen : ∀ i, RMTFoundations.Airy.airyHankelShift s (v i) = lam i • v i /- [standing] -/ )
    (hbridge : ∀ z : ℝ,
      (kernelFredholm RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s)) (z : ℂ)).re =
        ∏' i, (1 + z * lam i)  /- [standing] -/ )
    (hnorm : ‖RMTFoundations.Airy.airyHankelShift s‖ < 1 /- [standing] -/ )
    : (TW1 s).re ≤ 1 := by
  have hu : ∀ i, lam i < 1 := fun i =>
    eigenvalue_lt_one_of_norm (RMTFoundations.Airy.airyHankelShift s) (lam i) (v i) (hv i) (heigen i) hnorm
  have ht : 0 ≤ ∑' i, lam i := by
    rw [B_spectral_trace_of_product_bridge s lam hsum hbridge]
    exact (B_diagonal_integral_positive s).le
  have hb := hbridge (-1)
  have he : (TW1 s).re = ∏' i, (1 - lam i) := by
    simpa only [TW1, B_fredholm_physical, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul,
      sub_eq_add_neg] using hb
  rw [he]
  exact signed_tprod_le_one lam hsum hu ht

/-- The inverse of a strict real contraction has a nonnegative quadratic form.
Symmetry of the contraction is not needed for this assertion. -/
theorem contraction_resolvent_inner_nonneg
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (B R : E →L[ℝ] E /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (hR : ∀ x, R x - B (R x) = x /- [standing] -/ )
    (g : E /- [definition] -/ )
    : 0 ≤ inner ℝ g (R g) := by
  have hcs : inner ℝ (B (R g)) (R g) ≤ ‖B‖ * ‖R g‖^2 := by
    calc
      inner ℝ (B (R g)) (R g) ≤ ‖B (R g)‖ * ‖R g‖ := real_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖R g‖) * ‖R g‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm (R g)) (norm_nonneg _)
      _ = ‖B‖ * ‖R g‖^2 := by ring
  have hid : inner ℝ g (R g) = ‖R g‖^2 - inner ℝ (B (R g)) (R g) := by
    calc
      inner ℝ g (R g) = inner ℝ (R g - B (R g)) (R g) :=
        congrArg (fun x => inner ℝ x (R g)) (hR g).symm
      _ = ‖R g‖^2 - inner ℝ (B (R g)) (R g) := by
        rw [inner_sub_left, real_inner_self_eq_norm_sq]
  rw [hid]
  nlinarith [sq_nonneg ‖R g‖]

/-- Positive remainder behind the first polynomial resolvent bound. -/
theorem contraction_resolvent_polynomial_lower
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (B R : E →L[ℝ] E /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (hsym : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)  /- [standing] -/ )
    (hright : ∀ x, R x - B (R x) = x /- [standing] -/ )
    (hleft : ∀ x, R (x - B x) = x /- [standing] -/ )
    (g : E /- [definition] -/ )
    : inner ℝ g g + inner ℝ g (B g) ≤ inner ℝ g (R g) := by
  have hcomm (x : E) : R (B x) = B (R x) := by
    have hl := hleft x
    rw [map_sub] at hl
    have he : R x - R (B x) = R x - B (R x) := hl.trans (hright x).symm
    have hz : R (B x) - B (R x) = 0 := by
      calc
        R (B x) - B (R x) = (R x - B (R x)) - (R x - R (B x)) := by abel
        _ = 0 := by rw [hright x, hl]; simp
    exact sub_eq_zero.mp hz
  have hid : R g = g + B g + B (R (B g)) := by
    have h1 : R g = g + B (R g) := sub_eq_iff_eq_add.mp (hright g)
    have h2 : B (R g) = B g + B (B (R g)) := by
      conv_lhs => rw [h1]
      rw [map_add]
    calc
      R g = g + B (R g) := h1
      _ = g + (B g + B (B (R g))) := congrArg (fun x => g + x) h2
      _ = g + B g + B (R (B g)) := by rw [hcomm]; abel
  have hn := contraction_resolvent_inner_nonneg B R hB hright (B g)
  have he : inner ℝ g (R g) = inner ℝ g g + inner ℝ g (B g) +
      inner ℝ (B g) (R (B g)) := by
    rw [hid, inner_add_right, inner_add_right, ← hsym g (R (B g))]
  rw [he]
  linarith

/-- All operator-estimate premises are jointly satisfiable on a nonzero Hilbert
space, with a nonzero negative contraction and its exact inverse. -/
theorem contraction_resolvent_joint_probe :
    ∃ B R : ℝ →L[ℝ] ℝ,
      ‖B‖ < 1 ∧ (∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) ∧
      (∀ x, R x - B (R x) = x) ∧ (∀ x, R (x - B x) = x) ∧
      B 1 = -1 / 2 ∧ R 1 = 2 / 3 ∧
      inner ℝ (1 : ℝ) 1 + inner ℝ (1 : ℝ) (B 1) < inner ℝ (1 : ℝ) (R 1) := by
  let B : ℝ →L[ℝ] ℝ := (-1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  let R : ℝ →L[ℝ] ℝ := (2 / 3 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  refine ⟨B, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [B, norm_smul, ContinuousLinearMap.norm_id]
  · intro x y
    simp [B, mul_assoc]
    ring
  · intro x
    simp [B, R]
    ring
  · intro x
    simp [B, R]
    ring
  · norm_num [B]
  · norm_num [R]
  · norm_num [B, R]

/-- Completing a square in the inverse quadratic form, without assuming a
positive contraction. This is a Conditional operator lemma. -/
theorem resolvent_variational_lower
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (B R : E →L[ℝ] E /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (hsym : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)  /- [standing] -/ )
    (hright : ∀ x, R x - B (R x) = x /- [standing] -/ )
    (hleft : ∀ x, R (x - B x) = x /- [standing] -/ )
    (g : E /- [definition] -/ )
    (t : ℝ /- [definition] -/ )
    : 2 * t * inner ℝ g g - t^2 * (inner ℝ g g - inner ℝ g (B g)) ≤
        inner ℝ g (R g) := by
  let v := g - t • (g - B g)
  have hRv : R v = R g - t • g := by
    simp only [v, map_sub, map_smul, hleft]
  have hc : inner ℝ (g - B g) (R g) = inner ℝ g g := by
    rw [inner_sub_left, hsym]
    rw [← inner_sub_right, hright]
  have hd : inner ℝ (g - B g) g = inner ℝ g g - inner ℝ g (B g) := by
    rw [inner_sub_left, real_inner_comm (B g) g]
  have hn := contraction_resolvent_inner_nonneg B R hB hright v
  rw [hRv] at hn
  simp only [v, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hc, hd] at hn
  nlinarith

/-- The variational bound is optimized at the Rayleigh quotient. Its positive
denominator follows from strict contraction and a nonzero vector. -/
theorem contraction_resolvent_tangent_lower
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (B R : E →L[ℝ] E /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (hsym : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)  /- [standing] -/ )
    (hright : ∀ x, R x - B (R x) = x /- [standing] -/ )
    (hleft : ∀ x, R (x - B x) = x /- [standing] -/ )
    (g : E /- [definition] -/ )
    (hg : g ≠ 0 /- [standing] -/ )
    : 0 < inner ℝ g g - inner ℝ g (B g) ∧
      (inner ℝ g g)^2 / (inner ℝ g g - inner ℝ g (B g)) ≤ inner ℝ g (R g) := by
  have hc : inner ℝ g (B g) ≤ ‖B‖ * ‖g‖^2 := by
    calc
      inner ℝ g (B g) ≤ ‖g‖ * ‖B g‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * (‖B‖ * ‖g‖) :=
        mul_le_mul_of_nonneg_left (B.le_opNorm g) (norm_nonneg _)
      _ = ‖B‖ * ‖g‖^2 := by ring
  have hn : 0 < ‖g‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hd : 0 < inner ℝ g g - inner ℝ g (B g) := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [mul_pos (sub_pos.mpr hB) hn]
  refine ⟨hd, ?_⟩
  have hv := resolvent_variational_lower B R hB hsym hright hleft g
    (inner ℝ g g / (inner ℝ g g - inner ℝ g (B g)))
  have he : 2 * (inner ℝ g g / (inner ℝ g g - inner ℝ g (B g))) * inner ℝ g g -
      (inner ℝ g g / (inner ℝ g g - inner ℝ g (B g)))^2 *
        (inner ℝ g g - inner ℝ g (B g)) =
      (inner ℝ g g)^2 / (inner ℝ g g - inner ℝ g (B g)) := by
    field_simp
    <;> ring
  rwa [he] at hv

/-- Exact parity decomposition of the resolvent. In the Airy application the
two terms are u(s) and q(s)-RMTFoundations.Airy.airyAiReal(s). No sign of q is asserted here. -/
theorem resolvent_parity_identity
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [NormedSpace ℝ E /- [definition] -/ ]
    (B R S : E →L[ℝ] E /- [definition] -/ )
    (hleft : ∀ x, R (x - B x) = x /- [standing] -/ )
    (hS : ∀ x, S x - B (B (S x)) = x /- [standing] -/ )
    (g : E /- [definition] -/ )
    : R g = S g + B (S g) := by
  have he : (S g + B (S g)) - B (S g + B (S g)) = g := by
    rw [map_add]
    calc
      S g + B (S g) - (B (S g) + B (B (S g))) =
          S g - B (B (S g)) := by abel
      _ = g := hS g
  have hl := hleft (S g + B (S g))
  rwa [he] at hl

/-- All premises of the new bounds and parity identity hold simultaneously
on a nonzero space with a negative contraction and genuine inverses. -/
theorem tangent_parity_joint_probe :
    ∃ B R S : ℝ →L[ℝ] ℝ, ∃ g t : ℝ,
      ‖B‖ < 1 ∧ (∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) ∧
      (∀ x, R x - B (R x) = x) ∧ (∀ x, R (x - B x) = x) ∧
      (∀ x, S x - B (B (S x)) = x) ∧ g ≠ 0 ∧ t ≠ 0 ∧
      B g < 0 ∧ R g = S g + B (S g) ∧
      (inner ℝ g g)^2 / (inner ℝ g g - inner ℝ g (B g)) = inner ℝ g (R g) := by
  let B : ℝ →L[ℝ] ℝ := (-1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  let R : ℝ →L[ℝ] ℝ := (2 / 3 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  let S : ℝ →L[ℝ] ℝ := (4 / 3 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  refine ⟨B, R, S, 1, 2 / 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [B, norm_smul, ContinuousLinearMap.norm_id]
  · intro x y
    simp [B, mul_assoc]
    ring
  · intro x
    simp [B, R]
    ring
  · intro x
    simp [B, R]
    ring
  · intro x
    simp [B, S]
    ring
  · norm_num
  · norm_num
  · norm_num [B]
  · norm_num [B, R, S]
  · norm_num [B, R]

/-- A strict symmetric contraction does not force the sign of an arbitrary
boundary term a+<g,Rg>. This forbids a model-free monotonicity completion. -/
theorem boundary_sign_counterprobe :
    ∃ B R : ℝ →L[ℝ] ℝ, ∃ a g : ℝ,
      ‖B‖ < 1 ∧ (∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) ∧
      (∀ x, R x - B (R x) = x) ∧ (∀ x, R (x - B x) = x) ∧
      g ≠ 0 ∧ a + inner ℝ g (R g) < 0 := by
  let B : ℝ →L[ℝ] ℝ := (-1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  let R : ℝ →L[ℝ] ℝ := (2 / 3 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  refine ⟨B, R, -3 / 4, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [B, norm_smul, ContinuousLinearMap.norm_id]
  · intro x y
    simp [B, mul_assoc]
    ring
  · intro x
    simp [B, R]
    ring
  · intro x
    simp [B, R]
    ring
  · norm_num
  · norm_num [B, R]

/-- A universal half-norm bound, also valid at the zero vector. It connects
the far-left Airy energy certificate to a boundary resolvent once the genuine
Airy vector norm is identified with the energy. -/
theorem contraction_resolvent_half_norm_lower
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (B R : E →L[ℝ] E /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (hsym : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)  /- [standing] -/ )
    (hright : ∀ x, R x - B (R x) = x /- [standing] -/ )
    (hleft : ∀ x, R (x - B x) = x /- [standing] -/ )
    (g : E /- [definition] -/ )
    : inner ℝ g g / 2 ≤ inner ℝ g (R g) := by
  have hc : -inner ℝ g (B g) ≤ ‖B‖ * ‖g‖^2 := by
    calc
      -inner ℝ g (B g) = inner ℝ (-g) (B g) := by simp
      _ ≤ ‖-g‖ * ‖B g‖ := real_inner_le_norm _ _
      _ = ‖g‖ * ‖B g‖ := by rw [norm_neg]
      _ ≤ ‖g‖ * (‖B‖ * ‖g‖) :=
        mul_le_mul_of_nonneg_left (B.le_opNorm g) (norm_nonneg _)
      _ = ‖B‖ * ‖g‖^2 := by ring
  have hn : 0 ≤ inner ℝ g g + inner ℝ g (B g) := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hB.le) (sq_nonneg ‖g‖)]
  have hv := resolvent_variational_lower B R hB hsym hright hleft g (1/2)
  nlinarith

/-- Exact gain of the optimized certificate over its first-order polynomial. -/
theorem tangent_polynomial_gap
    (k m : ℝ /- [definition] -/ )
    (hd : 0 < k - m /- [standing] -/ )
    : k^2 / (k-m) - (k+m) = m^2 / (k-m) ∧ k+m ≤ k^2 / (k-m) := by
  have he : k^2 / (k-m) - (k+m) = m^2 / (k-m) := by
    field_simp
    <;> ring
  refine ⟨he, ?_⟩
  have hn : 0 ≤ m^2 / (k-m) := div_nonneg (sq_nonneg m) hd.le
  linarith

/-- Nondegenerate sharp certificate example: its boundary term is negative,
the polynomial fails, and the optimized lower bound succeeds. -/
theorem tangent_gap_joint_probe :
    ∃ k m a : ℝ, 0 < k ∧ m < 0 ∧ 0 < k-m ∧ a < 0 ∧
      a+k+m < 0 ∧ 0 < a+k^2/(k-m) := by
  exact ⟨1, -1/2, -3/5, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩


open MeasureTheory Set Filter
open scoped Topology

/-- Calculus part of Ferrari-Spohn Lemma 2. For a symmetric smooth kernel,
f(x)=A(x,x) and d(x)=partial_x A(x,x) obey f'=2d. The kernel-to-operator
trace identification and these smoothness premises must be proved at each
application; this Conditional lemma imports none of them. -/
theorem boundary_trace_from_diagonal_derivative
    (f d : ℝ → ℝ /- [definition] -/ )
    (hc : ContinuousWithinAt f (Ici 0) 0 /- [standing] -/ )
    (hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (2 * d x) x /- [standing] -/ )
    (hi : IntegrableOn d (Ioi 0)  /- [standing] -/ )
    (ht : Tendsto f atTop (𝓝 0)  /- [standing] -/ )
    : (∫ x in Ioi (0 : ℝ), d x) = -f 0 / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc hd (hi.const_mul 2) ht
  rw [integral_const_mul] at h
  linarith

/-- All calculus premises hold together for the nonzero diagonal of the
symmetric Hankel kernel exp(-(x+y)/2); its x-derivative is d(x). -/
theorem boundary_trace_joint_probe :
    ∃ f d : ℝ → ℝ,
      ContinuousWithinAt f (Ici 0) 0 ∧
      (∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (2 * d x) x) ∧
      IntegrableOn d (Ioi 0) ∧ Tendsto f atTop (𝓝 0) ∧ f 0 = 1 ∧
      (∀ x, f x = Real.exp (-(x+x)/2)) ∧
      (∀ x, d x = -Real.exp (-(x+x)/2) / 2) ∧
      (∫ x in Ioi (0 : ℝ), d x) = -1 / 2 := by
  let f : ℝ → ℝ := fun x => Real.exp (-x)
  let d : ℝ → ℝ := fun x => -Real.exp (-x) / 2
  have hc : ContinuousWithinAt f (Ici 0) 0 :=
    (Real.continuous_exp.comp continuous_neg).continuousWithinAt
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (2 * d x) x := by
    intro x _
    have h : HasDerivAt f (-Real.exp (-x)) x := by
      simpa [f] using ((hasDerivAt_id x).neg).exp
    convert h using 1
    dsimp [d]
    ring
  have hi : IntegrableOn d (Ioi 0) := (integrableOn_exp_neg_Ioi 0).neg.div_const 2
  have ht : Tendsto f atTop (𝓝 0) := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  refine ⟨f, d, hc, hd, hi, ht, ?_, ?_, ?_, ?_⟩
  · simp [f]
  · intro x
    dsimp [f]
    congr 1
    ring
  · intro x
    dsimp [d]
    congr 2
    ring
  · simpa [f] using boundary_trace_from_diagonal_derivative f d hc hd hi ht

/-- Actual physical Airy diagonal trace derivative. The factor 1/2 is derived
from the kernel normalization, with no determinant differential hypothesis. -/
theorem hasDerivAt_B_diagonal_trace
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (fun t : ℝ => ∫ x in Set.Ioi (0 : ℝ), RMTFoundations.Airy.airyAiReal (x + x + t))
      (-RMTFoundations.Airy.airyAiReal s / 2) s := by
  have hi : ∀ a, IntegrableOn RMTFoundations.Airy.airyAiReal (Set.Ioi a) :=
    exp_bound_integrable_Ioi RMTFoundations.Airy.airyAiReal Ai_continuous Ai_halfline_exp_bound
  have hd := (hasDerivAt_airyTailIntegral RMTFoundations.Airy.airyAiReal Ai_continuous hi s).div_const 2
  have he : (fun t : ℝ => ∫ x in Set.Ioi (0 : ℝ), RMTFoundations.Airy.airyAiReal (x + x + t)) =
      fun t => airyTailIntegral RMTFoundations.Airy.airyAiReal t / 2 := by
    funext t
    exact halfline_diagonal_integral RMTFoundations.Airy.airyAiReal t
  rw [he]
  exact hd

/-- A scalar ODE energy derivative that fixes the boundary value of the Airy
square kernel. It is independent of Fredholm determinant differentiation. -/
theorem hasDerivAt_Airy_square_energy
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (fun t : ℝ => (deriv RMTFoundations.Airy.airyAiReal t)^2 - t * (RMTFoundations.Airy.airyAiReal t)^2) (-(RMTFoundations.Airy.airyAiReal s)^2) s := by
  have ha := Ai_ODE_joint_probe.1 s
  have hap := Ai_ODE_joint_probe.2.1 s
  convert! (hap.mul hap).sub ((hasDerivAt_id s).mul (ha.mul ha)) using 1 <;>
    (try funext t) <;>
    (try simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, pow_two, id_eq]) <;> ring

/-- An elementary energy sign certificate. No special-function premise is
hidden in the scalar inequality. -/
theorem scalar_oscillator_energy_sign
    (a p s : ℝ /- [definition] -/ )
    (hs : s < 0 /- [standing] -/ )
    (ht : 4 ≤ (-s) * (p^2 - s * a^2)  /- [standing] -/ )
    : 0 ≤ a + (p^2 - s * a^2) / 2 := by
  let e := p^2 - s * a^2
  have he : 0 ≤ e := by dsimp [e]; nlinarith [sq_nonneg p, sq_nonneg a]
  have hb : (-s) * a^2 ≤ e := by dsimp [e]; nlinarith [sq_nonneg p]
  have hsq : (2*a)^2 ≤ e^2 := by
    calc
      (2*a)^2 = 4*a^2 := by ring
      _ ≤ ((-s)*e)*a^2 := mul_le_mul_of_nonneg_right ht (sq_nonneg a)
      _ = e*((-s)*a^2) := by ring
      _ ≤ e*e := mul_le_mul_of_nonneg_left hb he
      _ = e^2 := by ring
  have ha : |2*a| ≤ e := (sq_le_sq₀ (abs_nonneg (2*a)) he).mp
    (by simpa only [sq_abs] using hsq)
  have hneg : -(2*a) ≤ |2*a| := neg_le_abs (2*a)
  dsimp [e] at ha
  linarith

/-- The actual Airy energy is antitone on the whole line. -/
theorem Airy_square_energy_antitone :
    Antitone (fun s : ℝ => (deriv RMTFoundations.Airy.airyAiReal s)^2 - s * (RMTFoundations.Airy.airyAiReal s)^2) := by
  apply antitone_of_hasDerivAt_nonpos hasDerivAt_Airy_square_energy
  intro s
  exact neg_nonpos.mpr (sq_nonneg (RMTFoundations.Airy.airyAiReal s))

/-- A proved Airy boundary polynomial sign outside a compact window. The
remaining interval is [-4/RMTFoundations.Airy.airyAiReal'(0)^2,0]; this is not a global sign certificate. -/
theorem Airy_boundary_energy_nonneg_far_left
    (s : ℝ /- [definition] -/ )
    (hs : s ≤ -4 / (deriv RMTFoundations.Airy.airyAiReal 0)^2 /- [standing] -/ )
    : 0 ≤ RMTFoundations.Airy.airyAiReal s + ((deriv RMTFoundations.Airy.airyAiReal s)^2 - s * (RMTFoundations.Airy.airyAiReal s)^2) / 2 := by
  have hp : 0 < (deriv RMTFoundations.Airy.airyAiReal 0)^2 := by
    apply sq_pos_of_ne_zero
    exact ne_of_lt deriv_airyAiReal_zero_neg
  have ht : -4 / (deriv RMTFoundations.Airy.airyAiReal 0)^2 < 0 := div_neg_of_neg_of_pos (by norm_num) hp
  have hs0 : s < 0 := hs.trans_lt ht
  have hc : 4 ≤ (-s) * (deriv RMTFoundations.Airy.airyAiReal 0)^2 := by
    have h := (le_div_iff₀ hp).mp hs
    nlinarith
  have he : (deriv RMTFoundations.Airy.airyAiReal 0)^2 ≤ (deriv RMTFoundations.Airy.airyAiReal s)^2 - s * (RMTFoundations.Airy.airyAiReal s)^2 := by
    simpa using Airy_square_energy_antitone hs0.le
  apply scalar_oscillator_energy_sign (RMTFoundations.Airy.airyAiReal s) (deriv RMTFoundations.Airy.airyAiReal s) s hs0
  exact hc.trans (mul_le_mul_of_nonneg_left he (by linarith))

/-- Actual RMTFoundations.Airy.airyAiReal and a strictly interior far-left shift simultaneously satisfy
the nondegenerate ODE/energy certificate premises. -/
theorem Airy_far_left_joint_probe :
    ∃ s : ℝ, s < -4 / (deriv RMTFoundations.Airy.airyAiReal 0)^2 ∧ s < 0 ∧
      0 < (deriv RMTFoundations.Airy.airyAiReal s)^2 - s * (RMTFoundations.Airy.airyAiReal s)^2 ∧
      4 ≤ (-s)*((deriv RMTFoundations.Airy.airyAiReal s)^2 - s*(RMTFoundations.Airy.airyAiReal s)^2) ∧
      0 ≤ RMTFoundations.Airy.airyAiReal s + ((deriv RMTFoundations.Airy.airyAiReal s)^2 - s*(RMTFoundations.Airy.airyAiReal s)^2)/2 := by
  have hp : 0 < (deriv RMTFoundations.Airy.airyAiReal 0)^2 := sq_pos_of_ne_zero (ne_of_lt deriv_airyAiReal_zero_neg)
  let s := -4 / (deriv RMTFoundations.Airy.airyAiReal 0)^2 - 1
  have hs : s < -4 / (deriv RMTFoundations.Airy.airyAiReal 0)^2 := by dsimp [s]; linarith
  have hs0 : s < 0 := hs.trans (div_neg_of_neg_of_pos (by norm_num) hp)
  have he : (deriv RMTFoundations.Airy.airyAiReal 0)^2 ≤ (deriv RMTFoundations.Airy.airyAiReal s)^2 - s*(RMTFoundations.Airy.airyAiReal s)^2 := by
    simpa using Airy_square_energy_antitone hs0.le
  have hc : 4 ≤ (-s)*(deriv RMTFoundations.Airy.airyAiReal 0)^2 := by
    have h := (le_div_iff₀ hp).mp hs.le
    nlinarith
  exact ⟨s, hs, hs0, hp.trans_le he,
    hc.trans (mul_le_mul_of_nonneg_left he (by linarith)),
    Airy_boundary_energy_nonneg_far_left s hs.le⟩

/-- The scalar energy certificate permits a negative Airy-like boundary
value and nonzero derivative; all of its binders have a common witness. -/
theorem scalar_energy_joint_probe :
    ∃ a p s : ℝ, a < 0 ∧ p ≠ 0 ∧ s < 0 ∧
      4 ≤ (-s)*(p^2-s*a^2) ∧ 0 < a+(p^2-s*a^2)/2 := by
  exact ⟨-1, 1, -4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The Airy boundary resolvent is positive on the nonnegative half-line,
using the actual RMTFoundations.Airy.airyAiReal positivity theorem. This does not prove its negative
half-line sign or its equality to the TW1 logarithmic derivative. -/
theorem Airy_boundary_positive_of_nonneg_shift
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (B R : E →L[ℝ] E /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (hR : ∀ x, R x - B (R x) = x /- [standing] -/ )
    (g : E /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (hs : 0 ≤ s /- [standing] -/ )
    : 0 < RMTFoundations.Airy.airyAiReal s + inner ℝ g (R g) := by
  have ha : 0 < RMTFoundations.Airy.airyAiReal s := airyAiReal_pos_of_nonneg hs
  exact add_pos_of_pos_of_nonneg ha (contraction_resolvent_inner_nonneg B R hB hR g)

/-- All physical trace/ODE parameters use the actual RMTFoundations.Airy.airyAiReal. All additional
operator premises in the half-line sign lemma hold jointly and nontrivially. -/
theorem physical_boundary_joint_probe :
    ∃ B R : ℝ →L[ℝ] ℝ, ∃ g s : ℝ,
      ‖B‖ < 1 ∧ (∀ x, R x - B (R x) = x) ∧ g ≠ 0 ∧ 0 ≤ s ∧
      RMTFoundations.Airy.airyAiReal s ≠ 0 ∧ 0 < RMTFoundations.Airy.airyAiReal s + inner ℝ g (R g) ∧
      HasDerivAt (fun t : ℝ => ∫ x in Set.Ioi (0 : ℝ), RMTFoundations.Airy.airyAiReal (x + x + t)) (-RMTFoundations.Airy.airyAiReal s / 2) s ∧
      HasDerivAt (fun t : ℝ => (deriv RMTFoundations.Airy.airyAiReal t)^2 - t * (RMTFoundations.Airy.airyAiReal t)^2) (-(RMTFoundations.Airy.airyAiReal s)^2) s := by
  let B : ℝ →L[ℝ] ℝ := (-1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  let R : ℝ →L[ℝ] ℝ := (2 / 3 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hB : ‖B‖ < 1 := by norm_num [B, norm_smul, ContinuousLinearMap.norm_id]
  have hR : ∀ x, R x - B (R x) = x := by
    intro x
    simp [B, R]
    ring
  refine ⟨B, R, 1, 0, hB, hR, by norm_num, by norm_num, ?_, ?_,
    hasDerivAt_B_diagonal_trace 0, hasDerivAt_Airy_square_energy 0⟩
  · exact airyAiReal_zero_pos.ne'
  · exact Airy_boundary_positive_of_nonneg_shift B R hB hR 1 0 (by norm_num)



open MeasureTheory Set Filter
open scoped Topology ENNReal InnerProductSpace
open RMTFoundations.Fredholm RMTFoundations.Airy

/-- The actual L² boundary row of the Airy Hankel operator. -/
noncomputable def airyBoundaryVector (s : ℝ /- [definition] -/ )
    : Lp ℝ 2 halfLineMeasure := sliceLp halfLineMeasure (airyHankelShiftKernel s) 0

/-- Boundary evaluation is realized as an L² vector, without a delta vector. -/
theorem airyBoundaryVector_apply_ae (s : ℝ /- [definition] -/ )
    : airyBoundaryVector s =ᵐ[halfLineMeasure] fun x => airyAiReal (s+x) := by
  filter_upwards [sliceLp_apply_ae (memLp_airyHankelShiftSlice s 0)] with x hx
  change (sliceLp halfLineMeasure (airyHankelShiftKernel s) 0) x = airyAiReal (s+x)
  rw [hx]
  simp only [airyHankelShiftKernel, zero_add, add_zero, star_trivial, add_comm]

/-- Physical boundary-vector norm, from the Airy square integral. -/
theorem airyBoundaryVector_inner_self (s : ℝ /- [definition] -/ )
    : inner ℝ (airyBoundaryVector s) (airyBoundaryVector s) = airyEnergy s := by
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ ((airyBoundaryVector s) x) ((airyBoundaryVector s) x)
      ∂halfLineMeasure) = ∫ x, (airyAiReal (s+x))^2 ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards [airyBoundaryVector_apply_ae s] with x hx
        simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = airyEnergy s := airyAiReal_sq_integral s

/-- The energy is the squared norm of the genuine boundary row. -/
theorem airyBoundaryVector_norm_sq (s : ℝ /- [definition] -/ )
    : ‖airyBoundaryVector s‖^2 = airyEnergy s := by
  simpa only [real_inner_self_eq_norm_sq] using airyBoundaryVector_inner_self s

/-- Boundary row composed with the physical Hankel kernel is the Airy-kernel row. -/
theorem airyBoundaryVector_hankel_apply_ae (s : ℝ /- [definition] -/ )
    : airyHankelShift s (airyBoundaryVector s) =ᵐ[halfLineMeasure]
        fun y => airyKernelIntegral (y+s) s := by
  simpa only [airyBoundaryVector, zero_add] using airyHankelShift_slice_apply_ae s 0

/-- The cubic boundary moment is an ordinary, genuine Airy-kernel integral. -/
theorem airyBoundaryVector_cubic_moment (s : ℝ /- [definition] -/ )
    : inner ℝ (airyBoundaryVector s) (airyHankelShift s (airyBoundaryVector s)) =
        ∫ x, airyAiReal (s+x) * airyKernelIntegral (x+s) s ∂halfLineMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [airyBoundaryVector_apply_ae s,
    airyBoundaryVector_hankel_apply_ae s] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Energy positivity follows from the ODE or positive half-line integral. -/
theorem airyEnergy_pos (s : ℝ /- [definition] -/ )
    : 0 < airyEnergy s := by
  by_cases hs : s ≤ 0
  · have hm : Antitone airyEnergy := antitone_of_hasDerivAt_nonpos
      hasDerivAt_airyEnergy (fun x => neg_nonpos.mpr (sq_nonneg (airyAiReal x)))
    have hp : 0 < airyEnergy 0 := by
      simpa only [airyEnergy, zero_mul, sub_zero] using
        sq_pos_of_ne_zero (ne_of_lt deriv_airyAiReal_zero_neg)
    exact hp.trans_le (hm hs)
  · have hs0 : 0 ≤ s := (lt_of_not_ge hs).le
    rw [airyEnergy, ← airyAiReal_sq_integral s]
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun x => sq_nonneg (airyAiReal (s+x)))
      (integrable_airyAiReal_sq_comp_add_Ioi s)).mpr
    have he : Function.support (fun x => (airyAiReal (s+x))^2) ∩ Ioi 0 = Ioi 0 := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, Function.mem_support, ne_eq,
        sq_eq_zero_iff]
      constructor
      · exact fun h => h.2
      · intro hx
        exact ⟨(airyAiReal_pos_of_nonneg (by linarith)).ne', hx⟩
    rw [he]
    simp

/-- The genuine boundary row is nonzero at every real shift. -/
theorem airyBoundaryVector_ne_zero (s : ℝ /- [definition] -/ )
    : airyBoundaryVector s ≠ 0 := by
  intro h
  have he := airyBoundaryVector_norm_sq s
  rw [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at he
  exact (airyEnergy_pos s).ne' he.symm

/-- Nondegenerate simultaneous probe for the genuine row, energy and composition. -/
theorem airyBoundaryVector_joint_probe :
    ∃ s : ℝ, s < 0 ∧ airyBoundaryVector s ≠ 0 ∧
      (airyBoundaryVector s =ᵐ[halfLineMeasure] fun x => airyAiReal (s+x)) ∧
      ‖airyBoundaryVector s‖^2 = airyEnergy s ∧ 0 < airyEnergy s ∧
      (airyHankelShift s (airyBoundaryVector s) =ᵐ[halfLineMeasure]
        fun y => airyKernelIntegral (y+s) s) := by
  exact ⟨-1, by norm_num, airyBoundaryVector_ne_zero (-1),
    airyBoundaryVector_apply_ae (-1), airyBoundaryVector_norm_sq (-1),
    airyEnergy_pos (-1), airyBoundaryVector_hankel_apply_ae (-1)⟩


open scoped InnerProductSpace

/-- A strict contraction has a genuine right resolvent via the Banach-ring inverse. -/
theorem contraction_ringInverse_right
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [NormedSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (B : E →L[ℝ] E /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (x : E /- [definition] -/ )
    : Ring.inverse (1-B) x - B (Ring.inverse (1-B) x) = x := by
  have he : (1-B) * Ring.inverse (1-B) = (1 : E →L[ℝ] E) := by
    rw [NormedRing.inverse_one_sub B hB]
    exact (Units.oneSub B hB).val_inv
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] using congrArg (fun T : E →L[ℝ] E => T x) he

/-- The same canonical inverse is also a genuine left resolvent. -/
theorem contraction_ringInverse_left
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [NormedSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (B : E →L[ℝ] E /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (x : E /- [definition] -/ )
    : Ring.inverse (1-B) (x-B x) = x := by
  have he : Ring.inverse (1-B) * (1-B) = (1 : E →L[ℝ] E) := by
    rw [NormedRing.inverse_one_sub B hB]
    exact (Units.oneSub B hB).inv_val
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] using congrArg (fun T : E →L[ℝ] E => T x) he

/-- Nonzero symmetric contraction and nonzero vector satisfying both actual
ring-inverse conclusions with the sole norm premise jointly. -/
theorem contraction_ringInverse_joint_probe :
    ∃ B : ℝ →L[ℝ] ℝ, ∃ x : ℝ,
      ‖B‖ < 1 ∧ B ≠ 0 ∧ x ≠ 0 ∧
      (∀ u v, inner ℝ (B u) v = inner ℝ u (B v)) ∧
      Ring.inverse (1-B) x - B (Ring.inverse (1-B) x) = x ∧
      Ring.inverse (1-B) (x-B x) = x := by
  let B : ℝ →L[ℝ] ℝ := (-1/2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hB : ‖B‖ < 1 := by norm_num [B, norm_smul, ContinuousLinearMap.norm_id]
  refine ⟨B, 1, hB, ?_, by norm_num, ?_,
    contraction_ringInverse_right B hB 1, contraction_ringInverse_left B hB 1⟩
  · intro h
    have he := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h
    norm_num [B] at he
  · intro u v
    simp only [B, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      RCLike.inner_apply, conj_trivial, smul_eq_mul]
    ring


/-- The far-left energy argument now acts on the genuine Airy L² row.
The contraction can be arbitrary: the row and scalar boundary are physical. -/
theorem airy_boundary_nonneg_far_left_of_resolvent
    (B R : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (hB : ‖B‖ < 1 /- [standing] -/ )
    (hsym : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)  /- [standing] -/ )
    (hright : ∀ x, R x - B (R x) = x /- [standing] -/ )
    (hleft : ∀ x, R (x - B x) = x /- [standing] -/ )
    (s : ℝ /- [definition] -/ )
    (hs : s ≤ -4 / (deriv airyAiReal 0)^2 /- [standing] -/ )
    : 0 ≤ airyAiReal s + inner ℝ (airyBoundaryVector s) (R (airyBoundaryVector s)) := by
  have hq := contraction_resolvent_half_norm_lower B R hB hsym hright hleft
    (airyBoundaryVector s)
  rw [airyBoundaryVector_inner_self] at hq
  have ha := Airy_boundary_energy_nonneg_far_left s hs
  change 0 ≤ airyAiReal s + airyEnergy s / 2 at ha
  linarith

/-- All additional contraction/left/right-inverse and far-left premises
hold jointly on a nonzero genuine L² Airy boundary row. The probe's B is
an explicit scalar contraction, not claimed to be the Airy Hankel operator. -/
theorem airy_boundary_resolvent_joint_probe :
    ∃ B R : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure, ∃ s : ℝ,
      ‖B‖ < 1 ∧
      (∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) ∧
      (∀ x, R x - B (R x) = x) ∧ (∀ x, R (x - B x) = x) ∧
      s < -4 / (deriv airyAiReal 0)^2 ∧ airyBoundaryVector s ≠ 0 ∧
      0 ≤ airyAiReal s + inner ℝ (airyBoundaryVector s) (R (airyBoundaryVector s)) := by
  let B : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
    (-1/2 : ℝ) • ContinuousLinearMap.id ℝ _
  let R : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
    (2/3 : ℝ) • ContinuousLinearMap.id ℝ _
  let s := -4 / (deriv airyAiReal 0)^2 - 1
  have hs : s < -4 / (deriv airyAiReal 0)^2 := by dsimp [s]; linarith
  have hB : ‖B‖ < 1 := by
    have hb : ‖B‖ ≤ |(-1/2 : ℝ)| * 1 := by
      calc
        ‖B‖ = |(-1/2 : ℝ)| * ‖ContinuousLinearMap.id ℝ (Lp ℝ 2 halfLineMeasure)‖ := by
          simp only [B, norm_smul, Real.norm_eq_abs]
        _ ≤ |(-1/2 : ℝ)| * 1 := mul_le_mul_of_nonneg_left
          ContinuousLinearMap.norm_id_le (abs_nonneg _)
    norm_num at hb ⊢
    linarith
  have hsym : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y) := by
    intro x y
    simp only [B, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_smul_right]
  have hright : ∀ x, R x - B (R x) = x := by
    intro x
    simp only [B, R, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_smul, ← sub_smul]
    norm_num
  have hleft : ∀ x, R (x - B x) = x := by
    intro x
    simp only [B, R, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_sub, smul_smul, ← sub_smul]
    norm_num
  exact ⟨B, R, s, hB, hsym, hright, hleft, hs, airyBoundaryVector_ne_zero s,
    airy_boundary_nonneg_far_left_of_resolvent B R hB hsym hright hleft s hs.le⟩

/-- The physical cubic certificate now has a kernel integral expression.
This is a lower bound, not an assumption of the sign of that expression. -/
theorem airy_boundary_cubic_lower
    (R : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (hB : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    (hright : ∀ x, R x - airyHankelShift s (R x) = x /- [standing] -/ )
    (hleft : ∀ x, R (x - airyHankelShift s x) = x /- [standing] -/ )
    : airyAiReal s + airyEnergy s +
        (∫ x, airyAiReal (s+x) * airyKernelIntegral (x+s) s ∂halfLineMeasure) ≤
      airyAiReal s + inner ℝ (airyBoundaryVector s) (R (airyBoundaryVector s)) := by
  have hsym : ∀ x y, inner ℝ (airyHankelShift s x) y = inner ℝ x (airyHankelShift s y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_airyHankelShift s)
  have hq := contraction_resolvent_polynomial_lower (airyHankelShift s) R hB hsym
    hright hleft (airyBoundaryVector s)
  rw [airyBoundaryVector_inner_self, airyBoundaryVector_cubic_moment] at hq
  linarith

/-- A sign certificate under the stated contraction and inverse-identity hypotheses. -/
theorem airy_hankel_boundary_nonneg_far_left
    (R : Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (hB : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    (hright : ∀ x, R x - airyHankelShift s (R x) = x /- [standing] -/ )
    (hleft : ∀ x, R (x - airyHankelShift s x) = x /- [standing] -/ )
    (hs : s ≤ -4 / (deriv airyAiReal 0)^2 /- [standing] -/ )
    : 0 ≤ airyAiReal s + inner ℝ (airyBoundaryVector s) (R (airyBoundaryVector s)) := by
  have hsym : ∀ x y, inner ℝ (airyHankelShift s x) y = inner ℝ x (airyHankelShift s y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_airyHankelShift s)
  exact airy_boundary_nonneg_far_left_of_resolvent (airyHankelShift s) R hB hsym
    hright hleft s hs

/-- Genuine Airy-Hankel far-left sign with no inverse-equation hypotheses.
Only strict contraction and the displayed shift range remain conditional. -/
theorem airy_hankel_inverse_boundary_nonneg_far_left
    (s : ℝ /- [definition] -/ )
    (hB : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    (hs : s ≤ -4 / (deriv airyAiReal 0)^2 /- [standing] -/ )
    : 0 ≤ airyAiReal s + inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1-airyHankelShift s) (airyBoundaryVector s)) := by
  exact airy_hankel_boundary_nonneg_far_left (Ring.inverse (1-airyHankelShift s))
    s hB (contraction_ringInverse_right (airyHankelShift s) hB)
    (contraction_ringInverse_left (airyHankelShift s) hB) hs

/-- Genuine Airy-Hankel boundary sign on the nonnegative half-line, also
using the canonical Banach-ring inverse rather than inverse premises. -/
theorem airy_hankel_inverse_boundary_pos_nonneg
    (s : ℝ /- [definition] -/ )
    (hB : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    (hs : 0 ≤ s /- [standing] -/ )
    : 0 < airyAiReal s + inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1-airyHankelShift s) (airyBoundaryVector s)) := by
  exact Airy_boundary_positive_of_nonneg_shift (airyHankelShift s)
    (Ring.inverse (1-airyHankelShift s)) hB
    (contraction_ringInverse_right (airyHankelShift s) hB) (airyBoundaryVector s) s hs


/-- Real diagonal minors on a complete eigenbasis. -/
theorem real_eigenbasis_minor
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, T (b i) = lam i • b i /- [standing] -/ )
    (t : Finset ι /- [definition] -/ )
    : realNuclearMinor b (fun i => T (b i)) t = ∏ i ∈ t, lam i := by
  classical
  have hm : (fun i j : t => inner ℝ (b i) (T (b j)) : Matrix t t ℝ) =
      Matrix.diagonal (fun i : t => lam i) := by
    ext i j
    simp only [hdiag, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
      Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [realNuclearMinor, hm, Matrix.det_diagonal, Finset.prod_coe_sort]

/-- A trace-class factorization gives absolute summability on a complete
real eigenbasis. No spectral summability or product identity is assumed. -/
theorem real_eigenbasis_absolute
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hT : ∃ A B : E →L[ℝ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧
      Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (hdiag : ∀ i, T (b i) = lam i • b i /- [standing] -/ )
    : Summable (fun i => ‖lam i‖) := by
  classical
  have ha := (realOperatorDet_absolute b T hT 1).comp_injective
    (show Function.Injective (fun i : ι => ({i} : Finset ι)) from by
      intro i j h; simpa using h)
  simpa only [Function.comp_def, real_eigenbasis_minor b T lam hdiag, Finset.prod_singleton,
    one_pow, mul_one] using ha

/-- The real operator determinant is the eigenvalue product at every coupling,
proved from its registered minor series and genuine trace-class factorization. -/
theorem real_eigenbasis_product
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hT : ∃ A B : E →L[ℝ] E, T = A ∘L B ∧
      Summable (fun i => ‖A (b i)‖ ^ 2) ∧
      Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (hdiag : ∀ i, T (b i) = lam i • b i /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : realOperatorDet b T z = ∏' i, (1 + z * lam i) := by
  classical
  have ht : (fun t : Finset ι => realNuclearMinor b (fun i => T (b i)) t * z ^ t.card) =
      (fun t : Finset ι => ∏ i ∈ t, z * lam i) := by
    funext t
    rw [real_eigenbasis_minor b T lam hdiag, Finset.prod_mul_distrib, Finset.prod_const]
    exact mul_comm _ _
  have hs : Summable (fun t : Finset ι => ∏ i ∈ t, z * lam i) := by
    rw [← ht]
    exact (realOperatorDet_absolute b T hT z).of_norm
  rw [realOperatorDet, realNuclearDet, ht]
  exact (tprod_one_add hs).symm

/-- The landed physical bridge is discharged; only a complete Airy eigenbasis
is a premise of this all-coupling product statement. -/
theorem airy_eigenbasis_product
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : (kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y+s)) (z : ℂ)).re =
      ∏' i, (1 + z * lam i) := by
  rw [airyHankelFredholm_eq_realOperatorDet b s z, Complex.ofReal_re]
  exact real_eigenbasis_product b (airyHankelShift s) lam
    ⟨airyDerivativeFactor s, airyVolterraFactor.adjoint,
      airyHankelShift_eq_derivative_volterra s,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
        (memLp_airyDerivativeFactorKernel s)) b,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
        memLp_airyVolterraFactorKernel).adjoint b⟩ hdiag z

/-- Absolute summability is also discharged for the actual Airy factorization. -/
theorem airy_eigenbasis_absolute
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    : Summable (fun i => ‖lam i‖) := by
  exact real_eigenbasis_absolute b (airyHankelShift s) lam
    ⟨airyDerivativeFactor s, airyVolterraFactor.adjoint,
      airyHankelShift_eq_derivative_volterra s,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
        (memLp_airyDerivativeFactorKernel s)) b,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
        memLp_airyVolterraFactorKernel).adjoint b⟩ hdiag

/-- The genuine spectral trace is the positive half Airy tail. Neither a
trace identity nor a determinant bridge nor summability is a premise. -/
theorem airy_eigenbasis_trace
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    : (∑' i, lam i) = airyTailIntegral airyAiReal s / 2 := by
  rw [B_spectral_trace_of_product_bridge s lam
    (airy_eigenbasis_absolute s b lam hdiag).of_norm
    (airy_eigenbasis_product s b lam hdiag)]
  exact B_diagonal_integral_eq_half_tail s

/-- The physical upper bound with the bridge and summability discharged.
The two open premises are a complete real eigenbasis and strict contraction. -/
theorem TW1R_le_one_of_eigenbasis
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : TW1R s ≤ 1 := by
  exact TW1R_le_one_of_eigenvalue_product_bridge s lam b
    (airy_eigenbasis_absolute s b lam hdiag).of_norm
    (fun i => by have h := b.orthonormal.norm_eq_one i; intro hz; simp [hz] at h)
    hdiag (airy_eigenbasis_product s b lam hdiag) hnorm

/-- A sharper upper bound using the proved strictly positive Airy tail. -/
theorem TW1R_le_exp_neg_half_tail_of_eigenbasis
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : TW1R s ≤ Real.exp (-(airyTailIntegral airyAiReal s / 2)) := by
  rw [TW1R_eq_realOperatorDet b s,
    real_eigenbasis_product b (airyHankelShift s) lam
      ⟨airyDerivativeFactor s, airyVolterraFactor.adjoint,
        airyHankelShift_eq_derivative_volterra s,
        summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
          (memLp_airyDerivativeFactorKernel s)) b,
        summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
          memLp_airyVolterraFactorKernel).adjoint b⟩ hdiag]
  simp only [neg_one_mul, ← sub_eq_add_neg]
  rw [← airy_eigenbasis_trace s b lam hdiag]
  exact signed_tprod_le_exp_trace lam (airy_eigenbasis_absolute s b lam hdiag).of_norm
    (fun i => eigenvalue_lt_one_of_norm (airyHankelShift s) (lam i) (b i)
      (by have h := b.orthonormal.norm_eq_one i; intro hz; simp [hz] at h)
      (hdiag i) hnorm)


/-- Strict positivity uses the convergent logarithm, rather than assuming
nonnegativity of every Fredholm coefficient. -/
theorem signed_tprod_pos
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (hsum : Summable lam /- [standing] -/ )
    (hupper : ∀ i, lam i < 1 /- [standing] -/ )
    : 0 < ∏' i, (1 - lam i) := by
  have hp : ∀ i, 0 < 1 - lam i := fun i => sub_pos.mpr (hupper i)
  have hl : Summable (fun i => Real.log (1 - lam i)) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hsum.neg
  rw [← Real.rexp_tsum_eq_tprod hp hl]
  exact Real.exp_pos _

/-- Strict upper bound for the actual TW1R. -/
theorem TW1R_lt_one_of_eigenbasis
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : TW1R s < 1 := by
  apply (TW1R_le_exp_neg_half_tail_of_eigenbasis s b lam hdiag hnorm).trans_lt
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (neg_neg_of_pos (div_pos (airy_tail_positive s) (by norm_num)))

/-- Positivity for the physical determinant under exactly the same two open
spectral premises as the upper bound. -/
theorem TW1R_pos_of_eigenbasis
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : 0 < TW1R s := by
  have hp := airy_eigenbasis_product s b lam hdiag (-1)
  have he : TW1R s = ∏' i, (1 - lam i) := by
    simpa only [TW1R, TW1, B_fredholm_physical, Complex.ofReal_neg,
      Complex.ofReal_one, neg_one_mul, sub_eq_add_neg] using hp
  rw [he]
  exact signed_tprod_pos lam (airy_eigenbasis_absolute s b lam hdiag).of_norm
    (fun i => eigenvalue_lt_one_of_norm (airyHankelShift s) (lam i) (b i)
      (by have h := b.orthonormal.norm_eq_one i; intro hz; simp [hz] at h)
      (hdiag i) hnorm)
/-- The new canonical determinant supplies the right limit without
any operator bridge hypothesis. -/
theorem real_eigenbasis_joint_probe
    : ∃ b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2),
      ∃ T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      ∃ lam : ℕ → ℝ,
      (∃ A B : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
        T = A ∘L B ∧ Summable (fun i => ‖A (b i)‖ ^ 2) ∧
        Summable (fun i => ‖B (b i)‖ ^ 2)) ∧
      (∀ i, T (b i) = lam i • b i) ∧ ‖T‖ < 1 ∧
      ‖T (b 0)‖ = 1/2 ∧ Summable (fun i => ‖lam i‖) ∧
      (∑' i, lam i) = 1/2 ∧
      (∀ z : ℝ, realOperatorDet b T z = ∏' i, (1 + z * lam i)) ∧
      realOperatorDet b T (-1) = 1/2 := by
  classical
  let b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  let P := InnerProductSpace.rankOne ℝ (b 0) (b 0)
  let T := (1/2 : ℝ) • P
  let lam : ℕ → ℝ := fun i => if i = 0 then 1/2 else 0
  have hP : Summable (fun i => ‖P (b i)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [P, InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal, hi, Ne.symm hi]
  have hTsum : Summable (fun i => ‖T (b i)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [T, P, InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal, hi, Ne.symm hi]
  have hfac : ∃ A B : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      T = A ∘L B ∧ Summable (fun i => ‖A (b i)‖ ^ 2) ∧
        Summable (fun i => ‖B (b i)‖ ^ 2) := by
    refine ⟨T, P, ?_, hTsum, hP⟩
    ext x
    simp [T, P, InnerProductSpace.rankOne_apply, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal, b.orthonormal.norm_eq_one 0, smul_smul]
  have hd : ∀ i, T (b i) = lam i • b i := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [T, P, lam, InnerProductSpace.rankOne_apply,
        orthonormal_iff_ite.mp b.orthonormal, b.orthonormal.norm_eq_one 0]
    · simp [T, P, lam, InnerProductSpace.rankOne_apply,
        orthonormal_iff_ite.mp b.orthonormal, hi, Ne.symm hi]
  have hn : ‖T‖ < 1 := by
    simp only [T, norm_smul, InnerProductSpace.norm_rankOne, P,
      b.orthonormal.norm_eq_one 0]
    norm_num
  refine ⟨b, T, lam, hfac, hd, hn, ?_,
    real_eigenbasis_absolute b T lam hfac hd, ?_,
    real_eigenbasis_product b T lam hfac hd, ?_⟩
  · rw [hd 0, norm_smul, b.orthonormal.norm_eq_one 0]
    norm_num [lam]
  · rw [tsum_eq_sum (s := {0}) (fun i hi => by
      simp only [Finset.mem_singleton] at hi; simp [lam, hi])]
    norm_num [lam]
  · rw [real_eigenbasis_product b T lam hfac hd (-1),
      tprod_eq_prod (s := {0}) (fun i hi => by
        simp only [Finset.mem_singleton] at hi; simp [lam, hi])]
    norm_num [lam]

noncomputable def spectralCoeff_on
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℝ := ∑' s : {s : Finset ι // s.card = n}, ∏ i ∈ s.val, lam i

theorem spectral_finset_summable_on
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : Summable (fun s : Finset ι => (∏ i ∈ s, lam i) * z ^ s.card) := by
  have hm := summable_finsetProd_of_summable_nonneg
    (fun i => mul_nonneg (norm_nonneg z) (norm_nonneg (lam i))) (hs.norm.mul_left ‖z‖)
  have hn : Summable (fun s : Finset ι => ‖(∏ i ∈ s, lam i) * z ^ s.card‖) := by
    convert hm using 1
    funext s
    rw [norm_mul, norm_pow, norm_prod, Finset.prod_mul_distrib, Finset.prod_const]
    ring
  exact hn.of_norm

theorem spectralCoeff_hasSum_on
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : HasSum (fun n => spectralCoeff_on lam n * z ^ n) (∏' i, (1 + z * lam i)) := by
  have hp : HasSum (fun s : Finset ι => ∏ i ∈ s, z * lam i) (∏' i, (1 + z * lam i)) := by
    have hss : Summable (fun s : Finset ι => ∏ i ∈ s, z * lam i) := by
      simpa only [Finset.prod_mul_distrib, Finset.prod_const, mul_comm] using
        spectral_finset_summable_on lam hs z
    rw [tprod_one_add hss]
    exact hss.hasSum
  have hgroup := hp.tsum_fiberwise Finset.card
  refine hgroup.congr_fun (fun n => ?_)
  rw [spectralCoeff_on, ← tsum_mul_right]
  apply tsum_congr
  intro s
  rw [Finset.prod_mul_distrib, Finset.prod_const, s.property]
  ring

theorem spectralCoeff_radius_top_on
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    : (FormalMultilinearSeries.ofScalars ℝ (spectralCoeff_on lam)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  have h := (spectralCoeff_hasSum_on lam hs (R : ℝ)).summable.norm
  simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
    Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg] using h

theorem spectralCoeff_one_on
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    : spectralCoeff_on lam 1 = ∑' i, lam i := by
  classical
  let e : ι ≃ {s : Finset ι // s.card = 1} := Equiv.ofBijective
    (fun i => ⟨{i}, Finset.card_singleton i⟩) (by
      constructor
      · intro i j hij
        have he := congrArg Subtype.val hij
        simpa using he
      · intro s
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp s.property
        exact ⟨i, Subtype.ext hi.symm⟩)
  have h := e.tsum_eq (fun s => ∏ i ∈ s.val, lam i)
  simpa [spectralCoeff_on, e] using h.symm

/-- Equality of the whole determinant function identifies the trace coefficient.
This does not assume the eigenvalue sum equals a kernel diagonal integral. -/
theorem trace_coefficient_of_product_bridge_on
    {ι : Type* /- [definition] -/ }
    (c : ℕ → ℝ /- [definition] -/ )
    (hc : ∀ R : NNReal, Summable (fun n => ‖c n‖ * (R : ℝ) ^ n)  /- [standing] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hs : Summable lam /- [standing] -/ )
    (hbridge : ∀ z : ℝ, (∑' n, c n * z ^ n) = ∏' i, (1 + z * lam i)  /- [standing] -/ )
    : c 1 = ∑' i, lam i := by
  let p := FormalMultilinearSeries.ofScalars ℝ c
  let q := FormalMultilinearSeries.ofScalars ℝ (spectralCoeff_on lam)
  have hrp : p.radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
    intro R
    simpa only [p, FormalMultilinearSeries.ofScalars_norm] using hc R
  have hrq : q.radius = ⊤ := spectralCoeff_radius_top_on lam hs
  have hp := p.hasFPowerSeriesOnBall (by rw [hrp]; exact ENNReal.zero_lt_top)
  have hq := q.hasFPowerSeriesOnBall (by rw [hrq]; exact ENNReal.zero_lt_top)
  have heq : p.sum = q.sum := by
    funext z
    rw [show p.sum z = ∑' n, c n * z ^ n from FormalMultilinearSeries.ofScalars_sum_eq c z,
      show q.sum z = ∑' n, spectralCoeff_on lam n * z ^ n from
        FormalMultilinearSeries.ofScalars_sum_eq (spectralCoeff_on lam) z,
      (spectralCoeff_hasSum_on lam hs z).tsum_eq, hbridge z]
  have hseries : p = q := by
    rw [heq] at hp
    exact hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hq.hasFPowerSeriesAt
  have hcoeff : c = spectralCoeff_on lam := FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ hseries
  rw [hcoeff, spectralCoeff_one_on]

theorem B_spectral_trace_of_product_bridge_on
    {ι : Type* /- [definition] -/ }
    (s : ℝ /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hsum : Summable lam /- [standing] -/ )
    (hbridge : ∀ z : ℝ,
      (kernelFredholm RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s)) (z : ℂ)).re =
        ∏' i, (1 + z * lam i)  /- [standing] -/ )
    : (∑' i, lam i) = (∫ x, RMTFoundations.Airy.airyAiReal (x + x + s) ∂ RMTFoundations.Airy.halfLineMeasure) := by
  have hc : ∀ R : NNReal, Summable (fun n =>
      ‖kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s)) n‖ * (R : ℝ) ^ n) := by
    intro R
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg R.coe_nonneg] using B_physical_fredholm_absolute s ((R : ℝ) : ℂ)
  have hb : ∀ z : ℝ,
      (∑' n, kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s)) n * z ^ n) =
        ∏' i, (1 + z * lam i) := by
    intro z
    simpa only [kernelFredholm_real_coupling, Complex.ofReal_re] using hbridge z
  have h := trace_coefficient_of_product_bridge_on
    (kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x + y + s))) hc lam hsum hb
  rw [kernelCoefficient_one] at h
  exact h.symm

/-- The landed physical bridge is discharged; only a complete Airy eigenbasis
is a premise of this all-coupling product statement. -/
theorem airy_eigenbasis_product_on
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : (kernelFredholm halfLineMeasure (fun x y => airyAiReal (x+y+s)) (z : ℂ)).re =
      ∏' i, (1 + z * lam i) := by
  rw [airyHankelFredholm_eq_realOperatorDet b s z, Complex.ofReal_re]
  exact real_eigenbasis_product b (airyHankelShift s) lam
    ⟨airyDerivativeFactor s, airyVolterraFactor.adjoint,
      airyHankelShift_eq_derivative_volterra s,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
        (memLp_airyDerivativeFactorKernel s)) b,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
        memLp_airyVolterraFactorKernel).adjoint b⟩ hdiag z

/-- Absolute summability is also discharged for the actual Airy factorization. -/
theorem airy_eigenbasis_absolute_on
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    : Summable (fun i => ‖lam i‖) := by
  exact real_eigenbasis_absolute b (airyHankelShift s) lam
    ⟨airyDerivativeFactor s, airyVolterraFactor.adjoint,
      airyHankelShift_eq_derivative_volterra s,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
        (memLp_airyDerivativeFactorKernel s)) b,
      summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
        memLp_airyVolterraFactorKernel).adjoint b⟩ hdiag

/-- The genuine spectral trace is the positive half Airy tail. Neither a
trace identity nor a determinant bridge nor summability is a premise. -/
theorem airy_eigenbasis_trace_on
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    : (∑' i, lam i) = airyTailIntegral airyAiReal s / 2 := by
  rw [B_spectral_trace_of_product_bridge_on s lam
    (airy_eigenbasis_absolute_on s b lam hdiag).of_norm
    (airy_eigenbasis_product_on s b lam hdiag)]
  exact B_diagonal_integral_eq_half_tail s

/-- A sharper upper bound using the proved strictly positive Airy tail. -/
theorem TW1R_le_exp_neg_half_tail_of_eigenbasis_on
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : TW1R s ≤ Real.exp (-(airyTailIntegral airyAiReal s / 2)) := by
  rw [TW1R_eq_realOperatorDet b s,
    real_eigenbasis_product b (airyHankelShift s) lam
      ⟨airyDerivativeFactor s, airyVolterraFactor.adjoint,
        airyHankelShift_eq_derivative_volterra s,
        summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
          (memLp_airyDerivativeFactorKernel s)) b,
        summable_norm_sq_apply_basis (isHilbertSchmidt_kernelOperator
          memLp_airyVolterraFactorKernel).adjoint b⟩ hdiag]
  simp only [neg_one_mul, ← sub_eq_add_neg]
  rw [← airy_eigenbasis_trace_on s b lam hdiag]
  exact signed_tprod_le_exp_trace lam (airy_eigenbasis_absolute_on s b lam hdiag).of_norm
    (fun i => eigenvalue_lt_one_of_norm (airyHankelShift s) (lam i) (b i)
      (by have h := b.orthonormal.norm_eq_one i; intro hz; simp [hz] at h)
      (hdiag i) hnorm)


/-- Strict upper bound for the actual TW1R. -/
theorem TW1R_lt_one_of_eigenbasis_on
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : TW1R s < 1 := by
  apply (TW1R_le_exp_neg_half_tail_of_eigenbasis_on s b lam hdiag hnorm).trans_lt
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (neg_neg_of_pos (div_pos (airy_tail_positive s) (by norm_num)))

/-- Positivity for the physical determinant under exactly the same two open
spectral premises as the upper bound. -/
theorem TW1R_pos_of_eigenbasis_on
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (s : ℝ /- [definition] -/ )
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (lam : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ i, airyHankelShift s (b i) = lam i • b i /- [standing] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : 0 < TW1R s := by
  have hp := airy_eigenbasis_product_on s b lam hdiag (-1)
  have he : TW1R s = ∏' i, (1 - lam i) := by
    simpa only [TW1R, TW1, B_fredholm_physical, Complex.ofReal_neg,
      Complex.ofReal_one, neg_one_mul, sub_eq_add_neg] using hp
  rw [he]
  exact signed_tprod_pos lam (airy_eigenbasis_absolute_on s b lam hdiag).of_norm
    (fun i => eigenvalue_lt_one_of_norm (airyHankelShift s) (lam i) (b i)
      (by have h := b.orthonormal.norm_eq_one i; intro hz; simp [hz] at h)
      (hdiag i) hnorm)
#check RMTFoundations.TWOneBounds.TW1R_le_one_of_eigenvalue_product_bridge
#check RMTFoundations.TWOneBounds.airyBoundaryVector_norm_sq
#check RMTFoundations.TWOneBounds.airyBoundaryVector_cubic_moment
#check RMTFoundations.TWOneBounds.airy_boundary_cubic_lower
#check RMTFoundations.TWOneBounds.airy_hankel_inverse_boundary_nonneg_far_left
#check RMTFoundations.TWOneBounds.airy_hankel_inverse_boundary_pos_nonneg

theorem compact_symmetric_real_eigenbasis
    {E : Type u /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    (T : E →L[ℝ] E /- [definition] -/ )
    (hc : IsCompactOperator T /- [standing] -/ )
    (hs : T.IsSymmetric /- [standing] -/ )
    : ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (lam : ι → ℝ),
        ∀ i, T (b i) = lam i • b i := by
  classical
  let V : ℝ → Submodule ℝ E := fun μ => Module.End.eigenspace T.toLinearMap μ
  let J := fun μ : ℝ => canonicalIndex ℝ (V μ)
  let bb := fun μ : ℝ => canonicalBasis ℝ (V μ)
  let v : (Σ μ : ℝ, J μ) → E := fun a => (bb a.1 a.2 : E)
  have ho : Orthonormal ℝ v :=
    hs.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (fun μ => (bb μ).orthonormal)
  have hz : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hb : ∀ μ j, inner ℝ x (bb μ j : E) = 0 := by
      intro μ j
      exact (Submodule.mem_orthogonal' _ _).mp hx _
        (Submodule.subset_span ⟨⟨μ,j⟩,rfl⟩)
    have hk : (⨆ μ, V μ) ≤ (innerSL ℝ x).ker := by
      apply iSup_le
      intro μ y hy
      let yy : V μ := ⟨y,hy⟩
      have hh := ((bb μ).hasSum_repr yy).mapL
        ((innerSL ℝ x).comp (V μ).subtypeL)
      have he : HasSum (fun _ : J μ => (0 : ℝ)) (inner ℝ x y) := by
        simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          Submodule.coe_smul, innerSL_apply_apply, inner_smul_right,
          hb, mul_zero] using hh
      have heq := he.unique (show HasSum (fun _ : J μ => (0 : ℝ)) 0 from hasSum_zero)
      exact heq
    have hmem : x ∈ (⨆ μ, V μ)ᗮ := by
      apply (Submodule.mem_orthogonal' _ _).mpr
      intro y hy
      exact hk hy
    have hh := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs
    change (⨆ μ, V μ)ᗮ = ⊥ at hh
    simpa only [hh, Submodule.mem_bot] using hmem
  let b := HilbertBasis.mkOfOrthogonalEqBot ho hz
  refine ⟨Σ μ : ℝ, J μ, b, fun a => a.1, ?_⟩
  intro a
  change T (b a) = a.1 • b a
  rw [show b a = v a from congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot ho hz) a]
  exact Module.End.mem_eigenspace_iff.mp (bb a.1 a.2).property

theorem airy_hankel_norm_vanishing_envelope
    : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ,
      ‖airyHankelShift s‖ ≤ (C * Real.exp (-s)) *
        (eLpNorm (fun p : ℝ × ℝ => Real.exp (-p.1) * Real.exp (-p.2)) 2
          (halfLineMeasure.prod halfLineMeasure)).toReal := by
  obtain ⟨C,hC,hbound⟩ := airyAiReal_abs_le_exp'
  refine ⟨C,hC,?_⟩
  intro s
  let a : ℝ := C * Real.exp (-s)
  let w : ℝ × ℝ → ℝ := fun p => Real.exp (-p.1) * Real.exp (-p.2)
  have ha : 0 ≤ a := (mul_pos hC (Real.exp_pos _)).le
  have hi : MemLp (fun p => a * w p) 2 (halfLineMeasure.prod halfLineMeasure) :=
    memLp_expPair.const_mul a
  have hb : ∀ p, ‖airyHankelShiftKernel s p‖ ≤ ‖a * w p‖ := by
    intro p
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ a * w p)]
    calc |airyHankelShiftKernel s p| ≤ C * Real.exp (-(p.1+p.2+s)) := hbound _
      _ = a * w p := by dsimp [a,w]; simp only [neg_add, Real.exp_add]; ring
  have hm := eLpNorm_mono_ae (p := (2 : ENNReal)) (μ := halfLineMeasure.prod halfLineMeasure)
    (memLp_airyHankelShiftKernel s).aestronglyMeasurable
    (Eventually.of_forall hb)
  have hn : ‖airyHankelShift s‖ ≤
      (eLpNorm (airyHankelShiftKernel s) 2 (halfLineMeasure.prod halfLineMeasure)).toReal := by
    change ‖kernelOperator (memLp_airyHankelShiftKernel s)‖ ≤ _
    simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using
      ENNReal.toReal_mono (memLp_airyHankelShiftKernel s).eLpNorm_ne_top
        (enorm_kernelOperator_le (memLp_airyHankelShiftKernel s))
  have he : eLpNorm (fun p => a * w p) 2 (halfLineMeasure.prod halfLineMeasure) =
      ‖a‖ₑ * eLpNorm w 2 (halfLineMeasure.prod halfLineMeasure) := by
    change eLpNorm (a • w) 2 (halfLineMeasure.prod halfLineMeasure) = _
    exact eLpNorm_const_smul a w 2 (halfLineMeasure.prod halfLineMeasure)
  calc ‖airyHankelShift s‖ ≤ _ := hn
    _ ≤ (eLpNorm (fun p => a * w p) 2 (halfLineMeasure.prod halfLineMeasure)).toReal :=
      ENNReal.toReal_mono hi.eLpNorm_ne_top hm
    _ = _ := by rw [he,ENNReal.toReal_mul,← ofReal_norm,ENNReal.toReal_ofReal (norm_nonneg a),Real.norm_eq_abs,abs_of_nonneg ha]

theorem airy_hankel_norm_tendsto_zero
    : Tendsto (fun s : ℝ => ‖airyHankelShift s‖) atTop (𝓝 0) := by
  obtain ⟨C,_,hb⟩ := airy_hankel_norm_vanishing_envelope
  have ht := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).mul_const
    (eLpNorm (fun p : ℝ × ℝ => Real.exp (-p.1) * Real.exp (-p.2)) 2
      (halfLineMeasure.prod halfLineMeasure)).toReal
  exact squeeze_zero (fun s => norm_nonneg _) hb (by simpa using ht)

/-- A genuine nondegenerate Airy contraction exists: this is a joint
inhabitation witness, not a global contraction assumption. -/
theorem airy_hankel_contraction_joint_probe
    : ∃ s : ℝ, 0 ≤ s ∧ ‖airyHankelShift s‖ < 1 ∧
      0 < airyHankelShiftKernel s (0,0) ∧
      IsTraceClass (airyHankelShift s) ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      TW1R s = airyOperatorTW1 s := by
  have he := airy_hankel_norm_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨s,hn,hs⟩ := (he.and (eventually_ge_atTop (0 : ℝ))).exists
  refine ⟨s,hs,hn,?_,isTraceClass_airyHankelShift s,shiftedUnitVector_norm 0,
    TW1R_eq_airyOperatorTW1 s⟩
  simpa only [airyHankelShiftKernel,zero_add] using airyAiReal_pos_of_nonneg hs


/-- The complete spectral basis is constructed, and the landed determinant
bridge is called inside the proof. Strict contraction is the sole premise. -/
theorem TW1R_bounds_of_contraction
    (s : ℝ /- [definition] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : 0 < TW1R s ∧
      TW1R s ≤ Real.exp (-(airyTailIntegral airyAiReal s / 2)) ∧
      Real.exp (-(airyTailIntegral airyAiReal s / 2)) < 1 := by
  obtain ⟨ι,b,lam,hd⟩ := compact_symmetric_real_eigenbasis (airyHankelShift s)
    (isTraceClass_airyHankelShift s).isCompactOperator
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_airyHankelShift s))
  letI := airyL2_basis_countable b
  refine ⟨TW1R_pos_of_eigenbasis_on s b lam hd hnorm,
    TW1R_le_exp_neg_half_tail_of_eigenbasis_on s b lam hd hnorm, ?_⟩
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith [airy_tail_positive s])

/-- Physical upper bound: neither a bridge nor spectral data are hypotheses. -/
theorem TW1R_le_one_of_contraction
    (s : ℝ /- [definition] -/ )
    (hnorm : ‖airyHankelShift s‖ < 1 /- [standing] -/ )
    : TW1R s ≤ 1 :=
  (TW1R_bounds_of_contraction s hnorm).2.1.trans
    (TW1R_bounds_of_contraction s hnorm).2.2.le

/-- Every new physical upper-bound premise holds jointly on a genuine,
nondegenerate Airy instance. The complete basis, trace and product are conclusions. -/
theorem airy_upper_bound_all_binder_joint_probe
    : ∃ s : ℝ, ∃ (ι : Type) (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure))
      (lam : ι → ℝ),
      Countable ι ∧ 0 ≤ s ∧ ‖airyHankelShift s‖ < 1 ∧
      (∀ i, airyHankelShift s (b i) = lam i • b i) ∧
      Summable (fun i => ‖lam i‖) ∧
      (∑' i, lam i) = airyTailIntegral airyAiReal s / 2 ∧
      (∀ z : ℝ, (kernelFredholm halfLineMeasure
        (fun x y => airyAiReal (x+y+s)) (z : ℂ)).re = ∏' i, (1 + z * lam i)) ∧
      0 < airyHankelShiftKernel s (0,0) ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      0 < TW1R s ∧ TW1R s < 1 := by
  obtain ⟨s,hs,hn,hk,_,hu,_⟩ := airy_hankel_contraction_joint_probe
  obtain ⟨ι,b,lam,hd⟩ := compact_symmetric_real_eigenbasis (airyHankelShift s)
    (isTraceClass_airyHankelShift s).isCompactOperator
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_airyHankelShift s))
  letI := airyL2_basis_countable b
  exact ⟨s,ι,b,lam,inferInstance,hs,hn,hd,airy_eigenbasis_absolute_on s b lam hd,
    airy_eigenbasis_trace_on s b lam hd,airy_eigenbasis_product_on s b lam hd,hk,hu,
    TW1R_pos_of_eigenbasis_on s b lam hd hn,TW1R_lt_one_of_eigenbasis_on s b lam hd hn⟩


/-- Genuine operator trace identity, unconditional for every real level. -/
theorem airy_hankel_trace_eq_half_tail
    (s : ℝ /- [definition] -/ )
    : RMTFoundations.Airy.trace (airyHankelShift s) =
      airyTailIntegral airyAiReal s / 2 := by
  obtain ⟨ι,b,lam,hd⟩ := compact_symmetric_real_eigenbasis (airyHankelShift s)
    (isTraceClass_airyHankelShift s).isCompactOperator
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_airyHankelShift s))
  letI := airyL2_basis_countable b
  calc RMTFoundations.Airy.trace (airyHankelShift s) =
      ∑' i, inner ℝ (b i) (airyHankelShift s (b i)) :=
        trace_eq_tsum_inner (isTraceClass_airyHankelShift s) b
    _ = ∑' i, lam i := by
      apply tsum_congr
      intro i
      rw [hd i,inner_smul_right]
      simp [inner_self_eq_norm_sq_to_K,b.orthonormal.norm_eq_one i]
    _ = airyTailIntegral airyAiReal s / 2 := airy_eigenbasis_trace_on s b lam hd

/-- Strict positivity of the genuine trace; no spectral or bridge premise. -/
theorem airy_hankel_trace_positive
    (s : ℝ /- [definition] -/ )
    : 0 < RMTFoundations.Airy.trace (airyHankelShift s) := by
  rw [airy_hankel_trace_eq_half_tail]
  exact div_pos (airy_tail_positive s) (by norm_num)

/-- Genuine trace level derivative. This is separate from the still-open
log-determinant level derivative identity needed for global monotonicity. -/
theorem hasDerivAt_airy_hankel_trace
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (fun t => RMTFoundations.Airy.trace (airyHankelShift t))
      (-airyAiReal s / 2) s := by
  exact (hasDerivAt_B_diagonal_trace s).congr_of_eventuallyEq
    (Eventually.of_forall fun t => by
      change RMTFoundations.Airy.trace (airyHankelShift t) =
        ∫ x, airyAiReal (x+x+t) ∂halfLineMeasure
      rw [airy_hankel_trace_eq_half_tail t,B_diagonal_integral_eq_half_tail t])

/-- Unconditional eventual physical positivity and strict upper bound. -/
theorem TW1R_eventually_between_zero_one
    : ∀ᶠ s : ℝ in atTop, 0 < TW1R s ∧ TW1R s < 1 := by
  have he := airy_hankel_norm_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he] with s hs
  have h := TW1R_bounds_of_contraction s hs
  exact ⟨h.1,h.2.1.trans_lt h.2.2⟩


/-- The trace-product upper bound survives eigenvalue 1: that factor kills the determinant. -/
theorem signed_tprod_le_exp_trace_of_le_one
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (hsum : Summable lam /- [standing] -/ )
    (hupper : ∀ i, lam i ≤ 1 /- [standing] -/ )
    : (∏' i, (1 - lam i)) ≤ Real.exp (-(∑' i, lam i)) := by
  classical
  by_cases he : ∃ i, lam i = 1
  · obtain ⟨i,hi⟩ := he
    rw [tprod_of_exists_eq_zero (show ∃ i, (1 - lam i) = 0 from ⟨i,by rw [hi]; ring⟩)]
    exact (Real.exp_pos _).le
  · apply signed_tprod_le_exp_trace lam hsum
    intro i
    exact lt_of_le_of_ne (hupper i) (fun hi => he ⟨i,hi⟩)

/-- The same endpoint-aware product is nonnegative. -/
theorem signed_tprod_nonneg_of_le_one
    {ι : Type* /- [definition] -/ }
    (lam : ι → ℝ /- [definition] -/ )
    (hsum : Summable lam /- [standing] -/ )
    (hupper : ∀ i, lam i ≤ 1 /- [standing] -/ )
    : 0 ≤ ∏' i, (1 - lam i) := by
  classical
  by_cases he : ∃ i, lam i = 1
  · obtain ⟨i,hi⟩ := he
    rw [tprod_of_exists_eq_zero (show ∃ i, (1 - lam i) = 0 from ⟨i,by rw [hi]; ring⟩)]
  · exact (signed_tprod_pos lam hsum (fun i =>
      lt_of_le_of_ne (hupper i) (fun hi => he ⟨i,hi⟩))).le

/-- Eigenvalues of a contraction lie below 1, including the endpoint. -/
theorem eigenvalue_le_one_of_contraction
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [NormedSpace ℝ E /- [definition] -/ ]
    (T : E →L[ℝ] E /- [definition] -/ )
    (lam : ℝ /- [definition] -/ )
    (v : E /- [definition] -/ )
    (hne : v ≠ 0 /- [standing] -/ )
    (he : T v = lam • v /- [standing] -/ )
    (hn : ‖T‖ ≤ 1 /- [standing] -/ )
    : lam ≤ 1 := by
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hne
  have h : |lam| * ‖v‖ ≤ ‖T‖ * ‖v‖ := by
    simpa only [he, norm_smul, Real.norm_eq_abs] using T.le_opNorm v
  have hn' := mul_le_mul_of_nonneg_right hn hv.le
  nlinarith [le_abs_self lam]

/-- Physical TW1 range: strict contraction is unnecessary for this conclusion. -/
theorem TW1R_bounds
    (s : ℝ /- [definition] -/ )
    : 0 ≤ TW1R s ∧
      TW1R s ≤ Real.exp (-(airyTailIntegral airyAiReal s / 2)) ∧
      Real.exp (-(airyTailIntegral airyAiReal s / 2)) < 1 := by
  obtain ⟨ι,b,lam,hd⟩ := compact_symmetric_real_eigenbasis (airyHankelShift s)
    (isTraceClass_airyHankelShift s).isCompactOperator
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_airyHankelShift s))
  letI := airyL2_basis_countable b
  have hu : ∀ i, lam i ≤ 1 := fun i => eigenvalue_le_one_of_contraction
    (airyHankelShift s) (lam i) (b i)
    (by have h := b.orthonormal.norm_eq_one i; intro hz; simp [hz] at h)
    (hd i) (RMTFoundations.AiryBounds.norm_airyHankelShift_le_one s)
  have hp : TW1R s = ∏' i, (1 - lam i) := by
    simpa only [TW1R, TW1, B_fredholm_physical, Complex.ofReal_neg,
      Complex.ofReal_one, neg_one_mul, sub_eq_add_neg] using
        airy_eigenbasis_product_on s b lam hd (-1)
  have ht := airy_eigenbasis_trace_on s b lam hd
  have ha := (airy_eigenbasis_absolute_on s b lam hd).of_norm
  refine ⟨?_,?_,?_⟩
  · rw [hp]
    exact signed_tprod_nonneg_of_le_one lam ha hu
  · rw [hp, ← ht]
    exact signed_tprod_le_exp_trace_of_le_one lam ha hu
  · rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [airy_tail_positive s])

theorem TW1R_le_one
    (s : ℝ /- [definition] -/ )
    : TW1R s ≤ 1 :=
  (TW1R_bounds s).2.1.trans (TW1R_bounds s).2.2.le

theorem TW1R_lt_one
    (s : ℝ /- [definition] -/ )
    : TW1R s < 1 :=
  (TW1R_bounds s).2.1.trans_lt (TW1R_bounds s).2.2

/-- Actual Airy joint probe; no norm, determinant, trace or spectral premise. -/
theorem airy_unconditional_upper_bound_joint_probe
    (s : ℝ /- [definition] -/ )
    : airyAiReal 0 > 0 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      ‖airyHankelShift s‖ ≤ 1 ∧ 0 ≤ TW1R s ∧ TW1R s < 1 :=
  ⟨airyAiReal_zero_pos, shiftedUnitVector_norm 0, RMTFoundations.AiryBounds.norm_airyHankelShift_le_one s,
    (TW1R_bounds s).1, TW1R_lt_one s⟩

/-- Damping already proves a quantitative strict norm bound at positive shifts. -/
theorem norm_airyHankelShift_lt_one_of_pos
    (s : ℝ /- [definition] -/ )
    (hs : 0 < s /- [standing] -/ )
    : ‖airyHankelShift s‖ < 1 := by
  let β := min s 1
  have hb : 0 < β := lt_min hs (by norm_num)
  have hb1 : β ≤ 1 := min_le_right _ _
  have hbs : β ≤ s := min_le_left _ _
  have hb2 : β^2 ≤ β := by nlinarith
  have hex : β^3 / 3 - β * s < 0 := by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hbs)]
  have hn : ‖airyHankelShift s‖ ≤ Real.exp (β^3 / 3 - β * s) := by
    apply (airyHankelShift s).opNorm_le_bound (Real.exp_pos _).le
    intro f
    exact RMTFoundations.AiryBounds.airyHankelShift_norm_apply_le_damping s β hb f
  exact hn.trans_lt (by simpa using Real.exp_lt_exp.mpr hex)

/-- A shifted Gaussian is dominated by a wider centered Gaussian. -/
theorem gaussian_linear_bound
    (a b t : ℝ /- [definition] -/ )
    (ha : 0 < a /- [standing] -/ )
    : Real.exp (-a*t^2 + b*|t|) ≤
      Real.exp (b^2/a) * Real.exp (-(a/2)*t^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : a*(b^2/a) = b^2 := by field_simp
  have hsq := sq_nonneg (a*|t|-b)
  have habs : (a*|t|)^2 = a^2*t^2 := by rw [mul_pow,sq_abs]
  have hyoung : 2*(a*|t|)*b ≤ a^2*t^2+b^2 := by nlinarith
  have hk : a*(-a*t^2+b*|t|) ≤ a*(b^2/a+(-(a/2)*t^2)) := by nlinarith
  nlinarith

/-- Gaussian decay makes the complex Laplace transform integrable everywhere. -/
theorem gaussian_laplace_integrable
    (g : ℝ → ℂ /- [definition] -/ )
    (hg : AEStronglyMeasurable g /- [standing] -/ )
    (a C : ℝ /- [definition] -/ )
    (ha : 0 < a /- [standing] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (hb : ∀ t, ‖g t‖ ≤ C*Real.exp (-a*t^2)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Integrable (fun t : ℝ => Complex.exp ((t:ℂ)*z) * g t) := by
  have hi := (integrable_exp_neg_mul_sq (show 0 < a/2 by positivity)).const_mul
    (C*Real.exp (‖z‖^2/a))
  apply hi.mono' ((by fun_prop : Continuous (fun t : ℝ => Complex.exp ((t:ℂ)*z))).aestronglyMeasurable.mul hg)
  apply ae_of_all
  intro t
  simp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_exp]
  have hr : ((t:ℂ)*z).re ≤ ‖z‖*|t| := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc t*z.re ≤ |t*z.re| := le_abs_self _
      _ = |t| *|z.re| := abs_mul _ _
      _ ≤ |t| *‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)
      _ = _ := mul_comm _ _
  calc Real.exp (((t:ℂ)*z).re)*‖g t‖ ≤ Real.exp (‖z‖*|t|)*(C*Real.exp (-a*t^2)) :=
      mul_le_mul (Real.exp_le_exp.mpr hr) (hb t) (norm_nonneg _) (Real.exp_pos _).le
    _ = C*Real.exp (-a*t^2+‖z‖*|t|) := by rw [Real.exp_add]; ring
    _ ≤ C*(Real.exp (‖z‖^2/a)*Real.exp (-(a/2)*t^2)) :=
      mul_le_mul_of_nonneg_left (gaussian_linear_bound a ‖z‖ t ha) hC
    _ = _ := (mul_assoc _ _ _).symm

/-- Entire Gaussian Laplace transform: this is the smoothing seam needed for Airy uniqueness. -/
theorem gaussian_laplace_entire
    (g : ℝ → ℂ /- [definition] -/ )
    (hg : AEStronglyMeasurable g /- [standing] -/ )
    (a C : ℝ /- [definition] -/ )
    (ha : 0 < a /- [standing] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (hb : ∀ t, ‖g t‖ ≤ C*Real.exp (-a*t^2)  /- [standing] -/ )
    : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t : ℝ, Complex.exp ((t:ℂ)*z)*g t) univ := by
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  intro z
  let B := ‖z‖+1
  let d := fun w : ℂ => fun t : ℝ => (t:ℂ)*(Complex.exp ((t:ℂ)*w)*g t)
  let bound := fun t : ℝ => |t| *(C*Real.exp (B^2/a))*Real.exp (-(a/2)*t^2)
  have hi : Integrable bound := by
    have h := (integrable_mul_exp_neg_mul_sq (show 0 < a/2 by positivity)).norm.const_mul
      (C*Real.exp (B^2/a))
    convert h using 1
    funext t
    simp only [bound, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    ring
  have hm : ∀ w : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp ((t:ℂ)*w)*g t) :=
    fun w => ((by fun_prop : Continuous (fun t : ℝ => Complex.exp ((t:ℂ)*w))).aestronglyMeasurable.mul hg)
  have hd : ∀ (w : ℂ) (t : ℝ), HasDerivAt (fun w : ℂ => Complex.exp ((t:ℂ)*w)*g t) (d w t) w := by
    intro w t
    simpa [d,mul_assoc,mul_comm,mul_left_comm] using
      ((hasDerivAt_id w).const_mul (t:ℂ)).cexp.mul_const (g t)
  have hdm : AEStronglyMeasurable (d z) :=
    (Complex.continuous_ofReal.aestronglyMeasurable).mul (hm z)
  have hbound : ∀ᵐ t : ℝ, ∀ w ∈ Metric.ball z 1, ‖d w t‖ ≤ bound t := by
    apply ae_of_all
    intro t w hw
    have hwB : ‖w‖ ≤ B := by
      have hx : ‖w-z‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
      have ht := norm_add_le (w-z) z
      have he : w-z+z=w := by abel
      rw [he] at ht
      dsimp [B]
      linarith
    have hr : ((t:ℂ)*w).re ≤ B*|t| := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      calc t*w.re ≤ |t*w.re| := le_abs_self _
        _ = |t| *|w.re| := abs_mul _ _
        _ ≤ |t| *B := mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm w).trans hwB) (abs_nonneg _)
        _ = _ := mul_comm _ _
    have hs : ‖Complex.exp ((t:ℂ)*w)*g t‖ ≤
        (C*Real.exp (B^2/a))*Real.exp (-(a/2)*t^2) := by
      rw [norm_mul, Complex.norm_exp]
      calc Real.exp (((t:ℂ)*w).re)*‖g t‖ ≤ Real.exp (B*|t|)*(C*Real.exp (-a*t^2)) :=
          mul_le_mul (Real.exp_le_exp.mpr hr) (hb t) (norm_nonneg _) (Real.exp_pos _).le
        _ = C*Real.exp (-a*t^2+B*|t|) := by rw [Real.exp_add]; ring
        _ ≤ C*(Real.exp (B^2/a)*Real.exp (-(a/2)*t^2)) :=
          mul_le_mul_of_nonneg_left (gaussian_linear_bound a B t ha) hC
        _ = _ := (mul_assoc _ _ _).symm
    simpa only [d,bound,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc] using
      mul_le_mul_of_nonneg_left hs (abs_nonneg t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z (by norm_num : (0:ℝ)<1)) (Eventually.of_forall hm)
    (gaussian_laplace_integrable g hg a C ha hC hb z) hdm hbound hi
    (ae_of_all _ (fun t w _ => hd w t))).2.differentiableAt


/-- Genuine pointwise response, defined at every real coordinate. -/
noncomputable def airyResponse
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (x : ℝ /- [definition] -/ )
    : ℝ := ∫ y : ℝ, airyAiReal (x+y+s)*f y ∂halfLineMeasure

noncomputable def airyResponseSpectrum
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (ξ : ℝ /- [definition] -/ )
    : ℂ := RMTFoundations.AiryBounds.airyDampedShiftMultiplier 1 s ξ *
      (𝓕 (RMTFoundations.AiryBounds.dampedHalfLineFunction 1 f)) (-ξ)

/-- The actual response spectrum has Gaussian decay, without an assumed transform bridge. -/
theorem airyResponseSpectrum_gaussian
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : AEStronglyMeasurable (airyResponseSpectrum s f) ∧
      ∀ ξ : ℝ, ‖airyResponseSpectrum s f ξ‖ ≤
        (Real.exp (1/3)*(∫ y : ℝ, ‖dampedHalfLineFunction 1 f y‖))*
          Real.exp (-((2*Real.pi)^2)*ξ^2) := by
  have hf := RMTFoundations.AiryBounds.dampedHalfLine_integrable 1 (by norm_num) f
  have hc : Continuous (𝓕 (RMTFoundations.AiryBounds.dampedHalfLineFunction 1 f)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  refine ⟨(RMTFoundations.AiryBounds.airyDampedShiftMultiplier_integrable 1 s (by norm_num)).aestronglyMeasurable.mul
    (hc.comp continuous_neg).aestronglyMeasurable,?_⟩
  intro ξ
  have hh := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (RMTFoundations.AiryBounds.dampedHalfLineFunction 1 f) (-ξ)
  simp only [airyResponseSpectrum,RMTFoundations.AiryBounds.airyDampedShiftMultiplier,norm_mul,
    RMTFoundations.AiryBounds.fourierPositivePhase_norm,one_mul]
  rw [RMTFoundations.Airy.airyDamped_fourier_norm 1 ξ (by norm_num)]
  calc Real.exp (1^3/3-1*(2*Real.pi*ξ)^2)*‖(𝓕 (RMTFoundations.AiryBounds.dampedHalfLineFunction 1 f)) (-ξ)‖ ≤
      Real.exp (1^3/3-1*(2*Real.pi*ξ)^2)*(∫ y : ℝ, ‖dampedHalfLineFunction 1 f y‖) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = _ := by
      rw [show (1:ℝ)^3/3-1*(2*Real.pi*ξ)^2 = 1/3+(-((2*Real.pi)^2)*ξ^2) by ring,
        Real.exp_add]
      ring

noncomputable def airyResponseExtension
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : ℂ := Complex.exp (-(z+(s:ℂ))) *
      ∫ ξ : ℝ, Complex.exp ((ξ:ℂ)*((2*Real.pi:ℂ)*Complex.I*z))*airyResponseSpectrum s f ξ

/-- Gaussian Fourier smoothing supplies a genuine entire extension of the Airy response. -/
theorem airyResponseExtension_entire
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : AnalyticOnNhd ℂ (airyResponseExtension s f) univ := by
  have hc : 0 ≤ Real.exp (1/3)*(∫ y : ℝ, ‖dampedHalfLineFunction 1 f y‖) :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun y => norm_nonneg _))
  have ha : 0 < (2*Real.pi)^2 := sq_pos_of_pos (by positivity)
  have hG := gaussian_laplace_entire (airyResponseSpectrum s f)
    (airyResponseSpectrum_gaussian s f).1 ((2*Real.pi)^2) _ ha hc
    (airyResponseSpectrum_gaussian s f).2
  have hdG := Complex.analyticOnNhd_univ_iff_differentiable.mp hG
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  exact ((differentiable_id.add_const (s:ℂ)).neg.cexp).mul
    (hdG.comp (differentiable_id.const_mul ((2*Real.pi:ℂ)*Complex.I)))

/-- The entire extension equals the genuine integral response on the real axis. -/
theorem airyResponseExtension_real
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (x : ℝ /- [definition] -/ )
    : airyResponseExtension s f (x:ℂ) = (airyResponse s f x : ℂ) := by
  have he : (∫ ξ : ℝ, Complex.exp ((ξ:ℂ)*((2*Real.pi:ℂ)*Complex.I*(x:ℂ)))*
      airyResponseSpectrum s f ξ) = (𝓕⁻ (airyResponseSpectrum s f)) x := by
    rw [RMTFoundations.AiryBounds.inverse_fourier_eq_positivePhase]
    apply integral_congr_ae
    filter_upwards [] with ξ
    congr 1
    unfold RMTFoundations.AiryBounds.fourierPositivePhase
    congr 1
    push_cast
    ring
  unfold airyResponseExtension
  rw [he]
  unfold airyResponseSpectrum
  rw [← RMTFoundations.AiryBounds.inverse_fourier_kernel_apply (RMTFoundations.AiryBounds.airyDampedShiftMultiplier 1 s)
    (RMTFoundations.AiryBounds.dampedHalfLineFunction 1 f) (RMTFoundations.AiryBounds.airyDampedShiftMultiplier_integrable 1 s (by norm_num))
    (RMTFoundations.AiryBounds.dampedHalfLine_integrable 1 (by norm_num) f) x]
  rw [RMTFoundations.AiryBounds.airyDampedShift_response 1 s x (by norm_num) f]
  change Complex.exp (-((x:ℂ)+(s:ℂ))) *
    ((Real.exp (1*(x+s)):ℂ)*(airyResponse s f x:ℂ)) = _
  rw [one_mul,Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
  simp only [Complex.ofReal_add,neg_add_cancel,Complex.exp_zero,one_mul]

/-- Compactness turns exclusion of both unit eigenvalues into strict contraction. -/
theorem norm_lt_one_of_no_unit_eigenvalue
    {E : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [CompleteSpace E /- [definition] -/ ]
    [Nontrivial E /- [definition] -/ ]
    (T : E →L[ℝ] E /- [definition] -/ )
    (hc : IsCompactOperator T /- [standing] -/ )
    (hs : T.IsSymmetric /- [standing] -/ )
    (hn : ‖T‖ ≤ 1 /- [standing] -/ )
    (he : ∀ μ : ℝ, |μ| = 1 → ¬Module.End.HasEigenvalue T.toLinearMap μ /- [standing] -/ )
    : ‖T‖ < 1 := by
  by_contra! h
  have hn1 : ‖T‖ = 1 := le_antisymm hn h
  have hp : (1 : ℝ) ∈ resolventSet ℝ T := by
    by_contra hnot
    exact he 1 (by norm_num) ((hc.hasEigenvalue_iff_mem_spectrum
      (by norm_num : (1 : ℝ) ≠ 0)).mpr hnot)
  have hm : (-1 : ℝ) ∈ resolventSet ℝ T := by
    by_contra hnot
    exact he (-1) (by norm_num) ((hc.hasEigenvalue_iff_mem_spectrum
      (by norm_num : (-1 : ℝ) ≠ 0)).mpr hnot)
  obtain ⟨ε,hε,hb⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet
    (by simpa [hn1] using hp) (by simpa [hn1] using hm)
  have hh : ‖T‖ ≤ ‖T‖ - ε := by
    calc ‖T‖ = ⨆ x, |T.rayleighQuotient x| := T.norm_eq_iSup_rayleighQuotient hs
         _ ≤ ‖T‖ - ε := ciSup_le hb
  linarith


/-- Nondegenerate joint inhabitation of every spectral-reduction binder. -/
theorem strict_spectral_joint_probe
    : ∃ T : ℝ →L[ℝ] ℝ, IsCompactOperator T ∧ T.IsSymmetric ∧ ‖T‖ ≤ 1 ∧
      (∀ μ : ℝ, |μ| = 1 → ¬Module.End.HasEigenvalue T.toLinearMap μ) ∧
      T 1 = 1/2 ∧ ‖T‖ < 1 := by
  let T : ℝ →L[ℝ] ℝ := (1/2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_dom T
  have hs : T.IsSymmetric := by
    intro x y
    simp [T,inner_smul_left,inner_smul_right]
    ring
  have hn : ‖T‖ = 1/2 := by norm_num [T,norm_smul]
  have he : ∀ μ : ℝ, |μ| = 1 → ¬Module.End.HasEigenvalue T.toLinearMap μ := by
    intro μ hμ hm
    obtain ⟨v,hv,hne⟩ := hm.exists_hasEigenvector
    have hh : T v = μ • v := Module.End.mem_eigenspace_iff.mp hv
    have hn' := congrArg norm hh
    have hp := norm_pos_iff.mpr hne
    norm_num [T,norm_smul,Real.norm_eq_abs,hμ] at hn'
    change 0 < |v| at hp
    nlinarith
  refine ⟨T,hc,hs,by rw [hn]; norm_num,he,?_,?_⟩
  · norm_num [T]
  · exact norm_lt_one_of_no_unit_eigenvalue T hc hs (by rw [hn]; norm_num) he

/-- Entire functions vanishing on a real open interval vanish globally. -/
theorem entire_zero_of_real_unit_interval
    (G : ℂ → ℂ /- [definition] -/ )
    (hG : AnalyticOnNhd ℂ G univ /- [standing] -/ )
    (hz : ∀ x : ℝ, x ∈ Ioo 0 1 → G (x:ℂ) = 0 /- [standing] -/ )
    : G = 0 := by
  have hh : (1/2 : ℂ) ∈ closure ({z : ℂ | G z = 0} \ {(1/2:ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (ε/2) (1/4)
    have hd : 0 < δ := lt_min (by positivity) (by norm_num)
    have hd4 : δ ≤ 1/4 := min_le_right _ _
    have hde : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨((1/2+δ : ℝ):ℂ),?_,?_⟩
    · constructor
      · exact hz _ ⟨by linarith,by linarith⟩
      · simp only [mem_singleton_iff]
        intro he
        have hh := congrArg Complex.re he
        norm_num at hh
        linarith
    · rw [dist_comm]
      have hh : ((1/2+δ : ℝ):ℂ) - (1/2:ℂ) = (δ:ℂ) := by push_cast; ring
      simpa only [dist_eq_norm,hh,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] using hde
  have h := hG.eqOn_zero_of_preconnected_of_mem_closure isPreconnected_univ (mem_univ _) hh
  funext z
  exact h (mem_univ z)

/-- Exact translation of a half-line integral. -/
theorem integral_Ioi_translate
    (F : ℝ → ℝ /- [definition] -/ )
    (a b : ℝ /- [definition] -/ )
    : (∫ x in Ioi a, F (x+b)) = ∫ x in Ioi (a+b), F x := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  have he : (fun x : ℝ => (Ioi a).indicator (fun x => F (x+b)) x) =
      (fun x : ℝ => (Ioi (a+b)).indicator F (x+b)) := by
    funext x
    simp only [indicator,mem_Ioi,add_lt_add_iff_right]
  rw [he]
  exact integral_add_right_eq_self _ b

/-- A nonnegative integrable density loses zero mass on a subset exactly when it vanishes there. -/
theorem zero_on_removed_region_of_integral_eq
    (F : ℝ → ℝ /- [definition] -/ )
    (hi : IntegrableOn F (Ioi 0)  /- [standing] -/ )
    (hn : ∀ x, 0 ≤ F x /- [standing] -/ )
    (he : (∫ x in Ioi 0, F x) = ∫ x in Ioi 1, F x /- [standing] -/ )
    : F =ᵐ[volume.restrict (Ioc 0 1)] 0 := by
  have hsub : Ioi (1:ℝ) ⊆ Ioi 0 := by intro x hx; simp only [mem_Ioi] at *; linarith
  have hs : Ioc (0:ℝ) 1 ⊆ Ioi 0 := by intro x hx; exact hx.1
  have hid := hi.mono_set hs
  have hit := hi.mono_set hsub
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  have hu : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (hx|hx) <;> linarith
    · intro hx
      by_cases hy : x ≤ 1
      · exact Or.inl ⟨hx,hy⟩
      · exact Or.inr (lt_of_not_ge hy)
  have hh := setIntegral_union hdisj measurableSet_Ioi hid hit
  rw [hu] at hh
  have hzero : (∫ x in Ioc 0 1, F x) = 0 := by linarith
  exact (integral_eq_zero_iff_of_nonneg (fun x => hn x) hid).mp hzero


/-- The genuine response has the operator's squared L2 norm. -/
theorem airyResponse_norm_sq
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : (∫ x : ℝ, airyResponse s f x ^ 2 ∂halfLineMeasure) = ‖airyHankelShift s f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [airyHankelShift_apply_ae s f] with x hx
  change (airyResponse s f x)^2 = inner ℝ ((airyHankelShift s f) x) ((airyHankelShift s f) x)
  rw [hx]
  simp only [airyResponse,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

theorem airyResponse_sq_integrable
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : Integrable (fun x : ℝ => airyResponse s f x ^ 2) halfLineMeasure := by
  apply (L2.integrable_inner (𝕜 := ℝ) (airyHankelShift s f) (airyHankelShift s f)).congr
  filter_upwards [airyHankelShift_apply_ae s f] with x hx
  rw [hx]
  simp only [airyResponse,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

theorem airyResponse_translate
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (x : ℝ /- [definition] -/ )
    : airyResponse (s-1) f (x+1) = airyResponse s f x := by
  unfold airyResponse
  congr 1
  funext y
  congr 2
  ring

theorem airyResponse_continuous
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : Continuous (airyResponse s f) := by
  have h := Complex.continuous_re.comp
    ((airyResponseExtension_entire s f).continuous.comp Complex.continuous_ofReal)
  have he : (fun x : ℝ => (airyResponseExtension s f (x:ℂ)).re) = airyResponse s f := by
    funext x
    rw [airyResponseExtension_real s f x,Complex.ofReal_re]
  change Continuous (fun x : ℝ => (airyResponseExtension s f (x:ℂ)).re) at h
  rwa [he] at h

/-- Equality in the contraction bound forces zero response on the interval removed by a shift. -/
theorem airyResponse_zero_interval_of_equal_norm
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (hn : ‖airyHankelShift s f‖ = ‖f‖ /- [standing] -/ )
    : ∀ x : ℝ, x ∈ Ioo 0 1 → airyResponse (s-1) f x = 0 := by
  let F := fun x : ℝ => airyResponse (s-1) f x ^ 2
  have hi : IntegrableOn F (Ioi 0) := airyResponse_sq_integrable (s-1) f
  have ht : (∫ x in Ioi 1, F x) = ‖f‖^2 := by
    have hh := integral_Ioi_translate F 0 1
    simp only [zero_add] at hh
    rw [← hh]
    change (∫ x in Ioi 0, airyResponse (s-1) f (x+1)^2) = ‖f‖^2
    simp_rw [airyResponse_translate]
    change (∫ x : ℝ, airyResponse s f x ^ 2 ∂halfLineMeasure) = ‖f‖^2
    rw [airyResponse_norm_sq s f,hn]
  have htotal : (∫ x in Ioi 0, F x) ≤ ‖f‖^2 := by
    rw [show (∫ x in Ioi 0, F x) = ‖airyHankelShift (s-1) f‖^2 from
      airyResponse_norm_sq (s-1) f]
    exact pow_le_pow_left₀ (norm_nonneg _) (RMTFoundations.AiryBounds.airyHankelShift_norm_apply_le (s-1) f) 2
  have hsub : Ioi (1:ℝ) ⊆ Ioi 0 := by
    intro x hx
    exact lt_trans (show (0:ℝ)<1 by norm_num) hx
  have hrev := setIntegral_mono_set hi (ae_of_all _ (fun x => sq_nonneg _))
    (ae_of_all _ (fun x hx => hsub hx))
  change (∫ x in Ioi 1, F x) ≤ ∫ x in Ioi 0, F x at hrev
  have he : (∫ x in Ioi 0, F x) = ∫ x in Ioi 1, F x := by linarith
  have hz := zero_on_removed_region_of_integral_eq F hi (fun x => sq_nonneg _) he
  have hpoint := MeasureTheory.Measure.eqOn_Ioc_of_ae_eq volume hz
    ((airyResponse_continuous (s-1) f).pow 2).continuousOn continuous_const.continuousOn
  intro x hx
  have hh : airyResponse (s-1) f x ^ 2 = 0 := hpoint ⟨hx.1,hx.2.le⟩
  exact sq_eq_zero_iff.mp hh

/-- Entire uniqueness discharges the interval-vanishing obstruction. -/
theorem airyResponse_zero_of_equal_norm
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (hn : ‖airyHankelShift s f‖ = ‖f‖ /- [standing] -/ )
    : airyResponse s f = 0 := by
  have he := entire_zero_of_real_unit_interval (airyResponseExtension (s-1) f)
    (airyResponseExtension_entire (s-1) f) (by
      intro x hx
      rw [airyResponseExtension_real,
        airyResponse_zero_interval_of_equal_norm s f hn x hx,Complex.ofReal_zero])
  funext x
  have hh : airyResponse (s-1) f (x+1) = 0 := by
    have h0 := congrFun he ((x+1:ℝ):ℂ)
    rw [airyResponseExtension_real,Pi.zero_apply] at h0
    exact_mod_cast h0
  simpa only [airyResponse_translate,Pi.zero_apply] using hh

/-- Global strict contraction, from compactness, shifted norm loss and entire uniqueness. -/
theorem norm_airyHankelShift_lt_one
    (s : ℝ /- [definition] -/ )
    : ‖airyHankelShift s‖ < 1 := by
  letI : Nontrivial (Lp ℝ 2 halfLineMeasure) := ⟨⟨airyBoundaryVector s,0,airyBoundaryVector_ne_zero s⟩⟩
  apply norm_lt_one_of_no_unit_eigenvalue (airyHankelShift s)
    (isTraceClass_airyHankelShift s).isCompactOperator
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_airyHankelShift s))
    (RMTFoundations.AiryBounds.norm_airyHankelShift_le_one s)
  intro μ hμ hm
  obtain ⟨f,hf,hne⟩ := hm.exists_hasEigenvector
  have hh : airyHankelShift s f = μ • f := Module.End.mem_eigenspace_iff.mp hf
  have hn : ‖airyHankelShift s f‖ = ‖f‖ := by rw [hh,norm_smul,Real.norm_eq_abs,hμ,one_mul]
  have hz := airyResponse_zero_of_equal_norm s f hn
  have hzero : airyHankelShift s f = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [airyHankelShift_apply_ae s f] with x hx
    rw [hx]
    have hh := congrFun hz x
    simpa only [airyResponse,Pi.zero_apply] using hh
  exact hne (norm_eq_zero.mp (by rw [←hn,hzero,norm_zero]))

/-- Genuine TW1 positivity and sharp upper bound now have no mathematical premises. -/
theorem TW1R_positive_bounds
    (s : ℝ /- [definition] -/ )
    : 0 < TW1R s ∧ TW1R s ≤ Real.exp (-(airyTailIntegral airyAiReal s / 2)) ∧
      Real.exp (-(airyTailIntegral airyAiReal s / 2)) < 1 :=
  TW1R_bounds_of_contraction s (norm_airyHankelShift_lt_one s)

/-- Genuine nondegenerate instance of all strict-contraction and determinant theorems. -/
theorem airy_strict_all_binder_joint_probe
    (s : ℝ /- [definition] -/ )
    : airyAiReal 0 > 0 ∧ ‖shiftedUnitVector 0‖ = 1 ∧
      airyBoundaryVector s ≠ 0 ∧ ‖airyHankelShift s‖ < 1 ∧ 0 < TW1R s ∧ TW1R s < 1 :=
  ⟨airyAiReal_zero_pos,shiftedUnitVector_norm 0,airyBoundaryVector_ne_zero s,
    norm_airyHankelShift_lt_one s,(TW1R_positive_bounds s).1,TW1R_lt_one s⟩

/-- A genuine nonzero response witnesses inhabitation of the analytic theorems. -/
theorem airyResponse_boundary_zero_pos
    (s : ℝ /- [definition] -/ )
    : airyResponse s (airyBoundaryVector s) 0 = airyEnergy s := by
  unfold airyResponse
  calc (∫ y : ℝ, airyAiReal (0+y+s)*(airyBoundaryVector s) y ∂halfLineMeasure) =
      ∫ y : ℝ, (airyAiReal (s+y))^2 ∂halfLineMeasure := by
        apply integral_congr_ae
        filter_upwards [airyBoundaryVector_apply_ae s] with y hy
        rw [hy]
        simp only [zero_add,add_comm]
        ring
       _ = airyEnergy s := airyAiReal_sq_integral s

/-- The actual entire extension is nonzero and matches its real response at every shift. -/
theorem airy_response_analytic_joint_probe
    (s : ℝ /- [definition] -/ )
    : ∃ f : Lp ℝ 2 halfLineMeasure, f ≠ 0 ∧
      AnalyticOnNhd ℂ (airyResponseExtension s f) univ ∧
      (∀ x : ℝ, airyResponseExtension s f (x:ℂ) = (airyResponse s f x:ℂ)) ∧
      airyResponseExtension s f 0 ≠ 0 := by
  refine ⟨airyBoundaryVector s,airyBoundaryVector_ne_zero s,
    airyResponseExtension_entire s (airyBoundaryVector s),
    airyResponseExtension_real s (airyBoundaryVector s),?_⟩
  rw [show (0:ℂ)=(0:ℝ) from rfl,airyResponseExtension_real,airyResponse_boundary_zero_pos]
  exact_mod_cast (airyEnergy_pos s).ne'

/-- The canonical operator-determinant version inherits the unconditional sharp range. -/
theorem airyOperatorTW1_positive_bounds
    (s : ℝ /- [definition] -/ )
    : 0 < airyOperatorTW1 s ∧ airyOperatorTW1 s ≤ Real.exp (-(airyTailIntegral airyAiReal s / 2)) ∧
      Real.exp (-(airyTailIntegral airyAiReal s / 2)) < 1 := by
  rw [← TW1R_eq_airyOperatorTW1 s]
  exact TW1R_positive_bounds s

/-- The genuine boundary certificate is positive on the nonnegative half-line. -/
theorem airy_hankel_inverse_boundary_pos_of_nonneg
    (s : ℝ /- [definition] -/ )
    (hs : 0 ≤ s /- [standing] -/ )
    : 0 < airyAiReal s + inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1-airyHankelShift s) (airyBoundaryVector s)) :=
  airy_hankel_inverse_boundary_pos_nonneg s (norm_airyHankelShift_lt_one s) hs

/-- The far-left boundary certificate also has its contraction premise discharged. -/
theorem airy_hankel_inverse_boundary_nonneg_of_far_left
    (s : ℝ /- [definition] -/ )
    (hs : s ≤ -4 / (deriv airyAiReal 0)^2 /- [standing] -/ )
    : 0 ≤ airyAiReal s + inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1-airyHankelShift s) (airyBoundaryVector s)) :=
  airy_hankel_inverse_boundary_nonneg_far_left s (norm_airyHankelShift_lt_one s) hs

/-- Both boundary-theorem binder families hold on genuine nonzero Airy instances. -/
theorem airy_boundary_certificate_joint_probe
    : ∃ sp sm : ℝ, 0 ≤ sp ∧ sm ≤ -4 / (deriv airyAiReal 0)^2 ∧
      ‖airyHankelShift sp‖ < 1 ∧ ‖airyHankelShift sm‖ < 1 ∧
      airyBoundaryVector sp ≠ 0 ∧ airyBoundaryVector sm ≠ 0 ∧
      0 < airyAiReal sp + inner ℝ (airyBoundaryVector sp)
        (Ring.inverse (1-airyHankelShift sp) (airyBoundaryVector sp)) ∧
      0 ≤ airyAiReal sm + inner ℝ (airyBoundaryVector sm)
        (Ring.inverse (1-airyHankelShift sm) (airyBoundaryVector sm)) := by
  let sm : ℝ := -4 / (deriv airyAiReal 0)^2 - 1
  have hm : sm ≤ -4 / (deriv airyAiReal 0)^2 := by dsimp [sm]; linarith
  refine ⟨0,sm,le_rfl,hm,norm_airyHankelShift_lt_one 0,norm_airyHankelShift_lt_one sm,
    airyBoundaryVector_ne_zero 0,airyBoundaryVector_ne_zero sm,?_,?_⟩
  · exact airy_hankel_inverse_boundary_pos_of_nonneg 0 le_rfl
  · exact airy_hankel_inverse_boundary_nonneg_of_far_left sm hm




/-- Upper-tail calculus; no operator-determinant premise occurs here. -/
theorem shift_tail_hasDerivAt
    (f : ℝ → ℝ /- [definition] -/ )
    (hc : Continuous f /- [standing] -/ )
    (hi : ∀ a, IntegrableOn f (Ioi a)  /- [standing] -/ )
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (fun a => ∫ u in Ioi a, f u) (-f s) s := by
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 s) hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt).const_sub (∫ u in Ioi 0, f u)
  convert! hd using 1
  funext a
  have he := intervalIntegral.integral_interval_add_Ioi (hi 0) (hi a)
  linarith

/-- Exact simultaneous translation of both entries of the Airy square kernel. -/
theorem airyKernelIntegral_shift_eq_tail
    (x y s : ℝ /- [definition] -/ )
    : airyKernelIntegral (x+s) (y+s) =
      ∫ u in Ioi s, airyAiReal (x+u) * airyAiReal (y+u) := by
  have h := (fredholm_measurePreserving_shift s).integral_comp
    (MeasurableEquiv.addRight s).measurableEmbedding
    (fun u => airyAiReal (x+u) * airyAiReal (y+u))
  simpa only [airyKernelIntegral, halfLineMeasure, Function.comp_apply,
    MeasurableEquiv.coe_addRight, add_assoc, add_left_comm, add_comm] using h

/-- All real upper tails of the Airy product are integrable; this is derived. -/
theorem airy_product_all_tails_integrable
    (x y a : ℝ /- [definition] -/ )
    : IntegrableOn (fun u => airyAiReal (x+u) * airyAiReal (y+u)) (Ioi a) := by
  apply ((fredholm_measurePreserving_shift a).integrable_comp_emb
    (MeasurableEquiv.addRight a).measurableEmbedding).mp
  simpa only [IntegrableOn, Function.comp_def, MeasurableEquiv.coe_addRight, halfLineMeasure,
    add_assoc, add_left_comm, add_comm] using integrable_airyAiReal_mul_Ioi (x+a) (y+a)

/-- The derivative of the square kernel is rank one. It is not the derivative of B itself. -/
theorem hasDerivAt_airyKernelIntegral_simultaneous_shift
    (x y s : ℝ /- [definition] -/ )
    : HasDerivAt (fun t => airyKernelIntegral (x+t) (y+t))
      (-airyAiReal (x+s) * airyAiReal (y+s)) s := by
  have hc : Continuous (fun u => airyAiReal (x+u) * airyAiReal (y+u)) :=
    (Ai_continuous.comp (continuous_const.add continuous_id)).mul
      (Ai_continuous.comp (continuous_const.add continuous_id))
  have h := shift_tail_hasDerivAt _ hc (airy_product_all_tails_integrable x y) s
  have he : (fun t => airyKernelIntegral (x+t) (y+t)) =
      (fun t => ∫ u in Ioi t, airyAiReal (x+u) * airyAiReal (y+u)) :=
    funext (airyKernelIntegral_shift_eq_tail x y)
  rw [he]
  simpa only [neg_mul] using h

/-- Every weighted finite quadratic form of the square kernel has the exact negative-square derivative. -/
theorem hasDerivAt_airy_square_finite_quadratic
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    (x w c : ι → ℝ /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : HasDerivAt
      (fun t => ∑ i, ∑ j, (w i*c i) * (w j*c j) * airyKernelIntegral (x i+t) (x j+t))
      (-(∑ i, w i*c i*airyAiReal (x i+s))^2) s := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hasDerivAt_airyKernelIntegral_simultaneous_shift (x i) (x j) s).const_mul
        ((w i*c i)*(w j*c j))))
  convert! hd using 1
  rw [pow_two, Finset.sum_mul_sum]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Discrete compressions of B squared decrease in the quadratic-form order, without sign restrictions on weights. -/
theorem airy_square_finite_quadratic_antitone
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    (x w c : ι → ℝ /- [definition] -/ )
    : Antitone
      (fun t => ∑ i, ∑ j, (w i*c i) * (w j*c j) * airyKernelIntegral (x i+t) (x j+t)) := by
  apply antitone_of_hasDerivAt_nonpos (hasDerivAt_airy_square_finite_quadratic x w c)
  intro s
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Genuine nonzero Airy data jointly inhabit all finite-quadratic and derivative binders. -/
theorem airy_square_shift_joint_probe
    : ∃ (x w c : Fin 2 → ℝ) (s : ℝ),
      (∑ i, w i*c i*airyAiReal (x i+s)) ≠ 0 ∧
      HasDerivAt
        (fun t => ∑ i, ∑ j, (w i*c i) * (w j*c j) * airyKernelIntegral (x i+t) (x j+t))
        (-(∑ i, w i*c i*airyAiReal (x i+s))^2) s ∧
      Antitone
        (fun t => ∑ i, ∑ j, (w i*c i) * (w j*c j) * airyKernelIntegral (x i+t) (x j+t)) := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ => 1, 0, ?_,
    hasDerivAt_airy_square_finite_quadratic _ _ _ _, airy_square_finite_quadratic_antitone _ _ _⟩
  have hp := airyAiReal_zero_pos
  simp only [zero_add, one_mul, Fin.sum_univ_two]
  linarith


/-- General translation law for the actual integral response. -/
theorem airyResponse_general_translate
    (s x : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : airyResponse 0 f (x+s) = airyResponse s f x := by
  unfold airyResponse
  congr 1
  funext y
  congr 2
  ring

/-- A genuine response square is integrable on every translated half-line. -/
theorem airyResponse_sq_all_tails_integrable
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (a : ℝ /- [definition] -/ )
    : IntegrableOn (fun x => airyResponse 0 f x ^ 2) (Ioi a) := by
  apply ((fredholm_measurePreserving_shift a).integrable_comp_emb
    (MeasurableEquiv.addRight a).measurableEmbedding).mp
  simpa only [Function.comp_def, MeasurableEquiv.coe_addRight,
    airyResponse_general_translate, halfLineMeasure] using airyResponse_sq_integrable a f

/-- The moving-operator square norm is the upper tail of one fixed continuous response. -/
theorem airyResponse_norm_sq_eq_fixed_tail
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : ‖airyHankelShift s f‖ ^ 2 = ∫ x in Ioi s, airyResponse 0 f x ^ 2 := by
  rw [← airyResponse_norm_sq s f]
  have h := integral_Ioi_translate (fun x => airyResponse 0 f x ^ 2) 0 s
  simp only [zero_add, airyResponse_general_translate] at h
  exact h

/-- Unconditional weak derivative of B squared: a negative square at the boundary. -/
theorem hasDerivAt_airyHankelShift_norm_sq
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (fun t => ‖airyHankelShift t f‖ ^ 2)
      (-(airyResponse s f 0)^2) s := by
  have hd := shift_tail_hasDerivAt (fun x => airyResponse 0 f x ^ 2)
    ((airyResponse_continuous 0 f).pow 2) (airyResponse_sq_all_tails_integrable f) s
  have he : (fun t => ‖airyHankelShift t f‖ ^ 2) =
      (fun t => ∫ x in Ioi t, airyResponse 0 f x ^ 2) :=
    funext (fun t => airyResponse_norm_sq_eq_fixed_tail t f)
  rw [he]
  have ht := airyResponse_general_translate s 0 f
  simp only [zero_add] at ht
  simpa only [ht] using hd

/-- The actual square-operator quadratic form has the rank-one weak derivative. -/
theorem hasDerivAt_airyKernelShift_quadratic
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (fun t => inner ℝ f (airyKernelShift t f))
      (-(airyResponse s f 0)^2) s := by
  have he : (fun t => inner ℝ f (airyKernelShift t f)) =
      (fun t => ‖airyHankelShift t f‖^2) := by
    funext t
    change inner ℝ f (airyHankelShift t (airyHankelShift t f)) = _
    have hh := (isSelfAdjoint_airyHankelShift t).isSymmetric f (airyHankelShift t f)
    change inner ℝ (airyHankelShift t f) (airyHankelShift t f) =
      inner ℝ f (airyHankelShift t (airyHankelShift t f)) at hh
    exact hh.symm.trans (real_inner_self_eq_norm_sq _)
  rw [he]
  exact hasDerivAt_airyHankelShift_norm_sq f s

/-- The genuine Airy square operators decrease in quadratic-form order at every shift. -/
theorem airyKernelShift_quadratic_antitone
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : Antitone (fun t => inner ℝ f (airyKernelShift t f)) := by
  apply antitone_of_hasDerivAt_nonpos (hasDerivAt_airyKernelShift_quadratic f)
  intro s
  exact neg_nonpos.mpr (sq_nonneg _)

/-- The weak derivative is nonzero on an actual nonzero Airy vector at every shift. -/
theorem airy_square_operator_derivative_joint_probe
    (s : ℝ /- [definition] -/ )
    : ∃ f : Lp ℝ 2 halfLineMeasure, f ≠ 0 ∧
      HasDerivAt (fun t => inner ℝ f (airyKernelShift t f))
        (-(airyResponse s f 0)^2) s ∧
      -(airyResponse s f 0)^2 < 0 ∧
      Antitone (fun t => inner ℝ f (airyKernelShift t f)) := by
  refine ⟨airyBoundaryVector s, airyBoundaryVector_ne_zero s,
    hasDerivAt_airyKernelShift_quadratic _ s, ?_, airyKernelShift_quadratic_antitone _⟩
  rw [airyResponse_boundary_zero_pos]
  exact neg_neg_of_pos (sq_pos_of_pos (airyEnergy_pos s))

/-- Evaluation of the genuine response at zero is pairing with the actual Airy boundary vector. -/
theorem airyResponse_boundary_eq_inner
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : airyResponse s f 0 = inner ℝ (airyBoundaryVector s) f := by
  rw [L2.inner_def]
  unfold airyResponse
  apply integral_congr_ae
  filter_upwards [airyBoundaryVector_apply_ae s] with y hy
  simp only [zero_add, add_zero, Real.inner_apply, hy, mul_comm, add_comm]

/-- The rank-one quadratic derivative uses the same Airy space and operator. -/
theorem hasDerivAt_airyKernelShift_quadratic_rankOne
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (fun t => inner ℝ f (airyKernelShift t f))
      (-(inner ℝ (airyBoundaryVector s) f)^2) s := by
  simpa only [airyResponse_boundary_eq_inner] using hasDerivAt_airyKernelShift_quadratic f s

/-- Polarized weak derivative of the actual square operator; no derivative assumption is introduced. -/
theorem hasDerivAt_airyKernelShift_pairing
    (f g : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : HasDerivAt (fun t => inner ℝ f (airyKernelShift t g))
      (-(inner ℝ (airyBoundaryVector s) f) * inner ℝ (airyBoundaryVector s) g) s := by
  have hsym : ∀ t, inner ℝ f (airyKernelShift t g) = inner ℝ g (airyKernelShift t f) := by
    intro t
    calc inner ℝ f (airyKernelShift t g)
        = inner ℝ (airyHankelShift t f) (airyHankelShift t g) :=
          ((isSelfAdjoint_airyHankelShift t).isSymmetric f (airyHankelShift t g)).symm
      _ = inner ℝ (airyHankelShift t g) (airyHankelShift t f) := real_inner_comm _ _
      _ = inner ℝ g (airyKernelShift t f) :=
          (isSelfAdjoint_airyHankelShift t).isSymmetric g (airyHankelShift t f)
  have he : (fun t => inner ℝ f (airyKernelShift t g)) =
      (fun t => (inner ℝ (f+g) (airyKernelShift t (f+g)) -
        inner ℝ f (airyKernelShift t f) - inner ℝ g (airyKernelShift t g))/2) := by
    funext t
    simp only [map_add, inner_add_left, inner_add_right]
    rw [← hsym t]
    ring
  have hd := (((hasDerivAt_airyKernelShift_quadratic_rankOne (f+g) s).sub
    (hasDerivAt_airyKernelShift_quadratic_rankOne f s)).sub
    (hasDerivAt_airyKernelShift_quadratic_rankOne g s)).div_const 2
  rw [he]
  convert! hd using 1
  simp only [inner_add_right]
  ring

/-- Nonzero actual Airy vectors jointly instantiate the full weak rank-one derivative. -/
theorem airy_square_pairing_joint_probe
    (s : ℝ /- [definition] -/ )
    : ∃ f g : Lp ℝ 2 halfLineMeasure, f ≠ 0 ∧ g ≠ 0 ∧
      HasDerivAt (fun t => inner ℝ f (airyKernelShift t g))
        (-(inner ℝ (airyBoundaryVector s) f) * inner ℝ (airyBoundaryVector s) g) s ∧
      inner ℝ (airyBoundaryVector s) f ≠ 0 ∧ inner ℝ (airyBoundaryVector s) g ≠ 0 := by
  refine ⟨airyBoundaryVector s, airyBoundaryVector s,
    airyBoundaryVector_ne_zero s, airyBoundaryVector_ne_zero s,
    hasDerivAt_airyKernelShift_pairing _ _ s, ?_, ?_⟩ <;>
    rw [airyBoundaryVector_inner_self] <;> exact (airyEnergy_pos s).ne'

#check RMTFoundations.TWOneBounds.hasDerivAt_airyKernelIntegral_simultaneous_shift
#check RMTFoundations.TWOneBounds.hasDerivAt_airyKernelShift_pairing
#check RMTFoundations.TWOneBounds.airyKernelShift_quadratic_antitone
#check RMTFoundations.TWOneBounds.TW1R_positive_bounds


/-- The square kernel inherits strict contraction from the already proved Hankel strictness. -/
theorem norm_airyKernelShift_lt_one
    (s : ℝ /- [definition] -/ )
    : ‖airyKernelShift s‖ < 1 := by
  have hn := norm_airyHankelShift_lt_one s
  calc ‖airyKernelShift s‖ ≤ ‖airyHankelShift s‖ * ‖airyHankelShift s‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ < 1 := by nlinarith [norm_nonneg (airyHankelShift s)]

/-- Canonical parity decomposition: both resolvents are genuine ring inverses and no inverse premise remains. -/
theorem airy_boundary_resolvent_parity_identity
    (s : ℝ /- [definition] -/ )
    : airyAiReal s + inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1-airyHankelShift s) (airyBoundaryVector s)) =
      (airyAiReal s + inner ℝ (airyBoundaryVector s)
        (airyHankelShift s (Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)))) +
      inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)) := by
  have hleft := contraction_ringInverse_left (airyHankelShift s) (norm_airyHankelShift_lt_one s)
  have hright : ∀ x, Ring.inverse (1-airyKernelShift s) x -
      airyHankelShift s (airyHankelShift s (Ring.inverse (1-airyKernelShift s) x)) = x := by
    intro x
    exact contraction_ringInverse_right (airyKernelShift s) (norm_airyKernelShift_lt_one s) x
  have he := resolvent_parity_identity (airyHankelShift s)
    (Ring.inverse (1-airyHankelShift s)) (Ring.inverse (1-airyKernelShift s))
    hleft hright (airyBoundaryVector s)
  rw [he, inner_add_right]
  ring

/-- The u term of the canonical q+u certificate is strictly positive, without a q-sign premise. -/
theorem airy_inverse_square_boundary_positive
    (s : ℝ /- [definition] -/ )
    : 0 < inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)) := by
  have hH := (isSelfAdjoint_airyHankelShift s).isSymmetric
  have hK : ∀ x y, inner ℝ (airyKernelShift s x) y = inner ℝ x (airyKernelShift s y) := by
    intro x y
    exact (hH (airyHankelShift s x) y).trans (hH x (airyHankelShift s y))
  have hn := norm_airyKernelShift_lt_one s
  have hl := contraction_resolvent_half_norm_lower (airyKernelShift s)
    (Ring.inverse (1-airyKernelShift s)) hn hK
    (contraction_ringInverse_right (airyKernelShift s) hn)
    (contraction_ringInverse_left (airyKernelShift s) hn) (airyBoundaryVector s)
  rw [airyBoundaryVector_inner_self] at hl
  linarith [airyEnergy_pos s]

/-- Both canonical inverses and the parity certificate are inhabited by the same nonzero actual Airy row. -/
theorem airy_canonical_parity_joint_probe
    (s : ℝ /- [definition] -/ )
    : airyBoundaryVector s ≠ 0 ∧ ‖airyHankelShift s‖ < 1 ∧ ‖airyKernelShift s‖ < 1 ∧
      (∀ x, Ring.inverse (1-airyHankelShift s) (x-airyHankelShift s x) = x) ∧
      (∀ x, Ring.inverse (1-airyKernelShift s) x -
        airyHankelShift s (airyHankelShift s (Ring.inverse (1-airyKernelShift s) x)) = x) ∧
      0 < inner ℝ (airyBoundaryVector s)
        (Ring.inverse (1-airyKernelShift s) (airyBoundaryVector s)) :=
  ⟨airyBoundaryVector_ne_zero s, norm_airyHankelShift_lt_one s, norm_airyKernelShift_lt_one s,
    contraction_ringInverse_left (airyHankelShift s) (norm_airyHankelShift_lt_one s),
    contraction_ringInverse_right (airyKernelShift s) (norm_airyKernelShift_lt_one s),
    airy_inverse_square_boundary_positive s⟩

#check RMTFoundations.TWOneBounds.airy_boundary_resolvent_parity_identity
#check RMTFoundations.TWOneBounds.airy_inverse_square_boundary_positive

end RMTFoundations.TWOneBounds

#print axioms RMTFoundations.TWOneBounds.tailEnergy
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_tailEnergy
#print axioms RMTFoundations.TWOneBounds.positive_of_tail_energy
#print axioms RMTFoundations.TWOneBounds.positive_of_third_order_ode
#print axioms RMTFoundations.TWOneBounds.airyTailIntegral
#print axioms RMTFoundations.TWOneBounds.exp_bound_integrable_Ioi
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_airyTailIntegral
#print axioms RMTFoundations.TWOneBounds.airyTailIntegral_abs_le
#print axioms RMTFoundations.TWOneBounds.airyTailIntegral_pos_of_nonneg
#print axioms RMTFoundations.TWOneBounds.linear_exp_bound
#print axioms RMTFoundations.TWOneBounds.linear_mul_exp_bound_integrable
#print axioms RMTFoundations.TWOneBounds.airyTailIntegral_weighted_tendsto
#print axioms RMTFoundations.TWOneBounds.decaying_airy_tail_pos
#print axioms RMTFoundations.TWOneBounds.halfline_translate_integral
#print axioms RMTFoundations.TWOneBounds.halfline_diagonal_integral
#print axioms RMTFoundations.TWOneBounds.airy_tail_positive
#print axioms RMTFoundations.TWOneBounds.B_diagonal_integral_eq_half_tail
#print axioms RMTFoundations.TWOneBounds.B_diagonal_integral_positive
#print axioms RMTFoundations.TWOneBounds.airy_tail_analytic_joint_probe
#print axioms RMTFoundations.TWOneBounds.spectralCoeff
#print axioms RMTFoundations.TWOneBounds.spectral_finset_summable
#print axioms RMTFoundations.TWOneBounds.spectralCoeff_hasSum
#print axioms RMTFoundations.TWOneBounds.spectralCoeff_radius_top
#print axioms RMTFoundations.TWOneBounds.spectralCoeff_one
#print axioms RMTFoundations.TWOneBounds.trace_coefficient_of_product_bridge
#print axioms RMTFoundations.TWOneBounds.signed_tprod_le_exp_trace
#print axioms RMTFoundations.TWOneBounds.signed_tprod_le_one
#print axioms RMTFoundations.TWOneBounds.signed_tprod_joint_probe
#print axioms RMTFoundations.TWOneBounds.series_le_one_of_product_bridge
#print axioms RMTFoundations.TWOneBounds.determinant_bridge_joint_probe
#print axioms RMTFoundations.TWOneBounds.single_coupling_does_not_identify_trace
#print axioms RMTFoundations.TWOneBounds.kernelCoefficient_one
#print axioms RMTFoundations.TWOneBounds.eigenvalue_lt_one_of_norm
#print axioms RMTFoundations.TWOneBounds.eigenvalue_norm_joint_probe
#print axioms RMTFoundations.TWOneBounds.airy_tail_energy_joint_probe
#print axioms RMTFoundations.TWOneBounds.B_spectral_trace_of_product_bridge
#print axioms RMTFoundations.TWOneBounds.TW1R_le_one_of_eigenvalue_product_bridge
#print axioms RMTFoundations.TWOneBounds.contraction_resolvent_inner_nonneg
#print axioms RMTFoundations.TWOneBounds.contraction_resolvent_polynomial_lower
#print axioms RMTFoundations.TWOneBounds.contraction_resolvent_joint_probe
#print axioms RMTFoundations.TWOneBounds.resolvent_variational_lower
#print axioms RMTFoundations.TWOneBounds.contraction_resolvent_tangent_lower
#print axioms RMTFoundations.TWOneBounds.resolvent_parity_identity
#print axioms RMTFoundations.TWOneBounds.tangent_parity_joint_probe
#print axioms RMTFoundations.TWOneBounds.boundary_sign_counterprobe
#print axioms RMTFoundations.TWOneBounds.contraction_resolvent_half_norm_lower
#print axioms RMTFoundations.TWOneBounds.tangent_polynomial_gap
#print axioms RMTFoundations.TWOneBounds.tangent_gap_joint_probe
#print axioms RMTFoundations.TWOneBounds.boundary_trace_from_diagonal_derivative
#print axioms RMTFoundations.TWOneBounds.boundary_trace_joint_probe
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_B_diagonal_trace
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_Airy_square_energy
#print axioms RMTFoundations.TWOneBounds.scalar_oscillator_energy_sign
#print axioms RMTFoundations.TWOneBounds.Airy_square_energy_antitone
#print axioms RMTFoundations.TWOneBounds.Airy_boundary_energy_nonneg_far_left
#print axioms RMTFoundations.TWOneBounds.Airy_far_left_joint_probe
#print axioms RMTFoundations.TWOneBounds.scalar_energy_joint_probe
#print axioms RMTFoundations.TWOneBounds.Airy_boundary_positive_of_nonneg_shift
#print axioms RMTFoundations.TWOneBounds.physical_boundary_joint_probe
#print axioms RMTFoundations.TWOneBounds.airyBoundaryVector
#print axioms RMTFoundations.TWOneBounds.airyBoundaryVector_apply_ae
#print axioms RMTFoundations.TWOneBounds.airyBoundaryVector_inner_self
#print axioms RMTFoundations.TWOneBounds.airyBoundaryVector_norm_sq
#print axioms RMTFoundations.TWOneBounds.airyBoundaryVector_hankel_apply_ae
#print axioms RMTFoundations.TWOneBounds.airyBoundaryVector_cubic_moment
#print axioms RMTFoundations.TWOneBounds.airyEnergy_pos
#print axioms RMTFoundations.TWOneBounds.airyBoundaryVector_ne_zero
#print axioms RMTFoundations.TWOneBounds.airyBoundaryVector_joint_probe
#print axioms RMTFoundations.TWOneBounds.contraction_ringInverse_right
#print axioms RMTFoundations.TWOneBounds.contraction_ringInverse_left
#print axioms RMTFoundations.TWOneBounds.contraction_ringInverse_joint_probe
#print axioms RMTFoundations.TWOneBounds.airy_boundary_nonneg_far_left_of_resolvent
#print axioms RMTFoundations.TWOneBounds.airy_boundary_resolvent_joint_probe
#print axioms RMTFoundations.TWOneBounds.airy_boundary_cubic_lower
#print axioms RMTFoundations.TWOneBounds.airy_hankel_boundary_nonneg_far_left
#print axioms RMTFoundations.TWOneBounds.airy_hankel_inverse_boundary_nonneg_far_left
#print axioms RMTFoundations.TWOneBounds.airy_hankel_inverse_boundary_pos_nonneg
#print axioms RMTFoundations.TWOneBounds.real_eigenbasis_minor
#print axioms RMTFoundations.TWOneBounds.real_eigenbasis_absolute
#print axioms RMTFoundations.TWOneBounds.real_eigenbasis_product
#print axioms RMTFoundations.TWOneBounds.airy_eigenbasis_product
#print axioms RMTFoundations.TWOneBounds.airy_eigenbasis_absolute
#print axioms RMTFoundations.TWOneBounds.airy_eigenbasis_trace
#print axioms RMTFoundations.TWOneBounds.TW1R_le_one_of_eigenbasis
#print axioms RMTFoundations.TWOneBounds.TW1R_le_exp_neg_half_tail_of_eigenbasis
#print axioms RMTFoundations.TWOneBounds.signed_tprod_pos
#print axioms RMTFoundations.TWOneBounds.TW1R_lt_one_of_eigenbasis
#print axioms RMTFoundations.TWOneBounds.TW1R_pos_of_eigenbasis
#print axioms RMTFoundations.TWOneBounds.real_eigenbasis_joint_probe
#print axioms RMTFoundations.TWOneBounds.spectralCoeff_on
#print axioms RMTFoundations.TWOneBounds.spectral_finset_summable_on
#print axioms RMTFoundations.TWOneBounds.spectralCoeff_hasSum_on
#print axioms RMTFoundations.TWOneBounds.spectralCoeff_radius_top_on
#print axioms RMTFoundations.TWOneBounds.spectralCoeff_one_on
#print axioms RMTFoundations.TWOneBounds.trace_coefficient_of_product_bridge_on
#print axioms RMTFoundations.TWOneBounds.B_spectral_trace_of_product_bridge_on
#print axioms RMTFoundations.TWOneBounds.airy_eigenbasis_product_on
#print axioms RMTFoundations.TWOneBounds.airy_eigenbasis_absolute_on
#print axioms RMTFoundations.TWOneBounds.airy_eigenbasis_trace_on
#print axioms RMTFoundations.TWOneBounds.TW1R_le_exp_neg_half_tail_of_eigenbasis_on
#print axioms RMTFoundations.TWOneBounds.TW1R_lt_one_of_eigenbasis_on
#print axioms RMTFoundations.TWOneBounds.TW1R_pos_of_eigenbasis_on
#print axioms RMTFoundations.TWOneBounds.compact_symmetric_real_eigenbasis
#print axioms RMTFoundations.TWOneBounds.airy_hankel_norm_vanishing_envelope
#print axioms RMTFoundations.TWOneBounds.airy_hankel_norm_tendsto_zero
#print axioms RMTFoundations.TWOneBounds.airy_hankel_contraction_joint_probe
#print axioms RMTFoundations.TWOneBounds.TW1R_bounds_of_contraction
#print axioms RMTFoundations.TWOneBounds.TW1R_le_one_of_contraction
#print axioms RMTFoundations.TWOneBounds.airy_upper_bound_all_binder_joint_probe
#print axioms RMTFoundations.TWOneBounds.airy_hankel_trace_eq_half_tail
#print axioms RMTFoundations.TWOneBounds.airy_hankel_trace_positive
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_airy_hankel_trace
#print axioms RMTFoundations.TWOneBounds.TW1R_eventually_between_zero_one
#print axioms RMTFoundations.TWOneBounds.signed_tprod_le_exp_trace_of_le_one
#print axioms RMTFoundations.TWOneBounds.signed_tprod_nonneg_of_le_one
#print axioms RMTFoundations.TWOneBounds.eigenvalue_le_one_of_contraction
#print axioms RMTFoundations.TWOneBounds.TW1R_bounds
#print axioms RMTFoundations.TWOneBounds.TW1R_le_one
#print axioms RMTFoundations.TWOneBounds.TW1R_lt_one
#print axioms RMTFoundations.TWOneBounds.airy_unconditional_upper_bound_joint_probe
#print axioms RMTFoundations.TWOneBounds.norm_airyHankelShift_lt_one_of_pos
#print axioms RMTFoundations.TWOneBounds.gaussian_linear_bound
#print axioms RMTFoundations.TWOneBounds.gaussian_laplace_integrable
#print axioms RMTFoundations.TWOneBounds.gaussian_laplace_entire
#print axioms RMTFoundations.TWOneBounds.airyResponse
#print axioms RMTFoundations.TWOneBounds.airyResponseSpectrum
#print axioms RMTFoundations.TWOneBounds.airyResponseSpectrum_gaussian
#print axioms RMTFoundations.TWOneBounds.airyResponseExtension
#print axioms RMTFoundations.TWOneBounds.airyResponseExtension_entire
#print axioms RMTFoundations.TWOneBounds.airyResponseExtension_real
#print axioms RMTFoundations.TWOneBounds.norm_lt_one_of_no_unit_eigenvalue
#print axioms RMTFoundations.TWOneBounds.strict_spectral_joint_probe
#print axioms RMTFoundations.TWOneBounds.entire_zero_of_real_unit_interval
#print axioms RMTFoundations.TWOneBounds.integral_Ioi_translate
#print axioms RMTFoundations.TWOneBounds.zero_on_removed_region_of_integral_eq
#print axioms RMTFoundations.TWOneBounds.airyResponse_norm_sq
#print axioms RMTFoundations.TWOneBounds.airyResponse_sq_integrable
#print axioms RMTFoundations.TWOneBounds.airyResponse_translate
#print axioms RMTFoundations.TWOneBounds.airyResponse_continuous
#print axioms RMTFoundations.TWOneBounds.airyResponse_zero_interval_of_equal_norm
#print axioms RMTFoundations.TWOneBounds.airyResponse_zero_of_equal_norm
#print axioms RMTFoundations.TWOneBounds.norm_airyHankelShift_lt_one
#print axioms RMTFoundations.TWOneBounds.TW1R_positive_bounds
#print axioms RMTFoundations.TWOneBounds.airy_strict_all_binder_joint_probe
#print axioms RMTFoundations.TWOneBounds.airyResponse_boundary_zero_pos
#print axioms RMTFoundations.TWOneBounds.airy_response_analytic_joint_probe
#print axioms RMTFoundations.TWOneBounds.airyOperatorTW1_positive_bounds
#print axioms RMTFoundations.TWOneBounds.airy_hankel_inverse_boundary_pos_of_nonneg
#print axioms RMTFoundations.TWOneBounds.airy_hankel_inverse_boundary_nonneg_of_far_left
#print axioms RMTFoundations.TWOneBounds.airy_boundary_certificate_joint_probe
#print axioms RMTFoundations.TWOneBounds.shift_tail_hasDerivAt
#print axioms RMTFoundations.TWOneBounds.airyKernelIntegral_shift_eq_tail
#print axioms RMTFoundations.TWOneBounds.airy_product_all_tails_integrable
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_airyKernelIntegral_simultaneous_shift
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_airy_square_finite_quadratic
#print axioms RMTFoundations.TWOneBounds.airy_square_finite_quadratic_antitone
#print axioms RMTFoundations.TWOneBounds.airy_square_shift_joint_probe
#print axioms RMTFoundations.TWOneBounds.airyResponse_general_translate
#print axioms RMTFoundations.TWOneBounds.airyResponse_sq_all_tails_integrable
#print axioms RMTFoundations.TWOneBounds.airyResponse_norm_sq_eq_fixed_tail
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_airyHankelShift_norm_sq
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_airyKernelShift_quadratic
#print axioms RMTFoundations.TWOneBounds.airyKernelShift_quadratic_antitone
#print axioms RMTFoundations.TWOneBounds.airy_square_operator_derivative_joint_probe
#print axioms RMTFoundations.TWOneBounds.airyResponse_boundary_eq_inner
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_airyKernelShift_quadratic_rankOne
#print axioms RMTFoundations.TWOneBounds.hasDerivAt_airyKernelShift_pairing
#print axioms RMTFoundations.TWOneBounds.airy_square_pairing_joint_probe
#print axioms RMTFoundations.TWOneBounds.norm_airyKernelShift_lt_one
#print axioms RMTFoundations.TWOneBounds.airy_boundary_resolvent_parity_identity
#print axioms RMTFoundations.TWOneBounds.airy_inverse_square_boundary_positive
#print axioms RMTFoundations.TWOneBounds.airy_canonical_parity_joint_probe
