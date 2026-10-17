import RMTFoundations.TracyWidom.ResolventCoordinates
import RMTFoundations.Airy.HankelFactorization


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMAiryEnvelope
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
open RMTFoundations.Fredholm RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.ResolventCoordinates

/-- Actual Airy decay at plus infinity, from the global exponential bound. -/
theorem airyAi_atTop_zero : Tendsto airyAiReal atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := airyAiReal_abs_le_exp'
  apply squeeze_zero_norm' (a := fun x : ℝ => C*Real.exp (-x))
  · exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)
  · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C

/-- Actual Airy derivative decay, from its proved half-line exponential bound. -/
theorem airyAi_derivative_atTop_zero : Tendsto (deriv airyAiReal) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := airy_deriv_halfline_exp_bound 0
  apply squeeze_zero_norm' (a := fun x : ℝ => C*Real.exp (-x/2))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simpa only [Real.norm_eq_abs] using hb x hx
  · have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
    simpa only [Function.comp_def,id_eq,neg_div,mul_zero] using ht.const_mul C

/-- Differentiating the weighted Airy sum uses the actual Airy ODE. -/
theorem hasDerivAt_exp_neg_Airy_sum
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => Real.exp (-t)*(deriv airyAiReal t+airyAiReal t))
      (Real.exp (-s)*(s-1)*airyAiReal s) s := by
  convert! (((Real.hasDerivAt_exp (-s)).comp s ((hasDerivAt_id s).neg)).mul
    ((hasDerivAt_deriv_airyAiReal' s).add (hasDerivAt_airyAiReal' s))) using 1 <;>
    simp only [Function.comp_def,Pi.add_apply] <;> ring

/-- The actual Airy sum obeys Ai′+Ai≤0 for s≥1. -/
theorem airyAi_derivative_add_nonpos
    (s : ℝ) -- [definition]
    (hs : 1 ≤ s) -- [standing]
    : deriv airyAiReal s + airyAiReal s ≤ 0 := by
  let f : ℝ → ℝ := fun t => Real.exp (-t)*(deriv airyAiReal t+airyAiReal t)
  have hc : Continuous f :=
    (Real.continuous_exp.comp continuous_id.neg).mul
      (continuous_deriv_airyAiReal.add continuous_airyAiReal)
  have hd (t : ℝ) : HasDerivAt f (Real.exp (-t)*(t-1)*airyAiReal t) t :=
    hasDerivAt_exp_neg_Airy_sum t
  have hm : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1) hc.continuousOn
    · intro t ht
      exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      have ht1 : 1 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      have ha := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ t)).le
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith)) ha
  have hl : Tendsto f atTop (𝓝 0) := by
    simpa only [f,zero_add,mul_zero] using
      Real.tendsto_exp_neg_atTop_nhds_zero.mul
        (airyAi_derivative_atTop_zero.add airyAi_atTop_zero)
  have hle : f s ≤ 0 := ge_of_tendsto hl (by
    filter_upwards [eventually_ge_atTop s] with t ht
    exact hm hs (show 1 ≤ t from hs.trans ht) ht)
  change Real.exp (-s)*(deriv airyAiReal s+airyAiReal s) ≤ 0 at hle
  apply le_of_mul_le_mul_left ?_ (Real.exp_pos (-s))
  simpa only [mul_zero] using hle

/-- The exponential Airy weight is antitone on the genuine positive tail. -/
theorem exp_mul_airyAi_antitoneOn :
    AntitoneOn (fun s => Real.exp s*airyAiReal s) (Ici 1) := by
  have hd (s : ℝ) : HasDerivAt (fun t => Real.exp t*airyAiReal t)
      (Real.exp s*(deriv airyAiReal s+airyAiReal s)) s := by
    convert! (Real.hasDerivAt_exp s).mul (hasDerivAt_airyAiReal' s) using 1 <;> ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    (Real.continuous_exp.mul continuous_airyAiReal).continuousOn
  · intro s hs
    exact (hd s).differentiableAt.differentiableWithinAt
  · intro s hs
    change deriv (fun t => Real.exp t * airyAiReal t) s ≤ 0
    rw [(hd s).deriv]
    have hs1 : 1 < s := by simpa only [interior_Ici,mem_Ioi] using hs
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (airyAi_derivative_add_nonpos s hs1.le)

/-- The tail is controlled relative to its actual Airy value, not by a fixed global constant. -/
theorem airyAi_relative_exp_envelope
    (s x : ℝ) -- [definition]
    (hs : 1 ≤ s) -- [standing]
    (hx : 0 ≤ x) -- [standing]
    : airyAiReal (s + x) ≤ airyAiReal s*Real.exp (-x) := by
  have h := exp_mul_airyAi_antitoneOn hs (by linarith : 1 ≤ s + x) (by linarith : s ≤ s + x)
  apply (mul_le_mul_iff_of_pos_left (Real.exp_pos (s + x))).mp
  have he : Real.exp (s + x)*Real.exp (-x)=Real.exp s := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (s + x)*airyAiReal (s + x) ≤ Real.exp s*airyAiReal s := h
    _ = Real.exp (s + x)*(airyAiReal s*Real.exp (-x)) := by rw [←he]; ring

/-- The genuine half-line row energy obeys the relative Airy square bound. -/
theorem airyEnergy_le_airyAi_sq_half
    (s : ℝ) -- [definition]
    (hs : 1 ≤ s) -- [standing]
    : airyEnergy s ≤ (airyAiReal s)^2/2 := by
  have hi := integrable_airyAiReal_sq_comp_add_Ioi s
  have hm : Integrable (fun x : ℝ => (airyAiReal s)^2*Real.exp (-(2*x))) halfLineMeasure :=
    (integrableOn_exp_neg_two_mul 0).const_mul _
  have hb : ∀ᵐ x ∂halfLineMeasure,
      (airyAiReal (s + x))^2 ≤ (airyAiReal s)^2*Real.exp (-(2*x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have ha := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ s + x)).le
    have hp := pow_le_pow_left₀ ha (airyAi_relative_exp_envelope s x hs hx.le) 2
    have he : (Real.exp (-x))^2=Real.exp (-(2*x)) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow,he] using hp
  have h := integral_mono_ae hi hm hb
  rw [integral_const_mul,integral_exp_neg_two_mul_Ioi] at h
  have he := airyAiReal_sq_integral s
  change (∫ x, (airyAiReal (s + x))^2 ∂halfLineMeasure)=airyEnergy s at he
  rw [he] at h
  simpa only [mul_zero,neg_zero,Real.exp_zero,one_div,div_eq_mul_inv,one_mul] using h

/-- Every new tail-floor binder is realized by the actual nonzero shift-one instance. -/
theorem airy_relative_tail_joint_probe :
    airyBoundaryVector 1 ≠ 0 ∧ 0<airyAiReal 1 ∧
      deriv airyAiReal 1+airyAiReal 1 ≤ 0 ∧
      (∀ x : ℝ, 0 ≤ x → airyAiReal (1+x)≤airyAiReal 1*Real.exp (-x)) ∧
      airyEnergy 1 ≤ (airyAiReal 1)^2/2 :=
  ⟨airyBoundaryVector_ne_zero 1,airyAiReal_pos_of_nonneg (by norm_num),
    airyAi_derivative_add_nonpos 1 le_rfl,
    fun x hx => airyAi_relative_exp_envelope 1 x le_rfl hx,
    airyEnergy_le_airyAi_sq_half 1 le_rfl⟩

end RMTFoundations.TracyWidom.HMAiryEnvelope
#print axioms RMTFoundations.TracyWidom.HMAiryEnvelope.airyAi_atTop_zero
#print axioms RMTFoundations.TracyWidom.HMAiryEnvelope.airyAi_derivative_atTop_zero
#print axioms RMTFoundations.TracyWidom.HMAiryEnvelope.hasDerivAt_exp_neg_Airy_sum
#print axioms RMTFoundations.TracyWidom.HMAiryEnvelope.airyAi_derivative_add_nonpos
#print axioms RMTFoundations.TracyWidom.HMAiryEnvelope.exp_mul_airyAi_antitoneOn
#print axioms RMTFoundations.TracyWidom.HMAiryEnvelope.airyAi_relative_exp_envelope
#print axioms RMTFoundations.TracyWidom.HMAiryEnvelope.airyEnergy_le_airyAi_sq_half
#print axioms RMTFoundations.TracyWidom.HMAiryEnvelope.airy_relative_tail_joint_probe
