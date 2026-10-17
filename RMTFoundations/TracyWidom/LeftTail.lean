import RMTFoundations.Airy.Consequences
import RMTFoundations.Airy.Spectral
import RMTFoundations.Airy.Contraction
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in compact-spectral-LICENSE.
Authors: Adam Benenson; adaptations for this project by Le Chen's lab.
The eigenbasis construction below is adapted from compact-spectral at
72cd62dbdd4c397d26fc0c5777d60fea2211e938; it uses the spectral theorem
already proved in the project's pinned mathlib, with no upstream approximation dependency.
-/
import Mathlib
import RMTFoundations.Airy.HankelFactorization
import RMTFoundations.Airy.Distribution
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TWLeftTail

open MeasureTheory Set Filter
open scoped Topology Classical
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm

set_option autoImplicit false

/-- The literal diagonal integral of the Airy kernel on (s,infinity).
No operator trace or determinant identity is built into this definition. -/
noncomputable def airyTraceIntegral (s : ℝ /- [definition] -/) : ℝ :=
  ∫ x in Ioi s, airyKernelIntegral x x

/-- Compatibility with the positive-half-line coordinates. -/
lemma airyTraceIntegral_shift (s : ℝ /- [definition] -/) :
    (∫ x, airyKernelIntegral (x+s) (x+s) ∂ halfLineMeasure) = airyTraceIntegral s := by
  exact (fredholm_measurePreserving_shift s).integral_comp
    (MeasurableEquiv.addRight s).measurableEmbedding
    (fun x => airyKernelIntegral x x)

/-- A positive constant already certified by the Airy initial data. -/
noncomputable def originMass : ℝ := (deriv airyAiReal 0)^2

lemma originMass_pos : 0 < originMass := by
  exact sq_pos_of_ne_zero deriv_airyAiReal_zero_neg.ne

lemma diagonal_eq_energy (x : ℝ /- [definition] -/) :
    airyKernelIntegral x x = airyEnergy x := by
  simpa only [airyKernelIntegral, ← sq, airyEnergy] using airyAiReal_sq_integral x

lemma diagonal_nonneg (x : ℝ /- [definition] -/) :
    0 ≤ airyKernelIntegral x x := by
  unfold airyKernelIntegral
  exact integral_nonneg (fun _ => mul_self_nonneg _)

lemma energy_antitone : Antitone airyEnergy := by
  apply antitone_of_hasDerivAt_nonpos
    (fun x => hasDerivAt_airyEnergy x)
  intro x
  exact neg_nonpos.mpr (sq_nonneg _)

lemma diagonal_ge_origin (x : ℝ /- [definition] -/)
    (hx : x ≤ 0 /- [standing] -/) :
    originMass ≤ airyKernelIntegral x x := by
  rw [diagonal_eq_energy]
  have he := energy_antitone hx
  simpa only [airyEnergy, originMass, zero_mul, sub_zero] using he

lemma diagonal_continuous : Continuous (fun x : ℝ => airyKernelIntegral x x) := by
  have hc : Continuous airyEnergy :=
    (continuous_deriv_airyAiReal.pow 2).sub (continuous_id.mul (continuous_airyAiReal.pow 2))
  exact hc.congr (fun x => (diagonal_eq_energy x).symm)

lemma diagonal_integrable (s : ℝ /- [definition] -/) :
    IntegrableOn (fun x : ℝ => airyKernelIntegral x x) (Ioi s) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound s
  apply ((integrableOn_exp_neg_two_mul s).const_mul (C^2)).mono
    diagonal_continuous.aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ C^2 * Real.exp (-(2*x)))]
  calc
    |airyKernelIntegral x x| ≤ (C^2 * Real.exp (-x) * Real.exp (-x)) *
        ∫ t, Real.exp (-t)^2 ∂ halfLineMeasure :=
      K_Ai_abs_le s C hC.le hb x x hx.le hx.le
    _ ≤ C^2 * Real.exp (-x) * Real.exp (-x) := by
      simpa using mul_le_mul_of_nonneg_left integral_exp_square_le_one
        (show 0 ≤ C^2 * Real.exp (-x) * Real.exp (-x) by positivity)
    _ = C^2 * Real.exp (-(2*x)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

lemma airyTraceIntegral_nonneg (s : ℝ /- [definition] -/) :
    0 ≤ airyTraceIntegral s := by
  exact integral_nonneg diagonal_nonneg

/-- Fixed positive mass is enough; negative-argument Airy asymptotics are unnecessary. -/
theorem airyTraceIntegral_linear_lower (s : ℝ /- [definition] -/)
    (hs : s ≤ 0 /- [standing] -/) :
    (-s) * originMass ≤ airyTraceIntegral s := by
  have hi : IntegrableOn (fun x : ℝ => airyKernelIntegral x x) (Ioo s 0) :=
    (diagonal_integrable s).mono_set Ioo_subset_Ioi_self
  have hm := setIntegral_mono_on
    (f := fun _ : ℝ => originMass) (g := fun x => airyKernelIntegral x x)
    (integrableOn_const (by simp : volume (Ioo s (0 : ℝ)) ≠ ⊤)) hi
    measurableSet_Ioo (fun x hx => diagonal_ge_origin x hx.2.le)
  have hsub : (Ioo s (0 : ℝ)) ≤ᵐ[volume] Ioi s :=
    Eventually.of_forall (fun _ hx => hx.1)
  have hfull := setIntegral_mono_set (diagonal_integrable s)
    (Eventually.of_forall diagonal_nonneg) hsub
  have hc : ∫ _x in Ioo s (0 : ℝ), originMass = (-s) * originMass := by
    rw [setIntegral_const]
    simp only [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal
      (by linarith : 0 ≤ (0 : ℝ) - s), smul_eq_mul]
    ring
  rw [hc] at hm
  exact hm.trans hfull

theorem airyTraceIntegral_tendsto_atBot_atTop :
    Tendsto airyTraceIntegral atBot atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_le_atBot (min 0 (-b / originMass))] with s hs
  have hs0 : s ≤ 0 := hs.trans (min_le_left _ _)
  have hsb : s ≤ -b / originMass := hs.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ originMass_pos).mp hsb
  have hlo := airyTraceIntegral_linear_lower s hs0
  nlinarith

/-- Conditional estimate from a positive-contraction determinant bound with its diagonal trace integral. -/
theorem TW2R_tendsto_atBot_zero_of_trace_estimate
    (hTWB : ∀ s : ℝ, 0 ≤ TW2R s ∧
      TW2R s ≤ Real.exp (-(∫ x in Ioi s, airyKernelIntegral x x))  /- [standing] -/ ) :
    Tendsto TW2R atBot (𝓝 0) := by
  apply squeeze_zero (fun s => (hTWB s).1) (fun s => (hTWB s).2)
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp airyTraceIntegral_tendsto_atBot_atTop)

/-- Scalar eigenvalue-product bound, including possible eigenvalue 1.
The determinant estimate is proved here rather than hidden in the bridge. -/
theorem product_le_exp_neg_sum
    (eigen : ℕ → ℝ /- [definition] -/)
    (d t : ℝ /- [definition] -/)
    (hl : ∀ j, 0 ≤ eigen j /- [standing] -/)
    (hu : ∀ j, eigen j ≤ 1 /- [standing] -/)
    (hp : HasProd (fun j => 1 - eigen j) d /- [standing] -/)
    (ht : HasSum eigen t /- [standing] -/) :
    0 ≤ d ∧ d ≤ Real.exp (-t) := by
  have hn : ∀ S : Finset ℕ, 0 ≤ ∏ j ∈ S, (1 - eigen j) := by
    intro S
    exact Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (hu j))
  have hb : ∀ S : Finset ℕ, ∏ j ∈ S, (1 - eigen j) ≤ ∏ j ∈ S, Real.exp (-eigen j) := by
    intro S
    apply Finset.prod_le_prod₀
    · exact fun j _ => sub_nonneg.mpr (hu j)
    · intro j _
      have he := Real.add_one_le_exp (-eigen j)
      linarith
  exact ⟨ge_of_tendsto hp (Eventually.of_forall hn),
    le_of_tendsto_of_tendsto hp ht.neg.rexp (Eventually.of_forall hb)⟩

/-- The order-two Fredholm distribution tends to zero at the left endpoint
under a nonnegative contraction spectrum with the specified product and trace. -/
theorem TW2R_tendsto_atBot_zero
    (hTWB : ∀ s : ℝ, ∃ eigen : ℕ → ℝ,
      (∀ j, 0 ≤ eigen j) ∧ (∀ j, eigen j ≤ 1) ∧
      HasProd (fun j => 1 - eigen j) (TW2R s) ∧
      HasSum eigen (∫ x in Ioi s, airyKernelIntegral x x)  /- [standing] -/ ) :
    Tendsto TW2R atBot (𝓝 0) := by
  apply TW2R_tendsto_atBot_zero_of_trace_estimate
  intro s
  obtain ⟨eigen,hl,hu,hp,ht⟩ := hTWB s
  exact product_le_exp_neg_sum eigen (TW2R s) (airyTraceIntegral s) hl hu hp ht

/-- The same left-endpoint limit with the trace in shifted L2(0,infinity) coordinates. -/
theorem TW2R_tendsto_atBot_zero_of_shifted_bridge
    (hTWB : ∀ s : ℝ, ∃ eigen : ℕ → ℝ,
      (∀ j, 0 ≤ eigen j) ∧ (∀ j, eigen j ≤ 1) ∧
      HasProd (fun j => 1 - eigen j) (TW2R s) ∧
      HasSum eigen (∫ x, airyKernelIntegral (x+s) (x+s) ∂ halfLineMeasure)  /- [standing] -/ ) :
    Tendsto TW2R atBot (𝓝 0) := by
  apply TW2R_tendsto_atBot_zero
  intro s
  obtain ⟨eigen,hl,hu,hp,ht⟩ := hTWB s
  rw [airyTraceIntegral_shift s] at ht
  exact ⟨eigen,hl,hu,hp,ht⟩

/-- A nonzero rank-one spectrum jointly inhabits EVERY binder of the scalar
product bound. This does not assert the pending bridge for the actual Airy operator. -/
theorem product_bound_all_binder_probe :
    ∃ eigen : ℕ → ℝ, ∃ d t : ℝ,
      eigen 0 = 1/2 ∧ 0 < d ∧ 0 < t ∧
      (∀ j, 0 ≤ eigen j) ∧ (∀ j, eigen j ≤ 1) ∧
      HasProd (fun j => 1 - eigen j) d ∧ HasSum eigen t ∧
      (0 ≤ d ∧ d ≤ Real.exp (-t)) := by
  let eigen : ℕ → ℝ := fun j => if j = 0 then 1/2 else 0
  have hl : ∀ j, 0 ≤ eigen j := by intro j; dsimp [eigen]; split_ifs <;> norm_num
  have hu : ∀ j, eigen j ≤ 1 := by intro j; dsimp [eigen]; split_ifs <;> norm_num
  have hp : HasProd (fun j => 1 - eigen j) (1/2) := by
    convert hasProd_ite_eq (0 : ℕ) (1/2 : ℝ) using 1
    funext j
    dsimp [eigen]
    split_ifs <;> norm_num
  have ht : HasSum eigen (1/2) := hasSum_ite_eq (0 : ℕ) (1/2 : ℝ)
  refine ⟨eigen,1/2,1/2,by simp [eigen],by norm_num,by norm_num,hl,hu,hp,ht,?_⟩
  exact product_le_exp_neg_sum eigen (1/2) (1/2) hl hu hp ht

/-- An actual negative endpoint inhabits both binders of the trace lower bound. -/
theorem trace_lower_all_binder_probe :
    ∃ s : ℝ, s < 0 ∧ s ≤ 0 ∧ 0 < originMass ∧
      IntegrableOn (fun x : ℝ => airyKernelIntegral x x) (Ioi s) ∧
      (-s) * originMass ≤ airyTraceIntegral s ∧ 0 < airyTraceIntegral s := by
  have hbound := airyTraceIntegral_linear_lower (-1) (by norm_num)
  refine ⟨-1,by norm_num,by norm_num,originMass_pos,diagonal_integrable (-1),hbound,?_⟩
  nlinarith [originMass_pos]

/-- The scalar bound also covers a zero determinant caused by eigenvalue 1. -/
theorem product_bound_unit_eigenvalue_probe :
    ∃ eigen : ℕ → ℝ,
      eigen 0 = 1 ∧ (∀ j, 0 ≤ eigen j) ∧ (∀ j, eigen j ≤ 1) ∧
      HasProd (fun j => 1 - eigen j) 0 ∧ HasSum eigen 1 ∧
      (0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ Real.exp (-1)) := by
  let eigen : ℕ → ℝ := fun j => if j = 0 then 1 else 0
  have hl : ∀ j, 0 ≤ eigen j := by intro j; dsimp [eigen]; split_ifs <;> norm_num
  have hu : ∀ j, eigen j ≤ 1 := by intro j; dsimp [eigen]; split_ifs <;> norm_num
  have hp : HasProd (fun j => 1 - eigen j) 0 := by
    convert hasProd_ite_eq (0 : ℕ) (0 : ℝ) using 1
    funext j
    dsimp [eigen]
    split_ifs <;> norm_num
  have ht : HasSum eigen 1 := hasSum_ite_eq (0 : ℕ) (1 : ℝ)
  exact ⟨eigen,by simp [eigen],hl,hu,hp,ht,product_le_exp_neg_sum eigen 0 1 hl hu hp ht⟩

/-- Joint probe for the deterministic Airy data used in every trace theorem. -/
theorem airy_data_joint_probe :
    0 < originMass ∧ airyAiReal 0 ≠ 0 ∧
    (∀ s : ℝ, IntegrableOn (fun x : ℝ => airyKernelIntegral x x) (Ioi s)) ∧
    (∀ x : ℝ, 0 ≤ airyKernelIntegral x x) ∧
    (∀ s : ℝ, s ≤ 0 → (-s) * originMass ≤ airyTraceIntegral s) := by
  exact ⟨originMass_pos, airyAiReal_zero_pos.ne', diagonal_integrable,
    diagonal_nonneg, airyTraceIntegral_linear_lower⟩


lemma one_sub_le_exp_quadratic
    (x : ℝ /- [definition] -/)
    (hl : -1 ≤ x /- [standing] -/)
    (hu : x ≤ 1 /- [standing] -/) :
    1 - x ≤ Real.exp (-x - x^2/8) := by
  by_cases hx : x = 1
  · subst x
    simpa only [sub_self] using (Real.exp_pos (-1-(1:ℝ)^2/8)).le
  have hlt : x < 1 := lt_of_le_of_ne hu hx
  have hp : 0 < 1-x := by linarith
  let y := Real.sqrt (1-x)
  have hy : 0 < y := Real.sqrt_pos.mpr hp
  have hysq : y^2 = 1-x := Real.sq_sqrt hp.le
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hr : 0 ≤ 1-x/2-x^2/16 := by nlinarith
  have hcross : 0 ≤ x^2*(x+1) := mul_nonneg (sq_nonneg x) (by linarith)
  have hfour : 0 ≤ (x^2)^2 := sq_nonneg _
  have hyb : y ≤ 1-x/2-x^2/16 := by nlinarith [sq_nonneg (y-(1-x/2-x^2/16))]
  have hlog := Real.log_le_sub_one_of_pos hy
  have he : Real.log (1-x) = 2*Real.log y := by
    rw [← hysq, Real.log_pow]
    norm_num
  have hbound : Real.log (1-x) ≤ -x-x^2/8 := by rw [he]; linarith
  exact (Real.log_le_iff_le_exp hp).mp hbound

theorem signed_product_le_exp_trace_square
    (eigen : ℕ → ℝ /- [definition] -/)
    (d t q : ℝ /- [definition] -/)
    (hl : ∀ j, -1 ≤ eigen j /- [standing] -/)
    (hu : ∀ j, eigen j ≤ 1 /- [standing] -/)
    (hp : HasProd (fun j => 1-eigen j) d /- [standing] -/)
    (ht : HasSum eigen t /- [standing] -/)
    (hq : HasSum (fun j => (eigen j)^2) q /- [standing] -/) :
    0 ≤ d ∧ d ≤ Real.exp (-t-q/8) := by
  have hn : ∀ S : Finset ℕ, 0 ≤ ∏ j ∈ S, (1-eigen j) := by
    intro S
    exact Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (hu j))
  have hb : ∀ S : Finset ℕ, ∏ j ∈ S, (1-eigen j) ≤
      ∏ j ∈ S, Real.exp (-eigen j-(eigen j)^2/8) := by
    intro S
    apply Finset.prod_le_prod₀ (fun j _ => sub_nonneg.mpr (hu j))
    exact fun j _ => one_sub_le_exp_quadratic (eigen j) (hl j) (hu j)
  have hs : HasSum (fun j => -eigen j-(eigen j)^2/8) (-t-q/8) :=
    ht.neg.sub (hq.div_const 8)
  exact ⟨ge_of_tendsto hp (Eventually.of_forall hn),
    le_of_tendsto_of_tendsto hp hs.rexp (Eventually.of_forall hb)⟩

noncomputable def primitiveBarrier (x : ℝ /- [definition] -/) : ℝ :=
  deriv airyAiReal x / x - airyEnergyFull x / 2 + 1/(2*x)
lemma airyEnergyFull_nonneg (x : ℝ /- [definition] -/)
    (hx : x < 0 /- [standing] -/) : 0 ≤ airyEnergyFull x := by
  exact add_nonneg (sq_nonneg _)
    (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (neg_nonneg.mpr hx.le)))
lemma hasDerivAt_primitiveBarrier (x : ℝ /- [definition] -/)
    (hx : x < 0 /- [standing] -/) :
    HasDerivAt primitiveBarrier
      (airyAiReal x - (deriv airyAiReal x + 1)^2/(2*x^2)) x := by
  have hx0 := hx.ne
  have hg : HasDerivAt (deriv airyAiReal) (x*airyAiReal x) x := by
    have he : deriv (deriv airyAiReal) x = x*airyAiReal x := by
      simpa [iteratedDeriv_succ,iteratedDeriv_one] using iteratedDeriv_two_airyAiReal x
    simpa [he] using (hasDerivAt_deriv_airyAiReal x).differentiableAt.hasDerivAt
  have hh := (hg.div (hasDerivAt_id x) hx0).sub
    ((hasDerivAt_airyEnergyFull x hx).div_const 2)
  have hr := (hasDerivAt_const x (1:ℝ)).div
    ((hasDerivAt_id x).const_mul 2) (mul_ne_zero (by norm_num) hx0)
  have h := hh.add hr
  change HasDerivAt primitiveBarrier _ x at h
  have he : airyAiReal x - (deriv airyAiReal x+1)^2/(2*x^2) =
      ((x*airyAiReal x*x-deriv airyAiReal x*1)/x^2-(deriv airyAiReal x)^2/x^2/2) +
      ((0*(2*x)-1*(2*1))/(2*x)^2) := by
    field_simp [hx0]
    ring
  rw [he]
  exact h
lemma primitiveBarrier_upper (s : ℝ /- [definition] -/)
    (hs : s ≤ -1 /- [standing] -/) :
    primitiveBarrier s ≤ (airyEnergyFull (-1)+1)/2 := by
  have hs0 : s < 0 := by linarith
  have hsne : s ≠ 0 := hs0.ne
  have he := airyEnergy_monotoneOn hs (show (-1:ℝ) ≤ -1 from le_rfl) hs
  have hE := airyEnergyFull_nonneg s hs0
  have hg : (deriv airyAiReal s / s)^2 ≤ airyEnergyFull s := by
    have hn : 0 ≤ (airyAiReal s)^2 := sq_nonneg _
    have hEeq : airyEnergyFull s = (airyAiReal s)^2 - (deriv airyAiReal s)^2/s := by
      simp [airyEnergyFull,inv_neg,div_eq_mul_inv,sub_eq_add_neg]
    rw [hEeq,div_pow]
    apply (div_le_iff₀ (sq_pos_of_ne_zero hsne)).mpr
    have hf : ((airyAiReal s)^2 - (deriv airyAiReal s)^2/s)*s^2 =
        (airyAiReal s)^2*s^2 - (deriv airyAiReal s)^2*s := by
      field_simp [hsne]
      <;> ring
    rw [hf]
    nlinarith [mul_nonneg (sq_nonneg (deriv airyAiReal s)) (show 0 ≤ -s-1 by linarith),
      mul_nonneg hn (sq_nonneg s)]
  have hb : deriv airyAiReal s / s ≤ (airyEnergyFull (-1)+1)/2 := by
    nlinarith [sq_nonneg (deriv airyAiReal s / s - 1)]
  have hr : 1/(2*s) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
  dsimp [primitiveBarrier]
  linarith
lemma airy_negative_interval_lower (s : ℝ /- [definition] -/)
    (hs : s ≤ -1 /- [standing] -/) :
    primitiveBarrier (-1) - (airyEnergyFull (-1)+1)/2 ≤
      ∫ x in s..(-1:ℝ), airyAiReal x := by
  let f' : ℝ → ℝ := fun x => airyAiReal x - (deriv airyAiReal x+1)^2/(2*x^2)
  have hfc : ContinuousOn f' (Icc s (-1)) := by
    apply ContinuousOn.sub continuous_airyAiReal.continuousOn
    apply ContinuousOn.div ((continuous_deriv_airyAiReal.add continuous_const).pow 2).continuousOn
      (continuous_const.mul (continuous_id.pow 2)).continuousOn
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.2]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0)
  have hfi : IntervalIntegrable f' volume s (-1) := by
    apply hfc.intervalIntegrable_of_Icc hs
  have hAi : IntervalIntegrable airyAiReal volume s (-1) :=
    continuous_airyAiReal.intervalIntegrable s (-1)
  have hftc : (∫ x in s..(-1:ℝ), f' x) = primitiveBarrier (-1)-primitiveBarrier s := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hfi
    intro x hx
    rw [uIcc_of_le hs] at hx
    exact hasDerivAt_primitiveBarrier x (by linarith [hx.2])
  have hm := intervalIntegral.integral_mono_on hs hfi hAi (fun x hx => by
    dsimp [f']
    exact sub_le_self _ (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg x))))
  rw [hftc] at hm
  linarith [primitiveBarrier_upper s hs]
lemma airy_integrable_Ioi (s : ℝ /- [definition] -/) :
    IntegrableOn airyAiReal (Ioi s) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound s
  apply ((integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) s).const_mul C).mono'
    continuous_airyAiReal.aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro x hx
  simpa [Real.norm_eq_abs] using hb x hx.le
lemma airy_Ioi_split (s : ℝ /- [definition] -/)
    (hs : s ≤ -1 /- [standing] -/) :
    (∫ x in Ioi s, airyAiReal x) =
      (∫ x in s..(-1:ℝ), airyAiReal x) + ∫ x in Ioi (-1:ℝ), airyAiReal x := by
  rw [intervalIntegral.integral_of_le hs]
  have he : Ioi s = Ioc s (-1) ∪ Ioi (-1:ℝ) := by
    ext x
    simp only [mem_Ioi,mem_union,mem_Ioc]
    constructor
    · intro hx
      by_cases h : x ≤ -1
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨hx,_⟩ | hx)
      · exact hx
      · exact lt_of_le_of_lt hs hx
  have hd : Disjoint (Ioc s (-1:ℝ)) (Ioi (-1:ℝ)) := by
    rw [disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  rw [he]
  exact setIntegral_union hd measurableSet_Ioi
    ((airy_integrable_Ioi s).mono_set Ioc_subset_Ioi_self) (airy_integrable_Ioi (-1))
noncomputable def hankelSignedTrace (s : ℝ /- [definition] -/) : ℝ :=
  (∫ x in Ioi s, airyAiReal x)/2
noncomputable def signedTraceFloor : ℝ :=
  (primitiveBarrier (-1)-(airyEnergyFull (-1)+1)/2 + ∫ x in Ioi (-1:ℝ), airyAiReal x)/2
lemma hankelSignedTrace_lower (s : ℝ /- [definition] -/)
    (hs : s ≤ -1 /- [standing] -/) :
    signedTraceFloor ≤ hankelSignedTrace s := by
  dsimp [signedTraceFloor,hankelSignedTrace]
  rw [airy_Ioi_split s hs]
  linarith [airy_negative_interval_lower s hs]

/-- Left-endpoint limit under a signed contraction spectrum.
The plain hypothesis records spectral contraction, the canonical determinant
product, and BOTH literal diagonal traces; it assumes no left-tail estimate. -/
theorem TW1R_tendsto_atBot_zero
    (hTWB : ∀ s : ℝ, ∃ eigen : ℕ → ℝ,
      (∀ j, -1 ≤ eigen j) ∧ (∀ j, eigen j ≤ 1) ∧
      HasProd (fun j => 1-eigen j) (TW1R s) ∧
      HasSum eigen ((∫ x in Ioi s, airyAiReal x)/2) ∧
      HasSum (fun j => (eigen j)^2) (∫ x in Ioi s, airyKernelIntegral x x)  /- [standing] -/ ) :
    Tendsto TW1R atBot (𝓝 0) := by
  have hb : ∀ s : ℝ, 0 ≤ TW1R s ∧
      TW1R s ≤ Real.exp (-hankelSignedTrace s-airyTraceIntegral s/8) := by
    intro s
    obtain ⟨eigen,hl,hu,hp,ht,hq⟩ := hTWB s
    exact signed_product_le_exp_trace_square eigen (TW1R s)
      (hankelSignedTrace s) (airyTraceIntegral s) hl hu hp ht hq
  have hlim : Tendsto (fun s => -signedTraceFloor-airyTraceIntegral s/8) atBot atBot := by
    apply tendsto_atBot.2
    intro b
    filter_upwards [(tendsto_atTop.1 airyTraceIntegral_tendsto_atBot_atTop)
      (8*(-signedTraceFloor-b))] with s hs
    linarith
  apply squeeze_zero' (Eventually.of_forall (fun s => (hb s).1)) _
    (Real.tendsto_exp_atBot.comp hlim)
  filter_upwards [eventually_le_atBot (-1:ℝ)] with s hs
  exact (hb s).2.trans (Real.exp_le_exp.mpr (by linarith [hankelSignedTrace_lower s hs]))

/-- A genuinely signed, nonzero rank-two spectrum inhabits all binders
of the product/trace-square deduction at once. -/
theorem signed_product_all_binder_probe :
    ∃ (eigen : ℕ → ℝ) (d t q : ℝ),
      eigen 0 = 1/2 ∧ eigen 1 = -1/4 ∧ d = 5/8 ∧ t = 1/4 ∧ q = 5/16 ∧
      (∀ j, -1 ≤ eigen j) ∧ (∀ j, eigen j ≤ 1) ∧
      HasProd (fun j => 1-eigen j) d ∧ HasSum eigen t ∧
      HasSum (fun j => (eigen j)^2) q ∧
      (0 ≤ d ∧ d ≤ Real.exp (-t-q/8)) := by
  let eigen : ℕ → ℝ := fun j => (if j=0 then 1/2 else 0)+(if j=1 then -1/4 else 0)
  have hl : ∀ j, -1 ≤ eigen j := by
    intro j
    by_cases h0 : j=0
    · subst j; norm_num [eigen]
    · by_cases h1 : j=1 <;> simp [eigen,h0,h1] <;> norm_num
  have hu : ∀ j, eigen j ≤ 1 := by
    intro j
    by_cases h0 : j=0
    · subst j; norm_num [eigen]
    · by_cases h1 : j=1 <;> simp [eigen,h0,h1] <;> norm_num
  have he : (fun j => 1-eigen j) =
      (fun j : ℕ => (if j=0 then (1/2:ℝ) else 1)*(if j=1 then (5/4:ℝ) else 1)) := by
    funext j
    by_cases h0 : j=0
    · subst j; norm_num [eigen]
    · by_cases h1 : j=1 <;> simp [eigen,h0,h1] <;> norm_num
  have hp : HasProd (fun j => 1-eigen j) (5/8) := by
    rw [he]
    convert (hasProd_ite_eq (0:ℕ) (1/2:ℝ)).mul
      (hasProd_ite_eq (1:ℕ) (5/4:ℝ)) using 1 <;> norm_num
  have ht : HasSum eigen (1/4) := by
    convert (hasSum_ite_eq (0:ℕ) (1/2:ℝ)).add
      (hasSum_ite_eq (1:ℕ) (-1/4:ℝ)) using 1 <;> norm_num
  have heq : (fun j => (eigen j)^2) =
      (fun j : ℕ => (if j=0 then (1/4:ℝ) else 0)+(if j=1 then (1/16:ℝ) else 0)) := by
    funext j
    by_cases h0 : j=0
    · subst j; norm_num [eigen]
    · by_cases h1 : j=1 <;> simp [eigen,h0,h1] <;> norm_num
  have hq : HasSum (fun j => (eigen j)^2) (5/16) := by
    rw [heq]
    convert (hasSum_ite_eq (0:ℕ) (1/4:ℝ)).add
      (hasSum_ite_eq (1:ℕ) (1/16:ℝ)) using 1 <;> norm_num
  exact ⟨eigen,5/8,1/4,5/16,by norm_num [eigen],by norm_num [eigen],rfl,rfl,rfl,
    hl,hu,hp,ht,hq,signed_product_le_exp_trace_square eigen _ _ _ hl hu hp ht hq⟩

/-- Actual Airy data simultaneously satisfy the negative-endpoint
barrier, primitive, trace-floor and trace-divergence ingredients. -/
theorem signed_trace_all_binder_probe :
    ∃ s : ℝ, s < -1 ∧ s < 0 ∧ s ≤ -1 ∧ airyAiReal 0 ≠ 0 ∧
      0 ≤ airyEnergyFull s ∧
      primitiveBarrier s ≤ (airyEnergyFull (-1)+1)/2 ∧
      (primitiveBarrier (-1)-(airyEnergyFull (-1)+1)/2 ≤
        ∫ x in s..(-1:ℝ), airyAiReal x) ∧
      IntegrableOn airyAiReal (Ioi s) ∧
      signedTraceFloor ≤ hankelSignedTrace s ∧ 0 < airyTraceIntegral s := by
  have hs : (-2:ℝ) ≤ -1 := by norm_num
  have hb := airyTraceIntegral_linear_lower (-2) (by norm_num)
  exact ⟨-2,by norm_num,by norm_num,hs,airyAiReal_zero_pos.ne',
    airyEnergyFull_nonneg (-2) (by norm_num),primitiveBarrier_upper (-2) hs,
    airy_negative_interval_lower (-2) hs,airy_integrable_Ioi (-2),
    hankelSignedTrace_lower (-2) hs,by nlinarith [originMass_pos]⟩

/-- The signed trace equals the shifted Hankel diagonal integral. -/
lemma hankelSignedTrace_diagonal (s : ℝ /- [definition] -/) :
    (∫ x, airyAiReal (x+x+s) ∂ halfLineMeasure) = hankelSignedTrace s := by
  have hshift := (fredholm_measurePreserving_shift (s/2)).integral_comp
    (MeasurableEquiv.addRight (s/2)).measurableEmbedding (fun x => airyAiReal (2*x))
  have hmul := integral_comp_mul_left_Ioi airyAiReal (s/2) (by norm_num : (0:ℝ)<2)
  calc
    (∫ x, airyAiReal (x+x+s) ∂ halfLineMeasure) =
        ∫ x, airyAiReal (2*(x+s/2)) ∂ halfLineMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => congrArg airyAiReal (by ring))
    _ = ∫ x in Ioi (s/2), airyAiReal (2*x) := hshift
    _ = hankelSignedTrace s := by
      rw [show (2:ℝ)*(s/2) = s by ring] at hmul
      simpa [hankelSignedTrace,smul_eq_mul,div_eq_mul_inv,mul_comm] using hmul

/-- Literal half-line version of the same single signed-spectrum bridge. -/
theorem TW1R_tendsto_atBot_zero_of_diagonal_bridge
    (hTWB : ∀ s : ℝ, ∃ eigen : ℕ → ℝ,
      (∀ j, -1 ≤ eigen j) ∧ (∀ j, eigen j ≤ 1) ∧
      HasProd (fun j => 1-eigen j) (TW1R s) ∧
      HasSum eigen (∫ x, airyAiReal (x+x+s) ∂ halfLineMeasure) ∧
      HasSum (fun j => (eigen j)^2)
        (∫ x, airyKernelIntegral (x+s) (x+s) ∂ halfLineMeasure)  /- [standing] -/ ) :
    Tendsto TW1R atBot (𝓝 0) := by
  apply TW1R_tendsto_atBot_zero
  intro s
  obtain ⟨eigen,hl,hu,hp,ht,hq⟩ := hTWB s
  rw [hankelSignedTrace_diagonal s] at ht
  rw [airyTraceIntegral_shift s] at hq
  exact ⟨eigen,hl,hu,hp,ht,hq⟩


/-- Parseval and Tonelli identify the HS square sum with the L2 row mass. -/
theorem l2_rows_norm_square_hasSum
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (r : X → Lp ℝ 2 μ /- [definition] -/ )
    (heval : ∀ f, ∀ᵐ x ∂μ, (A f) x = inner ℝ (r x) f /- [standing] -/ )
    : HasSum (fun i => ‖A (b i)‖ ^ 2) (∫ x, ‖r x‖ ^ 2 ∂μ) := by
  classical
  have hm := l2_operator_rows_aestronglyMeasurable μ b A r heval
  have hc (i : ι) : (fun x => inner ℝ (b i) (r x)) =ᵐ[μ] (fun x => (A (b i)) x) := by
    filter_upwards [heval (b i)] with x hx
    exact (real_inner_comm _ _).trans hx.symm
  have hi (i : ι) : Integrable (fun x => ‖inner ℝ (b i) (r x)‖ ^ 2) μ := by
    apply ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A (b i)))).1
      (Lp.memLp (A (b i)))).congr
    filter_upwards [hc i] with x hx
    rw [hx]
  have hint (i : ι) : (∫ x, ‖inner ℝ (b i) (r x)‖ ^ 2 ∂μ) = ‖A (b i)‖ ^ 2 := by
    calc
      _ = ∫ x, ‖(A (b i)) x‖ ^ 2 ∂μ := integral_congr_ae ((hc i).fun_comp (fun t : ℝ => ‖t‖ ^ 2))
      _ = ‖A (b i)‖ ^ 2 := by
        simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply, star_trivial,
          Real.norm_eq_abs, sq_abs, ← pow_two] using real_inner_self_eq_norm_sq (A (b i))
  have hparseval (x : X) : ENNReal.ofReal (‖r x‖ ^ 2) =
      ∑' i, ENNReal.ofReal (‖inner ℝ (b i) (r x)‖ ^ 2) := by
    rw [← (realHilbertBasis_norm_sq_hasSum b (r x)).tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (realHilbertBasis_norm_sq_hasSum b (r x)).summable
  have hlin : (∫⁻ x, ENNReal.ofReal (‖r x‖ ^ 2) ∂μ) =
      ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
    simp_rw [hparseval]
    have hmeas (i : ι) : AEMeasurable
        (fun x => ENNReal.ofReal (‖inner ℝ (b i) (r x)‖ ^ 2)) μ := by
      simpa only [Pi.pow_apply] using
        ((hm.const_inner (𝕜 := ℝ) (c := b i)).norm.pow 2).aemeasurable.ennreal_ofReal
    rw [lintegral_tsum hmeas]
    apply tsum_congr
    intro i
    rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (Eventually.of_forall (fun _ => sq_nonneg _)), hint i]
  have hr : Integrable (fun x => ‖r x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hm).mp (l2_operator_rows_memLp μ b A hA r heval)
  have he : (∫ x, ‖r x‖ ^ 2 ∂μ) = ∑' i, ‖A (b i)‖ ^ 2 := by
    have hsame : ENNReal.ofReal (∫ x, ‖r x‖ ^ 2 ∂μ) =
        ENNReal.ofReal (∑' i, ‖A (b i)‖ ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hr (Eventually.of_forall (fun _ => sq_nonneg _)),
        hlin, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hA]
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
      ENNReal.toReal_ofReal (tsum_nonneg (fun _ => sq_nonneg _))] using
      congrArg ENNReal.toReal hsame
  rw [he]
  exact hA.hasSum

/-- The norm of the actual Hankel row is the diagonal of its square kernel. -/
theorem airy_hankel_row_norm_square
    (s x : ℝ /- [definition] -/ )
    : ‖sliceLp halfLineMeasure (airyHankelShiftKernel s) x‖ ^ 2 =
      airyKernelIntegral (x+s) (x+s) := by
  let r := sliceLp halfLineMeasure (airyHankelShiftKernel s) x
  calc
    ‖r‖ ^ 2 = ∫ t, (r t) * (r t) ∂halfLineMeasure := by
      simpa only [L2.inner_def, Real.inner_apply] using (real_inner_self_eq_norm_sq r).symm
    _ = airyKernelIntegral (x+s) (x+s) := by
      apply integral_congr_ae
      filter_upwards [sliceLp_apply_ae (memLp_airyHankelShiftSlice s x)] with t ht
      simp only [r, ht, star_trivial, airyHankelShiftKernel,
        halfLineMeasure, add_comm, add_left_comm]

/-- The Airy square trace identity is unconditional, for every countable basis. -/
theorem airy_hankel_square_trace_hasSum
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    : HasSum (fun i => ‖airyHankelShift s (b i)‖ ^ 2)
      (∫ x, airyKernelIntegral (x+s) (x+s) ∂halfLineMeasure) := by
  have h := l2_rows_norm_square_hasSum halfLineMeasure b (airyHankelShift s)
    (airyHankelShift_hs_summable b s)
    (sliceLp halfLineMeasure (airyHankelShiftKernel s)) (airyHankelShift_rows b s).2.2
  simpa only [airy_hankel_row_norm_square] using h


/-- Every finite RMTFoundations.AiryConsequences.compression of a diagonal operator has its literal eigenvalue product. -/
theorem diagonal_compression_det
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (eigen : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ j, T (b j) = eigen j • b j /- [standing] -/ )
    (t : Finset ι /- [definition] -/ )
    : Matrix.det ((1 : Matrix t t ℝ) -
        Matrix.of (fun i j : t => inner ℝ (b i) (T (b j)))) =
      ∏ j ∈ t, (1-eigen j) := by
  classical
  have he : ((1 : Matrix t t ℝ) -
      Matrix.of (fun i j : t => inner ℝ (b i) (T (b j)))) =
      Matrix.diagonal (fun j : t => 1-eigen j) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.of_apply, hdiag, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j; simp
    · have hv : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
      simp [hij,hv]
  rw [he, Matrix.det_diagonal]
  exact Finset.prod_coe_sort t (fun j => 1-eigen j)

/-- A diagonal normalized eigenvector inherits the operator contraction bound. -/
theorem diagonal_eigenvalue_abs_le_one
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (eigen : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ j, T (b j) = eigen j • b j /- [standing] -/ )
    (hcontract : ‖T‖ ≤ 1 /- [standing] -/ )
    (j : ι /- [definition] -/ )
    : |eigen j| ≤ 1 := by
  have h := T.le_opNorm (b j)
  rw [hdiag j, norm_smul, b.orthonormal.norm_eq_one j, mul_one, mul_one,
    Real.norm_eq_abs] at h
  exact h.trans hcontract

/-- A normalized diagonal eigenvector has squared norm equal to the squared eigenvalue. -/
theorem diagonal_apply_norm_square
    {E ι : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    (b : HilbertBasis ι ℝ E /- [definition] -/ )
    (T : E →L[ℝ] E /- [definition] -/ )
    (eigen : ι → ℝ /- [definition] -/ )
    (hdiag : ∀ j, T (b j) = eigen j • b j /- [standing] -/ )
    (j : ι /- [definition] -/ )
    : ‖T (b j)‖ ^ 2 = (eigen j)^2 := by
  rw [hdiag j,norm_smul,b.orthonormal.norm_eq_one j,mul_one,Real.norm_eq_abs,sq_abs]



/-- An actual Hankel eigenbasis has the canonical TW1 product. The landed
bridge supplies the determinant convergence; no product premise remains. -/
theorem TW1R_hasProd_of_eigenbasis
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (eigen : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ j, airyHankelShift s (b j) = eigen j • b j /- [standing] -/ )
    : HasProd (fun j => 1-eigen j) (TW1R s) := by
  classical
  letI : DecidableEq ℕ := Classical.typeDecidableEq ℕ
  have h := TW1R_finite_compressions_tendsto b s
  apply Filter.Tendsto.congr' ?_ h
  filter_upwards [] with t
  convert diagonal_compression_det b (airyHankelShift s) eigen hdiag t using 1
  all_goals first
    | exact Subsingleton.elim _ _
    | congr 1

/-- Squaring the actual Hankel eigenbasis gives the canonical TW2 product. -/
theorem TW2R_hasProd_of_hankel_eigenbasis
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (eigen : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ j, airyHankelShift s (b j) = eigen j • b j /- [standing] -/ )
    : HasProd (fun j => 1-(eigen j)^2) (TW2R s) := by
  classical
  letI : DecidableEq ℕ := Classical.typeDecidableEq ℕ
  have hsq : ∀ j, airyKernelShift s (b j) = (eigen j)^2 • b j := by
    intro j
    simp only [airyKernelShift,ContinuousLinearMap.comp_apply,hdiag,
      map_smul,smul_smul,pow_two]
  have h := TW2R_finite_compressions_tendsto b s
  apply Filter.Tendsto.congr' ?_ h
  filter_upwards [] with t
  convert diagonal_compression_det b (airyKernelShift s) (fun j => (eigen j)^2) hsq t using 1
  all_goals first
    | exact Subsingleton.elim _ _
    | congr 1

/-- The square-eigenvalue trace sum is discharged from actual Airy rows. -/
theorem airy_eigenvalue_square_hasSum
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (eigen : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ j, airyHankelShift s (b j) = eigen j • b j /- [standing] -/ )
    : HasSum (fun j => (eigen j)^2) (airyTraceIntegral s) := by
  have h := airy_hankel_square_trace_hasSum b s
  simp_rw [diagonal_apply_norm_square b (airyHankelShift s) eigen hdiag,
    airyTraceIntegral_shift] at h
  exact h

/-- The signed eigenvalue sum is the genuine operator trace, with no scalar
trace-identification premise. Trace class comes from the landed Hankel factorization. -/
theorem airy_eigenvalue_signed_hasSum
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (eigen : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ j, airyHankelShift s (b j) = eigen j • b j /- [standing] -/ )
    : HasSum eigen (trace (airyHankelShift s)) := by
  have h := (summable_inner_diagonal (isTraceClass_airyHankelShift s) b).hasSum
  rw [← trace_eq_tsum_inner (isTraceClass_airyHankelShift s) b] at h
  have he : (fun j => inner ℝ (b j) (airyHankelShift s (b j))) = eigen := by
    funext j
    rw [hdiag j,inner_smul_right,inner_self_eq_one_of_norm_eq_one (b.orthonormal.norm_eq_one j),mul_one]
  rw [he] at h
  exact h

/-- All determinant/product and square-trace bridge components are proved.
The only standing analytic requirement at this site is the contraction bound
on the actual operator; an eigenbasis is supplied as data with its equation. -/
theorem TW2R_trace_bound_of_contraction_eigenbasis
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (eigen : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ j, airyHankelShift s (b j) = eigen j • b j /- [standing] -/ )
    (hcontract : ‖airyHankelShift s‖ ≤ 1 /- [standing] -/ )
    : 0 ≤ TW2R s ∧ TW2R s ≤ Real.exp (-airyTraceIntegral s) := by
  have hab := diagonal_eigenvalue_abs_le_one b (airyHankelShift s) eigen hdiag hcontract
  have hu : ∀ j, (eigen j)^2 ≤ 1 := by
    intro j
    have h := abs_le.mp (hab j)
    nlinarith
  exact product_le_exp_neg_sum (fun j => (eigen j)^2) _ _ (fun j => sq_nonneg _)
    hu (TW2R_hasProd_of_hankel_eigenbasis b s eigen hdiag)
    (airy_eigenvalue_square_hasSum b s eigen hdiag)

/-- The actual TW1 has a quadratic spectral bound. Product identification,
trace-class summability and the square trace are discharged in this proof. -/
theorem TW1R_trace_square_bound_of_contraction_eigenbasis
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (eigen : ℕ → ℝ /- [definition] -/ )
    (hdiag : ∀ j, airyHankelShift s (b j) = eigen j • b j /- [standing] -/ )
    (hcontract : ‖airyHankelShift s‖ ≤ 1 /- [standing] -/ )
    : 0 ≤ TW1R s ∧ TW1R s ≤
      Real.exp (-trace (airyHankelShift s)-airyTraceIntegral s/8) := by
  have hab := diagonal_eigenvalue_abs_le_one b (airyHankelShift s) eigen hdiag hcontract
  exact signed_product_le_exp_trace_square eigen _ _ _
    (fun j => (abs_le.mp (hab j)).1) (fun j => (abs_le.mp (hab j)).2)
    (TW1R_hasProd_of_eigenbasis b s eigen hdiag)
    (airy_eigenvalue_signed_hasSum b s eigen hdiag)
    (airy_eigenvalue_square_hasSum b s eigen hdiag)

/-- Conditional conditional endpoint. Exact remaining items: the actual Hankel
operator is a contraction and has a complete real eigenbasis indexed by N.
The entire determinant bridge and the square trace identity are proved. -/
theorem TW2R_tendsto_atBot_zero_of_operator_spectrum
    (hSpectrum : ∀ s : ℝ, ∃ b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure),
      ∃ eigen : ℕ → ℝ, (∀ j, airyHankelShift s (b j) = eigen j • b j) ∧
        ‖airyHankelShift s‖ ≤ 1 /- [standing] -/ ) :
    Tendsto TW2R atBot (𝓝 0) := by
  apply TW2R_tendsto_atBot_zero_of_trace_estimate
  intro s
  obtain ⟨b,eigen,hdiag,hcontract⟩ := hSpectrum s
  exact TW2R_trace_bound_of_contraction_eigenbasis b s eigen hdiag hcontract

/-- Conditional conditional endpoint. In addition to the actual contraction
eigenbasis, only the signed operator-trace/diagonal-integral identity remains.
No product, square trace, tail limit, or Painleve identity is assumed. -/
theorem TW1R_tendsto_atBot_zero_of_operator_spectrum
    (hSpectrum : ∀ s : ℝ, ∃ b : HilbertBasis ℕ ℝ (Lp ℝ 2 halfLineMeasure),
      ∃ eigen : ℕ → ℝ, (∀ j, airyHankelShift s (b j) = eigen j • b j) ∧
        ‖airyHankelShift s‖ ≤ 1 /- [standing] -/ )
    (hSignedTrace : ∀ s : ℝ, trace (airyHankelShift s) =
      (∫ x in Ioi s, airyAiReal x)/2 /- [standing] -/ ) :
    Tendsto TW1R atBot (𝓝 0) := by
  apply TW1R_tendsto_atBot_zero
  intro s
  obtain ⟨b,eigen,hdiag,hcontract⟩ := hSpectrum s
  have hab := diagonal_eigenvalue_abs_le_one b (airyHankelShift s) eigen hdiag hcontract
  have ht := airy_eigenvalue_signed_hasSum b s eigen hdiag
  rw [hSignedTrace s] at ht
  exact ⟨eigen,(fun j => (abs_le.mp (hab j)).1),(fun j => (abs_le.mp (hab j)).2),
    TW1R_hasProd_of_eigenbasis b s eigen hdiag,ht,
    airy_eigenvalue_square_hasSum b s eigen hdiag⟩


/-- The finite-dimensional determinant bound needs only positivity of the
matrix itself, and holds even when some eigenvalues exceed one or vanish. -/
theorem posSemidef_det_le_exp_trace_sub_card
    {ι : Type* /- [definition] -/ }
    [Fintype ι /- [definition] -/ ]
    [DecidableEq ι /- [definition] -/ ]
    (M : Matrix ι ι ℝ /- [definition] -/ )
    (hM : M.PosSemidef /- [standing] -/ )
    : 0 ≤ M.det ∧ M.det ≤ Real.exp (M.trace-Fintype.card ι) := by
  constructor
  · exact hM.det_nonneg
  · rw [hM.isHermitian.det_eq_prod_eigenvalues, hM.isHermitian.trace_eq_sum_eigenvalues]
    have hprod : (∏ i, hM.isHermitian.eigenvalues i) ≤
        ∏ i, Real.exp (hM.isHermitian.eigenvalues i-1) := by
      apply Finset.prod_le_prod₀ (fun i _ => hM.eigenvalues_nonneg i)
      intro i _
      simpa only [sub_add_cancel] using Real.add_one_le_exp (hM.isHermitian.eigenvalues i-1)
    calc
      _ ≤ ∏ i, Real.exp (hM.isHermitian.eigenvalues i-1) := hprod
      _ = Real.exp ((∑ i, hM.isHermitian.eigenvalues i)-Fintype.card ι) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib]
        simp

/-- The diagonal of the actual Airy square is the squared norm of a Hankel image. -/
theorem airy_square_inner_diagonal
    (s : ℝ /- [definition] -/ )
    (f : Lp ℝ 2 halfLineMeasure /- [definition] -/ )
    : inner ℝ f (airyKernelShift s f) = ‖airyHankelShift s f‖^2 := by
  rw [airyKernelShift,ContinuousLinearMap.comp_apply]
  have hadj : (airyHankelShift s).adjoint = airyHankelShift s := isSelfAdjoint_airyHankelShift s
  have hi := (airyHankelShift s).adjoint_inner_right f (airyHankelShift s f)
  rw [hadj] at hi
  exact hi.trans (real_inner_self_eq_norm_sq (airyHankelShift s f))

/-- Finite RMTFoundations.AiryConsequences.compression trace uses the unconditional square-trace sum.
This step makes no eigenbasis assumption. -/
theorem airy_compression_trace
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (t : Finset ι /- [definition] -/ )
    : Matrix.trace ((1 : Matrix t t ℝ) -
        Matrix.of (fun i j : t => inner ℝ (b i) (airyKernelShift s (b j)))) =
      t.card - ∑ j ∈ t, ‖airyHankelShift s (b j)‖^2 := by
  classical
  rw [Matrix.trace_sub,Matrix.trace_one]
  simp only [Matrix.trace,Matrix.diag,Matrix.of_apply,airy_square_inner_diagonal]
  rw [Fintype.card_coe]
  congr 1
  exact Finset.sum_coe_sort t (fun j => ‖airyHankelShift s (b j)‖^2)

/-- A trace bound for TW2 under positivity of all I-K finite compressions. -/
theorem TW2R_trace_bound_of_positive_compressions
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (hPositive : ∀ t : Finset ι, ((1 : Matrix t t ℝ) -
      Matrix.of (fun i j : t => inner ℝ (b i) (airyKernelShift s (b j)))).PosSemidef /- [standing] -/ ) :
    0 ≤ TW2R s ∧ TW2R s ≤ Real.exp (-airyTraceIntegral s) := by
  have hd := TW2R_finite_compressions_tendsto b s
  have ht := airy_hankel_square_trace_hasSum b s
  rw [airyTraceIntegral_shift] at ht
  have hb : ∀ t : Finset ι, Matrix.det ((1 : Matrix t t ℝ) -
      Matrix.of (fun i j : t => inner ℝ (b i) (airyKernelShift s (b j)))) ≤
      ∏ j ∈ t, Real.exp (-‖airyHankelShift s (b j)‖^2) := by
    intro t
    have h := (posSemidef_det_le_exp_trace_sub_card _ (hPositive t)).2
    rw [airy_compression_trace b s t,Fintype.card_coe] at h
    simpa only [← Real.exp_sum,Finset.sum_neg_distrib,sub_sub_cancel_left] using h
  exact ⟨ge_of_tendsto hd (Eventually.of_forall (fun t => (hPositive t).det_nonneg)),
    le_of_tendsto_of_tendsto hd ht.neg.rexp (Eventually.of_forall hb)⟩

/-- Conditional endpoint with a single still-open operator-order family.
All analytic trace divergence and determinant identification are discharged. -/
theorem TW2R_tendsto_atBot_zero_of_positive_compressions
    {ι : Type* /- [definition] -/ }
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (hPositive : ∀ s : ℝ, ∀ t : Finset ι, ((1 : Matrix t t ℝ) -
      Matrix.of (fun i j : t => inner ℝ (b i) (airyKernelShift s (b j)))).PosSemidef /- [standing] -/ ) :
    Tendsto TW2R atBot (𝓝 0) := by
  apply TW2R_tendsto_atBot_zero_of_trace_estimate
  exact fun s => TW2R_trace_bound_of_positive_compressions b s (hPositive s)


/-- A nonzero rank-one operator inhabits all binders of the diagonal helpers
simultaneously, including a strict contraction and a nonempty RMTFoundations.AiryConsequences.compression. -/
theorem diagonal_operator_all_binder_probe :
    ∃ b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2),
      ∃ T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2,
      ∃ eigen : ℕ → ℝ, ∃ t : Finset ℕ, ∃ j : ℕ,
        t = {0} ∧ j = 0 ∧ eigen j = 1/2 ∧ ‖T‖ = 1/2 ∧
        (∀ k, T (b k) = eigen k • b k) ∧ ‖T‖ ≤ 1 ∧
        Matrix.det ((1 : Matrix t t ℝ) -
          Matrix.of (fun i k : t => inner ℝ (b i) (T (b k)))) =
          ∏ k ∈ t, (1-eigen k) ∧ |eigen j| ≤ 1 ∧
        ‖T (b j)‖^2 = (eigen j)^2 := by
  obtain ⟨b, _⟩ := realHsFactor_joint_probe
  let T := (1/2 : ℝ) • rankOne ℝ (b 0) (b 0)
  let eigen : ℕ → ℝ := fun j => if j = 0 then 1/2 else 0
  have hd : ∀ j, T (b j) = eigen j • b j := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [T,eigen,rankOne_apply,b.orthonormal.norm_eq_one 0]
    · simp [T,eigen,rankOne_apply,orthonormal_iff_ite.mp b.orthonormal,hj,Ne.symm hj]
  have he : rankOne ℝ (b 0) (b 0) = InnerProductSpace.rankOne ℝ (b 0) (b 0) := rfl
  have hn : ‖T‖ = 1/2 := by
    dsimp [T]
    rw [norm_smul,he,InnerProductSpace.norm_rankOne,b.orthonormal.norm_eq_one 0]
    norm_num
  have hc : ‖T‖ ≤ 1 := by rw [hn]; norm_num
  exact ⟨b,T,eigen,{0},0,rfl,rfl,by simp [eigen],hn,hd,hc,
    diagonal_compression_det b T eigen hd {0},
    diagonal_eigenvalue_abs_le_one b T eigen hd hc 0,
    diagonal_apply_norm_square b T eigen hd 0⟩

/-- Actual nonzero Airy data inhabit every argument of the square trace
identity, including the L2 row evaluation and the HS summability premises. -/
theorem airy_square_trace_all_binder_probe :
    ∃ b : HilbertBasis (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) ℝ
        (Lp ℝ 2 halfLineMeasure),
      Countable (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) ∧
      airyAiReal 0 ≠ 0 ∧ ‖shiftedUnitVector (-1)‖ = 1 ∧
      Summable (fun i => ‖airyHankelShift (-1) (b i)‖^2) ∧
      MemLp (sliceLp halfLineMeasure (airyHankelShiftKernel (-1))) 2 halfLineMeasure ∧
      (∀ f, ∀ᵐ x ∂halfLineMeasure, (airyHankelShift (-1) f) x =
        inner ℝ (sliceLp halfLineMeasure (airyHankelShiftKernel (-1)) x) f) ∧
      HasSum (fun i => ‖airyHankelShift (-1) (b i)‖^2) (airyTraceIntegral (-1)) ∧
      0 < airyTraceIntegral (-1) := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  have hb := airyL2_basis_countable b
  letI := hb
  have hr := airyHankelShift_rows b (-1)
  have ht := airy_hankel_square_trace_hasSum b (-1)
  rw [airyTraceIntegral_shift] at ht
  refine ⟨b,hb,airyAiReal_zero_pos.ne',shiftedUnitVector_norm (-1),
    airyHankelShift_hs_summable b (-1),hr.1,hr.2.2,ht,?_⟩
  have hlo := airyTraceIntegral_linear_lower (-1) (by norm_num)
  nlinarith [originMass_pos]

/-- The finite matrix determinant bound has a strictly positive, nonscalar,
nonzero-trace instance, so its positivity premises are jointly satisfiable. -/
theorem matrix_det_bound_all_binder_probe :
    ∃ M : Matrix (Fin 2) (Fin 2) ℝ,
      M.PosSemidef ∧ M 0 0 = 1/2 ∧ M 1 1 = 3/4 ∧
      M.det = 3/8 ∧ M.trace = 5/4 ∧
      (0 ≤ M.det ∧ M.det ≤ Real.exp (M.trace-Fintype.card (Fin 2))) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun i => if i = 0 then 1/2 else 3/4)
  have hM : M.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    dsimp
    split_ifs <;> norm_num
  refine ⟨M,hM,by norm_num [M],by norm_num [M],?_,?_,
    posSemidef_det_le_exp_trace_sub_card M hM⟩
  · norm_num [M,Matrix.det_fin_two]
  · norm_num [M,Matrix.trace,Matrix.diag,Fin.sum_univ_two]




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

theorem airy_one_sub_compression_positive
    {ι : Type* /- [definition] -/ }
    (b : HilbertBasis ι ℝ (Lp ℝ 2 halfLineMeasure)  /- [definition] -/ )
    (s : ℝ /- [definition] -/ )
    (t : Finset ι /- [definition] -/ )
    : ((1 : Matrix t t ℝ) - Matrix.of
      (fun i j : t => inner ℝ (b i) (airyKernelShift s (b j)))).PosSemidef := by
  classical
  have hle := RMTFoundations.AiryConsequences.positive_le_one_of_norm_le (airyKernelShift s)
    (RMTFoundations.AiryDistribution.isPositive_airyKernelShift s)
    (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s)
  have hp := RMTFoundations.AiryConsequences.compression_positive b (1 - airyKernelShift s)
    ((ContinuousLinearMap.le_def).mp hle) t
  rw [RMTFoundations.AiryConsequences.compression_one_sub] at hp
  exact hp

/-- Canonical TW2 has a global trace bound, without any bridge/order hypothesis. -/
theorem TW2R_trace_bound_unconditional
    (s : ℝ /- [definition] -/ )
    : 0 ≤ TW2R s ∧ TW2R s ≤ Real.exp (-airyTraceIntegral s) := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  letI := airyL2_basis_countable b
  exact TW2R_trace_bound_of_positive_compressions b s
    (airy_one_sub_compression_positive b s)

/-- The physical TW2 left endpoint, with every analytic premise discharged. -/
theorem TW2R_tendsto_atBot_zero_unconditional :
    Tendsto TW2R atBot (𝓝 0) := by
  exact TW2R_tendsto_atBot_zero_of_trace_estimate TW2R_trace_bound_unconditional

/-- Canonical operator-determinant endpoint supplied by the same actual kernel limit. -/
theorem airyOperatorTW2_tendsto_atBot_zero :
    Tendsto airyOperatorTW2 atBot (𝓝 0) := by
  have he : TW2R = airyOperatorTW2 := funext TW2R_eq_airyOperatorTW2
  rw [← he]
  exact TW2R_tendsto_atBot_zero_unconditional

/-- Actual nonzero Airy data jointly inhabit the RMTFoundations.AiryConsequences.compression, trace, and endpoint theorems. -/
theorem airy_left_endpoint_joint_probe :
    ∃ b : HilbertBasis (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) ℝ
      (Lp ℝ 2 halfLineMeasure),
      Countable (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)) ∧
      airyAiReal 0 ≠ 0 ∧ ‖shiftedUnitVector (-1)‖ = 1 ∧
      (airyKernelShift (-1)).IsPositive ∧ ‖airyKernelShift (-1)‖ ≤ 1 ∧
      (∀ t : Finset (canonicalIndex ℝ (Lp ℝ 2 halfLineMeasure)),
        ((1 : Matrix t t ℝ) - Matrix.of
          (fun i j : t => inner ℝ (b i) (airyKernelShift (-1) (b j)))).PosSemidef) ∧
      HasSum (fun i => ‖airyHankelShift (-1) (b i)‖^2) (airyTraceIntegral (-1)) ∧
      0 < airyTraceIntegral (-1) ∧
      (0 ≤ TW2R (-1) ∧ TW2R (-1) ≤ Real.exp (-airyTraceIntegral (-1))) ∧
      Tendsto TW2R atBot (𝓝 0) := by
  let b := canonicalBasis ℝ (Lp ℝ 2 halfLineMeasure)
  have hb := airyL2_basis_countable b
  letI := hb
  have ht := airy_hankel_square_trace_hasSum b (-1)
  rw [airyTraceIntegral_shift] at ht
  refine ⟨b,hb,airyAiReal_zero_pos.ne',shiftedUnitVector_norm (-1),
    RMTFoundations.AiryDistribution.isPositive_airyKernelShift (-1),
    RMTFoundations.AiryBounds.norm_airyKernelShift_le_one (-1),?_,ht,?_,
    TW2R_trace_bound_unconditional (-1),TW2R_tendsto_atBot_zero_unconditional⟩
  · intro t
    convert airy_one_sub_compression_positive b (-1) t using 1
    all_goals first
      | exact Subsingleton.elim _ _
      | (ext i j; by_cases hij : i = j <;> simp [Matrix.one, Matrix.diagonal, hij])
  · have hlo := airyTraceIntegral_linear_lower (-1) (by norm_num)
    nlinarith [originMass_pos]




open MeasureTheory Filter Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel

universe u

set_option maxHeartbeats 800000

theorem TW1R_trace_square_bound_unconditional
    (s : ℝ /- [definition] -/ )
    : 0 ≤ TW1R s ∧ TW1R s ≤
      Real.exp (-hankelSignedTrace s-airyTraceIntegral s/8) := by
  obtain ⟨e,hl,hu,hp,ht,hs⟩ := RMTFoundations.Fredholm.TW1R_spectral_bridge_of_contraction s
    (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s)
  have ht' : HasSum e (hankelSignedTrace s) := by
    simpa only [hankelSignedTrace,div_eq_mul_inv,mul_comm,one_div,one_mul] using ht
  exact signed_product_le_exp_trace_square e _ _ _ hl hu hp ht' hs

/-- TW1 is nonnegative at every actual Airy cutoff. -/
theorem TW1R_nonneg_unconditional
    (s : ℝ /- [definition] -/ )
    : 0 ≤ TW1R s := (TW1R_trace_square_bound_unconditional s).1

/-- The physical TW1 left endpoint, using the actual spectral and trace bridges. -/
theorem TW1R_tendsto_atBot_zero_unconditional :
    Tendsto TW1R atBot (𝓝 0) := by
  apply TW1R_tendsto_atBot_zero
  intro s
  obtain ⟨e,hl,hu,hp,ht,hs⟩ := RMTFoundations.Fredholm.TW1R_spectral_bridge_of_contraction s
    (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s)
  refine ⟨e,hl,hu,hp,?_,hs⟩
  simpa only [hankelSignedTrace,div_eq_mul_inv,mul_comm,one_div,one_mul] using ht

/-- The canonical operator TW1 endpoint follows from the genuine physical determinant. -/
theorem airyOperatorTW1_tendsto_atBot_zero :
    Tendsto airyOperatorTW1 atBot (𝓝 0) := by
  have he : TW1R = airyOperatorTW1 := funext TW1R_eq_airyOperatorTW1
  rw [← he]
  exact TW1R_tendsto_atBot_zero_unconditional

/-- All signed spectral/product/trace binders hold simultaneously for actual nonzero Airy data. -/
theorem airy_signed_left_endpoint_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ‖shiftedUnitVector (-1)‖ = 1 ∧
      ‖airyKernelShift (-1)‖ ≤ 1 ∧
      (∃ e : ℕ → ℝ, (∀ n, -1 ≤ e n) ∧ (∀ n, e n ≤ 1) ∧
        HasProd (fun n => 1-e n) (TW1R (-1)) ∧
        HasSum e (hankelSignedTrace (-1)) ∧
        HasSum (fun n => (e n)^2) (airyTraceIntegral (-1))) ∧
      (0 ≤ TW1R (-1) ∧ TW1R (-1) ≤
        Real.exp (-hankelSignedTrace (-1)-airyTraceIntegral (-1)/8)) ∧
      Tendsto TW1R atBot (𝓝 0) := by
  refine ⟨airyAiReal_zero_pos.ne',shiftedUnitVector_norm (-1),
    RMTFoundations.AiryBounds.norm_airyKernelShift_le_one (-1),?_,TW1R_trace_square_bound_unconditional (-1),
    TW1R_tendsto_atBot_zero_unconditional⟩
  obtain ⟨e,hl,hu,hp,ht,hs⟩ := RMTFoundations.Fredholm.TW1R_spectral_bridge_of_contraction (-1)
    (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one (-1))
  refine ⟨e,hl,hu,hp,?_,hs⟩
  simpa only [hankelSignedTrace,div_eq_mul_inv,mul_comm,one_div,one_mul] using ht


end RMTFoundations.TWLeftTail

#print axioms RMTFoundations.TWLeftTail.airyTraceIntegral
#print axioms RMTFoundations.TWLeftTail.airyTraceIntegral_shift
#print axioms RMTFoundations.TWLeftTail.originMass
#print axioms RMTFoundations.TWLeftTail.originMass_pos
#print axioms RMTFoundations.TWLeftTail.diagonal_eq_energy
#print axioms RMTFoundations.TWLeftTail.diagonal_nonneg
#print axioms RMTFoundations.TWLeftTail.energy_antitone
#print axioms RMTFoundations.TWLeftTail.diagonal_ge_origin
#print axioms RMTFoundations.TWLeftTail.diagonal_continuous
#print axioms RMTFoundations.TWLeftTail.diagonal_integrable
#print axioms RMTFoundations.TWLeftTail.airyTraceIntegral_nonneg
#print axioms RMTFoundations.TWLeftTail.airyTraceIntegral_linear_lower
#print axioms RMTFoundations.TWLeftTail.airyTraceIntegral_tendsto_atBot_atTop
#print axioms RMTFoundations.TWLeftTail.TW2R_tendsto_atBot_zero_of_trace_estimate
#print axioms RMTFoundations.TWLeftTail.product_le_exp_neg_sum
#print axioms RMTFoundations.TWLeftTail.TW2R_tendsto_atBot_zero
#print axioms RMTFoundations.TWLeftTail.TW2R_tendsto_atBot_zero_of_shifted_bridge
#print axioms RMTFoundations.TWLeftTail.product_bound_all_binder_probe
#print axioms RMTFoundations.TWLeftTail.trace_lower_all_binder_probe
#print axioms RMTFoundations.TWLeftTail.product_bound_unit_eigenvalue_probe
#print axioms RMTFoundations.TWLeftTail.airy_data_joint_probe
#print axioms RMTFoundations.TWLeftTail.one_sub_le_exp_quadratic
#print axioms RMTFoundations.TWLeftTail.signed_product_le_exp_trace_square
#print axioms RMTFoundations.TWLeftTail.primitiveBarrier
#print axioms RMTFoundations.TWLeftTail.airyEnergyFull_nonneg
#print axioms RMTFoundations.TWLeftTail.hasDerivAt_primitiveBarrier
#print axioms RMTFoundations.TWLeftTail.primitiveBarrier_upper
#print axioms RMTFoundations.TWLeftTail.airy_negative_interval_lower
#print axioms RMTFoundations.TWLeftTail.airy_integrable_Ioi
#print axioms RMTFoundations.TWLeftTail.airy_Ioi_split
#print axioms RMTFoundations.TWLeftTail.hankelSignedTrace
#print axioms RMTFoundations.TWLeftTail.signedTraceFloor
#print axioms RMTFoundations.TWLeftTail.hankelSignedTrace_lower
#print axioms RMTFoundations.TWLeftTail.TW1R_tendsto_atBot_zero
#print axioms RMTFoundations.TWLeftTail.signed_product_all_binder_probe
#print axioms RMTFoundations.TWLeftTail.signed_trace_all_binder_probe
#print axioms RMTFoundations.TWLeftTail.hankelSignedTrace_diagonal
#print axioms RMTFoundations.TWLeftTail.TW1R_tendsto_atBot_zero_of_diagonal_bridge
#print axioms RMTFoundations.TWLeftTail.l2_rows_norm_square_hasSum
#print axioms RMTFoundations.TWLeftTail.airy_hankel_row_norm_square
#print axioms RMTFoundations.TWLeftTail.airy_hankel_square_trace_hasSum
#print axioms RMTFoundations.TWLeftTail.diagonal_compression_det
#print axioms RMTFoundations.TWLeftTail.diagonal_eigenvalue_abs_le_one
#print axioms RMTFoundations.TWLeftTail.diagonal_apply_norm_square
#print axioms RMTFoundations.TWLeftTail.TW1R_hasProd_of_eigenbasis
#print axioms RMTFoundations.TWLeftTail.TW2R_hasProd_of_hankel_eigenbasis
#print axioms RMTFoundations.TWLeftTail.airy_eigenvalue_square_hasSum
#print axioms RMTFoundations.TWLeftTail.airy_eigenvalue_signed_hasSum
#print axioms RMTFoundations.TWLeftTail.TW2R_trace_bound_of_contraction_eigenbasis
#print axioms RMTFoundations.TWLeftTail.TW1R_trace_square_bound_of_contraction_eigenbasis
#print axioms RMTFoundations.TWLeftTail.TW2R_tendsto_atBot_zero_of_operator_spectrum
#print axioms RMTFoundations.TWLeftTail.TW1R_tendsto_atBot_zero_of_operator_spectrum
#print axioms RMTFoundations.TWLeftTail.posSemidef_det_le_exp_trace_sub_card
#print axioms RMTFoundations.TWLeftTail.airy_square_inner_diagonal
#print axioms RMTFoundations.TWLeftTail.airy_compression_trace
#print axioms RMTFoundations.TWLeftTail.TW2R_trace_bound_of_positive_compressions
#print axioms RMTFoundations.TWLeftTail.TW2R_tendsto_atBot_zero_of_positive_compressions
#print axioms RMTFoundations.TWLeftTail.diagonal_operator_all_binder_probe
#print axioms RMTFoundations.TWLeftTail.airy_square_trace_all_binder_probe
#print axioms RMTFoundations.TWLeftTail.matrix_det_bound_all_binder_probe
#print axioms RMTFoundations.TWLeftTail.airy_one_sub_compression_positive
#print axioms RMTFoundations.TWLeftTail.TW2R_trace_bound_unconditional
#print axioms RMTFoundations.TWLeftTail.TW2R_tendsto_atBot_zero_unconditional
#print axioms RMTFoundations.TWLeftTail.airyOperatorTW2_tendsto_atBot_zero
#print axioms RMTFoundations.TWLeftTail.airy_left_endpoint_joint_probe
#print axioms RMTFoundations.TWLeftTail.TW1R_trace_square_bound_unconditional
#print axioms RMTFoundations.TWLeftTail.TW1R_nonneg_unconditional
#print axioms RMTFoundations.TWLeftTail.TW1R_tendsto_atBot_zero_unconditional
#print axioms RMTFoundations.TWLeftTail.airyOperatorTW1_tendsto_atBot_zero
#print axioms RMTFoundations.TWLeftTail.airy_signed_left_endpoint_joint_probe
