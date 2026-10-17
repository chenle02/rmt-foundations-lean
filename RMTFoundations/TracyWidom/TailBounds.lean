import RMTFoundations.TracyWidom.LeftTail
import RMTFoundations.TracyWidom.OrderOneBounds


set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RMTFoundations.TracyWidom.Tails
open MeasureTheory Set Filter
open scoped Topology

lemma finite_product_lower
    (e : ℕ → ℝ /- [definition] -/)
    (hl : ∀ j, 0  ≤  e j /- [standing] -/)
    (hu : ∀ j, e j  ≤  1 /- [standing] -/)
    (S : Finset ℕ /- [definition] -/) :
    1 - ∑ j  ∈  S, e j  ≤  ∏ j  ∈  S, (1 - e j) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hp : 0  ≤  ∏ j  ∈  S, (1-e j) :=
      Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (hu j))
    have hs : 0  ≤  ∑ j  ∈  S, e j := Finset.sum_nonneg (fun j _ => hl j)
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hu a))
    nlinarith [mul_nonneg (hl a) hs]

theorem positive_product_tail_bounds
    (e : ℕ → ℝ /- [definition] -/)
    (d t : ℝ /- [definition] -/)
    (hl : ∀ j, 0  ≤  e j /- [standing] -/)
    (hu : ∀ j, e j  ≤  1 /- [standing] -/)
    (hp : HasProd (fun j => 1-e j) d /- [standing] -/)
    (ht : HasSum e t /- [standing] -/) :
    1-Real.exp (-t)  ≤  1-d ∧ 1-d  ≤  t := by
  have h := RMTFoundations.TWLeftTail.product_le_exp_neg_sum e d t hl hu hp ht
  have hlow : 1-t  ≤  d :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.sub ht) hp
      (Eventually.of_forall (finite_product_lower e hl hu))
  constructor <;> linarith

lemma exp_neg_linear_square_le_one_sub
    (x : ℝ /- [definition] -/)
    (hx : x  ≤  1/2 /- [standing] -/) :
    Real.exp (-x-2*x^2)  ≤  1-x := by
  have hp : 0 < 1-x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have hid : 1-(1-x)⁻¹ = -x-x^2/(1-x) := by
    field_simp [hp.ne']; ring
  rw [hid] at hlog
  have hsq : x^2/(1-x)  ≤  2*x^2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg (sq_nonneg x) (show 0  ≤  1/2-x by linarith)]
  apply (Real.le_log_iff_exp_le hp).mp
  linarith

theorem signed_product_lower
    (e : ℕ → ℝ /- [definition] -/)
    (d t q : ℝ /- [definition] -/)
    (hu : ∀ j, e j  ≤  1/2 /- [standing] -/)
    (hp : HasProd (fun j => 1-e j) d /- [standing] -/)
    (ht : HasSum e t /- [standing] -/)
    (hq : HasSum (fun j => (e j)^2) q /- [standing] -/) :
    Real.exp (-t-2*q)  ≤  d := by
  have hs : HasSum (fun j => -e j-2*(e j)^2) (-t-2*q) :=
    ht.neg.sub (hq.mul_left 2)
  apply le_of_tendsto_of_tendsto hs.rexp hp
  apply Eventually.of_forall
  intro S
  exact Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le)
    (fun j _ => exp_neg_linear_square_le_one_sub (e j) (hu j))

theorem signed_product_tail_bounds
    (e : ℕ → ℝ /- [definition] -/)
    (d t q : ℝ /- [definition] -/)
    (hu : ∀ j, e j  ≤  1/2 /- [standing] -/)
    (hp : HasProd (fun j => 1-e j) d /- [standing] -/)
    (ht : HasSum e t /- [standing] -/)
    (hq : HasSum (fun j => (e j)^2) q /- [standing] -/) :
    1-Real.exp (-t)  ≤  1-d ∧ 1-d  ≤  t+2*q := by
  have hlo := signed_product_lower e d t q hu hp ht hq
  have hup : d  ≤  Real.exp (-t) := by
    apply le_of_tendsto_of_tendsto hp ht.neg.rexp
    apply Eventually.of_forall
    intro S
    apply Finset.prod_le_prod₀ (fun j _ => by linarith [hu j])
    intro j _
    change 1-e j  ≤  Real.exp (-e j)
    linarith [Real.add_one_le_exp (-e j)]
  have he := Real.add_one_le_exp (-t-2*q)
  constructor <;> linarith

/-- Nonzero scalar joint instances for every bound and every binder. -/
theorem scalar_tail_all_binder_joint_probe :
    ∃ e : ℕ → ℝ, ∃ d t q : ℝ,
      e 0 = 1/2 ∧ 0 < d ∧ 0 < t ∧ 0 < q ∧
      (∀ j, 0  ≤  e j) ∧ (∀ j, e j  ≤  1/2) ∧
      HasProd (fun j => 1-e j) d ∧ HasSum e t ∧
      HasSum (fun j => (e j)^2) q ∧
      (1-Real.exp (-t)  ≤  1-d ∧ 1-d  ≤  t) ∧
      (1-Real.exp (-t)  ≤  1-d ∧ 1-d  ≤  t+2*q) := by
  let e : ℕ → ℝ := fun j => if j=0 then 1/2 else 0
  have hl : ∀ j, 0  ≤  e j := by intro j; dsimp [e]; split_ifs <;> norm_num
  have hu : ∀ j, e j  ≤  1/2 := by intro j; dsimp [e]; split_ifs <;> norm_num
  have hp : HasProd (fun j => 1-e j) (1/2) := by
    convert hasProd_ite_eq (0:ℕ) (1/2:ℝ) using 1
    funext j; dsimp [e]; split_ifs <;> norm_num
  have ht : HasSum e (1/2) := hasSum_ite_eq (0:ℕ) (1/2:ℝ)
  have hq : HasSum (fun j => (e j)^2) (1/4) := by
    convert hasSum_ite_eq (0:ℕ) (1/4:ℝ) using 1
    funext j; dsimp [e]; split_ifs <;> norm_num
  refine ⟨e,1/2,1/2,1/4,by simp [e],by norm_num,by norm_num,by norm_num,
    hl,hu,hp,ht,hq,positive_product_tail_bounds e _ _ hl
      (fun j => (hu j).trans (by norm_num)) hp ht, signed_product_tail_bounds e _ _ _ hu hp ht hq⟩

open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWLeftTail

lemma rpow_three_halves_increment
    (s u : ℝ /- [definition] -/)
    (hs : 1  ≤  s /- [standing] -/)
    (hu : s  ≤  u /- [standing] -/) :
    s^(3/2:ℝ)+(u-s)  ≤  u^(3/2:ℝ) := by
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := hs0.trans_le hu
  have hrs : s^(3/2:ℝ) = Real.sqrt s * s := by
    rw [show (3/2:ℝ)=1/2+1 by norm_num, Real.rpow_add_one hs0.ne', Real.sqrt_eq_rpow]
  have hru : u^(3/2:ℝ) = Real.sqrt u * u := by
    rw [show (3/2:ℝ)=1/2+1 by norm_num, Real.rpow_add_one hu0.ne', Real.sqrt_eq_rpow]
  have hroot : 1  ≤  Real.sqrt s := by
    simpa using Real.sqrt_le_sqrt hs
  have hm := Real.sqrt_le_sqrt hu
  rw [hrs,hru]
  nlinarith [mul_nonneg (show 0  ≤  u-s by linarith) (show 0  ≤  Real.sqrt s-1 by linarith),
    mul_nonneg (show 0  ≤  Real.sqrt u-Real.sqrt s by linarith) hu0.le]

lemma shifted_Airy_envelope
    (C s t : ℝ /- [definition] -/)
    (hC : 0 < C /- [standing] -/)
    (hb : ∀ u : ℝ, 0  ≤  u → |airyAiReal u|  ≤
      C*Real.exp (-(2/3*u^(3/2:ℝ))) /- [standing] -/)
    (hs : 1  ≤  s /- [standing] -/)
    (ht : 0  ≤  t /- [standing] -/) :
    |airyAiReal (s+t)|  ≤
      (C*Real.exp (-(2/3*s^(3/2:ℝ)))) * Real.exp (-(2/3)*t) := by
  have hu : 0  ≤  s+t := by linarith
  have hi := rpow_three_halves_increment s (s+t) hs (by linarith)
  have he : -(2/3*(s+t)^(3/2:ℝ))  ≤  -(2/3*s^(3/2:ℝ)) + -(2/3)*t := by linarith
  calc
    |airyAiReal (s+t)|  ≤  C*Real.exp (-(2/3*(s+t)^(3/2:ℝ))) := hb _ hu
    _  ≤  C*Real.exp (-(2/3*s^(3/2:ℝ)) + -(2/3)*t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC.le
    _ = _ := by rw [Real.exp_add]; ring

lemma halfline_exponential_integral
    (a : ℝ /- [definition] -/)
    (ha : 0 < a /- [standing] -/) :
    (∫ t, Real.exp (-a*t) ∂halfLineMeasure) = 1/a := by
  change (∫ t in Ioi (0:ℝ), Real.exp (-a*t)) = _
  rw [integral_exp_mul_Ioi (by linarith : -a<0) 0]
  simp

lemma hankel_trace_upper_of_envelope
    (C s : ℝ /- [definition] -/)
    (hC : 0 < C /- [standing] -/)
    (hb : ∀ u : ℝ, 0  ≤  u → |airyAiReal u|  ≤
      C*Real.exp (-(2/3*u^(3/2:ℝ))) /- [standing] -/)
    (hs : 1  ≤  s /- [standing] -/) :
    hankelSignedTrace s  ≤  (3/4*C)*Real.exp (-(2/3*s^(3/2:ℝ))) := by
  have hshift : (∫ t, airyAiReal (s+t) ∂halfLineMeasure) = ∫ t in Ioi s, airyAiReal t := by
    have h := (fredholm_measurePreserving_shift s).integral_comp
      (MeasurableEquiv.addRight s).measurableEmbedding airyAiReal
    simpa [add_comm] using h
  have hi : Integrable (fun t : ℝ =>
      (C*Real.exp (-(2/3*s^(3/2:ℝ))))*Real.exp (-(2/3)*t)) halfLineMeasure :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(2/3:ℝ)<0) 0).const_mul _
  have hiAi : Integrable (fun t : ℝ => airyAiReal (s+t)) halfLineMeasure := by
    apply hi.mono'
    · exact (continuous_airyAiReal.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    · apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro t ht
      simpa [Real.norm_eq_abs] using shifted_Airy_envelope C s t hC hb hs ht.le
  have hm := integral_mono_ae hiAi hi (by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    exact (le_abs_self _).trans (shifted_Airy_envelope C s t hC hb hs ht.le))
  rw [hshift,integral_const_mul,halfline_exponential_integral (2/3) (by norm_num)] at hm
  dsimp [hankelSignedTrace]
  linarith

lemma diagonal_upper_of_envelope
    (C s x : ℝ /- [definition] -/)
    (hC : 0 < C /- [standing] -/)
    (hb : ∀ u : ℝ, 0  ≤  u → |airyAiReal u|  ≤
      C*Real.exp (-(2/3*u^(3/2:ℝ))) /- [standing] -/)
    (hs : 1  ≤  s /- [standing] -/)
    (hx : s  ≤  x /- [standing] -/) :
    airyKernelIntegral x x  ≤
      (3/4*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))*Real.exp (-(4/3)*(x-s)) := by
  let A := C*Real.exp (-(2/3*s^(3/2:ℝ)))
  have hi : Integrable (fun t : ℝ => A^2*Real.exp (-(4/3)*(x-s))*Real.exp (-(4/3)*t)) halfLineMeasure :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(4/3:ℝ)<0) 0).const_mul _
  have hiAi := Ai_product_integrable x x
  have hm : airyKernelIntegral x x  ≤
      ∫ t, A^2*Real.exp (-(4/3)*(x-s))*Real.exp (-(4/3)*t) ∂halfLineMeasure := by
    apply integral_mono_ae hiAi hi
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have hh := shifted_Airy_envelope C s ((x-s)+t) hC hb hs (by have htpos : 0<t := ht; linarith)
    have he : (A*Real.exp (-(2/3)*((x-s)+t)))^2 =
        A^2*Real.exp (-(4/3)*(x-s))*Real.exp (-(4/3)*t) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2:ℝ)* (-(2/3)*((x-s)+t)) = -(4/3)*(x-s) + -(4/3)*t by ring,Real.exp_add]
      ring
    have harg : s+((x-s)+t)=x+t := by ring
    rw [harg] at hh
    change airyAiReal (x+t)*airyAiReal (x+t)  ≤  A^2*Real.exp (-(4/3)*(x-s))*Real.exp (-(4/3)*t)
    rw [← he]
    dsimp [A] at *
    nlinarith [sq_abs (airyAiReal (x+t)), abs_nonneg (airyAiReal (x+t)),
      show 0  ≤  C*Real.exp (-(2/3*s^(3/2:ℝ)))*Real.exp (-(2/3)*((x-s)+t)) by positivity]
  rw [integral_const_mul,halfline_exponential_integral (4/3) (by norm_num)] at hm
  have heA : A^2 = C^2*Real.exp (-(4/3*s^(3/2:ℝ))) := by
    dsimp [A]
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    congr 2 <;> ring
  rw [heA] at hm
  nlinarith
lemma Airy_trace_upper_of_envelope
    (C s : ℝ /- [definition] -/)
    (hC : 0 < C /- [standing] -/)
    (hb : ∀ u : ℝ, 0  ≤  u → |airyAiReal u|  ≤
      C*Real.exp (-(2/3*u^(3/2:ℝ))) /- [standing] -/)
    (hs : 1  ≤  s /- [standing] -/) :
    airyTraceIntegral s  ≤  (9/16*C^2)*Real.exp (-(4/3*s^(3/2:ℝ))) := by
  let A := (3/4*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))
  have hi : Integrable (fun t : ℝ => A*Real.exp (-(4/3)*t)) halfLineMeasure :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(4/3:ℝ)<0) 0).const_mul _
  have hh : ∀ t : ℝ, 0  ≤  t →
      airyKernelIntegral (t+s) (t+s)  ≤  A*Real.exp (-(4/3)*t) := by
    intro t ht
    have h := diagonal_upper_of_envelope C s (t+s) hC hb hs (by linarith)
    simpa only [add_sub_cancel_right] using h
  have hik : Integrable (fun t : ℝ => airyKernelIntegral (t+s) (t+s)) halfLineMeasure := by
    apply hi.mono'
    · exact (diagonal_continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro t ht
      rw [Real.norm_of_nonneg (diagonal_nonneg _)]
      exact hh t ht.le
  have hm := integral_mono_ae hik hi (by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    exact hh t ht.le)
  rw [airyTraceIntegral_shift,integral_const_mul,
    halfline_exponential_integral (4/3) (by norm_num)] at hm
  dsimp [A] at hm
  nlinarith

/-- Fixed actual Airy data inhabit all envelope binders on a nonzero instance. -/
theorem Airy_envelope_all_binder_joint_probe :
    ∃ C s : ℝ, 0<C ∧ 1 ≤ s ∧ airyAiReal s  ≠  0 ∧
      (∀ u : ℝ, 0 ≤ u → |airyAiReal u| ≤ C*Real.exp (-(2/3*u^(3/2:ℝ)))) ∧
      hankelSignedTrace s ≤ (3/4*C)*Real.exp (-(2/3*s^(3/2:ℝ))) ∧
      airyTraceIntegral s ≤ (9/16*C^2)*Real.exp (-(4/3*s^(3/2:ℝ))) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_superexponential_bound
  exact ⟨C,1,hC,le_rfl,(airyAiReal_pos_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).ne',hb,
    hankel_trace_upper_of_envelope C 1 hC hb le_rfl,
    Airy_trace_upper_of_envelope C 1 hC hb le_rfl⟩

open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWLeftTail

noncomputable def lowerAiryConstant : ℝ := Real.sqrt (1/3:ℝ)/Real.pi
noncomputable def lowerAiryRate : ℝ := (2/3)*Real.cosh 1
noncomputable def lowerAiryEnvelope (x : ℝ /- [definition] -/) : ℝ :=
  lowerAiryConstant*Real.exp (-lowerAiryRate*x^(3/2:ℝ))

lemma lowerAiryConstant_pos : 0<lowerAiryConstant :=
  div_pos (Real.sqrt_pos.mpr (by norm_num)) Real.pi_pos
lemma lowerAiryRate_pos : 0<lowerAiryRate :=
  mul_pos (by norm_num) (Real.cosh_pos _)
lemma lowerAiryEnvelope_pos (x : ℝ /- [definition] -/) : 0<lowerAiryEnvelope x :=
  mul_pos lowerAiryConstant_pos (Real.exp_pos _)

lemma schlaefli_lower
    (z : ℝ /- [definition] -/)
    (hz : 0<z /- [standing] -/) :
    Real.exp (-z*Real.cosh 1)  ≤  schlaefliK13 z := by
  have hi := (integrable_schlaefliK13_integrand hz).integrableOn
    (s:=Ioo (0:ℝ) 1)
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (-z*Real.cosh 1)) (Ioo (0:ℝ) 1) :=
    integrableOn_const (by simp)
  have hm := setIntegral_mono_on hc hi measurableSet_Ioo (fun t ht => by
    have ht0 : 0 ≤ t := ht.1.le
    have hh : Real.cosh t ≤ Real.cosh 1 := Real.cosh_le_cosh.mpr
      (by rw [abs_of_nonneg ht0]; norm_num; exact ht.2.le)
    have he : Real.exp (-z*Real.cosh 1) ≤ Real.exp (-z*Real.cosh t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hh (by linarith))
    exact he.trans (le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_cosh _)))
  have hsub : Ioo (0:ℝ) 1  ≤ᵐ[volume] Ioi (0:ℝ) :=
    Eventually.of_forall (fun _ ht => ht.1)
  have hf := setIntegral_mono_set (integrableOn_schlaefliK13_integrand hz)
    (Eventually.of_forall (fun t =>
      (mul_pos (Real.exp_pos _) (Real.cosh_pos _)).le)) hsub
  have hcval : (∫ t in Ioo (0:ℝ) 1, Real.exp (-z*Real.cosh 1)) = Real.exp (-z*Real.cosh 1) := by
    rw [setIntegral_const]
    simp [Measure.real]
  rw [hcval] at hm
  exact hm.trans hf

/-- Explicit positive lower envelope, proved from the Schlaefli integral. -/
theorem Ai_lower_envelope
    (x : ℝ /- [definition] -/)
    (hx : 1 ≤ x /- [standing] -/) : lowerAiryEnvelope x ≤ airyAiReal x := by
  have hx0 : 0<x := by linarith
  have hz : 0<(2/3:ℝ)*x^(3/2:ℝ) := by positivity
  have hr : Real.sqrt (1/3:ℝ) ≤ Real.sqrt (x/3) :=
    Real.sqrt_le_sqrt (by linarith)
  have hk := schlaefli_lower ((2/3)*x^(3/2:ℝ)) hz
  rw [airyAiReal_eq_airyBesselY_div_pi hx0]
  dsimp [airyBesselY,lowerAiryEnvelope,lowerAiryConstant,lowerAiryRate]
  have he : -((2/3)*x^(3/2:ℝ))*Real.cosh 1 = -((2/3)*Real.cosh 1)*x^(3/2:ℝ) := by ring
  rw [he] at hk
  calc
    Real.sqrt (1/3:ℝ)/Real.pi*Real.exp (-((2/3)*Real.cosh 1)*x^(3/2:ℝ)) =
      (Real.sqrt (1/3:ℝ)*Real.exp (-((2/3)*Real.cosh 1)*x^(3/2:ℝ)))/Real.pi := by ring
    _  ≤  (Real.sqrt (x/3)*schlaefliK13 ((2/3)*x^(3/2:ℝ)))/Real.pi :=
      div_le_div_of_nonneg_right (mul_le_mul hr hk (Real.exp_pos _).le (Real.sqrt_nonneg _)) Real.pi_pos.le

lemma lowerAiryEnvelope_antitone_nonneg : AntitoneOn lowerAiryEnvelope (Ici (0:ℝ)) := by
  intro x hx y hy hxy
  apply mul_le_mul_of_nonneg_left _ lowerAiryConstant_pos.le
  apply Real.exp_le_exp.mpr
  have hr := Real.rpow_le_rpow hx hxy (by norm_num : (0:ℝ) ≤ 3/2)
  exact mul_le_mul_of_nonpos_left hr (neg_nonpos.mpr lowerAiryRate_pos.le)

lemma hankel_trace_lower_envelope
    (s : ℝ /- [definition] -/)
    (hs : 1 ≤ s /- [standing] -/) :
    lowerAiryEnvelope (s+1)/2 ≤ hankelSignedTrace s := by
  have hi := (airy_integrable_Ioi s).mono_set (show Ioo s (s+1) ⊆ Ioi s from fun _ hx => hx.1)
  have hc : IntegrableOn (fun _ : ℝ => lowerAiryEnvelope (s+1)) (Ioo s (s+1)) :=
    integrableOn_const (by simp)
  have hm := setIntegral_mono_on hc hi measurableSet_Ioo (fun x hx =>
    (lowerAiryEnvelope_antitone_nonneg (by change 0 ≤ x; linarith [hx.1])
      (by change 0 ≤ s+1; linarith) hx.2.le).trans (Ai_lower_envelope x (by linarith [hx.1])))
  have hf := setIntegral_mono_set (airy_integrable_Ioi s)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx =>
      (airyAiReal_pos_of_nonneg (by have hxpos : s<x := hx; linarith)).le))
    (Eventually.of_forall (fun _ hx => hx.1) : Ioo s (s+1) ≤ᵐ[volume]Ioi s)
  have hv : (∫ x in Ioo s (s+1), lowerAiryEnvelope (s+1)) = lowerAiryEnvelope (s+1) := by
    rw [setIntegral_const]
    simp [Measure.real]
  rw [hv] at hm
  dsimp [hankelSignedTrace]
  linarith

lemma diagonal_lower_envelope
    (s x : ℝ /- [definition] -/)
    (hs : 1 ≤ s /- [standing] -/)
    (hx : x ∈ Ioo s (s+1) /- [standing] -/) :
    (lowerAiryEnvelope (s+2))^2 ≤ airyKernelIntegral x x := by
  have hiAi : IntegrableOn (fun t : ℝ => airyAiReal (x+t)*airyAiReal (x+t)) (Ioi (0:ℝ)) volume :=
    Ai_product_integrable x x
  have hi := hiAi.mono_set (show Ioo (0:ℝ) 1 ⊆ Ioi (0:ℝ) from fun _ ht => ht.1)
  have hc : IntegrableOn (fun _ : ℝ => (lowerAiryEnvelope (s+2))^2) (Ioo (0:ℝ) 1) :=
    integrableOn_const (by simp)
  have hm := setIntegral_mono_on hc hi measurableSet_Ioo (fun t ht => by
    have hb := (lowerAiryEnvelope_antitone_nonneg
      (by change 0 ≤ x+t; linarith [hx.1,ht.1])
      (by change 0 ≤ s+2; linarith) (by linarith [hx.2,ht.2])).trans
        (Ai_lower_envelope (x+t) (by linarith [hx.1,ht.1]))
    nlinarith [lowerAiryEnvelope_pos (s+2)])
  have hf := setIntegral_mono_set hiAi
    (Eventually.of_forall (fun t => mul_self_nonneg (airyAiReal (x+t))))
    (Eventually.of_forall (fun _ ht => ht.1) : Ioo (0:ℝ) 1 ≤ᵐ[volume]Ioi (0:ℝ))
  have hv : (∫ t in Ioo (0:ℝ) 1, (lowerAiryEnvelope (s+2))^2) =
      (lowerAiryEnvelope (s+2))^2 := by rw [setIntegral_const]; simp [Measure.real]
  rw [hv] at hm
  exact hm.trans hf

lemma Airy_trace_lower_envelope
    (s : ℝ /- [definition] -/)
    (hs : 1 ≤ s /- [standing] -/) :
    (lowerAiryEnvelope (s+2))^2 ≤ airyTraceIntegral s := by
  have hi := (diagonal_integrable s).mono_set (show Ioo s (s+1) ⊆ Ioi s from fun _ hx => hx.1)
  have hc : IntegrableOn (fun _ : ℝ => (lowerAiryEnvelope (s+2))^2) (Ioo s (s+1)) :=
    integrableOn_const (by simp)
  have hm := setIntegral_mono_on hc hi measurableSet_Ioo
    (fun x hx => diagonal_lower_envelope s x hs hx)
  have hf := setIntegral_mono_set (diagonal_integrable s)
    (Eventually.of_forall diagonal_nonneg)
    (Eventually.of_forall (fun _ hx => hx.1) : Ioo s (s+1) ≤ᵐ[volume]Ioi s)
  have hv : (∫ x in Ioo s (s+1), (lowerAiryEnvelope (s+2))^2) =
      (lowerAiryEnvelope (s+2))^2 := by rw [setIntegral_const]; simp [Measure.real]
  rw [hv] at hm
  exact hm.trans hf

/-- The full lower-envelope binder family holds on an actual positive Airy instance. -/
theorem lower_envelope_all_binder_joint_probe :
    0<lowerAiryConstant ∧ 0<lowerAiryRate ∧ 0<airyAiReal 1 ∧
      lowerAiryEnvelope 1 ≤ airyAiReal 1 ∧
      lowerAiryEnvelope 2/2 ≤ hankelSignedTrace 1 ∧
      (lowerAiryEnvelope 3)^2 ≤ airyTraceIntegral 1 := by
  refine ⟨lowerAiryConstant_pos,lowerAiryRate_pos,airyAiReal_pos_of_nonneg (by norm_num),
    Ai_lower_envelope 1 le_rfl,?_,?_⟩
  · convert hankel_trace_lower_envelope 1 le_rfl using 1 <;> norm_num
  · convert Airy_trace_lower_envelope 1 le_rfl using 1 <;> norm_num

open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWLeftTail

/-- Actual physical TW2 determinant: the lower and upper right-tail bounds
share the literal Airy trace. No imported spectral/trace fields are premises. -/
theorem TW2R_right_tail_trace_bounds
    (s : ℝ /- [definition] -/) :
    1-Real.exp (-airyTraceIntegral s)  ≤  1-TW2R s ∧
      1-TW2R s  ≤  airyTraceIntegral s := by
  obtain ⟨e,hl,hu,hp,ht⟩ := RMTFoundations.Fredholm.TW2R_spectral_bridge_of_contraction s
    (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s)
  exact positive_product_tail_bounds e _ _ hl hu hp ht

/-- A small literal Airy trace forces the constructed Hankel eigenvalues
below 1/2, giving explicit constants 1 and 2 in the signed tail estimate. -/
theorem TW1R_right_tail_trace_bounds
    (s : ℝ /- [definition] -/)
    (hqsmall : airyTraceIntegral s  ≤  1/4 /- [standing] -/) :
    1-Real.exp (-hankelSignedTrace s)  ≤  1-TW1R s ∧
      1-TW1R s  ≤  hankelSignedTrace s+2*airyTraceIntegral s := by
  obtain ⟨e,hl,hu,hp,ht,hq⟩ := RMTFoundations.Fredholm.TW1R_spectral_bridge_of_contraction s
    (RMTFoundations.AiryBounds.norm_airyKernelShift_le_one s)
  have ht' : HasSum e (hankelSignedTrace s) := by
    simpa [hankelSignedTrace,div_eq_mul_inv,mul_comm] using ht
  have hhalf : ∀ j, e j  ≤  1/2 := by
    intro j
    have hj : (e j)^2  ≤  airyTraceIntegral s := by
      simpa only [Finset.sum_singleton, airyTraceIntegral] using sum_le_hasSum ({j}:Finset ℕ) (fun i _ => sq_nonneg (e i)) hq
    nlinarith [sq_nonneg (e j-1/2)]
  exact signed_product_tail_bounds e _ _ _ hhalf hp ht' hq

/-- Faithful quantitative left estimate obtained from the trace bound. -/
theorem TW2R_left_tail_linear
    (s : ℝ /- [definition] -/)
    (hs : s  ≤  0 /- [standing] -/) :
    TW2R s  ≤  Real.exp (-originMass*|s|) := by
  apply (TW2R_trace_bound_unconditional s).2.trans
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonpos hs]
  nlinarith [airyTraceIntegral_linear_lower s hs]

/-- Faithful signed quantitative left estimate: the floor is a explicit Airy-data constant; cubic decay is not asserted here. -/
theorem TW1R_left_tail_linear
    (s : ℝ /- [definition] -/)
    (hs : s  ≤  -1 /- [standing] -/) :
    TW1R s  ≤  Real.exp (-signedTraceFloor-originMass*|s|/8) := by
  apply (TW1R_trace_square_bound_unconditional s).2.trans
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonpos (by linarith : s  ≤  0)]
  nlinarith [hankelSignedTrace_lower s hs,airyTraceIntegral_linear_lower s (by linarith)]

theorem left_tail_all_binder_joint_probe :
    ∃ s : ℝ, s<0 ∧ s ≤ -1 ∧ 0<originMass ∧ 0<airyTraceIntegral s ∧
      TW2R s  ≤  Real.exp (-originMass*|s|) ∧
      TW1R s  ≤  Real.exp (-signedTraceFloor-originMass*|s|/8) := by
  refine ⟨-1,by norm_num,by norm_num,originMass_pos,?_,
    TW2R_left_tail_linear (-1) (by norm_num),TW1R_left_tail_linear (-1) (by norm_num)⟩
  have h := airyTraceIntegral_linear_lower (-1) (by norm_num)
  nlinarith [originMass_pos]

/-- Cross-family control with both positive and negative eigenvalues.
The scalar signed argument must not rely on positive semidefiniteness. -/
theorem signed_tail_cross_family_joint_probe :
    ∃ e : ℕ → ℝ, ∃ d t q : ℝ,
      0<e 0 ∧ e 1<0 ∧ 0<d ∧ 0<t ∧ 0<q ∧ q ≤ 1/4 ∧
      (∀ j, e j ≤ 1/2) ∧ HasProd (fun j => 1-e j) d ∧ HasSum e t ∧
      HasSum (fun j => (e j)^2) q ∧
      (1-Real.exp (-t) ≤ 1-d ∧ 1-d ≤ t+2*q) := by
  let e : ℕ → ℝ := fun j => if j=0 then 1/4 else if j=1 then -1/8 else 0
  have hu : ∀ j, e j ≤ 1/2 := by intro j; dsimp [e]; split_ifs <;> norm_num
  have hp : HasProd (fun j => 1-e j) (27/32) := by
    have h : HasProd (fun j => 1-e j) (∏ j  ∈  ({0,1}:Finset ℕ), (1-e j)) :=
      hasProd_prod_of_ne_finset_one (fun j hj => by
        have hj01 : j  ≠  0 ∧ j  ≠  1 := by simpa using hj
        simp [e,hj01.1,hj01.2])
    norm_num [e] at h ⊢
    exact h
  have ht : HasSum e (1/8) := by
    have h : HasSum e (∑ j  ∈  ({0,1}:Finset ℕ), e j) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by
        have hj01 : j  ≠  0 ∧ j  ≠  1 := by simpa using hj
        simp [e,hj01.1,hj01.2])
    norm_num [e] at h ⊢
    exact h
  have hq : HasSum (fun j => (e j)^2) (5/64) := by
    have h : HasSum (fun j => (e j)^2) (∑ j  ∈  ({0,1}:Finset ℕ), (e j)^2) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by
        have hj01 : j  ≠  0 ∧ j  ≠  1 := by simpa using hj
        simp [e,hj01.1,hj01.2])
    norm_num [e] at h ⊢
    exact h
  exact ⟨e,27/32,1/8,5/64,by norm_num [e],by norm_num [e],by norm_num,by norm_num,
    by norm_num,by norm_num,hu,hp,ht,hq,signed_product_tail_bounds e _ _ _ hu hp ht hq⟩

/-- Counterinstance to extracting a cubic estimate solely from the scalar
product/trace interfaces. This is not a counterexample for the actual Airy kernel.
A strict rank-N contraction has trace N/2 but determinant 2^(-N). -/
theorem trace_interface_cubic_counterinstance
    (c : ℝ /- [definition] -/)
    (hc : 0<c /- [standing] -/) :
    ∃ N : ℕ, ∃ e : ℕ → ℝ, ∃ d t q : ℝ,
      0<N ∧ (∀ j, 0 ≤ e j) ∧ (∀ j, e j ≤ 1/2) ∧
      HasProd (fun j => 1-e j) d ∧ HasSum e t ∧
      HasSum (fun j => (e j)^2) q ∧ t=(N:ℝ)/2 ∧ q=(N:ℝ)/4 ∧
      0<d ∧ Real.exp (-c*(N:ℝ)^3)<d := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/c))
  have hn1 : 1<(N:ℝ) := (le_max_left _ _).trans_lt hN
  have hn0 : 0<(N:ℝ) := by linarith
  have hn : 0<N := by exact_mod_cast hn0
  have hcn : 1<c*(N:ℝ) := by
    have hd : 1/c<(N:ℝ) := (le_max_right _ _).trans_lt hN
    have hh := (div_lt_iff₀ hc).mp hd
    nlinarith
  have hsq : (N:ℝ)  ≤  (N:ℝ)^2 := by nlinarith
  have hcsq : 1<c*(N:ℝ)^2 :=
    hcn.trans_le (mul_le_mul_of_nonneg_left hsq hc.le)
  have hcube : (N:ℝ)<c*(N:ℝ)^3 := by
    have hh := mul_lt_mul_of_pos_right hcsq hn0
    nlinarith
  let e : ℕ → ℝ := fun j => if j<N then 1/2 else 0
  let d : ℝ := (1/2)^N
  have hl : ∀ j, 0 ≤ e j := by intro j; dsimp [e]; split_ifs <;> norm_num
  have hu : ∀ j, e j ≤ 1/2 := by intro j; dsimp [e]; split_ifs <;> norm_num
  have hp : HasProd (fun j => 1-e j) d := by
    have h : HasProd (fun j => 1-e j) (∏ j  ∈  Finset.range N, (1-e j)) :=
      hasProd_prod_of_ne_finset_one (fun j hj => by
        dsimp [e]; rw [if_neg (by simpa using hj)]; ring)
    convert h using 1
    calc
      d = ∏ _j  ∈  Finset.range N, (1/2:ℝ) := by simp [d]
      _ = ∏ j  ∈  Finset.range N, (1-e j) := by
        apply Finset.prod_congr rfl
        intro j hj
        norm_num [e,Finset.mem_range.mp hj]
  have ht : HasSum e ((N:ℝ)/2) := by
    have h : HasSum e (∑ j  ∈  Finset.range N, e j) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by dsimp [e]; exact if_neg (by simpa using hj))
    convert h using 1
    calc
      (N:ℝ)/2 = ∑ _j  ∈  Finset.range N, (1/2:ℝ) := by simp; ring
      _ = ∑ j  ∈  Finset.range N, e j := by
        apply Finset.sum_congr rfl
        intro j hj
        norm_num [e,Finset.mem_range.mp hj]
  have hq : HasSum (fun j => (e j)^2) ((N:ℝ)/4) := by
    have h : HasSum (fun j => (e j)^2) (∑ j  ∈  Finset.range N, (e j)^2) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by
        dsimp [e]; rw [if_neg (by simpa using hj)]; norm_num)
    convert h using 1
    calc
      (N:ℝ)/4 = ∑ _j  ∈  Finset.range N, (1/4:ℝ) := by simp; ring
      _ = ∑ j  ∈  Finset.range N, (e j)^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        norm_num [e,Finset.mem_range.mp hj]
  have hlo := signed_product_lower e d ((N:ℝ)/2) ((N:ℝ)/4) hu hp ht hq
  have hlo' : Real.exp (-(N:ℝ)) ≤ d := by convert hlo using 1 <;> ring
  refine ⟨N,e,d,(N:ℝ)/2,(N:ℝ)/4,hn,hl,hu,hp,ht,hq,rfl,rfl,?_,?_⟩
  · exact (Real.exp_pos _).trans_le hlo'
  · exact (Real.exp_lt_exp.mpr (by linarith : -c*(N:ℝ)^3 < -(N:ℝ))).trans_le hlo'

theorem cubic_counterinstance_all_binder_joint_probe :
    ∃ c : ℝ, 0<c ∧ ∃ N : ℕ, ∃ e : ℕ → ℝ, ∃ d t q : ℝ,
      0<N ∧ (∀ j, 0 ≤ e j) ∧ (∀ j, e j ≤ 1/2) ∧
      HasProd (fun j => 1-e j) d ∧ HasSum e t ∧
      HasSum (fun j => (e j)^2) q ∧ t=(N:ℝ)/2 ∧ q=(N:ℝ)/4 ∧
      0<d ∧ Real.exp (-c*(N:ℝ)^3)<d :=
  ⟨1,by norm_num,trace_interface_cubic_counterinstance 1 (by norm_num)⟩

noncomputable def traceTailThreshold (C : ℝ /- [definition] -/) : ℝ :=
  max 1 ((3/4)*Real.log ((9/4)*C^2))

lemma trace_small_at_threshold
    (C s : ℝ /- [definition] -/)
    (hC : 0<C /- [standing] -/)
    (hb : ∀ u : ℝ, 0 ≤ u → |airyAiReal u| ≤
      C*Real.exp (-(2/3*u^(3/2:ℝ))) /- [standing] -/)
    (hs : traceTailThreshold C ≤ s /- [standing] -/) :
    1 ≤ s ∧ airyTraceIntegral s ≤ 1/4 := by
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hslog : (3/4)*Real.log ((9/4)*C^2) ≤ s := (le_max_right _ _).trans hs
  have hr : s ≤ s^(3/2:ℝ) := by
    have h := rpow_three_halves_increment 1 s le_rfl hs1
    norm_num at h
    linarith
  have hp : 0<(9/4:ℝ)*C^2 := by positivity
  have he : -(4/3*s^(3/2:ℝ)) ≤ -Real.log ((9/4)*C^2) := by linarith
  refine ⟨hs1,(Airy_trace_upper_of_envelope C s hC hb hs1).trans ?_⟩
  calc
    (9/16*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))  ≤
        (9/16*C^2)*Real.exp (-Real.log ((9/4)*C^2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = 1/4 := by
      rw [Real.exp_neg,Real.exp_log hp]
      field_simp [hC.ne']
      <;> ring

/-- Fully quantitative two-sided right bounds at the literal physical determinants.
All constants are explicit multiples of one Airy-envelope witness;
the threshold is an explicit logarithm of that witness. -/
theorem TW_right_tail_bounds_of_envelope
    (C s : ℝ /- [definition] -/)
    (hC : 0<C /- [standing] -/)
    (hb : ∀ u : ℝ, 0 ≤ u → |airyAiReal u| ≤
      C*Real.exp (-(2/3*u^(3/2:ℝ))) /- [standing] -/)
    (hs : traceTailThreshold C ≤ s /- [standing] -/) :
    (1-Real.exp (-(lowerAiryEnvelope (s+1)/2)) ≤ 1-TW1R s ∧
      1-TW1R s ≤ (3/4*C)*Real.exp (-(2/3*s^(3/2:ℝ))) +
        (9/8*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))) ∧
    (1-Real.exp (-((lowerAiryEnvelope (s+2))^2)) ≤ 1-TW2R s ∧
      1-TW2R s ≤ (9/16*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))) := by
  obtain ⟨hs1,hq⟩ := trace_small_at_threshold C s hC hb hs
  have h1 := TW1R_right_tail_trace_bounds s hq
  have h2 := TW2R_right_tail_trace_bounds s
  have htu := hankel_trace_upper_of_envelope C s hC hb hs1
  have hqu := Airy_trace_upper_of_envelope C s hC hb hs1
  have htl := hankel_trace_lower_envelope s hs1
  have hql := Airy_trace_lower_envelope s hs1
  refine ⟨⟨?_,?_⟩,⟨?_,h2.2.trans hqu⟩⟩
  · have h := Real.exp_le_exp.mpr (neg_le_neg htl)
    linarith [h1.1]
  · linarith [h1.2]
  · have h := Real.exp_le_exp.mpr (neg_le_neg hql)
    linarith [h2.1]

/-- Unconditional family: the Airy witness is constructed by a result,
never taken from an assumed bundle or an unregistered import. -/
theorem TW_right_tail_bounds :
    ∃ C : ℝ, 0<C ∧ ∀ s : ℝ, traceTailThreshold C ≤ s →
    (1-Real.exp (-(lowerAiryEnvelope (s+1)/2)) ≤ 1-TW1R s ∧
      1-TW1R s ≤ (3/4*C)*Real.exp (-(2/3*s^(3/2:ℝ))) +
        (9/8*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))) ∧
    (1-Real.exp (-((lowerAiryEnvelope (s+2))^2)) ≤ 1-TW2R s ∧
      1-TW2R s ≤ (9/16*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_superexponential_bound
  exact ⟨C,hC,fun s hs => TW_right_tail_bounds_of_envelope C s hC hb hs⟩

/-- Every binder of the physical right-tail family holds jointly at a
nonzero actual Airy instance, including the same C and the trace-smallness floor. -/
theorem right_tail_all_binder_joint_probe :
    ∃ C s : ℝ, 0<C ∧ traceTailThreshold C ≤ s ∧ 1 ≤ s ∧ airyAiReal s  ≠  0 ∧
      (∀ u : ℝ, 0 ≤ u → |airyAiReal u| ≤ C*Real.exp (-(2/3*u^(3/2:ℝ)))) ∧
      0<airyTraceIntegral s ∧ airyTraceIntegral s ≤ 1/4 ∧
      0<hankelSignedTrace s ∧
      (1-Real.exp (-hankelSignedTrace s) ≤ 1-TW1R s ∧
        1-TW1R s ≤ hankelSignedTrace s+2*airyTraceIntegral s) ∧
      (1-Real.exp (-airyTraceIntegral s) ≤ 1-TW2R s ∧
        1-TW2R s ≤ airyTraceIntegral s) ∧
      (1-Real.exp (-(lowerAiryEnvelope (s+1)/2)) ≤ 1-TW1R s ∧
        1-TW1R s ≤ (3/4*C)*Real.exp (-(2/3*s^(3/2:ℝ))) +
          (9/8*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))) ∧
      (1-Real.exp (-((lowerAiryEnvelope (s+2))^2)) ≤ 1-TW2R s ∧
        1-TW2R s ≤ (9/16*C^2)*Real.exp (-(4/3*s^(3/2:ℝ)))) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_superexponential_bound
  let s := traceTailThreshold C
  obtain ⟨hs1,hq⟩ := trace_small_at_threshold C s hC hb le_rfl
  have hqp : 0<airyTraceIntegral s :=
    (sq_pos_of_pos (lowerAiryEnvelope_pos (s+2))).trans_le
      (Airy_trace_lower_envelope s hs1)
  have htp : 0<hankelSignedTrace s :=
    (div_pos (lowerAiryEnvelope_pos (s+1)) (by norm_num : (0:ℝ)<2)).trans_le
      (hankel_trace_lower_envelope s hs1)
  exact ⟨C,s,hC,le_rfl,hs1,(airyAiReal_pos_of_nonneg (by linarith)).ne',hb,hqp,hq,htp,
    TW1R_right_tail_trace_bounds s hq,TW2R_right_tail_trace_bounds s,
    TW_right_tail_bounds_of_envelope C s hC hb le_rfl⟩
end RMTFoundations.TracyWidom.Tails

#print axioms RMTFoundations.TracyWidom.Tails.finite_product_lower
#print axioms RMTFoundations.TracyWidom.Tails.positive_product_tail_bounds
#print axioms RMTFoundations.TracyWidom.Tails.exp_neg_linear_square_le_one_sub
#print axioms RMTFoundations.TracyWidom.Tails.signed_product_lower
#print axioms RMTFoundations.TracyWidom.Tails.signed_product_tail_bounds
#print axioms RMTFoundations.TracyWidom.Tails.scalar_tail_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Tails.rpow_three_halves_increment
#print axioms RMTFoundations.TracyWidom.Tails.shifted_Airy_envelope
#print axioms RMTFoundations.TracyWidom.Tails.halfline_exponential_integral
#print axioms RMTFoundations.TracyWidom.Tails.hankel_trace_upper_of_envelope
#print axioms RMTFoundations.TracyWidom.Tails.diagonal_upper_of_envelope
#print axioms RMTFoundations.TracyWidom.Tails.Airy_trace_upper_of_envelope
#print axioms RMTFoundations.TracyWidom.Tails.Airy_envelope_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Tails.lowerAiryConstant
#print axioms RMTFoundations.TracyWidom.Tails.lowerAiryRate
#print axioms RMTFoundations.TracyWidom.Tails.lowerAiryEnvelope
#print axioms RMTFoundations.TracyWidom.Tails.lowerAiryConstant_pos
#print axioms RMTFoundations.TracyWidom.Tails.lowerAiryRate_pos
#print axioms RMTFoundations.TracyWidom.Tails.lowerAiryEnvelope_pos
#print axioms RMTFoundations.TracyWidom.Tails.schlaefli_lower
#print axioms RMTFoundations.TracyWidom.Tails.Ai_lower_envelope
#print axioms RMTFoundations.TracyWidom.Tails.lowerAiryEnvelope_antitone_nonneg
#print axioms RMTFoundations.TracyWidom.Tails.hankel_trace_lower_envelope
#print axioms RMTFoundations.TracyWidom.Tails.diagonal_lower_envelope
#print axioms RMTFoundations.TracyWidom.Tails.Airy_trace_lower_envelope
#print axioms RMTFoundations.TracyWidom.Tails.lower_envelope_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Tails.TW2R_right_tail_trace_bounds
#print axioms RMTFoundations.TracyWidom.Tails.TW1R_right_tail_trace_bounds
#print axioms RMTFoundations.TracyWidom.Tails.TW2R_left_tail_linear
#print axioms RMTFoundations.TracyWidom.Tails.TW1R_left_tail_linear
#print axioms RMTFoundations.TracyWidom.Tails.left_tail_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Tails.signed_tail_cross_family_joint_probe
#print axioms RMTFoundations.TracyWidom.Tails.trace_interface_cubic_counterinstance
#print axioms RMTFoundations.TracyWidom.Tails.cubic_counterinstance_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Tails.traceTailThreshold
#print axioms RMTFoundations.TracyWidom.Tails.trace_small_at_threshold
#print axioms RMTFoundations.TracyWidom.Tails.TW_right_tail_bounds_of_envelope
#print axioms RMTFoundations.TracyWidom.Tails.TW_right_tail_bounds
#print axioms RMTFoundations.TracyWidom.Tails.right_tail_all_binder_joint_probe
