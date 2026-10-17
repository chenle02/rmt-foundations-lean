import RMTFoundations.TracyWidom.DetFactor
import RMTFoundations.TracyWidom.LeftTail


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds RMTFoundations.TWLeftTail
noncomputable def plusPrimitiveBarrier (x : ℝ /- [definition] -/) : ℝ :=
  -(deriv airyAiReal x) / x - airyEnergyFull x / 2 + 1/(2*x)
lemma hasDerivAt_plusPrimitiveBarrier (x : ℝ /- [definition] -/)
    (hx : x < 0 /- [standing] -/) :
    HasDerivAt plusPrimitiveBarrier
      (-airyAiReal x - (deriv airyAiReal x - 1)^2/(2*x^2)) x := by
  have hx0 := hx.ne
  have hg : HasDerivAt (deriv airyAiReal) (x*airyAiReal x) x := by
    have he : deriv (deriv airyAiReal) x = x*airyAiReal x := by
      simpa [iteratedDeriv_succ,iteratedDeriv_one] using iteratedDeriv_two_airyAiReal x
    simpa [he] using (hasDerivAt_deriv_airyAiReal x).differentiableAt.hasDerivAt
  have hh := (hg.neg.div (hasDerivAt_id x) hx0).sub
    ((hasDerivAt_airyEnergyFull x hx).div_const 2)
  have hr := (hasDerivAt_const x (1:ℝ)).div
    ((hasDerivAt_id x).const_mul 2) (mul_ne_zero (by norm_num) hx0)
  have h := hh.add hr
  change HasDerivAt plusPrimitiveBarrier _ x at h
  have he : -airyAiReal x - (deriv airyAiReal x-1)^2/(2*x^2) =
      ((-x*airyAiReal x*x-(-deriv airyAiReal x)*1)/x^2-(deriv airyAiReal x)^2/x^2/2) +
      ((0*(2*x)-1*(2*1))/(2*x)^2) := by
    field_simp [hx0]
    ring
  rw [he]
  simpa only [id_eq, Pi.neg_apply, neg_mul] using h
lemma plusPrimitiveBarrier_upper (s : ℝ /- [definition] -/)
    (hs : s ≤ -1 /- [standing] -/) :
    plusPrimitiveBarrier s ≤ (airyEnergyFull (-1)+1)/2 := by
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
  have hb : -(deriv airyAiReal s) / s ≤ (airyEnergyFull (-1)+1)/2 := by
    rw [neg_div]
    nlinarith [sq_nonneg (deriv airyAiReal s / s + 1)]
  have hr : 1/(2*s) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
  dsimp [plusPrimitiveBarrier]
  linarith
lemma negAiry_negative_interval_lower (s : ℝ /- [definition] -/)
    (hs : s ≤ -1 /- [standing] -/) :
    plusPrimitiveBarrier (-1) - (airyEnergyFull (-1)+1)/2 ≤
      ∫ x in s..(-1:ℝ), -airyAiReal x := by
  let f' : ℝ → ℝ := fun x => -airyAiReal x - (deriv airyAiReal x-1)^2/(2*x^2)
  have hfc : ContinuousOn f' (Icc s (-1)) := by
    apply ContinuousOn.sub continuous_airyAiReal.neg.continuousOn
    apply ContinuousOn.div ((continuous_deriv_airyAiReal.sub continuous_const).pow 2).continuousOn
      (continuous_const.mul (continuous_id.pow 2)).continuousOn
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.2]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0)
  have hfi : IntervalIntegrable f' volume s (-1) := by
    apply hfc.intervalIntegrable_of_Icc hs
  have hAi : IntervalIntegrable (fun x => -airyAiReal x) volume s (-1) :=
    continuous_airyAiReal.neg.intervalIntegrable s (-1)
  have hftc : (∫ x in s..(-1:ℝ), f' x) = plusPrimitiveBarrier (-1)-plusPrimitiveBarrier s := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hfi
    intro x hx
    rw [uIcc_of_le hs] at hx
    exact hasDerivAt_plusPrimitiveBarrier x (by linarith [hx.2])
  have hm := intervalIntegral.integral_mono_on hs hfi hAi (fun x hx => by
    dsimp [f']
    exact sub_le_self _ (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg x))))
  rw [hftc] at hm
  linarith [plusPrimitiveBarrier_upper s hs]

noncomputable def signedTraceCeiling : ℝ :=
  (-plusPrimitiveBarrier (-1)+(airyEnergyFull (-1)+1)/2 +
    ∫ x in Ioi (-1:ℝ), airyAiReal x)/2

theorem hankelSignedTrace_upper
    (s : ℝ /- [definition] -/)
    (hs : s ≤ -1 /- [standing] -/) : hankelSignedTrace s ≤ signedTraceCeiling := by
  dsimp [hankelSignedTrace,signedTraceCeiling]
  rw [airy_Ioi_split s hs]
  have h := negAiry_negative_interval_lower s hs
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem plus_product_le_exp_trace_square
    {ι : Type* /- [definition] -/}
    (e : ι → ℝ /- [definition] -/)
    (d t q : ℝ /- [definition] -/)
    (hb : ∀ i, |e i| ≤ 1 /- [standing] -/)
    (hp : HasProd (fun i => 1+e i) d /- [standing] -/)
    (ht : HasSum e t /- [standing] -/)
    (hq : HasSum (fun i => (e i)^2) q /- [standing] -/) :
    d ≤ Real.exp (t-q/8) := by
  have hs : HasSum (fun i => e i-(e i)^2/8) (t-q/8) := ht.sub (hq.div_const 8)
  apply le_of_tendsto_of_tendsto hp hs.rexp
  apply Eventually.of_forall
  intro S
  apply Finset.prod_le_prod₀ (fun i _ => by have := (abs_le.mp (hb i)).1; linarith)
  intro i hi
  have h := one_sub_le_exp_quadratic (-e i)
    (by have := (abs_le.mp (hb i)).2; linarith)
    (by have := (abs_le.mp (hb i)).1; linarith)
  simpa using h

theorem hankelDetPlus_trace_square_bound
    (s : ℝ /- [definition] -/) :
    hankelDetPlus s ≤ Real.exp (hankelSignedTrace s-airyTraceIntegral s/8) := by
  obtain ⟨ι,hι,b,e,he,hk,ha,ha2,ht,hq,hp,_⟩ := airy_spectral_data s
  have hb : ∀ i, |e i| ≤ 1 := by
    intro i
    have hh := (airyHankelShift s).le_opNorm (b i)
    rw [he i,norm_smul,b.orthonormal.norm_eq_one i,mul_one] at hh
    simp only [mul_one] at hh
    exact hh.trans (norm_airyHankelShift_lt_one s).le
  apply plus_product_le_exp_trace_square e _ _ _ hb
    (by simpa [hankelDetPlus] using hp 1)
  · simpa [hankelSignedTrace,div_eq_mul_inv,mul_comm] using ht
  · exact hq

theorem hankelDetPlus_left_tail_linear
    (s : ℝ /- [definition] -/)
    (hs : s ≤ -1 /- [standing] -/) :
    hankelDetPlus s ≤ Real.exp (signedTraceCeiling-originMass*|s|/8) := by
  apply (hankelDetPlus_trace_square_bound s).trans
  apply Real.exp_le_exp.mpr
  have hl := airyTraceIntegral_linear_lower s (by linarith)
  have hu := hankelSignedTrace_upper s hs
  rw [abs_of_nonpos (by linarith : s ≤ 0)]
  nlinarith

theorem tendsto_hankelDetPlus_atBot : Tendsto hankelDetPlus atBot (𝓝 0) := by
  have he : Tendsto (fun s : ℝ => signedTraceCeiling+originMass*s/8) atBot atBot := by
    apply tendsto_atBot.2
    intro r
    filter_upwards [eventually_le_atBot (8*(r-signedTraceCeiling)/originMass)] with s hs
    have := (le_div_iff₀ originMass_pos).mp hs
    nlinarith
  apply squeeze_zero' (Eventually.of_forall (fun s => (hankelDetPlus_positive s).le))
    _ (Real.tendsto_exp_atBot.comp he)
  filter_upwards [eventually_le_atBot (-1:ℝ)] with s hs
  have h := hankelDetPlus_left_tail_linear s hs
  rw [abs_of_nonpos (by linarith : s ≤ 0)] at h
  change hankelDetPlus s ≤ Real.exp (signedTraceCeiling+originMass*s/8)
  rw [show signedTraceCeiling-originMass*(-s)/8 = signedTraceCeiling+originMass*s/8 by ring] at h
  exact h

/-- A nonzero actual Airy cutoff inhabits both trace bounds together. -/
theorem plus_left_tail_all_binder_joint_probe :
    ∃ s : ℝ, s ≤ -1 ∧ 0 < hankelDetPlus s ∧ 0 < originMass ∧
      hankelSignedTrace s ≤ signedTraceCeiling ∧
      hankelDetPlus s ≤ Real.exp (signedTraceCeiling-originMass*|s|/8) ∧
      Tendsto hankelDetPlus atBot (𝓝 0) :=
  ⟨-1,by norm_num,hankelDetPlus_positive _,originMass_pos,
    hankelSignedTrace_upper _ (by norm_num),
    hankelDetPlus_left_tail_linear _ (by norm_num),tendsto_hankelDetPlus_atBot⟩
theorem plus_product_all_binder_joint_probe :
    ∃ e : ℕ → ℝ, ∃ d t q : ℝ,
      e 0 = 1/2 ∧ 1 < d ∧ 0 < t ∧ 0 < q ∧
      (∀ i, |e i| ≤ 1) ∧ HasProd (fun i => 1+e i) d ∧
      HasSum e t ∧ HasSum (fun i => (e i)^2) q ∧
      d ≤ Real.exp (t-q/8) := by
  let e : ℕ → ℝ := fun i => if i=0 then 1/2 else 0
  have hb : ∀ i, |e i| ≤ 1 := by intro i; dsimp [e]; split_ifs <;> norm_num
  have hp : HasProd (fun i => 1+e i) (3/2) := by
    convert hasProd_ite_eq (0:ℕ) (3/2:ℝ) using 1
    funext i; dsimp [e]; split_ifs <;> norm_num
  have ht : HasSum e (1/2) := hasSum_ite_eq (0:ℕ) (1/2:ℝ)
  have hq : HasSum (fun i => (e i)^2) (1/4) := by
    convert hasSum_ite_eq (0:ℕ) (1/4:ℝ) using 1
    funext i; dsimp [e]; split_ifs <;> norm_num
  exact ⟨e,3/2,1/2,1/4,by simp [e],by norm_num,by norm_num,by norm_num,
    hb,hp,ht,hq,plus_product_le_exp_trace_square e _ _ _ hb hp ht hq⟩

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.plusPrimitiveBarrier
#print axioms RMTFoundations.TracyWidom.hasDerivAt_plusPrimitiveBarrier
#print axioms RMTFoundations.TracyWidom.plusPrimitiveBarrier_upper
#print axioms RMTFoundations.TracyWidom.negAiry_negative_interval_lower
#print axioms RMTFoundations.TracyWidom.signedTraceCeiling
#print axioms RMTFoundations.TracyWidom.hankelSignedTrace_upper
#print axioms RMTFoundations.TracyWidom.plus_product_le_exp_trace_square
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_trace_square_bound
#print axioms RMTFoundations.TracyWidom.hankelDetPlus_left_tail_linear
#print axioms RMTFoundations.TracyWidom.tendsto_hankelDetPlus_atBot
#print axioms RMTFoundations.TracyWidom.plus_left_tail_all_binder_joint_probe

#print axioms RMTFoundations.TracyWidom.plus_product_all_binder_joint_probe
