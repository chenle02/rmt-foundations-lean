import RMTFoundations.Airy.Damping
import RMTFoundations.TracyWidom.LeftTail
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter Asymptotics
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TWLeftTail
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable def tailModel (c p a x : ℝ /- [definition] -/) : ℝ :=
  c * x ^ p * Real.exp (-a * x ^ (3/2 : ℝ))
noncomputable def tailForce (c p a x : ℝ /- [definition] -/) : ℝ :=
  (3/2*a)*c*x^(p+1/2)*Real.exp (-a*x^(3/2 : ℝ))
noncomputable def tailCorrection (p a x : ℝ /- [definition] -/) : ℝ :=
  1 - (p/(3/2*a))*x^(-3/2 : ℝ)
theorem tailModel_hasDerivAt (c p a x : ℝ /- [definition] -/)
    (ha : a ≠ 0 /- [standing] -/) (hx : 0 < x /- [standing] -/) :
    HasDerivAt (tailModel c p a)
      (-(tailForce c p a x)*tailCorrection p a x) x := by
  have hpow := (hasDerivAt_id x).rpow_const (p := p) (Or.inl hx.ne')
  have hexp := (((hasDerivAt_id x).rpow_const (p := (3/2 : ℝ))
    (Or.inl hx.ne')).const_mul (-a)).exp
  have h := ((hpow.const_mul c).mul hexp)
  convert h using 1 <;> try rfl
  dsimp only [tailForce,tailCorrection,id_eq]
  rw [show (3/2 : ℝ)-1=1/2 by norm_num]
  have h1 : x^(p+1/2)*x^(-3/2:ℝ)=x^(p-1) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have h2 : x^p*x^(1/2:ℝ)=x^(p+1/2) := (Real.rpow_add hx _ _).symm
  rw [mul_sub, mul_one]
  have hn : (3/2*a:ℝ) ≠ 0 := mul_ne_zero (by norm_num) ha
  rw [← h1]
  field_simp
  ring_nf at h2 ⊢
  rw [← h2]
  ring
theorem tailModel_tendsto_zero (c p a : ℝ /- [definition] -/)
    (hp : p < 0 /- [standing] -/) (ha : 0 < a /- [standing] -/) :
    Tendsto (tailModel c p a) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x^p) atTop (𝓝 0) := by
    simpa using tendsto_rpow_neg_atTop (neg_pos.mpr hp)
  have he : Tendsto (fun x : ℝ => Real.exp (-a*x^(3/2 : ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_const_mul_atBot_of_neg (by linarith : -a < 0)).2
      (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/2))
  change Tendsto (fun x : ℝ => c*x^p*Real.exp (-a*x^(3/2:ℝ))) atTop (𝓝 0)
  convert (hpow.const_mul c).mul he using 1 <;> try rfl
  congr 1
  ring
theorem tailCorrection_tendsto (p a : ℝ /- [definition] -/) :
    Tendsto (tailCorrection p a) atTop (𝓝 1) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/2)).const_mul (p/(3/2*a))
  have ht := (tendsto_const_nhds (x := (1:ℝ))).sub h
  have heq : (1:ℝ) - p/(3/2*a)*0 = 1 := by ring
  rw [heq] at ht
  convert ht using 1 <;> try rfl
  funext x
  unfold tailCorrection
  rw [show (-3/2:ℝ)=-(3/2) by norm_num]
theorem primitive_isEquivalent_tailModel
    (F f : ℝ → ℝ /- [definition] -/) (c p a : ℝ /- [definition] -/)
    (hc : c ≠ 0 /- [standing] -/) (hp : p < 0 /- [standing] -/)
    (ha : 0 < a /- [standing] -/)
    (hd : ∀ᶠ x in atTop, HasDerivAt F (-f x) x /- [standing] -/)
    (hz : Tendsto F atTop (𝓝 0) /- [standing] -/)
    (hf : f ~[atTop] tailForce c p a /- [standing] -/) :
    F ~[atTop] tailModel c p a := by
  have hforce : ∀ᶠ x in atTop, tailForce c p a x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    dsimp [tailForce]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) ha.ne') hc) (Real.rpow_pos_of_pos hx _).ne')
      (Real.exp_pos _).ne'
  have hmodel : ∀ᶠ x in atTop, tailModel c p a x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    dsimp [tailModel]
    exact mul_ne_zero (mul_ne_zero hc (Real.rpow_pos_of_pos hx _).ne')
      (Real.exp_pos _).ne'
  have hratio := (isEquivalent_iff_tendsto_one hforce).mp hf
  have hcort := tailCorrection_tendsto p a
  have hcorne : ∀ᶠ x in atTop, tailCorrection p a x ≠ 0 :=
    hcort.eventually_ne (by norm_num : (1:ℝ) ≠ 0)
  have hderiv : ∀ᶠ x in atTop, HasDerivAt (tailModel c p a)
      (-(tailForce c p a x)*tailCorrection p a x) x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact tailModel_hasDerivAt c p a x ha.ne' hx
  have hderivne : ∀ᶠ x in atTop,
      -(tailForce c p a x)*tailCorrection p a x ≠ 0 := by
    filter_upwards [hforce,hcorne] with x hx hy
    exact mul_ne_zero (neg_ne_zero.mpr hx) hy
  have hdiv : Tendsto (fun x => (-f x) /
      (-(tailForce c p a x)*tailCorrection p a x)) atTop (𝓝 1) := by
    have ht := hratio.div hcort (by norm_num : (1:ℝ) ≠ 0)
    simp only [div_one] at ht
    convert ht using 1
    funext x
    simp [div_mul_eq_div_div,neg_div_neg_eq]
  exact (isEquivalent_iff_tendsto_one hmodel).mpr
    (HasDerivAt.lhopital_zero_atTop hd hderiv hderivne hz
      (tailModel_tendsto_zero c p a hp ha) hdiv)

theorem tail_integral_hasDerivAt (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (hi : ∀ a : ℝ, IntegrableOn f (Ioi a) /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    HasDerivAt (fun a : ℝ => ∫ u in Ioi a, f u) (-f x) x := by
  have heq : (fun a : ℝ => ∫ u in Ioi a, f u) =
      (fun a => (∫ u in Ioi x, f u) - ∫ u in x..a, f u) := by
    funext a
    have h := intervalIntegral.integral_interval_add_Ioi (hi x) (hi a)
    linarith
  rw [heq]
  convert (hasDerivAt_const x (∫ u in Ioi x, f u)).sub
      (hf.integral_hasStrictDerivAt x x).hasDerivAt using 1 <;> try rfl
  ring
open RMTFoundations.Airy RMTFoundations.TWLeftTail
theorem airyTraceIntegral_hasDerivAt (x : ℝ /- [definition] -/) :
    HasDerivAt airyTraceIntegral (-airyEnergy x) x := by
  unfold airyTraceIntegral
  rw [←diagonal_eq_energy x]
  exact tail_integral_hasDerivAt (fun x => airyKernelIntegral x x)
    diagonal_continuous diagonal_integrable x
theorem airyTraceIntegral_tendsto_atTop_zero :
    Tendsto airyTraceIntegral atTop (𝓝 0) := by
  exact tendsto_integral_Ioi_zero tendsto_id
theorem airy_sq_isEquivalent_force :
    (fun x : ℝ => (airyAiReal x)^2) ~[atTop]
      tailForce (1/(8*Real.pi)) (-1) (4/3) := by
  have h := airyAiReal_isEquivalent.mul airyAiReal_isEquivalent
  refine h.congr_left (Eventually.of_forall (fun x => by simp [pow_two])) |>.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  dsimp [tailForce]
  have hr : x^(-1/4:ℝ)*x^(-1/4:ℝ)=x^(-1/2:ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  have he : Real.exp (-(2/3)*x^(3/2:ℝ))*Real.exp (-(2/3)*x^(3/2:ℝ)) =
      Real.exp (-(4/3)*x^(3/2:ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  rw [show ((1/(2*Real.sqrt Real.pi))*x^(-1/4:ℝ)*Real.exp (-(2/3)*x^(3/2:ℝ))) *
      ((1/(2*Real.sqrt Real.pi))*x^(-1/4:ℝ)*Real.exp (-(2/3)*x^(3/2:ℝ))) =
      (1/(2*Real.sqrt Real.pi))^2 * (x^(-1/4:ℝ)*x^(-1/4:ℝ)) *
      (Real.exp (-(2/3)*x^(3/2:ℝ))*Real.exp (-(2/3)*x^(3/2:ℝ))) by ring, hr,he]
  have hc : (1/(2*Real.sqrt Real.pi))^2 = (2:ℝ)*(1/(8*Real.pi)) := by
    rw [div_pow,mul_pow,Real.sq_sqrt Real.pi_pos.le]
    norm_num <;> ring_nf <;> simp
  rw [hc]
  norm_num <;> ring_nf <;> simp
theorem airyEnergy_isEquivalent :
    airyEnergy ~[atTop] tailModel (1/(8*Real.pi)) (-1) (4/3) := by
  exact primitive_isEquivalent_tailModel airyEnergy (fun x => airyAiReal x^2)
    (1/(8*Real.pi)) (-1) (4/3) (by positivity) (by norm_num) (by norm_num)
    (Eventually.of_forall hasDerivAt_airyEnergy) airyEnergy_tendsto_zero
    airy_sq_isEquivalent_force
theorem airyTraceIntegral_isEquivalent :
    airyTraceIntegral ~[atTop] tailModel (1/(16*Real.pi)) (-3/2) (4/3) := by
  apply primitive_isEquivalent_tailModel airyTraceIntegral airyEnergy
    (1/(16*Real.pi)) (-3/2) (4/3) (by positivity) (by norm_num) (by norm_num)
    (Eventually.of_forall airyTraceIntegral_hasDerivAt) airyTraceIntegral_tendsto_atTop_zero
  refine airyEnergy_isEquivalent.trans_eventuallyEq ?_
  filter_upwards [] with x
  dsimp [tailModel,tailForce]
  rw [show (-3/2:ℝ)+1/2=-1 by norm_num]
  have hc : (3/2*(4/3:ℝ))*(1/(16*Real.pi))=1/(8*Real.pi) := by
    field_simp
    ring
  rw [hc]
theorem airy_integral_isEquivalent :
    (fun s : ℝ => ∫ x in Ioi s, airyAiReal x) ~[atTop]
      tailModel (1/(2*Real.sqrt Real.pi)) (-3/4) (2/3) := by
  apply primitive_isEquivalent_tailModel (fun s : ℝ => ∫ x in Ioi s, airyAiReal x)
    airyAiReal (1/(2*Real.sqrt Real.pi)) (-3/4) (2/3)
    (by positivity) (by norm_num) (by norm_num)
    (Eventually.of_forall (tail_integral_hasDerivAt airyAiReal continuous_airyAiReal
      airy_integrable_Ioi)) (tendsto_integral_Ioi_zero tendsto_id)
  refine airyAiReal_isEquivalent.trans_eventuallyEq ?_
  filter_upwards [] with x
  dsimp [tailForce]
  norm_num
theorem tailModel_div (c p a d q b x : ℝ /- [definition] -/)
    (hx : 0 < x /- [standing] -/) :
    tailModel c p a x / tailModel d q b x =
      tailModel (c/d) (p-q) (a-b) x := by
  unfold tailModel
  rw [mul_div_mul_comm, mul_div_mul_comm, ← Real.rpow_sub hx, ← Real.exp_sub]
  congr 2
  ring
theorem hankelSignedTrace_isEquivalent :
    hankelSignedTrace ~[atTop] tailModel (1/(4*Real.sqrt Real.pi)) (-3/4) (2/3) := by
  have h := airy_integral_isEquivalent.div (IsEquivalent.refl (u := fun _ : ℝ => (2:ℝ)))
  refine h.congr_left (Eventually.of_forall (fun x => rfl)) |>.trans_eventuallyEq ?_
  filter_upwards [] with x
  dsimp [tailModel]
  ring
theorem trace_div_signedTrace_tendsto_zero :
    Tendsto (fun x : ℝ => airyTraceIntegral x / hankelSignedTrace x) atTop (𝓝 0) := by
  have h := airyTraceIntegral_isEquivalent.div hankelSignedTrace_isEquivalent
  apply h.symm.tendsto_nhds
  have heq : (fun x : ℝ => tailModel (1/(16*Real.pi)) (-3/2) (4/3) x /
      tailModel (1/(4*Real.sqrt Real.pi)) (-3/4) (2/3) x) =ᶠ[atTop]
      tailModel ((1/(16*Real.pi))/(1/(4*Real.sqrt Real.pi))) (-3/4) (2/3) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [tailModel_div _ _ _ _ _ _ x hx]
    norm_num
  exact (tailModel_tendsto_zero _ (-3/4) (2/3) (by norm_num) (by norm_num)).congr' heq.symm
theorem sharp_airy_tail_all_binder_probe :
    airyAiReal 1 ≠ 0 ∧
    Continuous (fun x : ℝ => airyKernelIntegral x x) ∧
    (∀ s : ℝ, IntegrableOn (fun x : ℝ => airyKernelIntegral x x) (Ioi s)) ∧
    (1/(8*Real.pi) : ℝ) ≠ 0 ∧ (-1:ℝ) < 0 ∧ (0:ℝ) < 4/3 ∧
    (∀ x : ℝ, HasDerivAt airyEnergy (-(airyAiReal x)^2) x) ∧
    Tendsto airyEnergy atTop (𝓝 0) ∧
    ((fun x : ℝ => (airyAiReal x)^2) ~[atTop] tailForce (1/(8*Real.pi)) (-1) (4/3)) ∧
    (1/(16*Real.pi) : ℝ) ≠ 0 ∧ (-3/2:ℝ) < 0 ∧
    (∀ x : ℝ, HasDerivAt airyTraceIntegral (-airyEnergy x) x) ∧
    Tendsto airyTraceIntegral atTop (𝓝 0) ∧
    (airyEnergy ~[atTop] tailForce (1/(16*Real.pi)) (-3/2) (4/3)) ∧
    Continuous airyAiReal ∧ (∀ a : ℝ, IntegrableOn airyAiReal (Ioi a)) ∧
    (1/(2*Real.sqrt Real.pi) : ℝ) ≠ 0 ∧ (-3/4:ℝ) < 0 ∧ (0:ℝ) < 2/3 ∧
    (∀ x : ℝ, HasDerivAt (fun a : ℝ => ∫ u in Ioi a, airyAiReal u) (-airyAiReal x) x) ∧
    Tendsto (fun a : ℝ => ∫ u in Ioi a, airyAiReal u) atTop (𝓝 0) ∧
    (airyAiReal ~[atTop] tailForce (1/(2*Real.sqrt Real.pi)) (-3/4) (2/3)) := by
  have he : airyEnergy ~[atTop] tailForce (1/(16*Real.pi)) (-3/2) (4/3) := by
    refine airyEnergy_isEquivalent.trans_eventuallyEq ?_
    filter_upwards [] with x
    dsimp [tailModel,tailForce]
    rw [show (-3/2:ℝ)+1/2=-1 by norm_num]
    have hc : (3/2*(4/3:ℝ))*(1/(16*Real.pi))=1/(8*Real.pi) := by
      field_simp
      ring
    rw [hc]
  have ha : airyAiReal ~[atTop] tailForce (1/(2*Real.sqrt Real.pi)) (-3/4) (2/3) := by
    refine airyAiReal_isEquivalent.trans_eventuallyEq ?_
    filter_upwards [] with x
    dsimp [tailForce]
    norm_num
  exact ⟨(airyAiReal_pos (by norm_num : (0:ℝ)<1)).ne', diagonal_continuous,
    diagonal_integrable, by positivity, by norm_num,
    by norm_num, hasDerivAt_airyEnergy, airyEnergy_tendsto_zero, airy_sq_isEquivalent_force,
    by positivity, by norm_num, airyTraceIntegral_hasDerivAt, airyTraceIntegral_tendsto_atTop_zero,
    he, continuous_airyAiReal, airy_integrable_Ioi, by positivity, by norm_num, by norm_num,
    tail_integral_hasDerivAt airyAiReal continuous_airyAiReal airy_integrable_Ioi,
    tendsto_integral_Ioi_zero tendsto_id, ha⟩
theorem primitive_model_all_binder_probe :
    ∃ (c p a : ℝ) (F f : ℝ → ℝ) (x : ℝ),
      c ≠ 0 ∧ p < 0 ∧ 0 < a ∧ a ≠ 0 ∧ 0 < x ∧ F x ≠ 0 ∧
      (∀ᶠ t in atTop, HasDerivAt F (-f t) t) ∧
      Tendsto F atTop (𝓝 0) ∧ (f ~[atTop] tailForce c p a) ∧
      (F ~[atTop] tailModel c p a) := by
  let F : ℝ → ℝ := tailModel 1 (-1) 1
  let f : ℝ → ℝ := fun x => tailForce 1 (-1) 1 x * tailCorrection (-1) 1 x
  have hd : ∀ᶠ x in atTop, HasDerivAt F (-f x) x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    convert tailModel_hasDerivAt 1 (-1) 1 x (by norm_num) hx using 1 <;> try rfl
    dsimp [f]
    ring
  have hf : f ~[atTop] tailForce 1 (-1) 1 := by
    have hcor : tailCorrection (-1) 1 ~[atTop] (fun _ : ℝ => (1:ℝ)) :=
      (isEquivalent_const_iff_tendsto (by norm_num : (1:ℝ) ≠ 0)).mpr
        (tailCorrection_tendsto (-1) 1)
    have h := (IsEquivalent.refl (u := tailForce 1 (-1) 1)).mul hcor
    convert h using 1 <;> try rfl
    all_goals
      funext x
      dsimp [f]
      ring
  have hz : Tendsto F atTop (𝓝 0) :=
    tailModel_tendsto_zero 1 (-1) 1 (by norm_num) (by norm_num)
  refine ⟨1,-1,1,F,f,1,by norm_num,by norm_num,by norm_num,by norm_num,
    by norm_num,?_,hd,hz,hf,?_⟩
  · dsimp [F,tailModel]
    positivity
  · exact primitive_isEquivalent_tailModel F f 1 (-1) 1
      (by norm_num) (by norm_num) (by norm_num) hd hz hf
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.tailModel
#print axioms RMTFoundations.TracyWidom.tailForce
#print axioms RMTFoundations.TracyWidom.tailCorrection
#print axioms RMTFoundations.TracyWidom.tailModel_hasDerivAt
#print axioms RMTFoundations.TracyWidom.tailModel_tendsto_zero
#print axioms RMTFoundations.TracyWidom.tailCorrection_tendsto
#print axioms RMTFoundations.TracyWidom.primitive_isEquivalent_tailModel
#print axioms RMTFoundations.TracyWidom.tail_integral_hasDerivAt
#print axioms RMTFoundations.TracyWidom.airyTraceIntegral_hasDerivAt
#print axioms RMTFoundations.TracyWidom.airyTraceIntegral_tendsto_atTop_zero
#print axioms RMTFoundations.TracyWidom.airy_sq_isEquivalent_force
#print axioms RMTFoundations.TracyWidom.airyEnergy_isEquivalent
#print axioms RMTFoundations.TracyWidom.airyTraceIntegral_isEquivalent
#print axioms RMTFoundations.TracyWidom.airy_integral_isEquivalent
#print axioms RMTFoundations.TracyWidom.tailModel_div
#print axioms RMTFoundations.TracyWidom.hankelSignedTrace_isEquivalent
#print axioms RMTFoundations.TracyWidom.trace_div_signedTrace_tendsto_zero
#print axioms RMTFoundations.TracyWidom.sharp_airy_tail_all_binder_probe
#print axioms RMTFoundations.TracyWidom.primitive_model_all_binder_probe
