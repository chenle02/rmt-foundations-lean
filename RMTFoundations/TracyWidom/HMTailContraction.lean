import RMTFoundations.TracyWidom.HMVolterra
import RMTFoundations.TracyWidom.HMAiryEnvelope
import RMTFoundations.TracyWidom.HMAiryPowerTail
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMTailContraction
open Set MeasureTheory Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.HMAiryEnvelope RMTFoundations.TracyWidom.HMAiryPowerTail
/-- The normalized PII forcing difference is controlled by the true Airy fourth power. -/
theorem normalized_forcing_difference_bound
    (q r : ℝ → ℝ /- [definition] -/)
    (s D : ℝ /- [definition] -/)
    (hA : 0 < airyAiReal s /- [standing] -/)
    (hq : |q s/airyAiReal s| ≤ 2 /- [standing] -/)
    (hr : |r s/airyAiReal s| ≤ 2 /- [standing] -/)
    (hD : |q s/airyAiReal s-r s/airyAiReal s| ≤ D /- [standing] -/)
    : |2*airyAiReal s*(q s)^3-2*airyAiReal s*(r s)^3| ≤
      24*D*(airyAiReal s)^4 := by
  have heq : 2*airyAiReal s*(q s)^3-2*airyAiReal s*(r s)^3 =
      2*(airyAiReal s)^4*((q s/airyAiReal s)^3-(r s/airyAiReal s)^3) := by
    field_simp [hA.ne']
  rw [heq,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*(airyAiReal s)^4)]
  calc
    2*(airyAiReal s)^4*|(q s/airyAiReal s)^3-(r s/airyAiReal s)^3| ≤
      2*(airyAiReal s)^4*(3*(2:ℝ)^2*|q s/airyAiReal s-r s/airyAiReal s|) :=
      mul_le_mul_of_nonneg_left (RMTFoundations.TracyWidom.HMVolterra.cubic_lipschitz _ _ 2 hq hr) (by positivity)
    _ ≤ 2*(airyAiReal s)^4*(3*(2:ℝ)^2*D) := by gcongr
    _ = _ := by ring
/-- Opposite nonzero Airy values jointly instantiate every finite forcing binder. -/
theorem forcing_difference_joint_probe :
    0 < airyAiReal 1 ∧ |airyAiReal 1/airyAiReal 1| ≤ 2 ∧
      |(-airyAiReal 1)/airyAiReal 1| ≤ 2 ∧
      |airyAiReal 1/airyAiReal 1-(-airyAiReal 1)/airyAiReal 1| ≤ 2 ∧
      |2*airyAiReal 1*(airyAiReal 1)^3-2*airyAiReal 1*(-airyAiReal 1)^3| ≤
        24*(2:ℝ)*(airyAiReal 1)^4 := by
  have hA : 0 < airyAiReal 1 := airyAiReal_pos_of_nonneg (by norm_num)
  have hq : |airyAiReal 1/airyAiReal 1| ≤ 2 := by rw [div_self hA.ne'];norm_num
  have hr : |(-airyAiReal 1)/airyAiReal 1| ≤ 2 := by rw [neg_div,div_self hA.ne'];norm_num
  have hD : |airyAiReal 1/airyAiReal 1-(-airyAiReal 1)/airyAiReal 1| ≤ 2 := by
    rw [neg_div,div_self hA.ne'];norm_num
  exact ⟨hA,hq,hr,hD,normalized_forcing_difference_bound airyAiReal
    (fun s => -airyAiReal s) 1 2 hA hq hr hD⟩
/-- Conditional nested Volterra contraction. The main uniqueness theorem
constructs every representation and integrability input from classical PII. -/
theorem nested_green_unique
    (q r : ℝ → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (ha : 1 ≤ a /- [standing] -/)
    (hq : ∀ s ≥ a, |q s/airyAiReal s| ≤ 2 /- [standing] -/)
    (hr : ∀ s ≥ a, |r s/airyAiReal s| ≤ 2 /- [standing] -/)
    (hsmall : 3*(airyAiReal a)^2 < 1 /- [standing] -/)
    (hiQ : ∀ s ≥ a, IntegrableOn (fun u => 2*airyAiReal u*(q u)^3) (Ioi s) /- [standing] -/)
    (hiR : ∀ s ≥ a, IntegrableOn (fun u => 2*airyAiReal u*(r u)^3) (Ioi s) /- [standing] -/)
    (hoQ : ∀ s ≥ a, IntegrableOn (fun t => (∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) (Ioi s) /- [standing] -/)
    (hoR : ∀ s ≥ a, IntegrableOn (fun t => (∫ u in Ioi t, 2*airyAiReal u*(r u)^3)/(airyAiReal t)^2) (Ioi s) /- [standing] -/)
    (heQ : ∀ s ≥ a, q s/airyAiReal s = 1+∫ t in Ioi s, (∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2 /- [standing] -/)
    (heR : ∀ s ≥ a, r s/airyAiReal s = 1+∫ t in Ioi s, (∫ u in Ioi t, 2*airyAiReal u*(r u)^3)/(airyAiReal t)^2 /- [standing] -/)
    : EqOn q r (Ici a) := by
  let Q : ℝ → ℝ := fun s => q s/airyAiReal s
  let R : ℝ → ℝ := fun s => r s/airyAiReal s
  let S : Set ℝ := (fun s => |Q s-R s|) '' Ici a
  have hne : S.Nonempty := ⟨|Q a-R a|,mem_image_of_mem _ (mem_Ici.mpr le_rfl)⟩
  have hb : BddAbove S := by
    refine ⟨4,?_⟩
    rintro x ⟨s,hs,rfl⟩
    exact (abs_sub _ _).trans (by dsimp [Q,R];linarith [hq s hs,hr s hs])
  let D := sSup S
  have hD : 0 ≤ D := (abs_nonneg _).trans (le_csSup hb (mem_image_of_mem _ (mem_Ici.mpr le_rfl)))
  have hle : ∀ s ≥ a, |Q s-R s| ≤ D := fun s hs => le_csSup hb (mem_image_of_mem _ hs)
  have hinner : ∀ t ≥ a,
      |(∫ u in Ioi t, 2*airyAiReal u*(q u)^3)-(∫ u in Ioi t, 2*airyAiReal u*(r u)^3)| ≤
        6*D*(airyAiReal t)^4 := by
    intro t ht
    have hi := (hiQ t ht).sub (hiR t ht)
    have hmass := airy_fourth_tail_bound t (ha.trans ht)
    have hdom : ∀ᵐ u ∂volume.restrict (Ioi t),
      |2*airyAiReal u*(q u)^3-2*airyAiReal u*(r u)^3| ≤ 24*D*(airyAiReal u)^4 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : t < u := hu
      exact normalized_forcing_difference_bound q r u D
        (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ u))
        (hq u (ht.trans hu.le)) (hr u (ht.trans hu.le)) (hle u (ht.trans hu.le))
    calc
      |(∫ u in Ioi t, 2*airyAiReal u*(q u)^3)-(∫ u in Ioi t, 2*airyAiReal u*(r u)^3)| =
        |∫ u in Ioi t, 2*airyAiReal u*(q u)^3-2*airyAiReal u*(r u)^3| :=
          congrArg abs (integral_sub (hiQ t ht) (hiR t ht)).symm
      _ ≤ ∫ u in Ioi t, |2*airyAiReal u*(q u)^3-2*airyAiReal u*(r u)^3| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ u in Ioi t, 24*D*(airyAiReal u)^4 := integral_mono_ae hi.abs (hmass.1.const_mul _) hdom
      _ = 24*D*(∫ u in Ioi t, (airyAiReal u)^4) := integral_const_mul _ _
      _ ≤ 24*D*((airyAiReal t)^4/4) := mul_le_mul_of_nonneg_left hmass.2 (by positivity)
      _ = _ := by ring
  let F : ℝ → ℝ := fun t =>
    (∫ u in Ioi t, 2*airyAiReal u*(q u)^3)/(airyAiReal t)^2-
      (∫ u in Ioi t, 2*airyAiReal u*(r u)^3)/(airyAiReal t)^2
  have hstep : ∀ s ≥ a, |Q s-R s| ≤ 3*D*(airyAiReal a)^2 := by
    intro s hs
    have hAi : 0 < airyAiReal s := airyAiReal_pos_of_nonneg (by linarith)
    have hSq : IntegrableOn (fun t => (airyAiReal t)^2) (Ioi s) := integrable_airyAiReal_sq_Ioi s
    have hdom : ∀ᵐ t ∂volume.restrict (Ioi s), |F t| ≤ 6*D*(airyAiReal t)^2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : s < t := ht
      have hp : 0 < airyAiReal t := airyAiReal_pos_of_nonneg (by linarith)
      dsimp only [F]
      rw [← sub_div,abs_div,abs_of_nonneg (sq_nonneg (airyAiReal t))]
      calc
        |(∫ u in Ioi t, 2*airyAiReal u*(q u)^3)-(∫ u in Ioi t, 2*airyAiReal u*(r u)^3)|/(airyAiReal t)^2 ≤
          (6*D*(airyAiReal t)^4)/(airyAiReal t)^2 :=
            div_le_div_of_nonneg_right (hinner t (hs.trans ht.le)) (sq_nonneg _)
        _ = _ := by field_simp [hp.ne']
    have hi : IntegrableOn F (Ioi s) := (hoQ s hs).sub (hoR s hs)
    have heq : Q s-R s = ∫ t in Ioi s, F t := by
      dsimp only [Q,R]
      rw [heQ s hs,heR s hs,show (1:ℝ)+(∫ t in Ioi s,(∫ u in Ioi t,2*airyAiReal u*(q u)^3)/(airyAiReal t)^2)-
        (1+(∫ t in Ioi s,(∫ u in Ioi t,2*airyAiReal u*(r u)^3)/(airyAiReal t)^2)) =
        (∫ t in Ioi s,(∫ u in Ioi t,2*airyAiReal u*(q u)^3)/(airyAiReal t)^2)-
        (∫ t in Ioi s,(∫ u in Ioi t,2*airyAiReal u*(r u)^3)/(airyAiReal t)^2) by ring,
        ← integral_sub (hoQ s hs) (hoR s hs)]
    have henergy : (∫ t in Ioi s, (airyAiReal t)^2) ≤ (airyAiReal s)^2/2 := by
      have he := airyAiReal_sq_integral s
      have hb := airyEnergy_le_airyAi_sq_half s (ha.trans hs)
      -- The translated energy and the unshifted square tail are identical.
      have htr := RMTFoundations.TWOneBounds.integral_Ioi_translate (fun t => (airyAiReal t)^2) 0 s
      change (∫ u in Ioi 0, (airyAiReal (s+u))^2)=airyEnergy s at he
      have h0 : (∫ u in Ioi s, (airyAiReal u)^2)=airyEnergy s := by
        simpa only [zero_add,add_zero,add_comm] using htr.symm.trans (by simpa only [add_comm] using he)
      exact h0.le.trans hb
    have hAs : airyAiReal s ≤ airyAiReal a := by
      have he := airyAi_relative_exp_envelope a (s-a) ha (sub_nonneg.mpr hs)
      rw [show a+(s-a)=s by ring] at he
      exact he.trans (by
        have hex : Real.exp (-(s-a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        simpa using mul_le_mul_of_nonneg_left hex
          (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ a)).le)
    calc
      |Q s-R s| = |∫ t in Ioi s,F t| := congrArg abs heq
      _ ≤ ∫ t in Ioi s,|F t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioi s,6*D*(airyAiReal t)^2 := integral_mono_ae hi.abs (hSq.const_mul _) hdom
      _ = 6*D*(∫ t in Ioi s,(airyAiReal t)^2) := integral_const_mul _ _
      _ ≤ 6*D*((airyAiReal s)^2/2) := mul_le_mul_of_nonneg_left henergy (by positivity)
      _ ≤ 3*D*(airyAiReal a)^2 := by
        have hp := pow_le_pow_left₀ hAi.le hAs 2
        nlinarith [mul_le_mul_of_nonneg_left hp hD]
  have hsup : D ≤ 3*D*(airyAiReal a)^2 := by
    apply csSup_le hne
    rintro x ⟨s,hs,rfl⟩
    exact hstep s hs
  have hz : D=0 := by nlinarith
  intro s hs
  have hs' : a ≤ s := hs
  have hrel : Q s=R s := sub_eq_zero.mp (abs_eq_zero.mp
    (le_antisymm (by simpa only [hz] using hle s hs) (abs_nonneg _)))
  have hneA := (airyAiReal_pos_of_nonneg (by linarith : 0 ≤ s)).ne'
  have h := congrArg (fun x => x*airyAiReal s) hrel
  dsimp only [Q,R] at h
  simpa only [div_mul_cancel₀ _ hneA] using h
end RMTFoundations.TracyWidom.HMTailContraction
#print axioms RMTFoundations.TracyWidom.HMTailContraction.normalized_forcing_difference_bound
#print axioms RMTFoundations.TracyWidom.HMTailContraction.nested_green_unique
#print axioms RMTFoundations.TracyWidom.HMTailContraction.forcing_difference_joint_probe
