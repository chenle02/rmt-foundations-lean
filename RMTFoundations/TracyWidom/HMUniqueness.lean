import RMTFoundations.TracyWidom.HMGreenRepresentation
import RMTFoundations.TracyWidom.HMTailContraction
import RMTFoundations.TracyWidom.HMAirySmallness
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMUniqueness
open Set Filter MeasureTheory
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.HMGreenRepresentation
/-- Hastings--McLeod uniqueness among real classical global PII solutions
with relative Airy normalization at positive infinity. Auxiliary representations,
boundary limits, integrability, and contraction constants are all constructed. -/
theorem hastings_mcleod_unique
    (q r : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hr : Differentiable ℝ r /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hrr : ∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s /- [standing] -/)
    (hnq : Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    (hnr : Tendsto (fun s => r s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    : q = r := by
  obtain ⟨aq,haq,hQ⟩ := normalized_nested_green_representation q hq hqq hnq
  obtain ⟨ar,har,hR⟩ := normalized_nested_green_representation r hr hrr hnr
  obtain ⟨ac,hac,hC⟩ := RMTFoundations.TracyWidom.HMAirySmallness.eventually_airy_cubic_coefficient_small 2
  let a := max aq (max ar ac)
  have haq' : aq ≤ a := le_max_left _ _
  have har' : ar ≤ a := (le_max_left _ _).trans (le_max_right _ _)
  have hac' : ac ≤ a := (le_max_right _ _).trans (le_max_right _ _)
  have ha : 1 ≤ a := haq.trans haq'
  have hsmall : 3*(airyAiReal a)^2 < 1 := by
    have h := (hC a hac').2
    nlinarith [sq_nonneg (airyAiReal a)]
  have htail : EqOn q r (Ici a) := RMTFoundations.TracyWidom.HMTailContraction.nested_green_unique q r a ha
    (fun s hs => (hQ s (haq'.trans hs)).2.1)
    (fun s hs => (hR s (har'.trans hs)).2.1) hsmall
    (fun s hs => (hQ s (haq'.trans hs)).2.2.1)
    (fun s hs => (hR s (har'.trans hs)).2.2.1)
    (fun s hs => (hQ s (haq'.trans hs)).2.2.2.2.1)
    (fun s hs => (hR s (har'.trans hs)).2.2.2.2.1)
    (fun s hs => (hQ s (haq'.trans hs)).2.2.2.2.2)
    (fun s hs => (hR s (har'.trans hs)).2.2.2.2.2)
  exact RMTFoundations.TracyWidom.HMLinearODE.pii_tail_unique q r a hq hr hqq hrr
    (fun s hs => htail (Ioi_subset_Ici_self hs))
/-- The Fredholm endpoint coordinate is the Hastings--McLeod solution. -/
theorem normalized_classical_eq_fredholm
    (q : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hnq : Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    : q = RMTFoundations.TracyWidom.ResolventCoordinates.resolventQ := by
  rcases RMTFoundations.TracyWidom.CanonicalPainleveWitness.canonical_painleveII_classical_tracyWidom_witness with
    ⟨_,_,_,_,r,hreq,hr,_,_,_,_,hrr,hnr,_⟩
  exact (hastings_mcleod_unique q r hq hr hqq hrr hnq hnr).trans hreq
/-- Existence is furnished by the canonical Fredholm construction; uniqueness
is proved for arbitrary real classical normalized candidates. -/
theorem exists_unique_hastings_mcleod :
    ∃! q : ℝ → ℝ, Differentiable ℝ q ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) := by
  obtain ⟨q,_,hq,hqq,hnq,_,_⟩ := RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe
  refine ⟨q,⟨hq,hqq,hnq⟩,?_⟩
  intro r hr
  exact hastings_mcleod_unique r q hr.1 hq hr.2.1 hqq hr.2.2 hnq
/-- Literal application of every uniqueness binder to the same actual nonzero
canonical model, with the full asymptotic condition at infinity supplied by terms. -/
theorem uniqueness_all_binder_joint_probe :
    ∃ q r : ℝ → ℝ, q ≠ 0 ∧ r ≠ 0 ∧
      Differentiable ℝ q ∧ Differentiable ℝ r ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      (∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s) ∧
      Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) ∧
      Tendsto (fun s => r s/airyAiReal s) atTop (𝓝 1) ∧ q=r ∧
      q=RMTFoundations.TracyWidom.ResolventCoordinates.resolventQ := by
  obtain ⟨q,hn,hq,hqq,hnq,_,_⟩ := RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe
  exact ⟨q,q,hn,hn,hq,hq,hqq,hqq,hnq,hnq,
    hastings_mcleod_unique q q hq hq hqq hqq hnq hnq,
    normalized_classical_eq_fredholm q hq hqq hnq⟩
/-- The conditional contraction theorem's entire binder list is simultaneously
realized by a genuine nonzero classical normalized Fredholm model on an infinite tail. -/
theorem nested_contraction_all_binder_joint_probe :
    ∃ (q r : ℝ → ℝ) (a : ℝ), q ≠ 0 ∧ r ≠ 0 ∧
      Differentiable ℝ q ∧ Differentiable ℝ r ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      (∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s) ∧
      Tendsto (fun s => q s/airyAiReal s) atTop (𝓝 1) ∧
      Tendsto (fun s => r s/airyAiReal s) atTop (𝓝 1) ∧
      1 ≤ a ∧ (∀ s ≥ a, |q s/airyAiReal s| ≤ 2) ∧
      (∀ s ≥ a, |r s/airyAiReal s| ≤ 2) ∧ 3*(airyAiReal a)^2<1 ∧
      (∀ s ≥ a, IntegrableOn (fun u => 2*airyAiReal u*(q u)^3) (Ioi s)) ∧
      (∀ s ≥ a, IntegrableOn (fun u => 2*airyAiReal u*(r u)^3) (Ioi s)) ∧
      (∀ s ≥ a, IntegrableOn (fun t => (∫ u in Ioi t,2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) (Ioi s)) ∧
      (∀ s ≥ a, IntegrableOn (fun t => (∫ u in Ioi t,2*airyAiReal u*(r u)^3)/(airyAiReal t)^2) (Ioi s)) ∧
      (∀ s ≥ a, q s/airyAiReal s=1+∫ t in Ioi s,(∫ u in Ioi t,2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) ∧
      (∀ s ≥ a, r s/airyAiReal s=1+∫ t in Ioi s,(∫ u in Ioi t,2*airyAiReal u*(r u)^3)/(airyAiReal t)^2) ∧
      EqOn q r (Ici a) := by
  obtain ⟨q,hn,hq,hqq,hnq,_,_⟩ := RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe
  obtain ⟨aq,haq,hQ⟩ := normalized_nested_green_representation q hq hqq hnq
  obtain ⟨ac,hac,hC⟩ := RMTFoundations.TracyWidom.HMAirySmallness.eventually_airy_cubic_coefficient_small 2
  let a := max aq ac
  have hqa : aq ≤ a := le_max_left _ _
  have hca : ac ≤ a := le_max_right _ _
  have ha : 1 ≤ a := haq.trans hqa
  have hs : 3*(airyAiReal a)^2<1 := by
    have h := (hC a hca).2
    nlinarith [sq_nonneg (airyAiReal a)]
  have hb : ∀ s ≥ a, |q s/airyAiReal s| ≤ 2 := fun s hs => (hQ s (hqa.trans hs)).2.1
  have hi : ∀ s ≥ a, IntegrableOn (fun u => 2*airyAiReal u*(q u)^3) (Ioi s) :=
    fun s hs => (hQ s (hqa.trans hs)).2.2.1
  have ho : ∀ s ≥ a, IntegrableOn (fun t => (∫ u in Ioi t,2*airyAiReal u*(q u)^3)/(airyAiReal t)^2) (Ioi s) :=
    fun s hs => (hQ s (hqa.trans hs)).2.2.2.2.1
  have he : ∀ s ≥ a, q s/airyAiReal s=1+∫ t in Ioi s,(∫ u in Ioi t,2*airyAiReal u*(q u)^3)/(airyAiReal t)^2 :=
    fun s hs => (hQ s (hqa.trans hs)).2.2.2.2.2
  exact ⟨q,q,a,hn,hn,hq,hq,hqq,hqq,hnq,hnq,ha,hb,hb,hs,hi,hi,ho,ho,he,he,
    RMTFoundations.TracyWidom.HMTailContraction.nested_green_unique q q a ha hb hb hs hi hi ho ho he he⟩
end RMTFoundations.TracyWidom.HMUniqueness
#print axioms RMTFoundations.TracyWidom.HMUniqueness.hastings_mcleod_unique
#print axioms RMTFoundations.TracyWidom.HMUniqueness.normalized_classical_eq_fredholm
#print axioms RMTFoundations.TracyWidom.HMUniqueness.exists_unique_hastings_mcleod
#print axioms RMTFoundations.TracyWidom.HMUniqueness.uniqueness_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.HMUniqueness.nested_contraction_all_binder_joint_probe
