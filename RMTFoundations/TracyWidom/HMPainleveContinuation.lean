import RMTFoundations.TracyWidom.CanonicalPainleveWitness
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMLinearODE
open Set Filter
open scoped NNReal Topology
/-- The first-order linearized second-order field has a uniform Lipschitz bound. -/
theorem linear_field_lipschitz (c M : ℝ /- [definition] -/)
    (hc : |c| ≤ M /- [standing] -/)
    : LipschitzWith ⟨max 1 M,le_max_of_le_left (by norm_num)⟩
      (fun z : ℝ × ℝ => (z.2,c*z.1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Prod.dist_eq,Real.dist_eq]
  have hm : 0 ≤ M := (abs_nonneg c).trans hc
  have hd : |x.1-y.1| ≤ max |x.1-y.1| |x.2-y.2| := le_max_left _ _
  have he : |x.2-y.2| ≤ max |x.1-y.1| |x.2-y.2| := le_max_right _ _
  change max |x.2-y.2| |c*x.1-c*y.1| ≤ max 1 M * max |x.1-y.1| |x.2-y.2|
  rw [max_le_iff]
  constructor
  · calc
      |x.2-y.2| ≤ 1 * max |x.1-y.1| |x.2-y.2| := by simpa only [one_mul] using he
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (le_trans (abs_nonneg _) hd)
  · rw [show c*x.1-c*y.1=c*(x.1-y.1) by ring,abs_mul]
    exact mul_le_mul (hc.trans (le_max_right _ _)) hd (abs_nonneg _) (le_trans (by norm_num) (le_max_left _ _))
/-- Any continuous coefficient is uniformly bounded on a compact time interval. -/
theorem coefficient_bounded (c : ℝ → ℝ /- [definition] -/)
    (a b : ℝ /- [definition] -/)
    (hc : Continuous c /- [standing] -/)
    : ∃ M : ℝ, ∀ t ∈ Icc a b, |c t| ≤ M := by
  rcases isCompact_Icc.bddAbove_image hc.abs.continuousOn with ⟨M,hM⟩
  exact ⟨M,fun t ht => hM (mem_image_of_mem _ ht)⟩

/-- Global initial-value uniqueness for the cubic Painleve II equation.
The classical first derivative is explicit; no existence is assumed. -/
theorem pii_initial_value_unique
    (q r : ℝ → ℝ /- [definition] -/)
    (s₀ : ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hr : Differentiable ℝ r /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hrr : ∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s /- [standing] -/)
    (hval : q s₀ = r s₀ /- [standing] -/)
    (hder : deriv q s₀ = deriv r s₀ /- [standing] -/)
    : q = r := by
  let c : ℝ → ℝ := fun s => s+2*((q s)^2+q s*r s+(r s)^2)
  have hqc := hq.continuous
  have hrc := hr.continuous
  have hc : Continuous c := by dsimp [c]; fun_prop
  let z : ℝ → ℝ × ℝ := fun s => (q s-r s,deriv q s-deriv r s)
  have hzc : Continuous z := by
    have hdq : Continuous (deriv q) := continuous_iff_continuousAt.mpr (fun s => (hqq s).continuousAt)
    have hdr : Continuous (deriv r) := continuous_iff_continuousAt.mpr (fun s => (hrr s).continuousAt)
    exact (hq.continuous.sub hr.continuous).prodMk (hdq.sub hdr)
  have hzd : ∀ s, HasDerivAt z ((z s).2,c s*(z s).1) s := by
    intro s
    change HasDerivAt (fun t => (q t-r t,deriv q t-deriv r t))
      (deriv q s-deriv r s,c s*(q s-r s)) s
    rw [show c s*(q s-r s)=(s*q s+2*(q s)^3)-(s*r s+2*(r s)^3) by dsimp [c];ring]
    exact ((hq s).hasDerivAt.sub (hr s).hasDerivAt).prodMk ((hqq s).sub (hrr s))
  have hz₀ : z s₀ = 0 := by simp [z,hval,hder]
  funext t
  let a := min s₀ t-1
  let b := max s₀ t+1
  have ht₀ : s₀ ∈ Ioo a b := by
    constructor
    · dsimp [a]; linarith [min_le_left s₀ t]
    · dsimp [b]; linarith [le_max_left s₀ t]
  have ht : t ∈ Icc a b := by
    constructor
    · dsimp [a]; linarith [min_le_right s₀ t]
    · dsimp [b]; linarith [le_max_right s₀ t]
  obtain ⟨M,hM⟩ := coefficient_bounded c a b hc
  let K : ℝ≥0 := ⟨max 1 M,le_max_of_le_left (by norm_num)⟩
  have heq : EqOn z (fun _ => (0:ℝ × ℝ)) (Icc a b) :=
    ODE_solution_unique_of_mem_Icc
      (v := fun s (x : ℝ × ℝ) => (x.2,c s*x.1))
      (s := fun _ => Set.univ) (K := K)
      (fun s hs => (linear_field_lipschitz (c s) M (hM s (Ioo_subset_Icc_self hs))).lipschitzOnWith)
      ht₀ hzc.continuousOn (fun s _ => hzd s) (fun _ _ => mem_univ _)
      continuous_const.continuousOn
      (fun s _ => by
        simp only [Prod.fst_zero,Prod.snd_zero,mul_zero]
        change HasDerivAt (fun _ : ℝ => (0:ℝ × ℝ)) (0:ℝ × ℝ) s
        exact hasDerivAt_const s (0:ℝ × ℝ))
      (fun _ _ => mem_univ _) hz₀
  have := congrArg Prod.fst (heq ht)
  change q t-r t=0 at this
  exact sub_eq_zero.mp this

/-- Equality on any open tail supplies equal initial jets and hence global equality. -/
theorem pii_tail_unique
    (q r : ℝ → ℝ /- [definition] -/)
    (a : ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hr : Differentiable ℝ r /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hrr : ∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s /- [standing] -/)
    (htail : EqOn q r (Ioi a) /- [standing] -/)
    : q = r := by
  have hmem : a+1 ∈ Ioi a := by simp
  have hnear : q =ᶠ[𝓝 (a+1)] r := by
    filter_upwards [Ioi_mem_nhds (show a<a+1 by linarith)] with t ht
    exact htail ht
  exact pii_initial_value_unique q r (a+1) hq hr hqq hrr
    (htail hmem) hnear.deriv_eq

/-- The global hypotheses hold together on the Airy-normalized Fredholm
coordinate, whose nonzero value follows from its limit. -/
theorem pii_global_all_binder_joint_probe :
    ∃ q : ℝ → ℝ,
      q ≠ 0 ∧ Differentiable ℝ q ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) ∧
      (∀ r : ℝ → ℝ, Differentiable ℝ r →
        (∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s) →
        q 0=r 0 → deriv q 0=deriv r 0 → q=r) ∧
      (∀ r : ℝ → ℝ, Differentiable ℝ r →
        (∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s) →
        EqOn q r (Ioi 0) → q=r) := by
  rcases RMTFoundations.TracyWidom.CanonicalPainleveWitness.canonical_painleveII_classical_tracyWidom_witness with
    ⟨_,_,_,_,q,_,hq,_,_,_,_,hode,hasym,_⟩
  have hn : q ≠ 0 := by
    intro he
    have hz : Tendsto (fun s : ℝ => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 0) := by
      simp only [he,Pi.zero_apply,zero_div]
      exact tendsto_const_nhds
    have heq : (0:ℝ)=1 := tendsto_nhds_unique hz hasym
    norm_num at heq
  refine ⟨q,hn,hq,hode,hasym,?_,?_⟩
  · intro r hr hr2 hv hd
    exact pii_initial_value_unique q r 0 hq hr hode hr2 hv hd
  · intro r hr hr2 ht
    exact pii_tail_unique q r 0 hq hr hode hr2 ht
/-- Literal application of every initial-value binder by terms on the same
nonzero classical global Fredholm witness. -/
theorem canonical_initial_jet_joint_probe :
    ∃ q r : ℝ → ℝ, q ≠ 0 ∧ r ≠ 0 ∧
      Differentiable ℝ q ∧ Differentiable ℝ r ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      (∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s) ∧
      q 0=r 0 ∧ deriv q 0=deriv r 0 ∧ EqOn q r (Ioi 0) ∧ q=r := by
  obtain ⟨q,hn,hq,hode,_,_,_⟩ := pii_global_all_binder_joint_probe
  refine ⟨q,q,hn,hn,hq,hq,hode,hode,rfl,rfl,fun _ _ => rfl,?_⟩
  exact pii_initial_value_unique q q 0 hq hq hode hode rfl rfl
/-- Literal tail-to-global application, with all asymptotic model fields
inhabited by the same nonzero canonical witness. -/
theorem canonical_tail_joint_probe :
    ∃ q r : ℝ → ℝ, q ≠ 0 ∧ r ≠ 0 ∧
      Differentiable ℝ q ∧ Differentiable ℝ r ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      (∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s) ∧
      EqOn q r (Ioi 0) ∧ q=r := by
  obtain ⟨q,hn,hq,hode,_,_,_⟩ := pii_global_all_binder_joint_probe
  refine ⟨q,q,hn,hn,hq,hq,hode,hode,fun _ _ => rfl,?_⟩
  exact pii_tail_unique q q 0 hq hq hode hode (fun _ _ => rfl)
end RMTFoundations.TracyWidom.HMLinearODE
#print axioms RMTFoundations.TracyWidom.HMLinearODE.linear_field_lipschitz
#print axioms RMTFoundations.TracyWidom.HMLinearODE.coefficient_bounded
#print axioms RMTFoundations.TracyWidom.HMLinearODE.pii_initial_value_unique
#print axioms RMTFoundations.TracyWidom.HMLinearODE.pii_tail_unique
#print axioms RMTFoundations.TracyWidom.HMLinearODE.pii_global_all_binder_joint_probe

#print axioms RMTFoundations.TracyWidom.HMLinearODE.canonical_initial_jet_joint_probe
#print axioms RMTFoundations.TracyWidom.HMLinearODE.canonical_tail_joint_probe
