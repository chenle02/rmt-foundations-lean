import RMTFoundations.TracyWidom.TW4Hamiltonian
import RMTFoundations.TracyWidom.TW4RightGap
import RMTFoundations.TracyWidom.TWLogConcaveMidpoint
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.EndpointCalculus
open RMTFoundations.TracyWidom.HMGreenRepresentation RMTFoundations.TracyWidom.HMNormalization

/-- The actual endpoint is log-concave on any right ray with its genuine
positive endpoint and Hamiltonian-gap conditions. NON-ledger comparison. -/
theorem physical_endpoint_log_concave_on_ray
    (a : ℝ) -- [definition]
    (hq : ∀ t, a ≤ t → 0 < resolventQ t) -- [standing]
    (hgap : ∀ t, a ≤ t → (resolventQ t)^4 ≤ resolventU t) -- [standing]
    : ConcaveOn ℝ (Ici a) (fun t => Real.log (resolventQ t)) := by
  let r : ℝ → ℝ := fun t => deriv resolventQ t/resolventQ t
  have hr (t : ℝ) (ht : a ≤ t) : HasDerivAt r
      (((resolventQ t)^4-resolventU t)/(resolventQ t)^2) t :=
    endpoint_logarithmic_slope_hasDerivAt t (hq t ht).ne'
  have hrd : DifferentiableOn ℝ r (Ici a) :=
    fun t ht => (hr t ht).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn r (Ici a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici a) hrd.continuousOn
      (hrd.mono interior_subset)
    intro t ht
    have ht' : a ≤ t := interior_subset ht
    rw [(hr t ht').deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hgap t ht'))
      (sq_nonneg _)
  have hlog (t : ℝ) (ht : a ≤ t) :
      HasDerivAt (fun z => Real.log (resolventQ z)) (r t) t :=
    ((hasDerivAt_resolventQ t).differentiableAt.hasDerivAt).log (hq t ht).ne'
  have hld : DifferentiableOn ℝ (fun t => Real.log (resolventQ t)) (Ici a) :=
    fun t ht => (hlog t ht).differentiableAt.differentiableWithinAt
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici a) hld.continuousOn
    (hld.mono interior_subset)
  intro x hx y hy hxy
  have hx' : a ≤ x := interior_subset hx
  have hy' : a ≤ y := interior_subset hy
  rw [(hlog x hx').deriv,(hlog y hy').deriv]
  exact hanti hx' hy' hxy

/-- Both analytic conditions are supplied by physical theorems on a nonempty right tail. -/
theorem exists_physical_endpoint_log_concave_tail :
    ∃ a : ℝ, 0 ≤ a ∧
      (∀ t, a ≤ t → 0 < resolventQ t) ∧
      (∀ t, a ≤ t → (resolventQ t)^4 ≤ resolventU t) ∧
      ConcaveOn ℝ (Ici a) (fun t => Real.log (resolventQ t)) := by
  obtain ⟨b,_,hb⟩ := normalized_positive_tail resolventQ resolventQ_relative_Airy_atTop
  obtain ⟨c,hc⟩ := eventually_atTop.1 eventually_endpoint_fourth_lt_resolventU
  let a := max 0 (max b c)
  have haq (t : ℝ) (ht : a ≤ t) : 0 < resolventQ t :=
    (hb t ((le_max_left b c).trans ((le_max_right 0 (max b c)).trans ht))).1
  have hag (t : ℝ) (ht : a ≤ t) : (resolventQ t)^4 ≤ resolventU t :=
    (hc t ((le_max_right b c).trans ((le_max_right 0 (max b c)).trans ht))).le
  exact ⟨a,le_max_left _ _,haq,hag,physical_endpoint_log_concave_on_ray a haq hag⟩

/-- The actual endpoint satisfies the midpoint product bound on a whole right tail. -/
theorem exists_physical_endpoint_midpoint_tail :
    ∃ a : ℝ, 0 ≤ a ∧ (∀ t, a ≤ t → 0 < resolventQ t) ∧
      (∀ s, a ≤ s → ∀ x, 0 ≤ x →
        resolventQ s*resolventQ (x+x+s) ≤ (resolventQ (x+s))^2) := by
  obtain ⟨a,ha,hq,hgap,hconc⟩ := exists_physical_endpoint_log_concave_tail
  refine ⟨a,ha,hq,?_⟩
  intro s hs x hx
  exact log_concave_midpoint_product resolventQ s x
    (fun t ht => hq t (hs.trans ht)) (by
      refine ⟨convex_Ici s,?_⟩
      intro x hx y hy c d hc hd hcd
      exact hconc.2 (hs.trans hx) (hs.trans hy) hc hd hcd) hx

/-- All physical log-concavity and midpoint binders coexist on a single genuine
nonzero right ray. The ray conditions are proved, not assumed through a bundle. -/
theorem physical_log_concavity_all_binder_joint_probe :
    ∃ a s : ℝ, 0 ≤ a ∧ a ≤ s ∧ airyBoundaryVector s ≠ 0 ∧
      0 < resolventQ s ∧
      (∀ t, a ≤ t → 0 < resolventQ t) ∧
      (∀ t, a ≤ t → (resolventQ t)^4 ≤ resolventU t) ∧
      ConcaveOn ℝ (Ici a) (fun t => Real.log (resolventQ t)) ∧
      (∀ x, 0 ≤ x → resolventQ s*resolventQ (x+x+s) ≤ (resolventQ (x+s))^2) := by
  obtain ⟨a,ha,hq,hgap,hconc⟩ := exists_physical_endpoint_log_concave_tail
  exact ⟨a,a,ha,le_rfl,airyBoundaryVector_ne_zero a,hq a le_rfl,hq,hgap,hconc,
    fun x hx => log_concave_midpoint_product resolventQ a x hq hconc hx⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.physical_endpoint_log_concave_on_ray
#print axioms RMTFoundations.TracyWidom.exists_physical_endpoint_log_concave_tail
#print axioms RMTFoundations.TracyWidom.exists_physical_endpoint_midpoint_tail
#print axioms RMTFoundations.TracyWidom.physical_log_concavity_all_binder_joint_probe
