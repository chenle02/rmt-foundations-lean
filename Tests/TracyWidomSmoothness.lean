import RMTFoundations.TracyWidom.Smoothness
import RMTFoundations.TracyWidom.TW4SecondOrder
import RMTFoundations.TracyWidom.HMNontrivialJets
import RMTFoundations.TracyWidom.Airy2ProbabilityCore
import RMTFoundations.TracyWidom.HermiteEdgeNormalization
set_option autoImplicit false
namespace Tests.TracyWidomSmoothness
open scoped ContDiff
open RMTFoundations.TracyWidom

/-- The new analytic exports coexist with genuine positive densities and normalized finite GUE data. -/
theorem all_binder_joint_probe :
    (∀ s : ℝ, 0 < TW1Density s ∧ 0 < TW2Density s) ∧
    ContDiff ℝ ∞ TW1R ∧ ContDiff ℝ ∞ TW2R ∧
    ContDiff ℝ ∞ TW1Density ∧ ContDiff ℝ ∞ TW2Density ∧
    ContDiff ℝ 2 TW4R ∧
    (∃ q : ℝ → ℝ, q ≠ 0 ∧ ∀ s : ℝ, q s ≠ 0 ∨ deriv q s ≠ 0) ∧
    (∀ N : ℕ, 0 < HermiteEdgeNormalization.amplitude (N+1)) := by
  obtain ⟨q,hn,hq,hqq,ha,hjet⟩ := HMNontrivialJets.canonical_all_binder_joint_probe
  exact ⟨fun s => ⟨TW1Density_positive s,TW2Density_positive s⟩,
    Smoothness.cdfs.1,Smoothness.cdfs.2,Smoothness.densities.1,Smoothness.densities.2,
    TW4R_contDiff_two,⟨q,hn,hjet⟩,HermiteEdgeNormalization.amplitude_pos⟩
end Tests.TracyWidomSmoothness

#print axioms Tests.TracyWidomSmoothness.all_binder_joint_probe
