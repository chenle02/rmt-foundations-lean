import RMTFoundations.TracyWidom.HermiteFredholmLimit
import RMTFoundations.TracyWidom.Airy2LimitPhysical
import RMTFoundations.TracyWidom.Airy2OneTimeGap
import RMTFoundations.TracyWidom.AiryComparisonNondegenerate
import RMTFoundations.TracyWidom.HermitePerturbationObstruction
import RMTFoundations.TracyWidom.TW4TwoTails
set_option autoImplicit false
namespace Tests.TracyWidomAiry2Limits
open Set Filter MeasureTheory
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TracyWidom RMTFoundations.TracyWidom.HermiteFredholmLimit

/-- The actual Airy model realizes the one-time Fredholm limit and two genuine
GSE tail intervals simultaneously. No compact-interval density sign is asserted. -/
theorem physical_joint_probe :
    airyAiReal 0 ≠ 0 ∧
    Tendsto (fun n : ℕ => (kernelFredholm halfLineMeasure (scaledHermiteKernel n (-1)) (-1)).re)
      atTop (𝓝 (RMTFoundations.TracyWidom.TW2R (-1))) ∧
    (∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧
      StrictMonoOn TW4R (Iic a) ∧ StrictMonoOn TW4R (Ici b) ∧
      (∀ x, x ≤ a ∨ b ≤ x → 0 < TW4Slope x)) := by
  exact ⟨airyAiReal_zero_pos.ne',scaledHermiteKernel_gap_tendsto (-1),
    exists_TW4R_strictMono_two_tails⟩
end Tests.TracyWidomAiry2Limits

#print axioms Tests.TracyWidomAiry2Limits.physical_joint_probe
