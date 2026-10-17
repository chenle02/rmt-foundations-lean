import Tests.TracyWidomHastingsMcLeod
import RMTFoundations.TracyWidom.TW1SharpRightTail
import RMTFoundations.TracyWidom.TW2RightTail
import RMTFoundations.TracyWidom.TW4Regularity
import RMTFoundations.TracyWidom.GUEDensity
import RMTFoundations.TracyWidom.AiryQuantitativeAsymptotics
set_option autoImplicit false
namespace Tests.TracyWidomSharpTails
open Filter MeasureTheory
open scoped Topology
open RMTFoundations.TracyWidom

/-- The actual nonzero canonical model realizes sharp tails, C1 TW4 and normalized finite GUE density jointly. -/
theorem sharp_tails_all_binder_joint_probe :
    Painleve.q ≠ 0 ∧ 0 < RMTFoundations.Airy.airyAiReal 1 ∧
    (∀ x : ℝ, 0 < x → |RMTFoundations.Airy.airyAiReal x /
      AiryQuantitativeAsymptotics.leading x-1| ≤ 5/(48*x^(3/2:ℝ))) ∧
    Tendsto (fun x : ℝ => (1-TW1R x)/
      (Real.exp (-(2/3:ℝ)*x^(3/2:ℝ))/(4*Real.sqrt Real.pi*x^(3/4:ℝ)))) atTop (𝓝 1) ∧
    Tendsto (fun x : ℝ => (1-TW2R x)/
      (Real.exp (-(4/3:ℝ)*x^(3/2:ℝ))/(16*Real.pi*x^(3/2:ℝ)))) atTop (𝓝 1) ∧
    ContDiff ℝ 1 TW4R ∧
    Integrable (GUEProjection.gueDensity 3) (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) ∧
    (∫ x : Fin 3 → ℝ, GUEProjection.gueDensity 3 x
      ∂Measure.pi (fun _ => (volume : Measure ℝ))) = 1 :=
  ⟨Tests.TracyWidomHastingsMcLeod.canonical_formulas_joint_probe.1,
    RMTFoundations.Airy.airyAiReal_pos_of_nonneg (by norm_num),
    AiryQuantitativeAsymptotics.airy_relative_error,
    TW1_rightTail_ratio_tendsto_one,TW2_rightTail_ratio_tendsto_one,
    TW4R_contDiff_one,GUEProjection.gue_density_integrable 3,GUEProjection.gue_density_integral 3⟩
end Tests.TracyWidomSharpTails

#print axioms Tests.TracyWidomSharpTails.sharp_tails_all_binder_joint_probe
