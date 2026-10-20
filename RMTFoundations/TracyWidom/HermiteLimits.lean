import RMTFoundations.TracyWidom.HermiteAiryCompact
import RMTFoundations.TracyWidom.HermiteAdjacentAmplitude
import RMTFoundations.TracyWidom.HermiteUniformTailMass
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteLimits
open scoped Topology
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeScale
open Real Set MeasureTheory Filter
open RMTFoundations.Airy RMTFoundations.TracyWidom.HermiteEdgeReduction
open RMTFoundations.TracyWidom.HermiteTailComparison
/-- Direct public export of HermiteAiryCompact.hermite_edge_locally_uniform with its unchanged hypotheses and conclusion. -/
theorem locally_uniform (R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x| ≤ R → |edgeMode (n+1) x-airyAiReal x| < ε :=
  HermiteAiryCompact.hermite_edge_locally_uniform R hR ε hε

/-- Direct public export of HermiteAdjacentAmplitude.adjacent_edge_tendsto with its unchanged hypotheses and conclusion. -/
theorem adjacent_tendsto (x : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => edgeAmplitude (n+2)*hermiteMode (n+1) (edgePoint (n+2) x))
      atTop (𝓝 (airyAiReal x)) :=
  HermiteAdjacentAmplitude.adjacent_edge_tendsto x

/-- Direct public export of HermiteUniformTail.uniform_halfline_tail with its unchanged hypotheses and conclusion. -/
theorem uniform_tail (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ y : ℝ, s ≤ y →
      |edgeMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) ∧
      |previousMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) :=
  HermiteUniformTail.uniform_halfline_tail s

/-- Direct public export of HermiteUniformTailMass.uniform_tail_masses with its unchanged hypotheses and conclusion. -/
theorem uniform_tail_masses (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ T : ℝ, s ≤ T →
      IntegrableOn (fun y => (edgeMode N y)^2) (Ioi T) ∧
      IntegrableOn (fun y => (previousMode N y)^2) (Ioi T) ∧
      (∫ y in Ioi T, (edgeMode N y)^2) ≤ C^2*exp (-(T-s)) ∧
      (∫ y in Ioi T, (previousMode N y)^2) ≤ C^2*exp (-(T-s)) :=
  HermiteUniformTailMass.uniform_tail_masses s

/-- Direct public export of HermiteUniformTailMass.uniform_adjacent_product with its unchanged hypotheses and conclusion. -/
theorem uniform_product (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ x y : ℝ, s ≤ x → s ≤ y →
      |edgeMode N x*previousMode N y| ≤
        C^2*exp (-(1/2:ℝ)*(x-s))*exp (-(1/2:ℝ)*(y-s)) :=
  HermiteUniformTailMass.uniform_adjacent_product s

end RMTFoundations.TracyWidom.HermiteLimits

#print axioms RMTFoundations.TracyWidom.HermiteLimits.locally_uniform
#print axioms RMTFoundations.TracyWidom.HermiteLimits.adjacent_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteLimits.uniform_tail
#print axioms RMTFoundations.TracyWidom.HermiteLimits.uniform_tail_masses
#print axioms RMTFoundations.TracyWidom.HermiteLimits.uniform_product
