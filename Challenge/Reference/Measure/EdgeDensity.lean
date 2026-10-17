import Mathlib
namespace RMTFoundations.EdgeDensity
open Set
def EdgeDensityBounds (f : ℝ → ℝ /- [definition] -/ ) (Eplus t c C w : ℝ /- [definition] -/ ) : Prop :=
  ∀ x ∈ Ioo (Eplus - w) Eplus,
    c * (Eplus - x) ^ t ≤ f x ∧ f x ≤ C * (Eplus - x) ^ t
end RMTFoundations.EdgeDensity

#print axioms RMTFoundations.EdgeDensity.EdgeDensityBounds
