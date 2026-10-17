import RMTFoundations.TracyWidom.Painleve
import RMTFoundations.TracyWidom.Regularity
import RMTFoundations.TracyWidom.TailBounds
import RMTFoundations.TracyWidom.Spectrum
import RMTFoundations.TracyWidom.OperatorCore

set_option autoImplicit false
namespace Tests.TracyWidomExpansion
open RMTFoundations.TracyWidom

/-- The joint analytic APIs coexist on the same canonically defined Fredholm functions. -/
theorem expansion_api_probe :
    ContDiff ℝ 1 TW1R ∧ ContDiff ℝ 1 TW2R ∧ StrictMono TW1R ∧ StrictMono TW2R ∧
    (∀ s, 0 < TW1Density s) ∧ (∀ s, 0 < TW2Density s) ∧
    (∀ s, HasDerivAt (deriv Painleve.q) (s*Painleve.q s+2*(Painleve.q s)^3) s) ∧
    (∃! s, TW1R s = 1/2) ∧ (∃! s, TW2R s = 1/2) :=
  ⟨contDiff_TW1R,contDiff_TW2R,strictMono_TW1R,strictMono_TW2R,
    TW1Density_positive,TW2Density_positive,Painleve.hasDerivAt_deriv_q,
    TW1R_median_exists_unique,TW2R_median_exists_unique⟩
end Tests.TracyWidomExpansion

#print axioms Tests.TracyWidomExpansion.expansion_api_probe
