import Challenge.Reference.Airy.Core
import Challenge.Reference.Airy.ODE
namespace RMTFoundations.Airy
/-- The concrete normalized Ai inhabits the original abstract ODE interface. -/
theorem airyAiReal_isAirySolution : IsAirySolution airyAiReal (deriv airyAiReal) :=
  ⟨hasDerivAt_airyAiReal', hasDerivAt_deriv_airyAiReal'⟩
/-- Nonzero Ai satisfies every ODE field jointly. -/
theorem airy_solution_inhabitation :
    IsAirySolution airyAiReal (deriv airyAiReal) ∧ 0 < airyAiReal 0 :=
  ⟨airyAiReal_isAirySolution, airyAiReal_pos_of_nonneg le_rfl⟩
end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.airyAiReal_isAirySolution
#print axioms RMTFoundations.Airy.airy_solution_inhabitation
