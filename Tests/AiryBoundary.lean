import RMTFoundations.Airy.Kernel
import RMTFoundations.Airy.ComplexRestriction
import Tests.AiryLegacy.Solution

/-!
# Airy kernel boundary fixtures

The legacy series construction is imported only as a test witness: it supplies
actual nonzero ODE solutions, rather than merely postulating satisfiable initial data.
The polynomial examples below test the unconditional algebraic contracts; they are
explicitly not presented as Airy solutions.


-/

open Filter
open scoped Topology
open RMTFoundations.Airy

namespace AiryBoundary

theorem completed_diagonal :
    solutionKernel (airySol 0 1) (airySolDeriv 0 1) 0 0 = 1 := by
  simp [solutionKernel_self, airySol_zero_eq, airySolDeriv_zero_eq]

theorem raw_diagonal :
    kernelQuotient (airySol 0 1) (airySolDeriv 0 1) 0 0 = 0 := by
  simp [kernelQuotient]

theorem completed_ne_raw :
    solutionKernel (airySol 0 1) (airySolDeriv 0 1) 0 0 ≠
      kernelQuotient (airySol 0 1) (airySolDeriv 0 1) 0 0 := by
  rw [completed_diagonal, raw_diagonal]
  norm_num

theorem nonzero_solution_continuity (x : ℝ /- [definition] -/ ) :
    Continuous (solutionKernel (airySol 0 1) (airySolDeriv 0 1) x) :=
  continuous_solutionKernel (isAirySolution_airySol 0 1) x

theorem nonzero_solution_diagonal_limit :
    Tendsto (kernelQuotient (airySol 0 1) (airySolDeriv 0 1) 0)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  simpa [airySol_zero_eq, airySolDeriv_zero_eq] using
    tendsto_kernelQuotient_diagonal (isAirySolution_airySol 0 1) 0

/-- A genuine second presentation of the same nonzero solution exercises uniqueness. -/
theorem nonzero_solution_uniqueness :
    airySol 0 1 = fun x => airySol 1 1 x - airySol 1 0 x := by
  apply airySolution_unique (isAirySolution_airySol 0 1)
    (airySolution_sub (isAirySolution_airySol 1 1)
      (isAirySolution_airySol 1 0)) (t₀ := 0)
  · simp [airySol_zero_eq]
  · simp [airySolDeriv_zero_eq]

/-- A nonzero Wronskian rules out an unconditional mixed-diagonal cancellation. -/
theorem fundamental_wronskian (x : ℝ /- [definition] -/ ) :
    airySol 1 0 x * airySolDeriv 0 1 x -
      airySolDeriv 1 0 x * airySol 0 1 x = 1 := by
  have h := mixed_numerator_diagonal
    (isAirySolution_airySol 1 0) (isAirySolution_airySol 0 1) x
  simpa [airySol_zero_eq, airySolDeriv_zero_eq] using h

theorem fundamental_wronskian_ne_zero (x : ℝ /- [definition] -/ ) :
    airySol 1 0 x * airySolDeriv 0 1 x -
      airySolDeriv 1 0 x * airySol 0 1 x ≠ 0 := by
  rw [fundamental_wronskian]
  norm_num

/-- Algebraic sign control: the supplied second function is not the derivative. -/
theorem signed_quotient :
    kernelQuotient (fun t : ℝ => t) (fun t => t ^ 2) 1 2 = -2 := by
  norm_num [kernelQuotient]

/-- Scaling a pair by two detects a missing polarization factor of one half. -/
theorem signed_polarization :
    polarizedKernel (fun t : ℝ => t) (fun t => t ^ 2)
      (fun t => 2 * t) (fun t => 2 * t ^ 2) 1 2 = -4 := by
  norm_num [polarizedKernel, solutionKernel, kernelQuotient]

/-- This pair has the correct first derivative, but fails the Airy equation. -/
theorem linear_pair_not_airy :
    ¬ IsAirySolution (fun t : ℝ => t) (fun _ => (1 : ℝ)) := by
  intro h
  have heq := (h.hasDerivAt_right 1).unique (hasDerivAt_const (1 : ℝ) (1 : ℝ))
  norm_num at heq

theorem linear_pair_diagonal :
    solutionKernel (fun t : ℝ => t) (fun _ => (1 : ℝ)) 2 2 = -7 := by
  norm_num [solutionKernel]

theorem linear_pair_off_diagonal {y : ℝ /- [definition] -/ } (hy : y ≠ 2 /- [standing] -/ ) :
    solutionKernel (fun t : ℝ => t) (fun _ => (1 : ℝ)) 2 y = 1 := by
  rw [solutionKernel_of_ne _ _ hy.symm]
  simp only [kernelQuotient, mul_one, one_mul]
  exact div_self (sub_ne_zero.mpr hy.symm)

/-- The ODE hypothesis cannot be dropped from the continuity theorem. -/
theorem linear_pair_not_continuousAt :
    ¬ ContinuousAt (solutionKernel (fun t : ℝ => t) (fun _ => (1 : ℝ)) 2) 2 := by
  intro hc
  have hlim : Tendsto
      (solutionKernel (fun t : ℝ => t) (fun _ => (1 : ℝ)) 2)
      (nhdsWithin 2 {2}ᶜ) (nhds (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (linear_pair_off_diagonal hy).symm
  have heq := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hlim
  rw [linear_pair_diagonal] at heq
  norm_num at heq

end AiryBoundary

#print axioms AiryBoundary.completed_diagonal
#print axioms AiryBoundary.raw_diagonal
#print axioms AiryBoundary.completed_ne_raw
#print axioms AiryBoundary.nonzero_solution_continuity
#print axioms AiryBoundary.nonzero_solution_diagonal_limit
#print axioms AiryBoundary.nonzero_solution_uniqueness
#print axioms AiryBoundary.fundamental_wronskian
#print axioms AiryBoundary.fundamental_wronskian_ne_zero
#print axioms AiryBoundary.signed_quotient
#print axioms AiryBoundary.signed_polarization
#print axioms AiryBoundary.linear_pair_not_airy
#print axioms AiryBoundary.linear_pair_diagonal
#print axioms AiryBoundary.linear_pair_off_diagonal
#print axioms AiryBoundary.linear_pair_not_continuousAt
