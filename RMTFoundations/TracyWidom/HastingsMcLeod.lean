import RMTFoundations.TracyWidom.HMUniqueness
import RMTFoundations.TracyWidom.Painleve

/-! Uniqueness of the real global Airy-normalized classical Painleve II solution.
The solution is the canonical Fredholm coordinate used by both TW integral formulas.
No boundary, Green representation, integrability or contraction premise is assumed. -/
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HastingsMcLeod
open Filter
open scoped Topology
open RMTFoundations.TracyWidom

/-- Two global classical Painleve II solutions with relative Airy normalization agree. -/
theorem unique
    (q r : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hr : Differentiable ℝ r /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hrr : ∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s /- [standing] -/)
    (hnq : Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) /- [standing] -/)
    (hnr : Tendsto (fun s => r s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) /- [standing] -/) :
    q = r := HMUniqueness.hastings_mcleod_unique q r hq hr hqq hrr hnq hnr

/-- Every normalized real global classical solution is the actual Fredholm response. -/
theorem eq_canonical
    (q : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hnq : Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) /- [standing] -/) :
    q = Painleve.q := HMUniqueness.normalized_classical_eq_fredholm q hq hqq hnq

/-- A unique real global classical Airy-normalized solution exists. -/
theorem exists_unique :
    ∃! q : ℝ → ℝ, Differentiable ℝ q ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) :=
  HMUniqueness.exists_unique_hastings_mcleod

/-- All uniqueness hypotheses hold jointly on the genuine nonzero Fredholm solution. -/
theorem all_binder_joint_probe :
    ∃ q r : ℝ → ℝ, q ≠ 0 ∧ r ≠ 0 ∧
      Differentiable ℝ q ∧ Differentiable ℝ r ∧
      (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
      (∀ s, HasDerivAt (deriv r) (s*r s+2*(r s)^3) s) ∧
      Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) ∧
      Tendsto (fun s => r s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) ∧ q=r ∧
      q=Painleve.q := HMUniqueness.uniqueness_all_binder_joint_probe
end RMTFoundations.TracyWidom.HastingsMcLeod

#print axioms RMTFoundations.TracyWidom.HastingsMcLeod.unique
#print axioms RMTFoundations.TracyWidom.HastingsMcLeod.eq_canonical
#print axioms RMTFoundations.TracyWidom.HastingsMcLeod.exists_unique
#print axioms RMTFoundations.TracyWidom.HastingsMcLeod.all_binder_joint_probe
