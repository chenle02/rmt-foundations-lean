import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.StirlingEffective
open Filter Topology

/-- The Robbins correction whose step monotonicity telescopes to a global bound. -/
noncomputable def lowerCorrection (n : ℕ /- [definition] -/) : ℝ :=
  Real.log (Stirling.stirlingSeq (n+1)) - 1/(12*((n+1 : ℕ) : ℝ))

lemma lower_correction_monotone : Monotone lowerCorrection := by
  apply monotone_nat_of_le_succ
  intro n
  have h := Stirling.log_stirlingSeq_sdiff_le (n+1)
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hm : (0 : ℝ) < ((n+1+1 : ℕ) : ℝ) := by positivity
  have hi : 1/(12*((n+1 : ℕ) : ℝ)) - 1/(12*((n+1+1 : ℕ) : ℝ)) =
      1/(12*((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+1)) := by
    push_cast
    field_simp
    ring
  unfold lowerCorrection
  push_cast at h ⊢
  push_cast at hi
  linarith

lemma lower_correction_tendsto :
    Tendsto lowerCorrection atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have h1 := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)).log hp
  have h2 := (tendsto_const_div_atTop_nhds_zero_nat (1/12 : ℝ)).comp
    (tendsto_add_atTop_nat 1)
  convert h1.sub h2 using 1
  · funext n
    dsimp [lowerCorrection]
    ring
  · norm_num

/-- Effective Robbins bound, derived from Mathlib's stepwise theorem and its proved limit. -/
theorem log_stirling_error_upper (n : ℕ /- [definition] -/) :
    Real.log (Stirling.stirlingSeq (n+1)) - Real.log (Real.sqrt Real.pi) ≤
      1/(12*((n+1 : ℕ) : ℝ)) := by
  have h := lower_correction_monotone.ge_of_tendsto lower_correction_tendsto n
  unfold lowerCorrection at h
  linarith

lemma log_stirling_error_nonneg (n : ℕ /- [definition] -/) :
    0 ≤ Real.log (Stirling.stirlingSeq (n+1)) - Real.log (Real.sqrt Real.pi) := by
  have h := Real.log_le_log (by positivity : 0 < Real.sqrt Real.pi)
    (Stirling.sqrt_pi_le_stirlingSeq (by omega : n+1 ≠ 0))
  linarith

/-- Joint satisfiability on the actual growing factorial sequence, with positive errors bounded. -/
theorem stirling_effective_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, 0 < Stirling.stirlingSeq (n+1) ∧
      0 ≤ Real.log (Stirling.stirlingSeq (n+1)) - Real.log (Real.sqrt Real.pi) ∧
      Real.log (Stirling.stirlingSeq (n+1)) - Real.log (Real.sqrt Real.pi) ≤
        1/(12*((n+1 : ℕ) : ℝ))) := by
  exact ⟨fun K => ⟨K, Nat.lt_succ_self K⟩, fun n =>
    ⟨Stirling.stirlingSeq'_pos n, log_stirling_error_nonneg n, log_stirling_error_upper n⟩⟩
end RMTFoundations.TracyWidom.StirlingEffective

#print axioms RMTFoundations.TracyWidom.StirlingEffective.lowerCorrection
#print axioms RMTFoundations.TracyWidom.StirlingEffective.lower_correction_monotone
#print axioms RMTFoundations.TracyWidom.StirlingEffective.lower_correction_tendsto
#print axioms RMTFoundations.TracyWidom.StirlingEffective.log_stirling_error_upper
#print axioms RMTFoundations.TracyWidom.StirlingEffective.log_stirling_error_nonneg
#print axioms RMTFoundations.TracyWidom.StirlingEffective.stirling_effective_joint_probe
