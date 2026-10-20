import RMTFoundations.TracyWidom.HermiteTailComparison
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteFiniteEnvelope
open Set Real
open RMTFoundations.TracyWidom.HermiteTailComparison RMTFoundations.TracyWidom.HermiteEdgeScale
open RMTFoundations.TracyWidom.HermiteEdgeReduction
/-- A literal relative tail supplies an absolute envelope on every fixed half-line,
with no uniformity claim across an infinite family. -/
theorem extend_relative_tail (u : ℝ → ℝ /- [definition] -/)
    (hu : Continuous u /- [standing] -/)
    (a s c : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/)
    (htail : ∀ y, a ≤ y → |u y| ≤ |u a| *exp (-c*(y-a)) /- [standing] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, s ≤ y → |u y| ≤ C*exp (-c*(y-s)) := by
  let f : ℝ → ℝ := fun y => |u y| *exp (c*(y-s))
  have hf : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨z,hz,hm⟩ := (isCompact_Icc (a:=min s a) (b:=a)).exists_isMaxOn
    ⟨a,min_le_right _ _,le_rfl⟩ hf.continuousOn
  let C : ℝ := max (c+1) (max (f z) (|u a| *exp (c*(a-s))))
  have hC : 0 < C := lt_of_lt_of_le (show (0:ℝ)<c+1 by linarith) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro y hy
  have H : f y ≤ C := by
    by_cases hya : y ≤ a
    · exact (hm ⟨(min_le_left _ _).trans hy,hya⟩).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · have h := mul_le_mul_of_nonneg_right (htail y (le_of_not_ge hya))
        (exp_pos (c*(y-s))).le
      have he : exp (-c*(y-a))*exp (c*(y-s)) = exp (c*(a-s)) := by
        rw [←exp_add]
        congr 1
        ring
      have H' : f y ≤ |u a| *exp (c*(a-s)) := by
        dsimp [f]
        simpa only [mul_assoc,he] using h
      exact H'.trans ((le_max_right _ _).trans (le_max_right _ _))
  have he : exp (c*(y-s))*exp (-c*(y-s)) = 1 := by
    rw [←exp_add,show c*(y-s)+(-c)*(y-s)=0 by ring,exp_zero]
  calc
    |u y| = f y*exp (-c*(y-s)) := by dsimp [f]; rw [mul_assoc,he,mul_one]
    _ ≤ C*exp (-c*(y-s)) := mul_le_mul_of_nonneg_right H (exp_pos _).le
/-- Both neighboring literal Hermite modes have a common finite-N envelope. -/
theorem hermite_envelope (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, s ≤ y →
      |edgeMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) ∧
      |previousMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) := by
  have hcurrent : Continuous (edgeMode N) := continuous_iff_continuousAt.mpr
    (fun y => (edgeMode_hasDerivAt N y).continuousAt)
  have hprevious : Continuous (previousMode N) := continuous_iff_continuousAt.mpr
    (fun y => (previousMode_hasDerivAt N y).continuousAt)
  obtain ⟨C,hC,h⟩ := extend_relative_tail (edgeMode N) hcurrent 1 s (1/2)
    (by norm_num) (fun y hy => edgeMode_relative_tail N hN y hy)
  obtain ⟨B,hB,hb⟩ := extend_relative_tail (previousMode N) hprevious 1 s (1/2)
    (by norm_num) (fun y hy => previousMode_relative_tail N hN y hy)
  refine ⟨max C B,hC.trans_le (le_max_left _ _),fun y hy => ⟨?_,?_⟩⟩
  · exact (h y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le)
  · exact (hb y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le)
/-- Finite exceptions in a contour argument can be absorbed into ONE constant. -/
theorem finite_dimensions_envelope (K : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → N ≤ K → ∀ y, s ≤ y →
      |edgeMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) ∧
      |previousMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) := by
  induction K with
  | zero => exact ⟨1,by norm_num,fun N hN hK => by omega⟩
  | succ K ih =>
    obtain ⟨C,hC,h⟩ := ih
    obtain ⟨B,hB,hb⟩ := hermite_envelope (K+1) (by omega) s
    refine ⟨max C B,hC.trans_le (le_max_left _ _),?_⟩
    intro N hN hK y hy
    by_cases hNK : N ≤ K
    · have H := h N hN hNK y hy
      exact ⟨H.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le),
        H.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le)⟩
    · have hn : N=K+1 := by omega
      subst N
      have H := hb y hy
      exact ⟨H.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le),
        H.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le)⟩
/-- Arbitrarily many positive dimensions and arbitrary left endpoints coexist. -/
theorem finite_envelope_joint_probe (k : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    ∃ K : ℕ, k < K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 0 < N → N ≤ K → ∀ y, s ≤ y →
        |edgeMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) ∧
        |previousMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) := by
  exact ⟨k+1,by omega,finite_dimensions_envelope (k+1) s⟩
end RMTFoundations.TracyWidom.HermiteFiniteEnvelope

#print axioms RMTFoundations.TracyWidom.HermiteFiniteEnvelope.extend_relative_tail
#print axioms RMTFoundations.TracyWidom.HermiteFiniteEnvelope.hermite_envelope
#print axioms RMTFoundations.TracyWidom.HermiteFiniteEnvelope.finite_dimensions_envelope
#print axioms RMTFoundations.TracyWidom.HermiteFiniteEnvelope.finite_envelope_joint_probe
