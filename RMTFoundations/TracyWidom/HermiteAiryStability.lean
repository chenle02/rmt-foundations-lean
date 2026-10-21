import RMTFoundations.TracyWidom.PerturbedAiryStability
import RMTFoundations.TracyWidom.HermiteEdgeReduction
import RMTFoundations.Airy.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteAiryStability
open Set Filter Topology Real
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.TracyWidom.HermiteEdgeScale
open RMTFoundations.Airy RMTFoundations.TracyWidom.PerturbedAiryStability

noncomputable def coefficientError (N : ℕ /- [definition] -/)
    (R : ℝ /- [definition] -/) : ℝ :=
  R^2/4 * (N:ℝ)^(-2/3:ℝ) + 1/2 * (N:ℝ)^(-1/3:ℝ)
noncomputable def cauchyError (N : ℕ /- [definition] -/) : ℝ :=
  max |edgeMode N 0-airyAiReal 0| |edgeSlope N 0-deriv airyAiReal 0|
lemma coefficientError_nonneg (N : ℕ /- [definition] -/)
    (R : ℝ /- [definition] -/) : 0 ≤ coefficientError N R := by
  unfold coefficientError; positivity
lemma cauchyError_nonneg (N : ℕ /- [definition] -/) : 0 ≤ cauchyError N :=
  (abs_nonneg _).trans (le_max_left _ _)
lemma coefficientError_tendsto (R : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => coefficientError (n+1) R) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_rpow_neg_atTop (show (0:ℝ)<2/3 by norm_num)).comp hn
  have h1 := (tendsto_rpow_neg_atTop (show (0:ℝ)<1/3 by norm_num)).comp hn
  have hc := (h2.const_mul (R^2/4)).add (h1.const_mul (1/2))
  convert hc using 1 <;> first | rfl | (funext n; norm_num [coefficientError]) | norm_num

lemma airy_compact_bound (R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |x| ≤ R → |airyAiReal x| ≤ M := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    continuous_airyAiReal.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have hb : |airyAiReal x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x (abs_le.mp hx)
  exact hb.trans (le_max_left _ _)

/-- A uniform positive potential floor on the entire right half-line, for every
positive dimension. This is an actual coefficient theorem, not a mode-tail claim. -/
theorem edgeCoefficient_tail_floor (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : 1 ≤ x /- [standing] -/) :
    (1/2:ℝ) ≤ edgeCoefficient N x := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num : (-1/3:ℝ) ≤ 0)
  have hpos : 0 ≤ x^2/4 * (N:ℝ)^(-2/3:ℝ) := by positivity
  unfold edgeCoefficient
  linarith

/-- Complete growing witness for the tail coefficient floor, with a positive scale. -/
theorem edge_coefficient_tail_joint_probe (n : ℕ /- [definition] -/) :
    0 < edgeScale (n+1) ∧ ∀ x : ℝ, 1 ≤ x → (1/2:ℝ) ≤ edgeCoefficient (n+1) x := by
  refine ⟨edgeScale_pos (n+1) (by omega), ?_⟩
  intro x hx
  exact edgeCoefficient_tail_floor (n+1) (by omega) x hx

/-- Actual Hermite mode and derivative; every analytic premise except the chosen
reference bound is discharged by the literal definitions and the exact edge ODE. -/
theorem edge_pair_error_bound
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (R M : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (hM : 0 ≤ M /- [standing] -/)
    (hAi : ∀ x, |x| ≤ R → |airyAiReal x| ≤ M /- [standing] -/)
    (hsmall : coefficientError N R ≤ 1 /- [standing] -/) :
    ∀ x, |x| ≤ R → max |edgeMode N x-airyAiReal x|
      |edgeSlope N x-deriv airyAiReal x| ≤
        gronwallBound (cauchyError N) (R+2) (coefficientError N R*M) R := by
  apply coefficient_stability_symmetric (edgeMode N) (edgeSlope N)
    airyAiReal (deriv airyAiReal) (edgeCoefficient N) id
    R (cauchyError N) (R+2) (coefficientError N R) M
    (edgeMode_hasDerivAt N) (edgeSlope_hasDerivAt N hN)
    hasDerivAt_airyAiReal' hasDerivAt_deriv_airyAiReal'
    hR (cauchyError_nonneg N) (by linarith) (coefficientError_nonneg N R) hM
  · intro x hx
    calc
      |edgeCoefficient N x| = |(edgeCoefficient N x-x)+x| := by congr 1; ring
      _ ≤ |edgeCoefficient N x-x|+|x| := abs_add_le _ _
      _ ≤ coefficientError N R+R := add_le_add (edge_coefficient_compact_error N R x hR hx) hx
      _ ≤ R+2 := by linarith
  · intro x hx; exact edge_coefficient_compact_error N R x hR hx
  · exact hAi
  · exact le_rfl

/-- Compact C1 convergence reduces to the two literal Cauchy data at zero.
This does not claim that those data converge: normalization is still an open seam. -/
theorem edge_pair_locally_uniform_of_cauchy
    (hinit : Tendsto (fun n : ℕ => cauchyError (n+1)) atTop (𝓝 0) /- [standing] -/)
    (R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ x, |x| ≤ R →
      max |edgeMode (n+1) x-airyAiReal x|
        |edgeSlope (n+1) x-deriv airyAiReal x| < ε := by
  obtain ⟨M,hM,hAi⟩ := airy_compact_bound R hR
  have he := coefficientError_tendsto R
  have hK : R+2 ≠ 0 := by linarith
  have hlim : Tendsto (fun n : ℕ =>
      gronwallBound (cauchyError (n+1)) (R+2) (coefficientError (n+1) R*M) R)
      atTop (𝓝 0) := by
    simp only [gronwallBound,if_neg hK]
    have H := (hinit.mul_const (exp ((R+2)*R))).add
      (((he.mul_const M).div_const (R+2)).mul_const (exp ((R+2)*R)-1))
    simpa using H
  filter_upwards [he.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hlim.eventually (gt_mem_nhds hε)] with n hn hb x hx
  exact lt_of_le_of_lt (edge_pair_error_bound (n+1) (by omega) R M hR hM hAi hn.le x hx) hb

/-- Every binder of the finite estimate is supplied on literal growing Hermite
modes and the  Ai, with a positive window and actual nonzero density. -/
theorem edge_pair_stability_joint_probe :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x, |x| ≤ 3 → |airyAiReal x| ≤ M) ∧
      ∀ᶠ n : ℕ in atTop,
        0 < edgeAmplitude (n+1) ∧ 0 < edgeScale (n+1) ∧
        0 < RMTFoundations.TracyWidom.GUEHermite.hermiteDensity (n+1) (fun i => (i.val:ℝ)) ∧
        (∀ x, |x| ≤ 3 → max |edgeMode (n+1) x-airyAiReal x|
          |edgeSlope (n+1) x-deriv airyAiReal x| ≤
          gronwallBound (cauchyError (n+1)) 5 (coefficientError (n+1) 3*M) 3) := by
  obtain ⟨M,hM,hAi⟩ := airy_compact_bound 3 (by norm_num)
  refine ⟨M,hM,hAi,?_⟩
  filter_upwards [(coefficientError_tendsto 3).eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn
  have H := edge_mode_all_binder_joint_probe n
  refine ⟨H.1,H.2.1,H.2.2.1,?_⟩
  simpa only [show (3:ℝ)+2=5 by norm_num] using
    edge_pair_error_bound (n+1) (by omega) 3 M (by norm_num) hM hAi hn.le
end RMTFoundations.TracyWidom.HermiteAiryStability

#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.coefficientError
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.cauchyError
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.coefficientError_nonneg
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.cauchyError_nonneg
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.coefficientError_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.airy_compact_bound
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.edgeCoefficient_tail_floor
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.edge_coefficient_tail_joint_probe
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.edge_pair_error_bound
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.edge_pair_locally_uniform_of_cauchy
#print axioms RMTFoundations.TracyWidom.HermiteAiryStability.edge_pair_stability_joint_probe
