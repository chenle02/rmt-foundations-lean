import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteEdgeScale
open Filter Topology
noncomputable def edgeScale (N : ℕ /- [definition] -/) : ℝ :=
  (N : ℝ) ^ (-1 / 6 : ℝ)
noncomputable def edgePoint (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ := 2 * Real.sqrt N + edgeScale N * x
noncomputable def edgeCoefficient (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  x + x^2 / 4 * (N : ℝ)^(-2/3 : ℝ) - 1/2 * (N : ℝ)^(-1/3 : ℝ)
lemma edgeScale_pos (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : 0 < edgeScale N := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _
lemma edgeScale_square (N : ℕ /- [definition] -/) :
    (edgeScale N)^2 = (N : ℝ)^(-1/3 : ℝ) := by
  rw [edgeScale, ← Real.rpow_mul_natCast (by positivity)]
  norm_num
lemma edgeScale_fourth (N : ℕ /- [definition] -/) :
    (edgeScale N)^4 = (N : ℝ)^(-2/3 : ℝ) := by
  rw [edgeScale, ← Real.rpow_mul_natCast (by positivity)]
  norm_num
lemma sqrt_mul_edgeScale_cube (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    Real.sqrt N * (edgeScale N)^3 = 1 := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, edgeScale, ← Real.rpow_mul_natCast h.le,
    ← Real.rpow_add h]
  norm_num
/-- Literal coefficient after the 2sqrt(N)+xN^(-1/6) change of variables. -/
theorem edge_coefficient_identity (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    (edgeScale N)^2 * ((edgePoint N x)^2/4 - (N : ℝ) - 1/2) =
      edgeCoefficient N x := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hc := sqrt_mul_edgeScale_cube N hN
  have hd2 := edgeScale_square N
  have hd4 := edgeScale_fourth N
  unfold edgePoint edgeCoefficient
  calc
    _ = (edgeScale N)^2 * ((Real.sqrt N)^2 - (N : ℝ)) +
      (Real.sqrt N * (edgeScale N)^3) * x +
      (edgeScale N)^4 * x^2 / 4 - (edgeScale N)^2 / 2 := by ring
    _ = _ := by rw [hs,hc,hd2,hd4]; ring

/-- A genuine uniform error bound on every bounded real window. -/
theorem edge_coefficient_compact_error (N : ℕ /- [definition] -/)
    (R x : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (hx : |x| ≤ R /- [standing] -/) :
    |edgeCoefficient N x - x| ≤
      R^2 / 4 * (N : ℝ)^(-2/3 : ℝ) + 1/2 * (N : ℝ)^(-1/3 : ℝ) := by
  have hp : 0 ≤ (N : ℝ)^(-2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hq : 0 ≤ (N : ℝ)^(-1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hx2 : x^2 ≤ R^2 := by nlinarith [sq_abs x, abs_nonneg x]
  have he : edgeCoefficient N x - x =
      x^2/4 * (N : ℝ)^(-2/3 : ℝ) - 1/2 * (N : ℝ)^(-1/3 : ℝ) := by
    unfold edgeCoefficient; ring
  rw [he]
  calc
    _ ≤ |x^2/4 * (N : ℝ)^(-2/3 : ℝ)| +
      |1/2 * (N : ℝ)^(-1/3 : ℝ)| := abs_sub _ _
    _ = x^2/4 * (N : ℝ)^(-2/3 : ℝ) +
      1/2 * (N : ℝ)^(-1/3 : ℝ) := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hx2 hp]

/-- Epsilon-uniform coefficient convergence; this makes no claim about mode amplitudes. -/
theorem edge_coefficient_locally_uniform (R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x| ≤ R →
      |edgeCoefficient (n+1) x - x| < ε := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2/3 by norm_num)).comp hn
  have h1 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/3 by norm_num)).comp hn
  have hlim : Tendsto (fun n : ℕ => R^2/4 * ((n+1 : ℕ) : ℝ)^(-2/3 : ℝ) +
      1/2 * ((n+1 : ℕ) : ℝ)^(-1/3 : ℝ)) atTop (𝓝 0) := by
    have hc := (h2.const_mul (R^2/4)).add (h1.const_mul (1/2))
    convert hc using 1 <;> first | rfl | (funext n; norm_num) | norm_num
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn x hx
  exact lt_of_le_of_lt (edge_coefficient_compact_error (n+1) R x hR hx) hn

/-- Complete joint probe: positive growing scale and compact uniform conclusion together. -/
theorem edge_scale_all_binder_joint_probe (n : ℕ /- [definition] -/) :
    0 < edgeScale (n+1) ∧
      (∀ x, (edgeScale (n+1))^2 * ((edgePoint (n+1) x)^2/4 - (n+1 : ℕ) - 1/2) =
        edgeCoefficient (n+1) x) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ x : ℝ, |x| ≤ 3 →
        |edgeCoefficient (m+1) x - x| < ε) := by
  refine ⟨edgeScale_pos _ (by omega), ?_, ?_⟩
  · intro x; exact edge_coefficient_identity _ (by omega) x
  · intro ε hε; exact edge_coefficient_locally_uniform 3 (by norm_num) ε hε
end RMTFoundations.TracyWidom.HermiteEdgeScale

#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edgeScale
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edgePoint
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edgeCoefficient
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edgeScale_pos
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edgeScale_square
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edgeScale_fourth
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.sqrt_mul_edgeScale_cube
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edge_coefficient_identity
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edge_coefficient_compact_error
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edge_coefficient_locally_uniform
#print axioms RMTFoundations.TracyWidom.HermiteEdgeScale.edge_scale_all_binder_joint_probe
