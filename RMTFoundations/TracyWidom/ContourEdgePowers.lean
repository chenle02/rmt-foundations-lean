import RMTFoundations.TracyWidom.HermiteEdgeReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourEdgePowers
open Real Filter Topology
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.HermiteEdgeReduction
noncomputable def edgeDelta (N : ℕ /- [definition] -/) : ℝ :=
  (N:ℝ)^(-1/3:ℝ)
lemma edgeDelta_pos (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : 0 < edgeDelta N := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  dsimp [edgeDelta]
  positivity
lemma dimension_delta_cube (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : (N:ℝ)*(edgeDelta N)^3=1 := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  rw [edgeDelta,←rpow_mul_natCast hn.le (-1/3:ℝ) 3]
  norm_num
  simpa only [rpow_neg_one] using mul_inv_cancel₀ hn.ne'
lemma edgeScale_delta (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    edgeScale N = sqrt (N:ℝ)*(edgeDelta N)^2 := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  rw [edgeScale,edgeDelta,←rpow_mul_natCast hn.le (-1/3:ℝ) 2,
    sqrt_eq_rpow,←rpow_add hn]
  congr 1
  norm_num
lemma amplitude_delta_balance (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    (edgeAmplitude N)^2*sqrt (N:ℝ) = (N:ℝ)*edgeDelta N := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  rw [edgeAmplitude,edgeDelta,←rpow_mul_natCast hn.le (1/12:ℝ) 2,
    sqrt_eq_rpow,←rpow_add hn]
  calc
    _ = (N:ℝ)^((1:ℝ)+(-1/3:ℝ)) := by congr 1; norm_num
    _ = _ := by rw [rpow_add hn,rpow_one]
lemma edgeDelta_half (N : ℕ /- [definition] -/)
    (hN : 8 ≤ N /- [standing] -/) : edgeDelta N ≤ (1/2:ℝ) := by
  have hNreal : (8:ℝ) ≤ N := by exact_mod_cast hN
  have H := rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<8) hNreal
    (by norm_num : (-1/3:ℝ) ≤ 0)
  have he : (8:ℝ)^(-1/3:ℝ)=(1/2:ℝ) := by
    rw [show (8:ℝ)=(2:ℝ)^3 by norm_num,
      ←rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) 3 (-1/3:ℝ)]
    norm_num
  exact H.trans_eq he
/-- The readiness threshold uses the actual scale and the requested endpoint. -/
theorem endpoint_threshold (s : ℝ /- [definition] -/) :
    ∃ K : ℕ, 8 ≤ K ∧ ∀ N : ℕ, K ≤ N →
      0 < edgeDelta N ∧ edgeDelta N ≤ (1/2:ℝ) ∧ edgeDelta N*|s| ≤ 1 := by
  have hd : Tendsto edgeDelta atTop (𝓝 0) := by
    have H : Tendsto (fun x : ℝ => x^(-1/3:ℝ)) atTop (𝓝 0) :=
      by simpa only [neg_div] using
        (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<(1/3:ℝ)))
    exact H.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)
  have H : ∀ᶠ N : ℕ in atTop, edgeDelta N*|s| < 1 := by
    have ht : Tendsto (fun N : ℕ => edgeDelta N*|s|) atTop (𝓝 0) := by
      simpa only [zero_mul] using hd.mul_const |s|
    exact ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨K,hK⟩ := eventually_atTop.mp H
  refine ⟨max K 8,le_max_right _ _,fun N hN => ⟨?_,?_,?_⟩⟩
  · exact edgeDelta_pos N (by omega)
  · exact edgeDelta_half N (by omega)
  · exact (hK N ((le_max_left _ _).trans hN)).le
/-- All endpoint and power premises coexist for every requested endpoint. -/
theorem powers_joint_probe (s : ℝ /- [definition] -/) :
    ∃ K : ℕ, 8 ≤ K ∧ ∀ N : ℕ, K ≤ N →
      0 < edgeDelta N ∧ edgeDelta N ≤ (1/2:ℝ) ∧ edgeDelta N*|s| ≤ 1 ∧
      (N:ℝ)*(edgeDelta N)^3=1 ∧
      edgeScale N=sqrt (N:ℝ)*(edgeDelta N)^2 ∧
      (edgeAmplitude N)^2*sqrt (N:ℝ)=(N:ℝ)*edgeDelta N := by
  obtain ⟨K,hK,h⟩ := endpoint_threshold s
  exact ⟨K,hK,fun N hN => ⟨(h N hN).1,(h N hN).2.1,(h N hN).2.2,
    dimension_delta_cube N (by omega),edgeScale_delta N (by omega),
    amplitude_delta_balance N (by omega)⟩⟩
end RMTFoundations.TracyWidom.ContourEdgePowers

#print axioms RMTFoundations.TracyWidom.ContourEdgePowers.edgeDelta
#print axioms RMTFoundations.TracyWidom.ContourEdgePowers.edgeDelta_pos
#print axioms RMTFoundations.TracyWidom.ContourEdgePowers.dimension_delta_cube
#print axioms RMTFoundations.TracyWidom.ContourEdgePowers.edgeScale_delta
#print axioms RMTFoundations.TracyWidom.ContourEdgePowers.amplitude_delta_balance
#print axioms RMTFoundations.TracyWidom.ContourEdgePowers.edgeDelta_half
#print axioms RMTFoundations.TracyWidom.ContourEdgePowers.endpoint_threshold
#print axioms RMTFoundations.TracyWidom.ContourEdgePowers.powers_joint_probe
