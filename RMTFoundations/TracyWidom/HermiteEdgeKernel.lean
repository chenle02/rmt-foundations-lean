import RMTFoundations.TracyWidom.HermiteEdgeReduction
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteEdgeKernel
open Polynomial RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeODE
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.HermiteEdgeReduction
lemma polySlope_succ (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : polySlope (n+1) x = (n+1 : ℕ) * hpoly n x := by
  unfold polySlope realHermite
  rw [Polynomial.derivative_map, hermite_derivative_succ]
  simp [hpoly, realHermite]
lemma modeSlope_lower (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    modeSlope (n+1) x = Real.sqrt ((n+1 : ℕ) : ℝ) * hermiteMode n x - x/2 * hermiteMode (n+1) x := by
  have h := sqrt_mul_hermiteNormalizer_succ n
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)
  have he : (n+1 : ℕ) * hermiteNormalizer (n+1) = Real.sqrt ((n+1 : ℕ) : ℝ) * hermiteNormalizer n := by
    calc
      _ = (Real.sqrt ((n+1 : ℕ) : ℝ))^2 * hermiteNormalizer (n+1) := by rw [hs]
      _ = Real.sqrt ((n+1 : ℕ) : ℝ) * (Real.sqrt ((n+1 : ℕ) : ℝ) * hermiteNormalizer (n+1)) := by ring
      _ = _ := by rw [h]
  unfold modeSlope
  rw [polySlope_succ]
  unfold hermiteMode
  have hh := congrArg (fun z : ℝ => gaussianWeight x * z * hpoly n x) he
  nlinarith [hh]
/-- The slope CD formula keeps the finite-N correction term with its sign. -/
theorem hermite_kernel_slope_cross (n : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    (x-y) * hermiteKernel (n+1) x y =
      hermiteMode (n+1) x * modeSlope (n+1) y -
      modeSlope (n+1) x * hermiteMode (n+1) y -
      (x-y)/2 * hermiteMode (n+1) x * hermiteMode (n+1) y := by
  rw [hermite_christoffel_darboux_cross, modeSlope_lower, modeSlope_lower]
  ring
noncomputable def scaledKernel (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : ℝ :=
  edgeScale N * hermiteKernel N (edgePoint N x) (edgePoint N y)
lemma amplitude_square_mul_scale (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : (edgeAmplitude N)^2 * edgeScale N = 1 := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  rw [edgeAmplitude, edgeScale, ← Real.rpow_mul_natCast h.le, ← Real.rpow_add h]
  norm_num
/-- Exact scaled CD formula in the convention used for the Airy kernel. -/
theorem scaled_kernel_slope_cross (n : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    (x-y) * scaledKernel (n+1) x y =
      edgeMode (n+1) x * edgeSlope (n+1) y -
      edgeSlope (n+1) x * edgeMode (n+1) y -
      (x-y) * (edgeScale (n+1))^2/2 * edgeMode (n+1) x * edgeMode (n+1) y := by
  have ha := amplitude_square_mul_scale (n+1) (by omega)
  have hd : edgePoint (n+1) x - edgePoint (n+1) y = edgeScale (n+1) * (x-y) := by
    unfold edgePoint; ring
  have h := hermite_kernel_slope_cross n (edgePoint (n+1) x) (edgePoint (n+1) y)
  rw [hd] at h
  unfold scaledKernel
  calc
    _ = (edgeScale (n+1) * (x-y)) * hermiteKernel (n+1)
      (edgePoint (n+1) x) (edgePoint (n+1) y) := by ring
    _ = _ := h
    _ = _ := by
      unfold edgeMode edgeSlope affineMode affineSlope
      dsimp only [edgePoint] at hd
      have hm := congrArg (fun z : ℝ => z *
        (hermiteMode (n+1) (edgePoint (n+1) x) * modeSlope (n+1) (edgePoint (n+1) y) -
        modeSlope (n+1) (edgePoint (n+1) x) * hermiteMode (n+1) (edgePoint (n+1) y))) ha
      have hc := congrArg (fun z : ℝ => z * (x-y) * edgeScale (n+1)/2 *
        hermiteMode (n+1) (edgePoint (n+1) x) * hermiteMode (n+1) (edgePoint (n+1) y)) ha
      dsimp [edgePoint] at hm hc ⊢
      nlinarith [hm,hc]

theorem scaled_kernel_slope (n : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/)
    (hxy : x ≠ y /- [standing] -/) :
    scaledKernel (n+1) x y =
      (edgeMode (n+1) x * edgeSlope (n+1) y -
        edgeSlope (n+1) x * edgeMode (n+1) y -
        (x-y) * (edgeScale (n+1))^2/2 * edgeMode (n+1) x * edgeMode (n+1) y) / (x-y) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).mpr
  simpa only [mul_comm] using scaled_kernel_slope_cross n x y
/-- Every standing binder is supplied, on the same growing normalized Hermite family. -/
theorem scaled_kernel_all_binder_joint_probe (n : ℕ /- [definition] -/) :
    0 < hermiteDensity (n+1) (fun i => (i.val : ℝ)) ∧
      (0 : ℝ) ≠ 1 ∧
      scaledKernel (n+1) 0 1 =
        (edgeMode (n+1) 0 * edgeSlope (n+1) 1 -
          edgeSlope (n+1) 0 * edgeMode (n+1) 1 -
          (0-1) * (edgeScale (n+1))^2/2 * edgeMode (n+1) 0 * edgeMode (n+1) 1) / (0-1) := by
  exact ⟨hermite_density_all_binder_joint_probe.2 n, by norm_num,
    scaled_kernel_slope n 0 1 (by norm_num)⟩
end RMTFoundations.TracyWidom.HermiteEdgeKernel

#print axioms RMTFoundations.TracyWidom.HermiteEdgeKernel.polySlope_succ
#print axioms RMTFoundations.TracyWidom.HermiteEdgeKernel.modeSlope_lower
#print axioms RMTFoundations.TracyWidom.HermiteEdgeKernel.hermite_kernel_slope_cross
#print axioms RMTFoundations.TracyWidom.HermiteEdgeKernel.scaledKernel
#print axioms RMTFoundations.TracyWidom.HermiteEdgeKernel.amplitude_square_mul_scale
#print axioms RMTFoundations.TracyWidom.HermiteEdgeKernel.scaled_kernel_slope_cross
#print axioms RMTFoundations.TracyWidom.HermiteEdgeKernel.scaled_kernel_slope
#print axioms RMTFoundations.TracyWidom.HermiteEdgeKernel.scaled_kernel_all_binder_joint_probe
