import RMTFoundations.TracyWidom.HermiteKernelTranslation
import RMTFoundations.TracyWidom.HermiteUniformTailMass
import RMTFoundations.Airy.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HermiteKernelIntegral
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeODE
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.TracyWidom.HermiteEdgeScale
open RMTFoundations.TracyWidom.HermiteEdgeKernel RMTFoundations.TracyWidom.HermiteKernelTranslation
open RMTFoundations.TracyWidom.HermiteUniformTail RMTFoundations.TracyWidom.HermiteTailComparison
open RMTFoundations.TracyWidom.HermiteGaussianDecay RMTFoundations.Airy

/-- The finite-N convolution coefficient equals one half in the literal edge convention. -/
theorem convolution_scale_identity (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    Real.sqrt (N : ℝ)*(edgeScale N)^2 = (edgeAmplitude N)^2 := by
  have hs := sqrt_mul_edgeScale_cube N hN
  have ha := amplitude_square_mul_scale N hN
  apply (mul_right_cancel₀ (edgeScale_pos N hN).ne')
  calc Real.sqrt (N : ℝ)*(edgeScale N)^2*edgeScale N =
      Real.sqrt (N : ℝ)*(edgeScale N)^3 := by ring
    _ = 1 := hs
    _ = (edgeAmplitude N)^2*edgeScale N := ha.symm

noncomputable def adjacentPair (N : ℕ /- [definition] -/)
    (x y u : ℝ /- [definition] -/) : ℝ :=
  edgeMode N (x+u)*previousMode N (y+u)+previousMode N (x+u)*edgeMode N (y+u)

/-- Exact simultaneous derivative of the actual scaled Hermite projection. -/
theorem scaledKernel_translation_hasDerivAt
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x y u : ℝ /- [definition] -/) :
    HasDerivAt (fun t => scaledKernel N (x+t) (y+t))
      (-(1/2:ℝ)*adjacentPair N x y u) u := by
  have hd := ((hermiteKernel_translation_hasDerivAt N (edgePoint N x)
      (edgePoint N y) (edgeScale N*u)).comp u ((hasDerivAt_id u).const_mul
      (edgeScale N))).const_mul (edgeScale N)
  convert hd using 1 <;> try rfl
  · funext t
    unfold scaledKernel edgePoint
    congr 2 <;> ring
  · have hc := convolution_scale_identity N hN
    unfold adjacentPair edgeMode previousMode affineMode edgePoint boundaryPair
    try simp only [Function.comp_def]
    have hx : 2*Real.sqrt (N : ℝ)+edgeScale N*(x+u) =
        2*Real.sqrt (N : ℝ)+edgeScale N*x+edgeScale N*u := by ring
    have hy : 2*Real.sqrt (N : ℝ)+edgeScale N*(y+u) =
        2*Real.sqrt (N : ℝ)+edgeScale N*y+edgeScale N*u := by ring
    rw [hx,hy]
    dsimp [edgePoint] at *
    nlinarith [congrArg (fun z : ℝ => z*(hermiteMode N
      (2*Real.sqrt (N : ℝ)+edgeScale N*x+edgeScale N*u)*hermiteMode (N-1)
      (2*Real.sqrt (N : ℝ)+edgeScale N*y+edgeScale N*u)+hermiteMode (N-1)
      (2*Real.sqrt (N : ℝ)+edgeScale N*x+edgeScale N*u)*hermiteMode N
      (2*Real.sqrt (N : ℝ)+edgeScale N*y+edgeScale N*u))) hc]

/-- A literal finite Hermite projection tends to zero at the translated endpoint. -/
theorem scaledKernel_translation_tendsto
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x y : ℝ /- [definition] -/) :
    Tendsto (fun u : ℝ => scaledKernel N (x+u) (y+u)) atTop (𝓝 0) := by
  have hx (k : Fin N) : Tendsto (fun u : ℝ => hermiteMode k.val (edgePoint N (x+u)))
      atTop (𝓝 0) := by
    have hh := affine_hermiteMode_tendsto k.val 1
      (2*Real.sqrt (N : ℝ)+edgeScale N*x) (edgeScale N) (edgeScale_pos N hN)
    convert hh using 1
    funext u
    unfold edgePoint
    congr 1 <;> ring
  have hy (k : Fin N) : Tendsto (fun u : ℝ => hermiteMode k.val (edgePoint N (y+u)))
      atTop (𝓝 0) := by
    have hh := affine_hermiteMode_tendsto k.val 1
      (2*Real.sqrt (N : ℝ)+edgeScale N*y) (edgeScale N) (edgeScale_pos N hN)
    convert hh using 1
    funext u
    unfold edgePoint
    congr 1 <;> ring
  have hh := tendsto_finsetSum Finset.univ (fun k _ => (hx k).mul (hy k))
  simpa [scaledKernel,hermiteKernel] using hh.const_mul (edgeScale N)

/-- The exact adjacent-mode convolution is absolutely integrable. -/
theorem adjacentPair_integrable
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x y : ℝ /- [definition] -/) :
    Integrable (adjacentPair N x y) halfLineMeasure := by
  let s : ℝ := min x y
  obtain ⟨C,hC,hb⟩ := uniform_halfline_tail s
  have henv (v : ℝ) (hv : s ≤ v) (u : ℝ) (hu : 0 ≤ u) :
      |edgeMode N (v+u)| ≤ C*Real.exp (-(1/2:ℝ)*u) ∧
      |previousMode N (v+u)| ≤ C*Real.exp (-(1/2:ℝ)*u) := by
    have hh := hb N hN (v+u) (by linarith)
    have he : C*Real.exp (-(1/2:ℝ)*(v+u-s)) ≤ C*Real.exp (-(1/2:ℝ)*u) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
    exact ⟨hh.1.trans he,hh.2.trans he⟩
  have hc : Continuous (edgeMode N) := continuous_iff_continuousAt.mpr
    (fun z => (edgeMode_hasDerivAt N z).continuousAt)
  have hp : Continuous (previousMode N) := continuous_iff_continuousAt.mpr
    (fun z => (previousMode_hasDerivAt N z).continuousAt)
  apply ((integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul (2*C^2)).mono'
    (show AEStronglyMeasurable (adjacentPair N x y) halfLineMeasure by
      unfold adjacentPair
      fun_prop)
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro u hu
  have hx := henv x (min_le_left _ _) u hu.le
  have hy := henv y (min_le_right _ _) u hu.le
  have h1 := mul_le_mul hx.1 hy.2 (abs_nonneg _) (by positivity : 0 ≤ C*Real.exp (-(1/2:ℝ)*u))
  have h2 := mul_le_mul hx.2 hy.1 (abs_nonneg _) (by positivity : 0 ≤ C*Real.exp (-(1/2:ℝ)*u))
  have he : (C*Real.exp (-(1/2:ℝ)*u))^2 = C^2*Real.exp (-u) := by
    have hh : (Real.exp (-(1/2:ℝ)*u))^2 = Real.exp (-u) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [mul_pow,hh]
  change |adjacentPair N x y u| ≤ (2*C^2)*Real.exp (-1*u)
  simp only [neg_one_mul]
  calc |adjacentPair N x y u| ≤ |edgeMode N (x+u)*previousMode N (y+u)|+
      |previousMode N (x+u)*edgeMode N (y+u)| := abs_add_le _ _
    _ ≤ 2*(C*Real.exp (-(1/2:ℝ)*u))^2 := by
      rw [abs_mul,abs_mul]
      nlinarith [h1,h2]
    _ = _ := by rw [he];ring

/-- Exact adjacent-mode integral representation, including the diagonal. -/
theorem scaledKernel_eq_adjacent_integral
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x y : ℝ /- [definition] -/) :
    scaledKernel N x y = (1/2:ℝ)*∫ u, adjacentPair N x y u ∂halfLineMeasure := by
  have hd := scaledKernel_translation_hasDerivAt N hN x y
  have hi := (adjacentPair_integrable N hN x y).const_mul (-(1/2:ℝ))
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hd 0).continuousAt.continuousWithinAt) (fun u _ => hd u) hi
    (scaledKernel_translation_tendsto N hN x y)
  rw [integral_const_mul] at hh
  simp only [add_zero] at hh
  linarith

/-- All finite-N derivative, integrability and convolution inputs hold on one
nondegenerate growing Hermite source, including coincident spatial arguments. -/
theorem complete_convolution_joint_probe :
    (∀ n : ℕ, 0 < n+2 ∧ 0 < hermiteDensity (n+2) (fun i => (i.val : ℝ))) ∧
    (∀ n : ℕ, ∀ x y u : ℝ, HasDerivAt
      (fun t => scaledKernel (n+2) (x+t) (y+t))
      (-(1/2:ℝ)*adjacentPair (n+2) x y u) u) ∧
    (∀ n : ℕ, ∀ x y : ℝ, Integrable (adjacentPair (n+2) x y) halfLineMeasure ∧
      Tendsto (fun u : ℝ => scaledKernel (n+2) (x+u) (y+u)) atTop (𝓝 0) ∧
      scaledKernel (n+2) x y = (1/2:ℝ)*∫ u, adjacentPair (n+2) x y u ∂halfLineMeasure) := by
  exact ⟨fun n => ⟨by omega,hermite_density_all_binder_joint_probe.2 (n+1)⟩,
    fun n x y u => scaledKernel_translation_hasDerivAt (n+2) (by omega) x y u,
    fun n x y => ⟨adjacentPair_integrable (n+2) (by omega) x y,
      scaledKernel_translation_tendsto (n+2) (by omega) x y,
      scaledKernel_eq_adjacent_integral (n+2) (by omega) x y⟩⟩

end RMTFoundations.TracyWidom.HermiteKernelIntegral

#print axioms RMTFoundations.TracyWidom.HermiteKernelIntegral.convolution_scale_identity
#print axioms RMTFoundations.TracyWidom.HermiteKernelIntegral.adjacentPair
#print axioms RMTFoundations.TracyWidom.HermiteKernelIntegral.scaledKernel_translation_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteKernelIntegral.scaledKernel_translation_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteKernelIntegral.adjacentPair_integrable
#print axioms RMTFoundations.TracyWidom.HermiteKernelIntegral.scaledKernel_eq_adjacent_integral
#print axioms RMTFoundations.TracyWidom.HermiteKernelIntegral.complete_convolution_joint_probe
