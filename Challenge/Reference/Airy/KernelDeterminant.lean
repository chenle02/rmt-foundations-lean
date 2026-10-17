import Mathlib
import Challenge.Reference.Airy.Core
import Challenge.Reference.Airy.Bounds

namespace RMTFoundations.AiryKernel

open MeasureTheory Set Filter
open scoped Topology ENNReal InnerProductSpace
open RMTFoundations.Airy


open Set

/-- A nonzero Airy solution positive at the origin cannot stay nonnegative to its left. -/
theorem airy_solution_negative_witness
    (f g : ℝ → ℝ /- [definition] -/)
    (hf : ∀ x, HasDerivAt f (g x) x /- [standing] -/)
    (hg : ∀ x, HasDerivAt g (x * f x) x /- [standing] -/)
    (h0 : 0 < f 0 /- [standing] -/) :
    ∃ x : ℝ, x < 0 ∧ f x < 0 := by
  by_contra hn
  have hnn : ∀ x : ℝ, x ≤ 0 → 0 ≤ f x := by
    intro x hx
    by_cases hz : x = 0
    · simpa [hz] using h0.le
    · exact le_of_not_gt (fun hn' => hn ⟨x, lt_of_le_of_ne hx hz, hn'⟩)
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hga : AntitoneOn g (Iic 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0) hgc.continuousOn
      (fun x _ => (hg x).hasDerivWithinAt)
    intro x hx
    have hx0 : x ≤ 0 := (show x ∈ Iic (0 : ℝ) from interior_subset hx)
    exact mul_nonpos_of_nonpos_of_nonneg hx0 (hnn x hx0)
  have hgn : ∀ x : ℝ, x ≤ 0 → g x ≤ 0 := by
    intro x hx
    by_contra hp
    have hd : 0 < g x := lt_of_not_ge hp
    let y := x - (f x + 1) / g x
    have hyx : y ≤ x := by
      dsimp [y]
      have hquot : 0 ≤ (f x + 1) / g x := div_nonneg (by linarith [hnn x hx]) hd.le
      linarith
    have hm : MonotoneOn (fun z : ℝ => f z - g x * z) (Iic x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic x)
        (hc.sub (continuous_const.mul continuous_id)).continuousOn
        (fun z _ => ((hf z).sub ((hasDerivAt_id z).const_mul (g x))).hasDerivWithinAt)
      intro z hz
      have hzx : z ≤ x := (show z ∈ Iic x from interior_subset hz)
      have := hga (hzx.trans hx) hx hzx
      linarith
    have hi := hm hyx (le_refl x) hyx
    have he : g x * ((f x + 1) / g x) = f x + 1 := by
      field_simp
    have hnny := hnn y (hyx.trans hx)
    dsimp [y] at hi hnny
    nlinarith
  have hfa : AntitoneOn f (Iic 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0) hc.continuousOn
      (fun x _ => (hf x).hasDerivWithinAt)
    exact fun x hx => hgn x (show x ∈ Iic (0 : ℝ) from interior_subset hx)
  have hl : ∀ x : ℝ, x ≤ 0 → f 0 ≤ f x :=
    fun x hx => hfa hx (show (0 : ℝ) ∈ Iic 0 from by simp) hx
  have hqa : AntitoneOn (fun x : ℝ => g x + f 0 * x) (Iic (-1)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic (-1))
      (hgc.add (continuous_const.mul continuous_id)).continuousOn
      (fun x _ => ((hg x).add ((hasDerivAt_id x).const_mul (f 0))).hasDerivWithinAt)
    intro x hx
    have hx1 : x ≤ -1 := (show x ∈ Iic (-1 : ℝ) from interior_subset hx)
    have hx0 : x ≤ 0 := by linarith
    have hff := hl x hx0
    have hprod := mul_le_mul_of_nonpos_left hff hx0
    nlinarith
  let y := -1 - (|g (-1)| + 1) / f 0
  have hy1 : y ≤ -1 := by
    dsimp [y]
    have hquot : 0 ≤ (|g (-1)| + 1) / f 0 := div_nonneg (by linarith [abs_nonneg (g (-1))]) h0.le
    linarith
  have hi := hqa hy1 (show (-1 : ℝ) ∈ Iic (-1) from by simp) hy1
  have hy0 : y ≤ 0 := by linarith
  have hyn := hgn y hy0
  have he : f 0 * ((|g (-1)| + 1) / f 0) = |g (-1)| + 1 := by
    field_simp
  have ha := neg_abs_le (g (-1))
  dsimp [y] at hi hyn
  nlinarith



open MeasureTheory Set

theorem scaled_diagonal_integrable
    (f : ℝ → ℝ /- [definition] -/)
    (hf : Continuous f /- [standing] -/)
    (a c C : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/)
    (hb : ∀ u : ℝ, c * a ≤ u → |f u| ≤ C * Real.exp (-u) /- [standing] -/ ) :
    Integrable (fun t : ℝ => f (c * (a + t)) * f (c * (a + t))) (volume.restrict (Ioi 0)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => f (c * (a + t)) ^ 2) (volume.restrict (Ioi 0)) :=
    (hf.comp (continuous_const.mul (continuous_const.add continuous_id))).pow 2
      |>.aestronglyMeasurable
  have hi : Integrable (fun t : ℝ => (C * Real.exp (-(c * a))) ^ 2 *
      Real.exp ((-2 * c) * t)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (by nlinarith : -2 * c < 0) 0).const_mul _
  have he : ∀ t : ℝ,
      (C * Real.exp (-(c * (a + t)))) ^ 2 =
      (C * Real.exp (-(c * a))) ^ 2 * Real.exp ((-2 * c) * t) := by
    intro t
    have hexp : Real.exp (-(c * (a + t))) ^ 2 =
        Real.exp (-(c * a)) ^ 2 * Real.exp ((-2 * c) * t) := by
      simp only [sq, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, mul_pow, hexp]
    ring
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ‖f (c * (a + t)) ^ 2‖ ≤
      (C * Real.exp (-(c * a))) ^ 2 * Real.exp ((-2 * c) * t) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have harg : c * a ≤ c * (a + t) := by nlinarith [show (0 : ℝ) < t from ht]
    have h := hb (c * (a + t)) harg
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc f (c * (a + t)) ^ 2 = |f (c * (a + t))| ^ 2 := (sq_abs _).symm
      _ ≤ (C * Real.exp (-(c * (a + t)))) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = _ := he t
  simpa [sq] using hi.mono' hm hbound




open MeasureTheory Set

/-- The all-binder Airy ODE instance used by the obstruction is nondegenerate. -/
theorem Ai_ODE_joint_probe :
    (∀ x : ℝ, HasDerivAt RMTFoundations.Airy.airyAiReal (deriv RMTFoundations.Airy.airyAiReal x) x) ∧
    (∀ x : ℝ, HasDerivAt (deriv RMTFoundations.Airy.airyAiReal) (x * RMTFoundations.Airy.airyAiReal x) x) ∧
    0 < RMTFoundations.Airy.airyAiReal 0 ∧ RMTFoundations.Airy.airyAiReal 1 ≠ 0 := by
  have hf : ∀ x : ℝ, HasDerivAt RMTFoundations.Airy.airyAiReal (deriv RMTFoundations.Airy.airyAiReal x) x :=
    fun x => (hasDerivAt_airyAiReal x).differentiableAt.hasDerivAt
  have hg : ∀ x : ℝ, HasDerivAt (deriv RMTFoundations.Airy.airyAiReal) (x * RMTFoundations.Airy.airyAiReal x) x := by
    intro x
    have he : deriv (deriv RMTFoundations.Airy.airyAiReal) x = x * RMTFoundations.Airy.airyAiReal x := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one] using RMTFoundations.AiryBounds.Ai_ODE x
    simpa [he] using (hasDerivAt_deriv_airyAiReal x).differentiableAt.hasDerivAt
  exact ⟨hf, hg, airyAiReal_zero_pos, (airyAiReal_pos_of_nonneg zero_le_one).ne'⟩

/-- A certified negative Airy value, with no oscillation/asymptotics assumption. -/
theorem Ai_negative_witness : ∃ a : ℝ, a < 0 ∧ RMTFoundations.Airy.airyAiReal a < 0 :=
  airy_solution_negative_witness RMTFoundations.Airy.airyAiReal (deriv RMTFoundations.Airy.airyAiReal)
    Ai_ODE_joint_probe.1 Ai_ODE_joint_probe.2.1 Ai_ODE_joint_probe.2.2.1

/-- The diagonal half-line product is an ordinary absolutely convergent integral. -/
theorem Ai_scaled_diagonal_integrable
    (a c : ℝ /- [definition] -/)
    (hc : 0 < c /- [standing] -/) :
    Integrable (fun t : ℝ => RMTFoundations.Airy.airyAiReal (c * (a + t)) * RMTFoundations.Airy.airyAiReal (c * (a + t))) RMTFoundations.Airy.halfLineMeasure := by
  obtain ⟨C, _, hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound (c * a)
  exact scaled_diagonal_integrable RMTFoundations.Airy.airyAiReal RMTFoundations.AiryBounds.Ai_continuous a c C hc hb

/-- The requested unshifted half-line convolution identity fails on the diagonal. -/
theorem Ai_halfline_convolution_counterexample :
    ∃ x : ℝ, x < 0 ∧
      RMTFoundations.Airy.airyAiReal (x + x) ≠ (2 : ℝ) ^ (1 / 3 : ℝ) *
        ∫ t, RMTFoundations.Airy.airyAiReal ((2 : ℝ) ^ (1 / 3 : ℝ) * (x + t)) *
          RMTFoundations.Airy.airyAiReal ((2 : ℝ) ^ (1 / 3 : ℝ) * (x + t)) ∂ RMTFoundations.Airy.halfLineMeasure := by
  obtain ⟨a, ha, hneg⟩ := Ai_negative_witness
  refine ⟨a / 2, by linarith, ?_⟩
  have hleft : RMTFoundations.Airy.airyAiReal (a / 2 + a / 2) < 0 := by
    convert hneg using 1 <;> ring
  have hright : 0 ≤ (2 : ℝ) ^ (1 / 3 : ℝ) *
      ∫ t, RMTFoundations.Airy.airyAiReal ((2 : ℝ) ^ (1 / 3 : ℝ) * (a / 2 + t)) *
        RMTFoundations.Airy.airyAiReal ((2 : ℝ) ^ (1 / 3 : ℝ) * (a / 2 + t)) ∂ RMTFoundations.Airy.halfLineMeasure :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (integral_nonneg fun t => mul_self_nonneg _)
  exact ne_of_lt (hleft.trans_le hright)

/-- Splitting the shift between the two factors also fails at x = y = 1. -/
theorem Ai_shifted_halfline_convolution_counterexample :
    ∃ s : ℝ, s < -2 ∧
      RMTFoundations.Airy.airyAiReal (1 + 1 + s) ≠ (2 : ℝ) ^ (1 / 3 : ℝ) *
        ∫ t, RMTFoundations.Airy.airyAiReal ((2 : ℝ) ^ (1 / 3 : ℝ) * (1 + t + s / 2)) *
          RMTFoundations.Airy.airyAiReal ((2 : ℝ) ^ (1 / 3 : ℝ) * (1 + t + s / 2)) ∂ RMTFoundations.Airy.halfLineMeasure := by
  obtain ⟨a, ha, hneg⟩ := Ai_negative_witness
  refine ⟨a - 2, by linarith, ?_⟩
  have hleft : RMTFoundations.Airy.airyAiReal (1 + 1 + (a - 2)) < 0 := by
    convert hneg using 1 <;> ring
  have hright : 0 ≤ (2 : ℝ) ^ (1 / 3 : ℝ) *
      ∫ t, RMTFoundations.Airy.airyAiReal ((2 : ℝ) ^ (1 / 3 : ℝ) * (1 + t + (a - 2) / 2)) *
        RMTFoundations.Airy.airyAiReal ((2 : ℝ) ^ (1 / 3 : ℝ) * (1 + t + (a - 2) / 2)) ∂ RMTFoundations.Airy.halfLineMeasure :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (integral_nonneg fun t => mul_self_nonneg _)
  exact ne_of_lt (hleft.trans_le hright)

open scoped InnerProductSpace
open InnerProductSpace


/-- Hadamard inequality, specialized from the pinned Gram--Schmidt API. -/
theorem coordinate_det_bound
    (n : ℕ /- [definition] -/ )
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))  /- [definition] -/ )
    (v : Fin n → EuclideanSpace ℝ (Fin n)  /- [definition] -/ )
    : |b.toBasis.det v| ≤ ∏ i, ‖v i‖ := by
  classical
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) :=
    Module.finrank_eq_card_basis b.toBasis
  let e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    gramSchmidtOrthonormalBasis hd v
  have heq : b.toBasis.det v = b.toBasis.det e * e.toBasis.det v := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det e.toBasis]
    rfl
  rw [← Real.norm_eq_abs, heq, norm_mul, b.det_to_matrix_orthonormalBasis,
    one_mul, gramSchmidtOrthonormalBasis_det hd v, norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i hi
  simpa only [e.orthonormal.norm_eq_one i, one_mul] using
    norm_inner_le_norm (e i) (v i)

/-- Entrywise bounded real matrices satisfy the sharp Hadamard growth estimate. -/
theorem uniform_matrix_det_bound
    (n : ℕ /- [definition] -/ )
    (M : Matrix (Fin n) (Fin n) ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (hM : ∀ i j, |M i j| ≤ C /- [standing] -/ )
    : |M.det| ≤ (Real.sqrt (n : ℝ) * C) ^ n := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (M i)
  have hv : b.toBasis.toMatrix v = M.transpose := by
    ext i j
    rfl
  have hb := coordinate_det_bound n b v
  rw [Module.Basis.det_apply, hv, Matrix.det_transpose] at hb
  calc
    |M.det| ≤ ∏ i, ‖v i‖ := hb
    _ ≤ ∏ i : Fin n, (Real.sqrt (n : ℝ) * C) := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i hi
      rw [EuclideanSpace.norm_eq]
      have hs : (∑ j : Fin n, ‖v i j‖ ^ 2) ≤ (n : ℝ) * C ^ 2 := by
        calc
          (∑ j : Fin n, ‖v i j‖ ^ 2) ≤ ∑ j : Fin n, C ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            simpa only [Real.norm_eq_abs] using
              (sq_le_sq₀ (abs_nonneg (M i j)) hC).mpr (hM i j)
          _ = (n : ℝ) * C ^ 2 := by simp
      calc
        Real.sqrt (∑ j : Fin n, ‖v i j‖ ^ 2) ≤ Real.sqrt ((n : ℝ) * C ^ 2) :=
          Real.sqrt_le_sqrt hs
        _ = Real.sqrt (n : ℝ) * C := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hC]
    _ = (Real.sqrt (n : ℝ) * C) ^ n := by simp

/-- The separable weighted Hadamard estimate, including zero weights. -/
theorem weighted_matrix_det_bound
    (n : ℕ /- [definition] -/ )
    (M : Matrix (Fin n) (Fin n) ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (a : Fin n → ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha : ∀ i, 0 ≤ a i /- [standing] -/ )
    (hM : ∀ i j, |M i j| ≤ C * a i * a j /- [standing] -/ )
    : |M.det| ≤ (Real.sqrt (n : ℝ) * C) ^ n * ∏ i, (a i) ^ 2 := by
  classical
  let N : Matrix (Fin n) (Fin n) ℝ := fun i j => M i j / (a i * a j)
  have hf : ∀ i j, a i * (a j * N i j) = M i j := by
    intro i j
    by_cases hz : a i * a j = 0
    · have hm : M i j = 0 := by
        apply abs_eq_zero.mp
        apply le_antisymm _ (abs_nonneg _)
        have hh := hM i j
        rw [mul_assoc, hz, mul_zero] at hh
        exact hh
      simp [N, hz, hm]
    · dsimp [N]
      rw [← mul_assoc, mul_div_cancel₀ _ hz]
  have hN : ∀ i j, |N i j| ≤ C := by
    intro i j
    by_cases hz : a i * a j = 0
    · simp [N, hz, hC]
    · have hp : 0 < a i * a j :=
        lt_of_le_of_ne (mul_nonneg (ha i) (ha j)) (Ne.symm hz)
      dsimp [N]
      rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
      simpa only [mul_assoc] using hM i j
  have hfac : M = Matrix.of (fun i j => a i * (a j * N i j)) := by
    ext i j
    exact (hf i j).symm
  have hdet : M.det = (∏ i, a i) * ((∏ i, a i) * N.det) := by
    calc
      M.det = (Matrix.of (fun i j : Fin n => a i * (a j * N i j))).det :=
        congrArg Matrix.det hfac
      _ = (∏ i, a i) * (Matrix.of (fun i j : Fin n => a j * N i j)).det :=
        Matrix.det_mul_column a (Matrix.of (fun i j : Fin n => a j * N i j))
      _ = (∏ i, a i) * ((∏ i, a i) * N.det) :=
        congrArg (fun r : ℝ => (∏ i, a i) * r) (Matrix.det_mul_row a N)
  have hp : 0 ≤ ∏ i, a i := Finset.prod_nonneg (fun i _ => ha i)
  rw [hdet]
  simp only [abs_mul, abs_of_nonneg hp]
  calc
    (∏ i, a i) * ((∏ i, a i) * |N.det|) ≤
        (∏ i, a i) * ((∏ i, a i) * (Real.sqrt (n : ℝ) * C) ^ n) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (uniform_matrix_det_bound n N C hC hN) hp) hp
    _ = (Real.sqrt (n : ℝ) * C) ^ n * ∏ i, (a i) ^ 2 := by
      rw [Finset.prod_pow]
      ring

/-- Square-root form of the Hadamard constant used by Fredholm coefficient bounds. -/
theorem weighted_matrix_det_bound_sqrt
    (n : ℕ /- [definition] -/ )
    (M : Matrix (Fin n) (Fin n) ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (a : Fin n → ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha : ∀ i, 0 ≤ a i /- [standing] -/ )
    (hM : ∀ i j, |M i j| ≤ C * a i * a j /- [standing] -/ )
    : |M.det| ≤ Real.sqrt ((n : ℝ) ^ n) * C ^ n * ∏ i, (a i) ^ 2 := by
  have hs : ∀ m : ℕ, Real.sqrt ((n : ℝ) ^ m) = Real.sqrt (n : ℝ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg n) m), ih, pow_succ]
  simpa only [mul_pow, hs n] using weighted_matrix_det_bound n M C a hC ha hM

/-- Fredholm minor bound for any pointwise dominated real kernel. -/
theorem weighted_kernel_minor_bound
    {X : Type* /- [definition] -/ }
    (n : ℕ /- [definition] -/ )
    (k : X → X → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (a : X → ℝ /- [definition] -/ )
    (x : Fin n → X /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha : ∀ u, 0 ≤ a u /- [standing] -/ )
    (hk : ∀ u v, |k u v| ≤ C * a u * a v /- [standing] -/ )
    : |(Matrix.of (fun i j => k (x i) (x j))).det| ≤
        Real.sqrt ((n : ℝ) ^ n) * C ^ n * ∏ i, (a (x i)) ^ 2 := by
  exact weighted_matrix_det_bound_sqrt n _ C (fun i => a (x i)) hC
    (fun i => ha (x i)) (fun i j => hk (x i) (x j))

/-- The same kernel estimate in the product-power form. -/
theorem weighted_kernel_minor_bound_pow
    {X : Type* /- [definition] -/ }
    (n : ℕ /- [definition] -/ )
    (k : X → X → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (a : X → ℝ /- [definition] -/ )
    (x : Fin n → X /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha : ∀ u, 0 ≤ a u /- [standing] -/ )
    (hk : ∀ u v, |k u v| ≤ C * a u * a v /- [standing] -/ )
    : |(Matrix.of (fun i j => k (x i) (x j))).det| ≤
        (Real.sqrt (n : ℝ) * C) ^ n * ∏ i, (a (x i)) ^ 2 := by
  exact weighted_matrix_det_bound n _ C (fun i => a (x i)) hC
    (fun i => ha (x i)) (fun i j => hk (x i) (x j))

/-- The weighted hypotheses have a jointly satisfiable, positive-dimensional instance. -/
theorem weighted_matrix_joint_probe
    : ∃ M : Matrix (Fin 1) (Fin 1) ℝ,
        (∀ i j, |M i j| ≤ (1 : ℝ) * 1 * 1) ∧ M.det ≠ 0 := by
  refine ⟨1, ?_, ?_⟩
  · intro i j
    simp [Matrix.one_apply, Subsingleton.elim i j]
  · simp

/-- A nondegenerate witness for all weighted-matrix binders simultaneously. -/
theorem weighted_matrix_all_binder_probe
    : ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) (a : Fin n → ℝ),
        0 < n ∧ 0 < C ∧ (∀ i, 0 < a i) ∧
        (∀ i j, |M i j| ≤ C * a i * a j) ∧ M.det ≠ 0 := by
  refine ⟨2, 1, 1, fun _ => 1, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro i
    norm_num
  · intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · simp



open Filter Topology MeasureTheory

noncomputable def kernelSeries
    (c : ℕ → ℂ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : ℂ := ∑' n, c n * z ^ n

noncomputable def hadamardMajorant
    (M : ℝ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℝ := (Real.sqrt n * M) ^ n / (n.factorial : ℝ)

theorem stirling_simple_lower
    (n : ℕ /- [definition] -/ )
    : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hp : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    apply Real.le_sqrt_of_sq_le
    have := Real.one_le_pi_div_two
    nlinarith
  exact le_trans (le_mul_of_one_le_left (by positivity) hp) (Stirling.le_factorial_stirling n)

theorem hadamardMajorant_le_geometric
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    (hn : 0 < n /- [standing] -/ )
    : hadamardMajorant M n ≤ (Real.exp 1 * M / Real.sqrt n) ^ n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnr
  calc
    hadamardMajorant M n ≤ (Real.sqrt n * M) ^ n / ((n : ℝ) / Real.exp 1) ^ n := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (stirling_simple_lower n)
    _ = (Real.exp 1 * M / Real.sqrt n) ^ n := by
      rw [← div_pow]
      congr 1
      have hs2 := Real.sq_sqrt (le_of_lt hnr)
      field_simp
      nlinarith

theorem hadamardMajorant_summable
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    : Summable (hadamardMajorant M) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((2 * Real.exp 1 * M) ^ 2 + 1)
  apply Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnr : ((2 * Real.exp 1 * M) ^ 2 + 1 : ℝ) ≤ n :=
    hN.trans (by exact_mod_cast hn)
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by nlinarith [sq_nonneg (2 * Real.exp 1 * M)])
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  have hsq : 2 * Real.exp 1 * M ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ hadamardMajorant M n by unfold hadamardMajorant; positivity)]
  exact (hadamardMajorant_le_geometric M hM n hn0).trans
    (pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hs).2 (by nlinarith)) n)

theorem hadamard_weight_summable
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ hadamardMajorant M n /- [standing] -/ )
    (R : ℝ /- [definition] -/ )
    (hR : 0 ≤ R /- [standing] -/ )
    : Summable (fun n => ‖c n‖ * R ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hadamardMajorant_summable (M * R) (mul_nonneg hM hR))
  calc
    ‖c n‖ * R ^ n ≤ hadamardMajorant M n * R ^ n :=
      mul_le_mul_of_nonneg_right (hc n) (pow_nonneg hR n)
    _ = hadamardMajorant (M * R) n := by unfold hadamardMajorant; simp only [mul_pow]; ring

theorem kernelSeries_absolute
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ hadamardMajorant M n /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun n => ‖c n * z ^ n‖) := by
  simpa only [norm_mul, norm_pow] using hadamard_weight_summable c M hM hc ‖z‖ (norm_nonneg z)

theorem kernelSeries_entire
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ hadamardMajorant M n /- [standing] -/ )
    : AnalyticOnNhd ℂ (kernelSeries c) Set.univ := by
  have hr : (FormalMultilinearSeries.ofScalars ℂ c).radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
    intro R
    simpa only [FormalMultilinearSeries.ofScalars_norm] using
      hadamard_weight_summable c M hM hc R R.coe_nonneg
  have h := (FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall
    (by rw [hr]; exact ENNReal.zero_lt_top)
  have heq : (FormalMultilinearSeries.ofScalars ℂ c).sum = kernelSeries c := by
    ext z
    exact FormalMultilinearSeries.ofScalars_sum_eq c z
  rw [heq] at h
  simpa only [hr, Metric.eball_top] using h.analyticOnNhd

theorem kernelSeries_family_continuous
    {X : Type* /- [definition] -/ }
    [TopologicalSpace X /- [definition] -/ ]
    (c : X → ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ x n, ‖c x n‖ ≤ hadamardMajorant M n /- [standing] -/ )
    (hcont : ∀ n, Continuous (fun x => c x n)  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Continuous (fun x => kernelSeries (c x) z) := by
  apply continuous_tsum (fun n => (hcont n).mul continuous_const)
    (hadamardMajorant_summable (M * ‖z‖) (by positivity))
  intro n x
  change ‖c x n * z ^ n‖ ≤ hadamardMajorant (M * ‖z‖) n
  rw [norm_mul, norm_pow]
  calc
    ‖c x n‖ * ‖z‖ ^ n ≤ hadamardMajorant M n * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right (hc x n) (by positivity)
    _ = hadamardMajorant (M * ‖z‖) n := by unfold hadamardMajorant; simp only [mul_pow]; ring

noncomputable def kernelMinor
    {α : Type* /- [definition] -/ }
    (k : α → α → ℝ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    (x : Fin n → α /- [definition] -/ )
    : ℝ := Matrix.det (fun i j => k (x i) (x j))

noncomputable def kernelCoefficient
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    (k : α → α → ℝ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : ℝ := (∫ x, kernelMinor k n x ∂Measure.pi (fun _ => μ)) / (n.factorial : ℝ)

noncomputable def kernelFredholm
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    (k : α → α → ℝ /- [definition] -/ )
    (z : ℂ /- [definition] -/ )
    : ℂ := kernelSeries (fun n => (kernelCoefficient μ k n : ℂ)) z

theorem kernelMinor_measurable
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/ )
    (hk : Measurable (Function.uncurry k)  /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : Measurable (kernelMinor k n) := by
  change Measurable (fun x : Fin n → α =>
    Matrix.det (Matrix.of (fun i j => k (x i) (x j))))
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  apply Finset.measurable_sum
  intro σ hσ
  apply measurable_const.mul
  apply Finset.measurable_prod
  intro i hi
  have hp : Measurable (fun x : Fin n → α => (x (σ i), x i)) :=
    (measurable_pi_apply (σ i)).prodMk (measurable_pi_apply i)
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using hk.comp hp

theorem kernelCoefficient_bound_of_minor_bound
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hdet : ∀ n x, |kernelMinor k n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : ‖(kernelCoefficient μ k n : ℂ)‖ ≤
      hadamardMajorant (C * ∫ x, a x ^ 2 ∂μ) n := by
  have hi : Integrable (fun x : Fin n → α => ∏ i, a (x i) ^ 2)
      (Measure.pi (fun _ => μ)) := Integrable.fintype_prod (fun _ => ha2)
  have hh := norm_integral_le_of_norm_le (f := kernelMinor k n) (hi.const_mul ((Real.sqrt n * C) ^ n))
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hdet n x))
  rw [integral_const_mul, integral_fintype_prod_eq_pow (fun x => a x ^ 2)] at hh
  have hf : (0 : ℝ) ≤ n.factorial := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold kernelCoefficient
  rw [abs_div, abs_of_nonneg hf]
  calc
    _ ≤ ((Real.sqrt n * C) ^ n * (∫ x, a x ^ 2 ∂μ) ^ n) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs, Fintype.card_fin] using hh) hf
    _ = hadamardMajorant (C * ∫ x, a x ^ 2 ∂μ) n := by
      unfold hadamardMajorant
      rw [← mul_pow]
      congr 2
      ring

theorem kernelFredholm_entire_of_minor_bound
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hdet : ∀ n x, |kernelMinor k n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    : AnalyticOnNhd ℂ (kernelFredholm μ k) Set.univ := by
  exact kernelSeries_entire _ _ (mul_nonneg hC (integral_nonneg (fun x => sq_nonneg _)))
    (kernelCoefficient_bound_of_minor_bound μ k a C hC ha2 hdet)


theorem kernelMinor_continuousAt
    {X α : Type* /- [definition] -/ }
    [TopologicalSpace X /- [definition] -/ ]
    (k : X → α → α → ℝ /- [definition] -/ )
    (p : X /- [definition] -/ )
    (hk : ∀ x y, ContinuousAt (fun t => k t x y) p /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    (x : Fin n → α /- [definition] -/ )
    : ContinuousAt (fun t => kernelMinor (k t) n x) p := by
  exact (continuous_id : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M)).matrix_det.continuousAt.comp
    (continuousAt_pi.2 (fun i => continuousAt_pi.2 (fun j => hk (x i) (x j))))

theorem kernelCoefficient_continuousAt_of_minor_bound
    {X α : Type* /- [definition] -/ }
    [TopologicalSpace X /- [definition] -/ ]
    [MeasurableSpace α /- [definition] -/ ]
    [FirstCountableTopology X /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : X → α → α → ℝ /- [definition] -/ )
    (p : X /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hm : ∀ᶠ t in 𝓝 p, Measurable (Function.uncurry (k t))  /- [standing] -/ )
    (hb : ∀ᶠ t in 𝓝 p, ∀ n x, |kernelMinor (k t) n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    (hcont : ∀ x y, ContinuousAt (fun t => k t x y) p /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : ContinuousAt (fun t => kernelCoefficient μ (k t) n) p := by
  have hi : Integrable (fun x : Fin n → α => ∏ i, a (x i) ^ 2)
      (Measure.pi (fun _ => μ)) := Integrable.fintype_prod (fun _ => ha2)
  have hc : ContinuousAt (fun t => ∫ x, kernelMinor (k t) n x
      ∂Measure.pi (fun _ => μ)) p := by
    apply MeasureTheory.continuousAt_of_dominated
      (bound := fun x => (Real.sqrt n * C)^n * ∏ i, a (x i)^2)
    · exact hm.mono (fun t ht => (kernelMinor_measurable (k t) ht n).aestronglyMeasurable)
    · exact hb.mono (fun t ht => ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs] using ht n x))
    · exact hi.const_mul _
    · exact ae_of_all _ (kernelMinor_continuousAt k p hcont n)
  exact hc.div_const _

theorem kernelSeries_family_continuousAt
    {X : Type* /- [definition] -/ }
    [TopologicalSpace X /- [definition] -/ ]
    (c : X → ℕ → ℂ /- [definition] -/ )
    (p : X /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ᶠ t in 𝓝 p, ∀ n, ‖c t n‖ ≤ hadamardMajorant M n /- [standing] -/ )
    (hcont : ∀ n, ContinuousAt (fun t => c t n) p /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : ContinuousAt (fun t => kernelSeries (c t) z) p := by
  apply tendsto_tsum_of_dominated_convergence
    (hadamardMajorant_summable (M * ‖z‖) (by positivity))
    (fun n => (hcont n).mul tendsto_const_nhds)
  filter_upwards [hc] with t ht
  intro n
  change ‖c t n * z ^ n‖ ≤ hadamardMajorant (M * ‖z‖) n
  rw [norm_mul, norm_pow]
  calc
    ‖c t n‖ * ‖z‖ ^ n ≤ hadamardMajorant M n * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right (ht n) (by positivity)
    _ = hadamardMajorant (M * ‖z‖) n := by unfold hadamardMajorant; simp only [mul_pow]; ring

theorem kernelFredholm_continuousAt_of_minor_bound
    {X α : Type* /- [definition] -/ }
    [TopologicalSpace X /- [definition] -/ ]
    [MeasurableSpace α /- [definition] -/ ]
    [FirstCountableTopology X /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : X → α → α → ℝ /- [definition] -/ )
    (p : X /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hm : ∀ᶠ t in 𝓝 p, Measurable (Function.uncurry (k t))  /- [standing] -/ )
    (hb : ∀ᶠ t in 𝓝 p, ∀ n x, |kernelMinor (k t) n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    (hcont : ∀ x y, ContinuousAt (fun t => k t x y) p /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : ContinuousAt (fun t => kernelFredholm μ (k t) z) p := by
  apply kernelSeries_family_continuousAt _ p (C * ∫ x, a x ^ 2 ∂μ)
    (mul_nonneg hC (integral_nonneg (fun x => sq_nonneg _)))
  · exact hb.mono (fun t ht => kernelCoefficient_bound_of_minor_bound μ (k t) a C hC ha2 ht)
  · intro n
    exact Complex.continuous_ofReal.continuousAt.comp
      (kernelCoefficient_continuousAt_of_minor_bound μ k p a C ha2 hm hb hcont n)

theorem kernel_data_joint_inhabitation
    : ∃ (k : Bool → Bool → ℝ) (a : Bool → ℝ) (C : ℝ),
      0 < C ∧ (∀ x, 0 < a x) ∧ Integrable a Measure.count ∧
      Integrable (fun x => a x ^ 2) Measure.count ∧
      Measurable (Function.uncurry k) ∧
      (∀ x y, |k x y| ≤ C * a x * a y) ∧ k true true = 1 := by
  refine ⟨fun _ _ => 1, fun _ => 1, 1, by norm_num, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro x
    norm_num
  · exact integrable_const 1
  · simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Bool => (1 : ℝ)) Measure.count)
  · exact measurable_const
  · intro x y
    norm_num


theorem kernelCoefficient_congr_ae
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    (k l : α → α → ℝ /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    (h : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), kernelMinor k n x = kernelMinor l n x /- [standing] -/ )
    : kernelCoefficient μ k n = kernelCoefficient μ l n := by
  unfold kernelCoefficient
  rw [integral_congr_ae h]

theorem kernelCoefficient_congr_on_full_measure
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k l : α → α → ℝ /- [definition] -/ )
    (S : Set α /- [definition] -/ )
    (hS : ∀ᵐ x ∂μ, x ∈ S /- [standing] -/ )
    (hkl : ∀ x ∈ S, ∀ y ∈ S, k x y = l x y /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : kernelCoefficient μ k n = kernelCoefficient μ l n := by
  apply kernelCoefficient_congr_ae μ k l n
  have hs : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ i, x i ∈ S :=
    eventually_all.2 (fun i => Measure.tendsto_eval_ae_ae.eventually hS)
  filter_upwards [hs] with x hx
  unfold kernelMinor
  congr 1
  funext i j
  exact hkl (x i) (hx i) (x j) (hx j)


theorem kernelMinor_integrable_of_minor_bound
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hk : Measurable (Function.uncurry k)  /- [standing] -/ )
    (hdet : ∀ n x, |kernelMinor k n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : Integrable (kernelMinor k n) (Measure.pi (fun _ => μ)) := by
  have hi : Integrable (fun x : Fin n → α => ∏ i, a (x i) ^ 2)
      (Measure.pi (fun _ => μ)) := Integrable.fintype_prod (fun _ => ha2)
  exact (hi.const_mul ((Real.sqrt n * C) ^ n)).mono'
    (kernelMinor_measurable k hk n).aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hdet n x))

theorem kernelFredholm_absolute_of_minor_bound
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hdet : ∀ n x, |kernelMinor k n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Summable (fun n => ‖(kernelCoefficient μ k n : ℂ) * z ^ n‖) := by
  exact kernelSeries_absolute _ _
    (mul_nonneg hC (integral_nonneg (fun x => sq_nonneg _)))
    (kernelCoefficient_bound_of_minor_bound μ k a C hC ha2 hdet) z

theorem kernelFredholm_hasSum_of_minor_bound
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hdet : ∀ n x, |kernelMinor k n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : HasSum (fun n => (kernelCoefficient μ k n : ℂ) * z ^ n) (kernelFredholm μ k z) := by
  exact (kernelFredholm_absolute_of_minor_bound μ k a C hC ha2 hdet z).of_norm.hasSum


theorem hadamard_coefficients_joint_inhabitation
    : ∃ c : ℕ → ℂ, c 0 = 1 ∧ c 1 = 1 ∧
      (∀ n, ‖c n‖ ≤ hadamardMajorant 1 n) := by
  refine ⟨fun n => if n ≤ 1 then 1 else 0, by simp, by simp, ?_⟩
  intro n
  rcases n with _ | n
  · simp [hadamardMajorant]
  rcases n with _ | n
  · simp [hadamardMajorant]
  · simp only [show ¬n + 1 + 1 ≤ 1 by omega, if_false, norm_zero]
    unfold hadamardMajorant
    positivity


theorem kernelFredholm_congr_on_full_measure
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k l : α → α → ℝ /- [definition] -/ )
    (S : Set α /- [definition] -/ )
    (hS : ∀ᵐ x ∂μ, x ∈ S /- [standing] -/ )
    (hkl : ∀ x ∈ S, ∀ y ∈ S, k x y = l x y /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : kernelFredholm μ k z = kernelFredholm μ l z := by
  unfold kernelFredholm kernelSeries
  apply tsum_congr
  intro n
  change (kernelCoefficient μ k n : ℂ) * z ^ n = (kernelCoefficient μ l n : ℂ) * z ^ n
  rw [kernelCoefficient_congr_on_full_measure μ k l S hS hkl n]


theorem kernelFredholm_real_coupling
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    (k : α → α → ℝ /- [definition] -/ )
    (z : ℝ /- [definition] -/ )
    : kernelFredholm μ k (z : ℂ) =
      ((∑' n, kernelCoefficient μ k n * z ^ n : ℝ) : ℂ) := by
  unfold kernelFredholm kernelSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]


theorem kernelMinor_tendsto
    {I α : Type* /- [definition] -/ }
    (l : Filter I /- [definition] -/ )
    (k : I → α → α → ℝ /- [definition] -/ )
    (k0 : α → α → ℝ /- [definition] -/ )
    (hk : ∀ x y, Tendsto (fun t => k t x y) l (𝓝 (k0 x y))  /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    (x : Fin n → α /- [definition] -/ )
    : Tendsto (fun t => kernelMinor (k t) n x) l (𝓝 (kernelMinor k0 n x)) := by
  exact (continuous_id : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M)).matrix_det.continuousAt.tendsto.comp
    (tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => hk (x i) (x j))))

theorem kernelCoefficient_tendsto_of_minor_bound
    {I α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (l : Filter I /- [definition] -/ )
    [l.IsCountablyGenerated /- [definition] -/ ]
    (k : I → α → α → ℝ /- [definition] -/ )
    (k0 : α → α → ℝ /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hm : ∀ᶠ t in l, Measurable (Function.uncurry (k t))  /- [standing] -/ )
    (hb : ∀ᶠ t in l, ∀ n x, |kernelMinor (k t) n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    (hlim : ∀ x y, Tendsto (fun t => k t x y) l (𝓝 (k0 x y))  /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : Tendsto (fun t => kernelCoefficient μ (k t) n) l (𝓝 (kernelCoefficient μ k0 n)) := by
  have hi : Integrable (fun x : Fin n → α => ∏ i, a (x i) ^ 2)
      (Measure.pi (fun _ => μ)) := Integrable.fintype_prod (fun _ => ha2)
  have hc : Tendsto (fun t => ∫ x, kernelMinor (k t) n x
      ∂Measure.pi (fun _ => μ)) l (𝓝 (∫ x, kernelMinor k0 n x ∂Measure.pi (fun _ => μ))) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => (Real.sqrt n * C)^n * ∏ i, a (x i)^2)
    · exact hm.mono (fun t ht => (kernelMinor_measurable (k t) ht n).aestronglyMeasurable)
    · exact hb.mono (fun t ht => ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs] using ht n x))
    · exact hi.const_mul _
    · exact ae_of_all _ (kernelMinor_tendsto l k k0 hlim n)
  exact hc.div_const _

theorem kernelFredholm_tendsto_of_minor_bound
    {I α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (l : Filter I /- [definition] -/ )
    [l.IsCountablyGenerated /- [definition] -/ ]
    (k : I → α → α → ℝ /- [definition] -/ )
    (k0 : α → α → ℝ /- [definition] -/ )
    (a : α → ℝ /- [definition] -/ )
    (C : ℝ /- [definition] -/ )
    (hC : 0 ≤ C /- [standing] -/ )
    (ha2 : Integrable (fun x => a x ^ 2) μ /- [standing] -/ )
    (hm : ∀ᶠ t in l, Measurable (Function.uncurry (k t))  /- [standing] -/ )
    (hb : ∀ᶠ t in l, ∀ n x, |kernelMinor (k t) n x| ≤
      (Real.sqrt n * C) ^ n * ∏ i, a (x i) ^ 2 /- [standing] -/ )
    (hlim : ∀ x y, Tendsto (fun t => k t x y) l (𝓝 (k0 x y))  /- [standing] -/ )
    (z : ℂ /- [definition] -/ )
    : Tendsto (fun t => kernelFredholm μ (k t) z) l (𝓝 (kernelFredholm μ k0 z)) := by
  change Tendsto (fun t => ∑' n, (kernelCoefficient μ (k t) n : ℂ) * z ^ n) l
    (𝓝 (∑' n, (kernelCoefficient μ k0 n : ℂ) * z ^ n))
  apply tendsto_tsum_of_dominated_convergence
    (hadamardMajorant_summable ((C * ∫ x, a x ^ 2 ∂μ) * ‖z‖) (by
      exact mul_nonneg (mul_nonneg hC (integral_nonneg (fun x => sq_nonneg _))) (norm_nonneg _)))
  · intro n
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (kernelCoefficient_tendsto_of_minor_bound μ l k k0 a C ha2 hm hb hlim n)).mul tendsto_const_nhds
  · filter_upwards [hb] with t ht
    intro n
    change ‖(kernelCoefficient μ (k t) n : ℂ) * z ^ n‖ ≤
      hadamardMajorant ((C * ∫ x, a x ^ 2 ∂μ) * ‖z‖) n
    rw [norm_mul, norm_pow]
    calc
      _ ≤ hadamardMajorant (C * ∫ x, a x ^ 2 ∂μ) n * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right
          (kernelCoefficient_bound_of_minor_bound μ (k t) a C hC ha2 ht n) (by positivity)
      _ = _ := by unfold hadamardMajorant; simp only [mul_pow]; ring


theorem kernelMinor_congr_on_full_measure
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k l : α → α → ℝ /- [definition] -/ )
    (S : Set α /- [definition] -/ )
    (hS : ∀ᵐ x ∂μ, x ∈ S /- [standing] -/ )
    (hkl : ∀ x ∈ S, ∀ y ∈ S, k x y = l x y /- [standing] -/ )
    (n : ℕ /- [definition] -/ )
    : kernelMinor k n =ᵐ[Measure.pi (fun _ : Fin n => μ)] kernelMinor l n := by
  have hs : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ i, x i ∈ S :=
    eventually_all.2 (fun i => Measure.tendsto_eval_ae_ae.eventually hS)
  filter_upwards [hs] with x hx
  unfold kernelMinor
  congr 1
  funext i j
  exact hkl (x i) (hx i) (x j) (hx j)




/-- Uniform exponential domination on all positive quadrants with shift bounded below. -/
theorem Ai_kernel_exp_bound_uniform (a : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ s x y : ℝ, a ≤ s → 0 ≤ x → 0 ≤ y →
      |RMTFoundations.Airy.airyAiReal (x + y + s)| ≤ C * Real.exp (-x) * Real.exp (-y) := by
  obtain ⟨C, hC, hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound a
  refine ⟨C * Real.exp (-a), mul_pos hC (Real.exp_pos _), ?_⟩
  intro s x y hs hx hy
  calc |RMTFoundations.Airy.airyAiReal (x+y+s)| ≤ C * Real.exp (-(x+y+s)) := hb _ (by linarith)
    _ = C * Real.exp (-s) * Real.exp (-x) * Real.exp (-y) := by
      simp only [neg_add, Real.exp_add]; ring
    _ ≤ C * Real.exp (-a) * Real.exp (-x) * Real.exp (-y) := by
      gcongr

theorem Ai_kernel_exp_bound (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |RMTFoundations.Airy.airyAiReal (x+y+s)| ≤ C * Real.exp (-(x+y)) := by
  obtain ⟨C,hC,hb⟩ := Ai_kernel_exp_bound_uniform s
  refine ⟨C,hC,fun x y hx hy => ?_⟩
  simpa only [neg_add, Real.exp_add, mul_assoc] using hb s x y le_rfl hx hy

noncomputable def K_kernel (s : ℝ /- [definition] -/) (q : ℝ × ℝ /- [definition] -/) : ℝ :=
  RMTFoundations.Airy.airyKernelIntegral (q.1+s) (q.2+s)

lemma Ai_product_exp_bound (a C : ℝ /- [definition] -/)
    (hC : 0 ≤ C /- [standing] -/)
    (hb : ∀ u : ℝ, a ≤ u → |RMTFoundations.Airy.airyAiReal u| ≤ C * Real.exp (-u) /- [standing] -/ )
    (u v t : ℝ /- [definition] -/)
    (hu : a ≤ u /- [standing] -/) (hv : a ≤ v /- [standing] -/)
    (ht : 0 ≤ t /- [standing] -/) :
    ‖RMTFoundations.Airy.airyAiReal (u+t) * RMTFoundations.Airy.airyAiReal (v+t)‖ ≤
      (C^2 * Real.exp (-u) * Real.exp (-v)) * (Real.exp (-t))^2 := by
  rw [Real.norm_eq_abs, abs_mul]
  calc |RMTFoundations.Airy.airyAiReal (u+t)| * |RMTFoundations.Airy.airyAiReal (v+t)| ≤ (C * Real.exp (-(u+t))) * (C * Real.exp (-(v+t))) :=
      mul_le_mul (hb _ (by linarith)) (hb _ (by linarith)) (abs_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by simp only [neg_add, Real.exp_add]; ring

lemma Ai_product_integrable (u v : ℝ /- [definition] -/) :
    Integrable (fun t => RMTFoundations.Airy.airyAiReal (u+t) * RMTFoundations.Airy.airyAiReal (v+t)) RMTFoundations.Airy.halfLineMeasure := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound (min u v)
  apply ((RMTFoundations.AiryBounds.integrable_exp_square).const_mul (C^2 * Real.exp (-u) * Real.exp (-v))).mono'
  · exact ((RMTFoundations.AiryBounds.Ai_continuous.comp (continuous_const.add continuous_id)).mul
      (RMTFoundations.AiryBounds.Ai_continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    exact Ai_product_exp_bound (min u v) C hC.le hb u v t
      (min_le_left _ _) (min_le_right _ _) ht.le

lemma K_Ai_abs_le (a C : ℝ /- [definition] -/) (hC : 0 ≤ C /- [standing] -/)
    (hb : ∀ u : ℝ, a ≤ u → |RMTFoundations.Airy.airyAiReal u| ≤ C * Real.exp (-u) /- [standing] -/ )
    (u v : ℝ /- [definition] -/) (hu : a ≤ u /- [standing] -/)
    (hv : a ≤ v /- [standing] -/) :
    |RMTFoundations.Airy.airyKernelIntegral u v| ≤ (C^2 * Real.exp (-u) * Real.exp (-v)) *
      ∫ t, (Real.exp (-t))^2 ∂ RMTFoundations.Airy.halfLineMeasure := by
  rw [← Real.norm_eq_abs]
  unfold RMTFoundations.Airy.airyKernelIntegral
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae (Ai_product_integrable u v).norm
    (RMTFoundations.AiryBounds.integrable_exp_square.const_mul _)
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  exact Ai_product_exp_bound a C hC hb u v t hu hv ht.le

lemma K_Ai_symm (u v : ℝ /- [definition] -/) : RMTFoundations.Airy.airyKernelIntegral u v = RMTFoundations.Airy.airyKernelIntegral v u := by
  unfold RMTFoundations.Airy.airyKernelIntegral
  congr 1
  funext t
  exact mul_comm _ _

lemma Ai_product_kernel_identity (s x y : ℝ /- [definition] -/) :
    (∫ t, RMTFoundations.Airy.airyHankelShiftKernel s (x,t) * RMTFoundations.Airy.airyHankelShiftKernel s (t,y) ∂ RMTFoundations.Airy.halfLineMeasure) = K_kernel s (x,y) := by
  unfold K_kernel RMTFoundations.Airy.airyKernelIntegral RMTFoundations.Airy.airyHankelShiftKernel
  congr 1
  funext t
  congr 1 <;> ring

lemma integral_exp_square_le_one : (∫ t, (Real.exp (-t))^2 ∂ RMTFoundations.Airy.halfLineMeasure) ≤ 1 := by
  rw [← integral_exp_neg_Ioi_zero]
  apply integral_mono_ae RMTFoundations.AiryBounds.integrable_exp_square (integrableOn_exp_neg_Ioi (0:ℝ))
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [show 0 < t from ht])
  nlinarith [Real.exp_pos (-t)]

lemma K_Ai_continuous : Continuous (fun q : ℝ × ℝ => RMTFoundations.Airy.airyKernelIntegral q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q₀
  let a := min q₀.1 q₀.2 - 1
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound a
  have hlow : ∀ᶠ q : ℝ × ℝ in 𝓝 q₀, a ≤ q.1 ∧ a ≤ q.2 := by
    have h1 : a < q₀.1 := by dsimp [a]; linarith [min_le_left q₀.1 q₀.2]
    have h2 : a < q₀.2 := by dsimp [a]; linarith [min_le_right q₀.1 q₀.2]
    exact ((continuous_fst.tendsto q₀).eventually (eventually_ge_nhds h1)).and
      ((continuous_snd.tendsto q₀).eventually (eventually_ge_nhds h2))
  apply continuousAt_of_dominated (bound := fun t : ℝ => (C^2 * Real.exp (-a)^2) * (Real.exp (-t))^2)
  · exact Eventually.of_forall fun q => ((RMTFoundations.AiryBounds.Ai_continuous.comp (continuous_const.add continuous_id)).mul
        (RMTFoundations.AiryBounds.Ai_continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · filter_upwards [hlow] with q hq
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    calc ‖RMTFoundations.Airy.airyAiReal (q.1+t) * RMTFoundations.Airy.airyAiReal (q.2+t)‖ ≤
        (C^2 * Real.exp (-q.1) * Real.exp (-q.2)) * (Real.exp (-t))^2 :=
      Ai_product_exp_bound a C hC.le hb q.1 q.2 t hq.1 hq.2 ht.le
      _ ≤ (C^2 * Real.exp (-a)^2) * (Real.exp (-t))^2 := by
        rw [sq (Real.exp (-a)), ← mul_assoc]
        gcongr
        · exact hq.1
        · exact hq.2
  · exact RMTFoundations.AiryBounds.integrable_exp_square.const_mul _
  · exact ae_of_all _ fun t => ((RMTFoundations.AiryBounds.Ai_continuous.comp (continuous_fst.add continuous_const)).mul
        (RMTFoundations.AiryBounds.Ai_continuous.comp (continuous_snd.add continuous_const))).continuousAt

lemma K_kernel_continuous (s : ℝ /- [definition] -/) : Continuous (K_kernel s) := by
  unfold K_kernel
  have hc : Continuous (fun q : ℝ × ℝ => (q.1+s,q.2+s)) :=
    (continuous_fst.add continuous_const).prodMk (continuous_snd.add continuous_const)
  have h := K_Ai_continuous.comp hc
  simpa only [Function.comp_def, K_kernel] using h

lemma K_kernel_shift_continuous (q : ℝ × ℝ /- [definition] -/) :
    Continuous (fun s : ℝ => K_kernel s q) := by
  have hc : Continuous (fun s : ℝ => (q.1+s,q.2+s)) :=
    (continuous_const.add continuous_id).prodMk (continuous_const.add continuous_id)
  have h := K_Ai_continuous.comp hc
  simpa only [Function.comp_def, K_kernel] using h

lemma K_kernel_exp_bound_uniform (a : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ s x y : ℝ, a ≤ s → 0 ≤ x → 0 ≤ y →
      |K_kernel s (x,y)| ≤ C * Real.exp (-x) * Real.exp (-y) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound a
  refine ⟨C^2 * Real.exp (-a)^2, mul_pos (sq_pos_of_pos hC) (sq_pos_of_pos (Real.exp_pos _)), ?_⟩
  intro s x y hs hx hy
  calc |K_kernel s (x,y)| ≤ (C^2 * Real.exp (-(x+s)) * Real.exp (-(y+s))) *
        ∫ t, (Real.exp (-t))^2 ∂ RMTFoundations.Airy.halfLineMeasure :=
      K_Ai_abs_le a C hC.le hb (x+s) (y+s) (by linarith) (by linarith)
    _ ≤ C^2 * Real.exp (-(x+s)) * Real.exp (-(y+s)) := by
      simpa using mul_le_mul_of_nonneg_left integral_exp_square_le_one
        (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le)
    _ = C^2 * Real.exp (-s)^2 * Real.exp (-x) * Real.exp (-y) := by
      simp only [neg_add, Real.exp_add]; ring
    _ ≤ (C^2 * Real.exp (-a)^2) * Real.exp (-x) * Real.exp (-y) := by
      gcongr

lemma K_kernel_memLp (s : ℝ /- [definition] -/) : MemLp (K_kernel s) 2 RMTFoundations.Airy.quadrantMeasure := by
  obtain ⟨C,hC,hb⟩ := K_kernel_exp_bound_uniform s
  apply (memLp_two_iff_integrable_sq (K_kernel_continuous s).aestronglyMeasurable).mpr
  apply (RMTFoundations.AiryBounds.integrable_quadrant_exp C).mono'
  · exact ((K_kernel_continuous s).pow 2).aestronglyMeasurable
  · filter_upwards [RMTFoundations.AiryBounds.ae_positive_quadrant] with q hq
    have he := hb s q.1 q.2 le_rfl hq.1.le hq.2.le
    have hn : 0 ≤ C * Real.exp (-q.1) * Real.exp (-q.2) := by positivity
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [neg_add,Real.exp_add,mul_assoc] at *
    nlinarith [sq_abs (K_kernel s q), abs_nonneg (K_kernel s q)]

noncomputable def K_operator (s : ℝ /- [definition] -/) :
    Lp ℝ 2 RMTFoundations.Airy.halfLineMeasure →L[ℝ] Lp ℝ 2 RMTFoundations.Airy.halfLineMeasure := kernelOperator (K_kernel_memLp s)

lemma K_operator_integral_apply_ae (s : ℝ /- [definition] -/)
    (f : Lp ℝ 2 RMTFoundations.Airy.halfLineMeasure /- [definition] -/) :
    ∀ᵐ x ∂ RMTFoundations.Airy.halfLineMeasure, (K_operator s f) x = ∫ y, RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s) * f y ∂ RMTFoundations.Airy.halfLineMeasure :=
  kernelOperator_apply_ae (K_kernel_memLp s) f

lemma integrable_exp_mul_Lp (f : Lp ℝ 2 RMTFoundations.Airy.halfLineMeasure /- [definition] -/) :
    Integrable (fun y => Real.exp (-y) * f y) RMTFoundations.Airy.halfLineMeasure := by
  have he : MemLp (fun y : ℝ => Real.exp (-y)) 2 RMTFoundations.Airy.halfLineMeasure :=
    (memLp_two_iff_integrable_sq (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable).mpr
      RMTFoundations.AiryBounds.integrable_exp_square
  exact he.integrable_mul (Lp.memLp f)

lemma Ai_composition_integrable (s x : ℝ /- [definition] -/)
    (hx : 0 ≤ x /- [standing] -/)
    (f : Lp ℝ 2 RMTFoundations.Airy.halfLineMeasure /- [definition] -/) :
    Integrable (fun q : ℝ × ℝ => RMTFoundations.Airy.airyAiReal (x+q.1+s) * RMTFoundations.Airy.airyAiReal (q.1+q.2+s) * f q.2) RMTFoundations.Airy.quadrantMeasure := by
  obtain ⟨C,hC,hb⟩ := Ai_kernel_exp_bound_uniform s
  have hd := (RMTFoundations.AiryBounds.integrable_exp_square.mul_prod (integrable_exp_mul_Lp f).norm).const_mul
    (C^2 * Real.exp (-x))
  apply hd.mono'
  · exact (((RMTFoundations.AiryBounds.Ai_continuous.comp ((continuous_const.add continuous_fst).add continuous_const)).mul
      (RMTFoundations.AiryBounds.Ai_continuous.comp ((continuous_fst.add continuous_snd).add continuous_const))).aestronglyMeasurable.mul
      (Lp.memLp f).aestronglyMeasurable.comp_snd)
  · filter_upwards [RMTFoundations.AiryBounds.ae_positive_quadrant] with q hq
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := hb s x q.1 le_rfl hx hq.1.le
    have h2 := hb s q.1 q.2 le_rfl hq.1.le hq.2.le
    calc
      |RMTFoundations.Airy.airyAiReal (x+q.1+s)| * |RMTFoundations.Airy.airyAiReal (q.1+q.2+s)| * ‖f q.2‖ ≤
          (C*Real.exp (-x)*Real.exp (-q.1)) * (C*Real.exp (-q.1)*Real.exp (-q.2)) * ‖f q.2‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = (C^2 * Real.exp (-x)) * ((Real.exp (-q.1))^2 * ‖Real.exp (-q.2) * f q.2‖) := by
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        ring

/-- The square of the actual Hankel operator has the physical Airy product kernel. -/
theorem H_square_eq_K_operator (s : ℝ /- [definition] -/) :
    (RMTFoundations.Airy.airyHankelShift s).comp (RMTFoundations.Airy.airyHankelShift s) = K_operator s := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [RMTFoundations.AiryBounds.H_integral_apply_ae s (RMTFoundations.Airy.airyHankelShift s f), K_operator_integral_apply_ae s f,
      ae_restrict_mem measurableSet_Ioi] with x hh hk hx
  change (RMTFoundations.Airy.airyHankelShift s (RMTFoundations.Airy.airyHankelShift s f)) x = (K_operator s f) x
  rw [hh,hk]
  have hi := Ai_composition_integrable s x hx.le f
  calc
    (∫ t, RMTFoundations.Airy.airyAiReal (x+t+s) * (RMTFoundations.Airy.airyHankelShift s f) t ∂ RMTFoundations.Airy.halfLineMeasure) =
        ∫ t, ∫ y, RMTFoundations.Airy.airyAiReal (x+t+s) * RMTFoundations.Airy.airyAiReal (t+y+s) * f y ∂ RMTFoundations.Airy.halfLineMeasure ∂ RMTFoundations.Airy.halfLineMeasure := by
      apply integral_congr_ae
      filter_upwards [RMTFoundations.AiryBounds.H_integral_apply_ae s f] with t ht
      rw [ht, ← integral_const_mul]
      congr 1
      funext y
      ring
    _ = ∫ y, ∫ t, RMTFoundations.Airy.airyAiReal (x+t+s) * RMTFoundations.Airy.airyAiReal (t+y+s) * f y ∂ RMTFoundations.Airy.halfLineMeasure ∂ RMTFoundations.Airy.halfLineMeasure :=
      integral_integral_swap hi
    _ = ∫ y, RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s) * f y ∂ RMTFoundations.Airy.halfLineMeasure := by
      congr 1
      funext y
      unfold RMTFoundations.Airy.airyKernelIntegral
      rw [← integral_mul_const]
      congr 1
      funext t
      congr 1 <;> ring

/-- Extension by zero makes the physical positive-quadrant domain explicit. -/
noncomputable def positiveExtension (k : ℝ → ℝ → ℝ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : ℝ := if 0 ≤ x ∧ 0 ≤ y then k x y else 0

lemma positiveExtension_measurable (k : ℝ → ℝ → ℝ /- [definition] -/)
    (hk : Measurable (Function.uncurry k) /- [standing] -/ ) :
    Measurable (Function.uncurry (positiveExtension k)) := by
  exact Measurable.ite ((measurableSet_Ici.preimage measurable_fst).inter
    (measurableSet_Ici.preimage measurable_snd)) hk measurable_const

lemma positiveExtension_ae (k : ℝ → ℝ → ℝ /- [definition] -/) :
    Function.uncurry (positiveExtension k) =ᵐ[RMTFoundations.Airy.quadrantMeasure] Function.uncurry k := by
  filter_upwards [RMTFoundations.AiryBounds.ae_positive_quadrant] with q hq
  simp only [Function.uncurry, positiveExtension, hq.1.le, hq.2.le, and_self, if_true]

lemma positiveExtension_bound (k : ℝ → ℝ → ℝ /- [definition] -/)
    (C : ℝ /- [definition] -/) (hC : 0 ≤ C /- [standing] -/)
    (hb : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |k x y| ≤ C * Real.exp (-x) * Real.exp (-y) /- [standing] -/ ) :
    ∀ x y : ℝ, |positiveExtension k x y| ≤ C * Real.exp (-x) * Real.exp (-y) := by
  intro x y
  unfold positiveExtension
  split_ifs with h
  · exact hb x y h.1 h.2
  · simp only [abs_zero]
    positivity

lemma positiveExtension_shift_continuous (k : ℝ → ℝ → ℝ → ℝ /- [definition] -/)
    (hk : ∀ x y, Continuous (fun s => k s x y) /- [standing] -/ )
    (x y : ℝ /- [definition] -/) : Continuous (fun s => positiveExtension (k s) x y) := by
  unfold positiveExtension
  by_cases h : 0 ≤ x ∧ 0 ≤ y
  · simp only [if_pos h]; exact hk x y
  · simp only [if_neg h]; exact continuous_const

noncomputable def B_fredholmKernel (s x y : ℝ /- [definition] -/) : ℝ :=
  positiveExtension (fun u v => RMTFoundations.Airy.airyAiReal (u+v+s)) x y
noncomputable def K_fredholmKernel (s x y : ℝ /- [definition] -/) : ℝ :=
  positiveExtension (fun u v => RMTFoundations.Airy.airyKernelIntegral (u+s) (v+s)) x y

lemma B_fredholmKernel_measurable (s : ℝ /- [definition] -/) :
    Measurable (Function.uncurry (B_fredholmKernel s)) :=
  positiveExtension_measurable _ (RMTFoundations.AiryBounds.continuous_shiftedKernel RMTFoundations.Airy.airyAiReal RMTFoundations.AiryBounds.Ai_continuous s).measurable
lemma K_fredholmKernel_measurable (s : ℝ /- [definition] -/) :
    Measurable (Function.uncurry (K_fredholmKernel s)) :=
  positiveExtension_measurable _ (K_kernel_continuous s).measurable
lemma B_fredholmKernel_shift_continuous (x y : ℝ /- [definition] -/) :
    Continuous (fun s => B_fredholmKernel s x y) :=
  positiveExtension_shift_continuous _ (fun u v => RMTFoundations.AiryBounds.Ai_continuous.comp (continuous_const.add continuous_id)) x y
lemma K_fredholmKernel_shift_continuous (x y : ℝ /- [definition] -/) :
    Continuous (fun s => K_fredholmKernel s x y) :=
  positiveExtension_shift_continuous _ (fun u v => K_kernel_shift_continuous (u,v)) x y

lemma B_fredholmKernel_bound_uniform (a : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, a ≤ s → ∀ x y : ℝ,
      |B_fredholmKernel s x y| ≤ C * Real.exp (-x) * Real.exp (-y) := by
  obtain ⟨C,hC,hb⟩ := Ai_kernel_exp_bound_uniform a
  exact ⟨C,hC,fun s hs => positiveExtension_bound _ C hC.le (hb s · · hs)⟩
lemma K_fredholmKernel_bound_uniform (a : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, a ≤ s → ∀ x y : ℝ,
      |K_fredholmKernel s x y| ≤ C * Real.exp (-x) * Real.exp (-y) := by
  obtain ⟨C,hC,hb⟩ := K_kernel_exp_bound_uniform a
  exact ⟨C,hC,fun s hs => positiveExtension_bound _ C hC.le (hb s · · hs)⟩

lemma airy_fredholm_weight_probe :
    Integrable (fun x : ℝ => Real.exp (-x)) RMTFoundations.Airy.halfLineMeasure ∧
    Integrable (fun x : ℝ => Real.exp (-x)^2) RMTFoundations.Airy.halfLineMeasure ∧
    (∀ x : ℝ, 0 < Real.exp (-x)) ∧ Real.exp (-(1:ℝ)) ≠ 0 :=
  ⟨integrableOn_exp_neg_Ioi 0, RMTFoundations.AiryBounds.integrable_exp_square, (fun x => Real.exp_pos (-x)), (Real.exp_pos _).ne'⟩

/-- The TW1 operator is the same physical shifted Airy Hankel operator. -/

theorem B_square_eq_K_operator (s : ℝ /- [definition] -/) :
    (RMTFoundations.Airy.airyHankelShift s).comp (RMTFoundations.Airy.airyHankelShift s) = K_operator s := H_square_eq_K_operator s


lemma kernelFredholm_entire_of_kernel_bound
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/) [SigmaFinite μ /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/) (a : α → ℝ /- [definition] -/)
    (C : ℝ /- [definition] -/) (hC : 0 ≤ C /- [standing] -/)
    (ha : ∀ x, 0 ≤ a x /- [standing] -/)
    (ha1 : Integrable a μ /- [standing] -/)
    (ha2 : Integrable (fun x => a x^2) μ /- [standing] -/)
    (hk : Measurable (Function.uncurry k) /- [standing] -/ )
    (hb : ∀ x y, |k x y| ≤ C * a x * a y /- [standing] -/) :
    AnalyticOnNhd ℂ (kernelFredholm μ k) Set.univ := by
  apply kernelFredholm_entire_of_minor_bound μ k a C hC ha2
  intro n x
  exact weighted_kernel_minor_bound_pow n k C a x hC ha hb

lemma B_fredholm_entire (s : ℝ /- [definition] -/) :
    AnalyticOnNhd ℂ (kernelFredholm RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s)) Set.univ := by
  obtain ⟨C,hC,hb⟩ := B_fredholmKernel_bound_uniform s
  exact kernelFredholm_entire_of_kernel_bound RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s)
    (fun x => Real.exp (-x)) C hC.le (fun x => (Real.exp_pos _).le)
    (integrableOn_exp_neg_Ioi 0) RMTFoundations.AiryBounds.integrable_exp_square
    (B_fredholmKernel_measurable s) (hb s le_rfl)

lemma K_fredholm_entire (s : ℝ /- [definition] -/) :
    AnalyticOnNhd ℂ (kernelFredholm RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s)) Set.univ := by
  obtain ⟨C,hC,hb⟩ := K_fredholmKernel_bound_uniform s
  exact kernelFredholm_entire_of_kernel_bound RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s)
    (fun x => Real.exp (-x)) C hC.le (fun x => (Real.exp_pos _).le)
    (integrableOn_exp_neg_Ioi 0) RMTFoundations.AiryBounds.integrable_exp_square
    (K_fredholmKernel_measurable s) (hb s le_rfl)

lemma B_fredholm_continuous (z : ℂ /- [definition] -/) :
    Continuous (fun s => kernelFredholm RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s) z) := by
  apply continuous_iff_continuousAt.mpr
  intro s₀
  obtain ⟨C,hC,hb⟩ := B_fredholmKernel_bound_uniform (s₀-1)
  apply kernelFredholm_continuousAt_of_minor_bound RMTFoundations.Airy.halfLineMeasure B_fredholmKernel s₀
    (fun x => Real.exp (-x)) C hC.le RMTFoundations.AiryBounds.integrable_exp_square
  · exact Eventually.of_forall B_fredholmKernel_measurable
  · filter_upwards [eventually_ge_nhds (show s₀-1 < s₀ by linarith)] with s hs
    intro n x
    exact weighted_kernel_minor_bound_pow n (B_fredholmKernel s) C (fun x => Real.exp (-x)) x hC.le
      (fun x => (Real.exp_pos _).le) (hb s hs)
  · exact fun x y => (B_fredholmKernel_shift_continuous x y).continuousAt

lemma K_fredholm_continuous (z : ℂ /- [definition] -/) :
    Continuous (fun s => kernelFredholm RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s) z) := by
  apply continuous_iff_continuousAt.mpr
  intro s₀
  obtain ⟨C,hC,hb⟩ := K_fredholmKernel_bound_uniform (s₀-1)
  apply kernelFredholm_continuousAt_of_minor_bound RMTFoundations.Airy.halfLineMeasure K_fredholmKernel s₀
    (fun x => Real.exp (-x)) C hC.le RMTFoundations.AiryBounds.integrable_exp_square
  · exact Eventually.of_forall K_fredholmKernel_measurable
  · filter_upwards [eventually_ge_nhds (show s₀-1 < s₀ by linarith)] with s hs
    intro n x
    exact weighted_kernel_minor_bound_pow n (K_fredholmKernel s) C (fun x => Real.exp (-x)) x hC.le
      (fun x => (Real.exp_pos _).le) (hb s hs)
  · exact fun x y => (K_fredholmKernel_shift_continuous x y).continuousAt

lemma B_fredholm_physical (s : ℝ /- [definition] -/) (z : ℂ /- [definition] -/) :
    kernelFredholm RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s) z =
      kernelFredholm RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) z := by
  refine kernelFredholm_congr_on_full_measure RMTFoundations.Airy.halfLineMeasure _ _ (Set.Ioi 0)
    (ae_restrict_mem measurableSet_Ioi) ?_ z
  intro x hx y hy
  exact if_pos ⟨hx.le,hy.le⟩

lemma K_fredholm_physical (s : ℝ /- [definition] -/) (z : ℂ /- [definition] -/) :
    kernelFredholm RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s) z =
      kernelFredholm RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)) z := by
  refine kernelFredholm_congr_on_full_measure RMTFoundations.Airy.halfLineMeasure _ _ (Set.Ioi 0)
    (ae_restrict_mem measurableSet_Ioi) ?_ z
  intro x hx y hy
  exact if_pos ⟨hx.le,hy.le⟩

/-- TW1 defined by the full kernel Fredholm series, at the physical coupling -1. -/
noncomputable def TW1 (s : ℝ /- [definition] -/) : ℂ :=
  kernelFredholm RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) (-1)
/-- TW2 defined by the full physical Airy product-kernel Fredholm series. -/
noncomputable def TW2 (s : ℝ /- [definition] -/) : ℂ :=
  kernelFredholm RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)) (-1)

theorem TW1_continuous : Continuous TW1 := by
  have he : TW1 = fun s => kernelFredholm RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s) (-1) := by
    funext s
    exact (B_fredholm_physical s (-1)).symm
  rw [he]
  exact B_fredholm_continuous (-1)
theorem TW2_continuous : Continuous TW2 := by
  have he : TW2 = fun s => kernelFredholm RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s) (-1) := by
    funext s
    exact (K_fredholm_physical s (-1)).symm
  rw [he]
  exact K_fredholm_continuous (-1)

lemma TW1_im_zero (s : ℝ /- [definition] -/) : (TW1 s).im = 0 := by
  unfold TW1
  rw [show (-1:ℂ) = ((-1:ℝ):ℂ) by norm_num, kernelFredholm_real_coupling]
  rfl
lemma TW2_im_zero (s : ℝ /- [definition] -/) : (TW2 s).im = 0 := by
  unfold TW2
  rw [show (-1:ℂ) = ((-1:ℝ):ℂ) by norm_num, kernelFredholm_real_coupling]
  rfl

lemma B_physical_minor_integrable (s : ℝ /- [definition] -/) (n : ℕ /- [definition] -/) :
    Integrable (kernelMinor (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) n) (Measure.pi (fun _ : Fin n => RMTFoundations.Airy.halfLineMeasure)) := by
  obtain ⟨C,hC,hb⟩ := B_fredholmKernel_bound_uniform s
  have hd : ∀ m x, |kernelMinor (B_fredholmKernel s) m x| ≤
      (Real.sqrt m * C)^m * ∏ i, Real.exp (-(x i))^2 := fun m x =>
    weighted_kernel_minor_bound_pow m (B_fredholmKernel s) C (fun x => Real.exp (-x)) x
      hC.le (fun x => (Real.exp_pos _).le) (hb s le_rfl)
  have hi := kernelMinor_integrable_of_minor_bound RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s)
    (fun x => Real.exp (-x)) C RMTFoundations.AiryBounds.integrable_exp_square (B_fredholmKernel_measurable s) hd n
  exact hi.congr (kernelMinor_congr_on_full_measure RMTFoundations.Airy.halfLineMeasure _ _ (Set.Ioi 0)
    (ae_restrict_mem measurableSet_Ioi) (fun x hx y hy => if_pos ⟨hx.le,hy.le⟩) n)

lemma B_physical_fredholm_absolute (s : ℝ /- [definition] -/) (z : ℂ /- [definition] -/) :
    Summable (fun n => ‖(kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) n : ℂ) * z^n‖) := by
  obtain ⟨C,hC,hb⟩ := B_fredholmKernel_bound_uniform s
  have hd : ∀ m x, |kernelMinor (B_fredholmKernel s) m x| ≤
      (Real.sqrt m * C)^m * ∏ i, Real.exp (-(x i))^2 := fun m x =>
    weighted_kernel_minor_bound_pow m (B_fredholmKernel s) C (fun x => Real.exp (-x)) x
      hC.le (fun x => (Real.exp_pos _).le) (hb s le_rfl)
  have hi := kernelFredholm_absolute_of_minor_bound RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s)
    (fun x => Real.exp (-x)) C hC.le RMTFoundations.AiryBounds.integrable_exp_square hd z
  have hc (n : ℕ) : kernelCoefficient RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s) n =
      kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) n :=
    kernelCoefficient_congr_on_full_measure RMTFoundations.Airy.halfLineMeasure _ _ (Set.Ioi 0)
      (ae_restrict_mem measurableSet_Ioi) (fun x hx y hy => if_pos ⟨hx.le,hy.le⟩) n
  simpa only [hc] using hi

lemma K_physical_minor_integrable (s : ℝ /- [definition] -/) (n : ℕ /- [definition] -/) :
    Integrable (kernelMinor (fun x y => RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)) n) (Measure.pi (fun _ : Fin n => RMTFoundations.Airy.halfLineMeasure)) := by
  obtain ⟨C,hC,hb⟩ := K_fredholmKernel_bound_uniform s
  have hd : ∀ m x, |kernelMinor (K_fredholmKernel s) m x| ≤
      (Real.sqrt m * C)^m * ∏ i, Real.exp (-(x i))^2 := fun m x =>
    weighted_kernel_minor_bound_pow m (K_fredholmKernel s) C (fun x => Real.exp (-x)) x
      hC.le (fun x => (Real.exp_pos _).le) (hb s le_rfl)
  have hi := kernelMinor_integrable_of_minor_bound RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s)
    (fun x => Real.exp (-x)) C RMTFoundations.AiryBounds.integrable_exp_square (K_fredholmKernel_measurable s) hd n
  exact hi.congr (kernelMinor_congr_on_full_measure RMTFoundations.Airy.halfLineMeasure _ _ (Set.Ioi 0)
    (ae_restrict_mem measurableSet_Ioi) (fun x hx y hy => if_pos ⟨hx.le,hy.le⟩) n)

lemma K_physical_fredholm_absolute (s : ℝ /- [definition] -/) (z : ℂ /- [definition] -/) :
    Summable (fun n => ‖(kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)) n : ℂ) * z^n‖) := by
  obtain ⟨C,hC,hb⟩ := K_fredholmKernel_bound_uniform s
  have hd : ∀ m x, |kernelMinor (K_fredholmKernel s) m x| ≤
      (Real.sqrt m * C)^m * ∏ i, Real.exp (-(x i))^2 := fun m x =>
    weighted_kernel_minor_bound_pow m (K_fredholmKernel s) C (fun x => Real.exp (-x)) x
      hC.le (fun x => (Real.exp_pos _).le) (hb s le_rfl)
  have hi := kernelFredholm_absolute_of_minor_bound RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s)
    (fun x => Real.exp (-x)) C hC.le RMTFoundations.AiryBounds.integrable_exp_square hd z
  have hc (n : ℕ) : kernelCoefficient RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s) n =
      kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)) n :=
    kernelCoefficient_congr_on_full_measure RMTFoundations.Airy.halfLineMeasure _ _ (Set.Ioi 0)
      (ae_restrict_mem measurableSet_Ioi) (fun x hx y hy => if_pos ⟨hx.le,hy.le⟩) n
  simpa only [hc] using hi


/-- The empty minor contributes exactly one, including for the zero kernel. -/
lemma kernelCoefficient_zero_order
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (k : α → α → ℝ /- [definition] -/ )
    : kernelCoefficient μ k 0 = 1 := by
  have hz (x : Fin 0 → α) : kernelMinor k 0 x = 1 := by
    change Matrix.det (Matrix.of (fun i j : Fin 0 => k (x i) (x j))) = 1
    exact Matrix.det_isEmpty
  simp only [kernelCoefficient, hz, Nat.factorial_zero, Nat.cast_one, div_one]
  simp [integral_const, measureReal_def]

lemma kernelCoefficient_zero_kernel_succ
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    (n : ℕ /- [definition] -/ )
    : kernelCoefficient μ (fun _ _ => 0) (n+1) = 0 := by
  have hz : kernelMinor (fun _ _ : α => (0 : ℝ)) (n+1) = fun _ => 0 := by
    funext x
    exact Matrix.det_zero
  simp only [kernelCoefficient, hz, integral_zero, zero_div]

lemma kernelFredholm_zero_kernel
    {α : Type* /- [definition] -/ }
    [MeasurableSpace α /- [definition] -/ ]
    (μ : Measure α /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (z : ℂ /- [definition] -/ )
    : kernelFredholm μ (fun _ _ => 0) z = 1 := by
  unfold kernelFredholm kernelSeries
  rw [tsum_eq_single 0]
  · simp [kernelCoefficient_zero_order]
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [kernelCoefficient_zero_kernel_succ]

/-- The standard Airy function tends to zero along the positive real axis. -/
theorem Ai_tendsto_atTop_zero : Tendsto RMTFoundations.Airy.airyAiReal atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound 0
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simpa only [Real.norm_eq_abs] using hb x hx
  · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C

lemma B_fredholmKernel_tendsto_zero (x y : ℝ /- [definition] -/) :
    Tendsto (fun s => B_fredholmKernel s x y) atTop (𝓝 0) := by
  unfold B_fredholmKernel positiveExtension
  by_cases h : 0 ≤ x ∧ 0 ≤ y
  · simp only [if_pos h]
    exact Ai_tendsto_atTop_zero.comp (tendsto_atTop_add_const_left atTop (x+y) tendsto_id)
  · simp only [if_neg h]
    exact tendsto_const_nhds

/-- An explicit vanishing exponential constant, stronger than pointwise kernel decay. -/
lemma K_kernel_vanishing_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s x y : ℝ, 0 ≤ s → 0 ≤ x → 0 ≤ y →
      |RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)| ≤ (C^2 * Real.exp (-s)^2) * Real.exp (-x) * Real.exp (-y) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound 0
  refine ⟨C,hC,?_⟩
  intro s x y hs hx hy
  have he := K_Ai_abs_le 0 C hC.le hb (x+s) (y+s) (by linarith) (by linarith)
  calc
    |RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)| ≤ (C^2 * Real.exp (-(x+s)) * Real.exp (-(y+s))) *
        ∫ t, Real.exp (-t)^2 ∂ RMTFoundations.Airy.halfLineMeasure := he
    _ ≤ C^2 * Real.exp (-(x+s)) * Real.exp (-(y+s)) := by
      simpa using mul_le_mul_of_nonneg_left integral_exp_square_le_one
        (show 0 ≤ C^2 * Real.exp (-(x+s)) * Real.exp (-(y+s)) by positivity)
    _ = _ := by simp only [neg_add, Real.exp_add]; ring

lemma B_kernel_vanishing_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s x y : ℝ, 0 ≤ s → 0 ≤ x → 0 ≤ y →
      |RMTFoundations.Airy.airyAiReal (x+y+s)| ≤ (C * Real.exp (-s)) * Real.exp (-x) * Real.exp (-y) := by
  obtain ⟨C,hC,hb⟩ := RMTFoundations.AiryBounds.Ai_halfline_exp_bound 0
  refine ⟨C,hC,?_⟩
  intro s x y hs hx hy
  calc
    |RMTFoundations.Airy.airyAiReal (x+y+s)| ≤ C * Real.exp (-(x+y+s)) := hb _ (by linarith)
    _ = _ := by simp only [neg_add, Real.exp_add]; ring

lemma K_fredholmKernel_tendsto_zero (x y : ℝ /- [definition] -/) :
    Tendsto (fun s => K_fredholmKernel s x y) atTop (𝓝 0) := by
  unfold K_fredholmKernel positiveExtension
  by_cases h : 0 ≤ x ∧ 0 ≤ y
  · simp only [if_pos h]
    obtain ⟨C,hC,hb⟩ := K_kernel_vanishing_bound
    apply squeeze_zero_norm'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      simpa only [Real.norm_eq_abs] using hb s x y hs h.1 h.2
    · simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).const_mul (C^2)).mul_const
        (Real.exp (-x)) |>.mul_const (Real.exp (-y))
  · simp only [if_neg h]
    exact tendsto_const_nhds

/-- Dominated convergence of the full series, with a uniform Hadamard majorant. -/
theorem B_fredholm_tendsto_atTop_one (z : ℂ /- [definition] -/) :
    Tendsto (fun s => kernelFredholm RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s) z) atTop (𝓝 1) := by
  obtain ⟨C,hC,hb⟩ := B_fredholmKernel_bound_uniform 0
  rw [← kernelFredholm_zero_kernel RMTFoundations.Airy.halfLineMeasure z]
  apply kernelFredholm_tendsto_of_minor_bound RMTFoundations.Airy.halfLineMeasure atTop B_fredholmKernel
    (fun _ _ => 0) (fun x => Real.exp (-x)) C hC.le RMTFoundations.AiryBounds.integrable_exp_square
  · exact Eventually.of_forall B_fredholmKernel_measurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    intro n x
    exact weighted_kernel_minor_bound_pow n (B_fredholmKernel s) C (fun x => Real.exp (-x)) x
      hC.le (fun x => (Real.exp_pos _).le) (hb s hs)
  · exact B_fredholmKernel_tendsto_zero

theorem K_fredholm_tendsto_atTop_one (z : ℂ /- [definition] -/) :
    Tendsto (fun s => kernelFredholm RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s) z) atTop (𝓝 1) := by
  obtain ⟨C,hC,hb⟩ := K_fredholmKernel_bound_uniform 0
  rw [← kernelFredholm_zero_kernel RMTFoundations.Airy.halfLineMeasure z]
  apply kernelFredholm_tendsto_of_minor_bound RMTFoundations.Airy.halfLineMeasure atTop K_fredholmKernel
    (fun _ _ => 0) (fun x => Real.exp (-x)) C hC.le RMTFoundations.AiryBounds.integrable_exp_square
  · exact Eventually.of_forall K_fredholmKernel_measurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    intro n x
    exact weighted_kernel_minor_bound_pow n (K_fredholmKernel s) C (fun x => Real.exp (-x)) x
      hC.le (fun x => (Real.exp_pos _).le) (hb s hs)
  · exact K_fredholmKernel_tendsto_zero

theorem TW1_tendsto_atTop_one : Tendsto TW1 atTop (𝓝 1) := by
  exact (B_fredholm_tendsto_atTop_one (-1)).congr
    (fun s => B_fredholm_physical s (-1))
theorem TW2_tendsto_atTop_one : Tendsto TW2 atTop (𝓝 1) := by
  exact (K_fredholm_tendsto_atTop_one (-1)).congr
    (fun s => K_fredholm_physical s (-1))

/-- Real-valued versions of the exact physical Fredholm series. -/
noncomputable def TW1R (s : ℝ /- [definition] -/) : ℝ := (TW1 s).re
noncomputable def TW2R (s : ℝ /- [definition] -/) : ℝ := (TW2 s).re

lemma TW1R_coe (s : ℝ /- [definition] -/) : (TW1R s : ℂ) = TW1 s := by
  apply Complex.ext
  · rfl
  · simpa using (TW1_im_zero s).symm
lemma TW2R_coe (s : ℝ /- [definition] -/) : (TW2R s : ℂ) = TW2 s := by
  apply Complex.ext
  · rfl
  · simpa using (TW2_im_zero s).symm

theorem TW1R_continuous : Continuous TW1R := Complex.continuous_re.comp TW1_continuous
theorem TW2R_continuous : Continuous TW2R := Complex.continuous_re.comp TW2_continuous

theorem TW1R_tendsto_atTop_one : Tendsto TW1R atTop (𝓝 1) := by
  change Tendsto (fun s => (TW1 s).re) atTop (𝓝 ((1 : ℂ).re))
  exact Complex.continuous_re.continuousAt.tendsto.comp TW1_tendsto_atTop_one
theorem TW2R_tendsto_atTop_one : Tendsto TW2R atTop (𝓝 1) := by
  change Tendsto (fun s => (TW2 s).re) atTop (𝓝 ((1 : ℂ).re))
  exact Complex.continuous_re.continuousAt.tendsto.comp TW2_tendsto_atTop_one

lemma B_kernel_bound_with_tendsto_constant :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun s : ℝ => C * Real.exp (-s)) atTop (𝓝 0) ∧
      ∀ s x y : ℝ, 0 ≤ s → 0 ≤ x → 0 ≤ y →
        |RMTFoundations.Airy.airyAiReal (x+y+s)| ≤ (C * Real.exp (-s)) * Real.exp (-x) * Real.exp (-y) := by
  obtain ⟨C,hC,hb⟩ := B_kernel_vanishing_bound
  exact ⟨C,hC,by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C,hb⟩

lemma K_kernel_bound_with_tendsto_constant :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun s : ℝ => C^2 * Real.exp (-s)^2) atTop (𝓝 0) ∧
      ∀ s x y : ℝ, 0 ≤ s → 0 ≤ x → 0 ≤ y →
        |RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)| ≤ (C^2 * Real.exp (-s)^2) * Real.exp (-x) * Real.exp (-y) := by
  obtain ⟨C,hC,hb⟩ := K_kernel_vanishing_bound
  exact ⟨C,hC,by simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).const_mul (C^2),hb⟩

lemma fredholm_limits_real_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
      Tendsto TW1R atTop (𝓝 1) ∧ Tendsto TW2R atTop (𝓝 1) ∧
      (∀ s : ℝ, (TW1R s : ℂ) = TW1 s ∧ (TW2R s : ℂ) = TW2 s) :=
  ⟨RMTFoundations.AiryBounds.Ai_kernel_inhabitation.1, TW1R_tendsto_atTop_one, TW2R_tendsto_atTop_one,
    fun s => ⟨TW1R_coe s,TW2R_coe s⟩⟩


/-- Actual Lebesgue measure on the physical moving half-line. -/
noncomputable abbrev fredholmHalfLineMeasure (s : ℝ /- [definition] -/) : Measure ℝ :=
  volume.restrict (Ioi s)

lemma fredholm_measurePreserving_shift (s : ℝ /- [definition] -/) :
    MeasurePreserving (fun x : ℝ => x+s) RMTFoundations.Airy.halfLineMeasure (fredholmHalfLineMeasure s) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) s).restrict_preimage
    (s := Ioi s) measurableSet_Ioi
  have he : (fun x : ℝ => x+s) ⁻¹' Ioi s = Ioi 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro hx <;> linarith
  simpa only [he] using h

lemma fredholm_measurePreserving_pi_shift (s : ℝ /- [definition] -/)
    (n : ℕ /- [definition] -/) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => x i+s)
      (Measure.pi (fun _ => RMTFoundations.Airy.halfLineMeasure))
      (Measure.pi (fun _ => fredholmHalfLineMeasure s)) :=
  measurePreserving_pi _ _ (fun _ => fredholm_measurePreserving_shift s)

/-- Change of variables is performed at each determinant integral, not postulated. -/
theorem kernelCoefficient_halfLine_shift
    (k : ℝ → ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (n : ℕ /- [definition] -/) :
    kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => k (x+s) (y+s)) n =
      kernelCoefficient (fredholmHalfLineMeasure s) k n := by
  unfold kernelCoefficient
  congr 1
  exact (fredholm_measurePreserving_pi_shift s n).integral_comp
    (MeasurableEquiv.piCongrRight (fun _ : Fin n => MeasurableEquiv.addRight s)).measurableEmbedding
    (kernelMinor k n)

/-- The full entire Fredholm series respects the physical translation. -/
theorem kernelFredholm_halfLine_shift
    (k : ℝ → ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    kernelFredholm RMTFoundations.Airy.halfLineMeasure (fun x y => k (x+s) (y+s)) z =
      kernelFredholm (fredholmHalfLineMeasure s) k z := by
  unfold kernelFredholm kernelSeries
  apply tsum_congr
  intro n
  dsimp only
  rw [kernelCoefficient_halfLine_shift]

lemma K_fredholm_halfLine (s : ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    kernelFredholm RMTFoundations.Airy.halfLineMeasure (K_fredholmKernel s) z =
      kernelFredholm (fredholmHalfLineMeasure s) RMTFoundations.Airy.airyKernelIntegral z := by
  rw [K_fredholm_physical, kernelFredholm_halfLine_shift]

theorem TW2_halfLine (s : ℝ /- [definition] -/) :
    TW2 s = kernelFredholm (fredholmHalfLineMeasure s) RMTFoundations.Airy.airyKernelIntegral (-1) :=
  kernelFredholm_halfLine_shift RMTFoundations.Airy.airyKernelIntegral s (-1)

/-- Shifting both arguments of a Hankel kernel uses half the shift. -/
lemma B_fredholm_halfLine (s : ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    kernelFredholm RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s) z =
      kernelFredholm (fredholmHalfLineMeasure (s/2)) (fun u v => RMTFoundations.Airy.airyAiReal (u+v)) z := by
  rw [B_fredholm_physical]
  have he : (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) =
      (fun x y => RMTFoundations.Airy.airyAiReal ((x+s/2)+(y+s/2))) := by
    funext x y
    congr 1
    ring
  rw [he]
  exact kernelFredholm_halfLine_shift (fun u v => RMTFoundations.Airy.airyAiReal (u+v)) (s/2) z

theorem TW1_halfLine (s : ℝ /- [definition] -/) :
    TW1 s = kernelFredholm (fredholmHalfLineMeasure (s/2)) (fun u v => RMTFoundations.Airy.airyAiReal (u+v)) (-1) := by
  exact (B_fredholm_physical s (-1)).symm.trans (B_fredholm_halfLine s (-1))

/-- Equivalent formula on (s,∞), retaining the required residual shift. -/
lemma B_fredholm_halfLine_full_shift (s : ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    kernelFredholm RMTFoundations.Airy.halfLineMeasure (B_fredholmKernel s) z =
      kernelFredholm (fredholmHalfLineMeasure s) (fun u v => RMTFoundations.Airy.airyAiReal (u+v-s)) z := by
  rw [B_fredholm_physical]
  have he : (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) =
      (fun x y => RMTFoundations.Airy.airyAiReal ((x+s)+(y+s)-s)) := by
    funext x y
    congr 1
    ring
  rw [he]
  exact kernelFredholm_halfLine_shift (fun u v => RMTFoundations.Airy.airyAiReal (u+v-s)) s z

lemma K_halfLine_minor_integrable (s : ℝ /- [definition] -/)
    (n : ℕ /- [definition] -/) :
    Integrable (kernelMinor RMTFoundations.Airy.airyKernelIntegral n) (Measure.pi (fun _ : Fin n => fredholmHalfLineMeasure s)) := by
  exact ((fredholm_measurePreserving_pi_shift s n).integrable_comp_emb
    (MeasurableEquiv.piCongrRight (fun _ : Fin n => MeasurableEquiv.addRight s)).measurableEmbedding).mp
      (K_physical_minor_integrable s n)

lemma B_halfLine_minor_integrable (s : ℝ /- [definition] -/)
    (n : ℕ /- [definition] -/) :
    Integrable (kernelMinor (fun u v => RMTFoundations.Airy.airyAiReal (u+v)) n)
      (Measure.pi (fun _ : Fin n => fredholmHalfLineMeasure (s/2))) := by
  have hi := B_physical_minor_integrable s n
  have he : (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) =
      (fun x y => RMTFoundations.Airy.airyAiReal ((x+s/2)+(y+s/2))) := by
    funext x y
    congr 1
    ring
  rw [he] at hi
  exact ((fredholm_measurePreserving_pi_shift (s/2) n).integrable_comp_emb
    (MeasurableEquiv.piCongrRight (fun _ : Fin n => MeasurableEquiv.addRight (s/2))).measurableEmbedding).mp hi

lemma K_halfLine_fredholm_absolute (s : ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    Summable (fun n => ‖(kernelCoefficient (fredholmHalfLineMeasure s) RMTFoundations.Airy.airyKernelIntegral n : ℂ) * z^n‖) := by
  simpa only [kernelCoefficient_halfLine_shift] using K_physical_fredholm_absolute s z

lemma B_halfLine_fredholm_absolute (s : ℝ /- [definition] -/)
    (z : ℂ /- [definition] -/) :
    Summable (fun n => ‖(kernelCoefficient (fredholmHalfLineMeasure (s/2))
      (fun u v => RMTFoundations.Airy.airyAiReal (u+v)) n : ℂ) * z^n‖) := by
  have hi := B_physical_fredholm_absolute s z
  have he : (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) =
      (fun x y => RMTFoundations.Airy.airyAiReal ((x+s/2)+(y+s/2))) := by
    funext x y
    congr 1
    ring
  rw [he] at hi
  have hc (n : ℕ) :
      kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyAiReal ((x+s/2)+(y+s/2))) n =
        kernelCoefficient (fredholmHalfLineMeasure (s/2)) (fun u v => RMTFoundations.Airy.airyAiReal (u+v)) n :=
    kernelCoefficient_halfLine_shift (fun u v => RMTFoundations.Airy.airyAiReal (u+v)) (s/2) n
  simpa only [hc] using hi

/-- Product restricted measures are literally Lebesgue measure on (s,∞)^n. -/
lemma fredholm_halfLine_pi_measure (s : ℝ /- [definition] -/)
    (n : ℕ /- [definition] -/) :
    Measure.pi (fun _ : Fin n => fredholmHalfLineMeasure s) =
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
        (Set.univ.pi (fun _ => Ioi s)) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin n => (volume : Measure ℝ)) (fun _ => Ioi s)).symm

lemma kernelCoefficient_halfLine_integral (k : ℝ → ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (n : ℕ /- [definition] -/) :
    kernelCoefficient (fredholmHalfLineMeasure s) k n =
      (∫ x in Set.univ.pi (fun _ : Fin n => Ioi s), kernelMinor k n x
        ∂Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) / (n.factorial : ℝ) := by
  unfold kernelCoefficient
  rw [fredholm_halfLine_pi_measure]

/-- Explicit original Airy-kernel determinant integrals over the moving physical domain. -/
theorem TW2_halfLine_series (s : ℝ /- [definition] -/) :
    TW2 s = ∑' n : ℕ,
      (((∫ x in Set.univ.pi (fun _ : Fin n => Ioi s),
        Matrix.det (fun i j => RMTFoundations.Airy.airyKernelIntegral (x i) (x j))
        ∂Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) / (n.factorial : ℝ) : ℝ) : ℂ) * (-1)^n := by
  rw [TW2_halfLine]
  unfold kernelFredholm kernelSeries
  apply tsum_congr
  intro n
  dsimp only
  rw [kernelCoefficient_halfLine_integral]
  rfl

theorem TW1_halfLine_series (s : ℝ /- [definition] -/) :
    TW1 s = ∑' n : ℕ,
      (((∫ x in Set.univ.pi (fun _ : Fin n => Ioi (s/2)),
        Matrix.det (fun i j => RMTFoundations.Airy.airyAiReal (x i+x j))
        ∂Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) / (n.factorial : ℝ) : ℝ) : ℂ) * (-1)^n := by
  rw [TW1_halfLine]
  unfold kernelFredholm kernelSeries
  apply tsum_congr
  intro n
  dsimp only
  rw [kernelCoefficient_halfLine_integral]
  rfl

/-- A nonzero genuine Airy kernel and every real shift satisfy the translation interface. -/
lemma fredholm_shift_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧ ∀ s : ℝ,
      MeasurePreserving (fun x : ℝ => x+s) RMTFoundations.Airy.halfLineMeasure (fredholmHalfLineMeasure s) ∧
      (∀ n : ℕ, kernelCoefficient RMTFoundations.Airy.halfLineMeasure (fun x y => RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)) n =
        kernelCoefficient (fredholmHalfLineMeasure s) RMTFoundations.Airy.airyKernelIntegral n) := by
  refine ⟨RMTFoundations.AiryBounds.Ai_kernel_inhabitation.1, fun s => ⟨fredholm_measurePreserving_shift s, ?_⟩⟩
  intro n
  exact kernelCoefficient_halfLine_shift RMTFoundations.Airy.airyKernelIntegral s n

end RMTFoundations.AiryKernel

#print axioms RMTFoundations.AiryKernel.airy_solution_negative_witness
#print axioms RMTFoundations.AiryKernel.scaled_diagonal_integrable
#print axioms RMTFoundations.AiryKernel.Ai_ODE_joint_probe
#print axioms RMTFoundations.AiryKernel.Ai_negative_witness
#print axioms RMTFoundations.AiryKernel.Ai_scaled_diagonal_integrable
#print axioms RMTFoundations.AiryKernel.Ai_halfline_convolution_counterexample
#print axioms RMTFoundations.AiryKernel.Ai_shifted_halfline_convolution_counterexample
#print axioms RMTFoundations.AiryKernel.coordinate_det_bound
#print axioms RMTFoundations.AiryKernel.uniform_matrix_det_bound
#print axioms RMTFoundations.AiryKernel.weighted_matrix_det_bound
#print axioms RMTFoundations.AiryKernel.weighted_matrix_det_bound_sqrt
#print axioms RMTFoundations.AiryKernel.weighted_kernel_minor_bound
#print axioms RMTFoundations.AiryKernel.weighted_kernel_minor_bound_pow
#print axioms RMTFoundations.AiryKernel.weighted_matrix_joint_probe
#print axioms RMTFoundations.AiryKernel.weighted_matrix_all_binder_probe
#print axioms RMTFoundations.AiryKernel.kernelSeries
#print axioms RMTFoundations.AiryKernel.hadamardMajorant
#print axioms RMTFoundations.AiryKernel.stirling_simple_lower
#print axioms RMTFoundations.AiryKernel.hadamardMajorant_le_geometric
#print axioms RMTFoundations.AiryKernel.hadamardMajorant_summable
#print axioms RMTFoundations.AiryKernel.hadamard_weight_summable
#print axioms RMTFoundations.AiryKernel.kernelSeries_absolute
#print axioms RMTFoundations.AiryKernel.kernelSeries_entire
#print axioms RMTFoundations.AiryKernel.kernelSeries_family_continuous
#print axioms RMTFoundations.AiryKernel.kernelMinor
#print axioms RMTFoundations.AiryKernel.kernelCoefficient
#print axioms RMTFoundations.AiryKernel.kernelFredholm
#print axioms RMTFoundations.AiryKernel.kernelMinor_measurable
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_bound_of_minor_bound
#print axioms RMTFoundations.AiryKernel.kernelFredholm_entire_of_minor_bound
#print axioms RMTFoundations.AiryKernel.kernelMinor_continuousAt
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_continuousAt_of_minor_bound
#print axioms RMTFoundations.AiryKernel.kernelSeries_family_continuousAt
#print axioms RMTFoundations.AiryKernel.kernelFredholm_continuousAt_of_minor_bound
#print axioms RMTFoundations.AiryKernel.kernel_data_joint_inhabitation
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_congr_ae
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_congr_on_full_measure
#print axioms RMTFoundations.AiryKernel.kernelMinor_integrable_of_minor_bound
#print axioms RMTFoundations.AiryKernel.kernelFredholm_absolute_of_minor_bound
#print axioms RMTFoundations.AiryKernel.kernelFredholm_hasSum_of_minor_bound
#print axioms RMTFoundations.AiryKernel.hadamard_coefficients_joint_inhabitation
#print axioms RMTFoundations.AiryKernel.kernelFredholm_congr_on_full_measure
#print axioms RMTFoundations.AiryKernel.kernelFredholm_real_coupling
#print axioms RMTFoundations.AiryKernel.kernelMinor_tendsto
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_tendsto_of_minor_bound
#print axioms RMTFoundations.AiryKernel.kernelFredholm_tendsto_of_minor_bound
#print axioms RMTFoundations.AiryKernel.kernelMinor_congr_on_full_measure
#print axioms RMTFoundations.AiryKernel.Ai_kernel_exp_bound_uniform
#print axioms RMTFoundations.AiryKernel.Ai_kernel_exp_bound
#print axioms RMTFoundations.AiryKernel.K_kernel
#print axioms RMTFoundations.AiryKernel.Ai_product_exp_bound
#print axioms RMTFoundations.AiryKernel.Ai_product_integrable
#print axioms RMTFoundations.AiryKernel.K_Ai_abs_le
#print axioms RMTFoundations.AiryKernel.K_Ai_symm
#print axioms RMTFoundations.AiryKernel.Ai_product_kernel_identity
#print axioms RMTFoundations.AiryKernel.integral_exp_square_le_one
#print axioms RMTFoundations.AiryKernel.K_Ai_continuous
#print axioms RMTFoundations.AiryKernel.K_kernel_continuous
#print axioms RMTFoundations.AiryKernel.K_kernel_shift_continuous
#print axioms RMTFoundations.AiryKernel.K_kernel_exp_bound_uniform
#print axioms RMTFoundations.AiryKernel.K_kernel_memLp
#print axioms RMTFoundations.AiryKernel.K_operator
#print axioms RMTFoundations.AiryKernel.K_operator_integral_apply_ae
#print axioms RMTFoundations.AiryKernel.integrable_exp_mul_Lp
#print axioms RMTFoundations.AiryKernel.Ai_composition_integrable
#print axioms RMTFoundations.AiryKernel.H_square_eq_K_operator
#print axioms RMTFoundations.AiryKernel.positiveExtension
#print axioms RMTFoundations.AiryKernel.positiveExtension_measurable
#print axioms RMTFoundations.AiryKernel.positiveExtension_ae
#print axioms RMTFoundations.AiryKernel.positiveExtension_bound
#print axioms RMTFoundations.AiryKernel.positiveExtension_shift_continuous
#print axioms RMTFoundations.AiryKernel.B_fredholmKernel
#print axioms RMTFoundations.AiryKernel.K_fredholmKernel
#print axioms RMTFoundations.AiryKernel.B_fredholmKernel_measurable
#print axioms RMTFoundations.AiryKernel.K_fredholmKernel_measurable
#print axioms RMTFoundations.AiryKernel.B_fredholmKernel_shift_continuous
#print axioms RMTFoundations.AiryKernel.K_fredholmKernel_shift_continuous
#print axioms RMTFoundations.AiryKernel.B_fredholmKernel_bound_uniform
#print axioms RMTFoundations.AiryKernel.K_fredholmKernel_bound_uniform
#print axioms RMTFoundations.AiryKernel.airy_fredholm_weight_probe
#print axioms RMTFoundations.AiryKernel.B_square_eq_K_operator
#print axioms RMTFoundations.AiryKernel.kernelFredholm_entire_of_kernel_bound
#print axioms RMTFoundations.AiryKernel.B_fredholm_entire
#print axioms RMTFoundations.AiryKernel.K_fredholm_entire
#print axioms RMTFoundations.AiryKernel.B_fredholm_continuous
#print axioms RMTFoundations.AiryKernel.K_fredholm_continuous
#print axioms RMTFoundations.AiryKernel.B_fredholm_physical
#print axioms RMTFoundations.AiryKernel.K_fredholm_physical
#print axioms RMTFoundations.AiryKernel.TW1
#print axioms RMTFoundations.AiryKernel.TW2
#print axioms RMTFoundations.AiryKernel.TW1_continuous
#print axioms RMTFoundations.AiryKernel.TW2_continuous
#print axioms RMTFoundations.AiryKernel.TW1_im_zero
#print axioms RMTFoundations.AiryKernel.TW2_im_zero
#print axioms RMTFoundations.AiryKernel.B_physical_minor_integrable
#print axioms RMTFoundations.AiryKernel.B_physical_fredholm_absolute
#print axioms RMTFoundations.AiryKernel.K_physical_minor_integrable
#print axioms RMTFoundations.AiryKernel.K_physical_fredholm_absolute
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_zero_order
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_zero_kernel_succ
#print axioms RMTFoundations.AiryKernel.kernelFredholm_zero_kernel
#print axioms RMTFoundations.AiryKernel.Ai_tendsto_atTop_zero
#print axioms RMTFoundations.AiryKernel.B_fredholmKernel_tendsto_zero
#print axioms RMTFoundations.AiryKernel.K_kernel_vanishing_bound
#print axioms RMTFoundations.AiryKernel.B_kernel_vanishing_bound
#print axioms RMTFoundations.AiryKernel.K_fredholmKernel_tendsto_zero
#print axioms RMTFoundations.AiryKernel.B_fredholm_tendsto_atTop_one
#print axioms RMTFoundations.AiryKernel.K_fredholm_tendsto_atTop_one
#print axioms RMTFoundations.AiryKernel.TW1_tendsto_atTop_one
#print axioms RMTFoundations.AiryKernel.TW2_tendsto_atTop_one
#print axioms RMTFoundations.AiryKernel.TW1R
#print axioms RMTFoundations.AiryKernel.TW2R
#print axioms RMTFoundations.AiryKernel.TW1R_coe
#print axioms RMTFoundations.AiryKernel.TW2R_coe
#print axioms RMTFoundations.AiryKernel.TW1R_continuous
#print axioms RMTFoundations.AiryKernel.TW2R_continuous
#print axioms RMTFoundations.AiryKernel.TW1R_tendsto_atTop_one
#print axioms RMTFoundations.AiryKernel.TW2R_tendsto_atTop_one
#print axioms RMTFoundations.AiryKernel.B_kernel_bound_with_tendsto_constant
#print axioms RMTFoundations.AiryKernel.K_kernel_bound_with_tendsto_constant
#print axioms RMTFoundations.AiryKernel.fredholm_limits_real_joint_probe
#print axioms RMTFoundations.AiryKernel.fredholmHalfLineMeasure
#print axioms RMTFoundations.AiryKernel.fredholm_measurePreserving_shift
#print axioms RMTFoundations.AiryKernel.fredholm_measurePreserving_pi_shift
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_halfLine_shift
#print axioms RMTFoundations.AiryKernel.kernelFredholm_halfLine_shift
#print axioms RMTFoundations.AiryKernel.K_fredholm_halfLine
#print axioms RMTFoundations.AiryKernel.TW2_halfLine
#print axioms RMTFoundations.AiryKernel.B_fredholm_halfLine
#print axioms RMTFoundations.AiryKernel.TW1_halfLine
#print axioms RMTFoundations.AiryKernel.B_fredholm_halfLine_full_shift
#print axioms RMTFoundations.AiryKernel.K_halfLine_minor_integrable
#print axioms RMTFoundations.AiryKernel.B_halfLine_minor_integrable
#print axioms RMTFoundations.AiryKernel.K_halfLine_fredholm_absolute
#print axioms RMTFoundations.AiryKernel.B_halfLine_fredholm_absolute
#print axioms RMTFoundations.AiryKernel.fredholm_halfLine_pi_measure
#print axioms RMTFoundations.AiryKernel.kernelCoefficient_halfLine_integral
#print axioms RMTFoundations.AiryKernel.TW2_halfLine_series
#print axioms RMTFoundations.AiryKernel.TW1_halfLine_series
#print axioms RMTFoundations.AiryKernel.fredholm_shift_joint_probe
