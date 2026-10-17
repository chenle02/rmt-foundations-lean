import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic



set_option autoImplicit false

namespace RMTFoundations.TracyWidom.GUEHermite

open Polynomial Matrix Finset

/-- The derivative lowering rule, derived from Mathlib's defining recursion. -/
theorem hermite_derivative_succ (n : ℕ /- [definition] -/) :
    derivative (hermite (n+1)) = C ((n+1 : ℕ) : ℤ) * hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ (n+1), derivative_sub, derivative_mul, derivative_X, one_mul, ih]
    rw [derivative_mul, derivative_C, zero_mul, zero_add]
    have hr := hermite_succ n
    have hc : C ((n+1+1 : ℕ) : ℤ) = C ((n+1 : ℕ) : ℤ) + 1 := by
      simp only [Nat.cast_add, Nat.cast_one, Polynomial.C_add, Polynomial.C_1]
    rw [hc, hr]
    ring

/-- Probabilists' three-term recurrence; this convention has edge 2 sqrt(N). -/
theorem hermite_three_term (n : ℕ /- [definition] -/) :
    hermite (n+2) = X * hermite (n+1) - C ((n+1 : ℕ) : ℤ) * hermite n := by
  rw [hermite_succ (n+1), hermite_derivative_succ]

/-- Real monic Hermite polynomial, with all integer coefficients retained. -/
noncomputable def realHermite (n : ℕ /- [definition] -/) : Polynomial ℝ :=
  (hermite n).map (Int.castRingHom ℝ)

noncomputable def hpoly (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ := (realHermite n).eval x

lemma hpoly_zero (x : ℝ /- [definition] -/) : hpoly 0 x = 1 := by
  simp [hpoly, realHermite]

lemma hpoly_one (x : ℝ /- [definition] -/) : hpoly 1 x = x := by
  simp [hpoly, realHermite]

lemma hpoly_three_term (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    hpoly (n+2) x = x * hpoly (n+1) x - (n+1 : ℕ) * hpoly n x := by
  simp only [hpoly, realHermite, hermite_three_term, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  norm_cast

/-- Polynomial part of the Hermite projection kernel. -/
noncomputable def polynomialKernel (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : ℝ :=
  ∑ k ∈ range N, hpoly k x * hpoly k y / (k.factorial : ℝ)

/-- Christoffel-Darboux without division by x-y: valid even on the diagonal. -/
theorem christoffel_darboux_cross (n : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    (x-y) * polynomialKernel (n+1) x y =
      (hpoly (n+1) x * hpoly n y - hpoly n x * hpoly (n+1) y) /
        (n.factorial : ℝ) := by
  induction n with
  | zero => simp [polynomialKernel, hpoly_zero, hpoly_one]
  | succ n ih =>
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hk : polynomialKernel (n+1+1) x y = polynomialKernel (n+1) x y +
        hpoly (n+1) x * hpoly (n+1) y / ((n+1).factorial : ℝ) := by
      exact sum_range_succ _ (n+1)
    rw [hk, mul_add, ih, hpoly_three_term n x, hpoly_three_term n y,
      Nat.factorial_succ, Nat.cast_mul]
    field_simp
    ring

/-- The off-diagonal quotient, with the nonzero denominator stated explicitly. -/
theorem christoffel_darboux (n : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/)
    (hxy : x ≠ y /- [standing] -/) :
    polynomialKernel (n+1) x y =
      (hpoly (n+1) x * hpoly n y - hpoly n x * hpoly (n+1) y) /
        ((n.factorial : ℝ) * (x-y)) := by
  have h := christoffel_darboux_cross n x y
  have hd : x-y ≠ 0 := sub_ne_zero.mpr hxy
  apply (eq_div_iff (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hd)).mpr
  have hh := (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mp h
  nlinarith [hh]

/-- Monicity and degree provide the literal Vandermonde determinant. -/
theorem hermite_evaluation_determinant (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    Matrix.det (fun i j : Fin N => hpoly j.val (x i)) =
      ∏ i : Fin N, ∏ j ∈ Ioi i, (x j - x i) := by
  have hd : ∀ j : Fin N, (realHermite j.val).natDegree = j.val := by
    intro j
    rw [realHermite, Polynomial.natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)]
    exact Polynomial.natDegree_hermite
  have hm : ∀ j : Fin N, (realHermite j.val).Monic := by
    intro j
    exact (Polynomial.hermite_monic j.val).map (Int.castRingHom ℝ)
  change Matrix.det (Matrix.of (fun i j : Fin N => (realHermite j.val).eval (x i))) = _
  rw [← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x
    (fun j : Fin N => realHermite j.val) hd hm, Matrix.det_vandermonde]

/-- Finite determinantal structure: a square feature Gram determinant is a square. -/
theorem gram_determinant (N : ℕ /- [definition] -/)
    (phi : Fin N → ℝ → ℝ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    Matrix.det (fun i j : Fin N => ∑ k : Fin N, phi k (x i) * phi k (x j)) =
      (Matrix.det (fun i k : Fin N => phi k (x i))) ^ 2 := by
  let V : Matrix (Fin N) (Fin N) ℝ := fun i k => phi k (x i)
  have he : (fun i j : Fin N => ∑ k : Fin N, phi k (x i) * phi k (x j)) = V * Vᵀ := by
    ext i j
    rfl
  rw [he, Matrix.det_mul, Matrix.det_transpose, pow_two]

/-- A nonnegative finite density numerator, before normalization/integration. -/
theorem gram_determinant_nonneg (N : ℕ /- [definition] -/)
    (phi : Fin N → ℝ → ℝ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    0 ≤ Matrix.det (fun i j : Fin N => ∑ k : Fin N, phi k (x i) * phi k (x j)) := by
  rw [gram_determinant]
  exact sq_nonneg _

/-- Gaussian weight in the requested 2 sqrt(N) convention. -/
noncomputable def gaussianWeight (x : ℝ /- [definition] -/) : ℝ :=
  Real.exp (-(x^2)/4)

noncomputable def hermiteNormalizer (k : ℕ /- [definition] -/) : ℝ :=
  1 / Real.sqrt (Real.sqrt (2 * Real.pi) * (k.factorial : ℝ))

/-- The actual normalized probabilists' Hermite oscillator functions. -/
noncomputable def hermiteMode (k : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  gaussianWeight x * (hermiteNormalizer k * hpoly k x)

lemma hermiteNormalizer_pos (k : ℕ /- [definition] -/) :
    0 < hermiteNormalizer k := by
  unfold hermiteNormalizer
  positivity

noncomputable def hermiteKernel (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : ℝ :=
  ∑ k : Fin N, hermiteMode k.val x * hermiteMode k.val y

lemma hermiteNormalizer_square (k : ℕ /- [definition] -/) :
    (hermiteNormalizer k)^2 = 1 / (Real.sqrt (2 * Real.pi) * (k.factorial : ℝ)) := by
  unfold hermiteNormalizer
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]

lemma sqrt_mul_hermiteNormalizer_succ (k : ℕ /- [definition] -/) :
    Real.sqrt ((k+1 : ℕ) : ℝ) * hermiteNormalizer (k+1) = hermiteNormalizer k := by
  unfold hermiteNormalizer
  rw [Nat.factorial_succ, Nat.cast_mul]
  have he : Real.sqrt (2 * Real.pi) * (((k+1 : ℕ) : ℝ) * (k.factorial : ℝ)) =
      ((k+1 : ℕ) : ℝ) * (Real.sqrt (2 * Real.pi) * (k.factorial : ℝ)) := by ring
  rw [he, Real.sqrt_mul (by positivity)]
  have hn : Real.sqrt ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

lemma hermiteMode_product (k : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    hermiteMode k x * hermiteMode k y =
      (gaussianWeight x * gaussianWeight y / Real.sqrt (2 * Real.pi)) *
      (hpoly k x * hpoly k y / (k.factorial : ℝ)) := by
  unfold hermiteMode
  calc
    gaussianWeight x * (hermiteNormalizer k * hpoly k x) *
        (gaussianWeight y * (hermiteNormalizer k * hpoly k y)) =
      gaussianWeight x * gaussianWeight y * (hermiteNormalizer k)^2 *
        (hpoly k x * hpoly k y) := by ring
    _ = _ := by
      rw [hermiteNormalizer_square]
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring

lemma hermiteKernel_eq_polynomialKernel (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    hermiteKernel N x y =
      (gaussianWeight x * gaussianWeight y / Real.sqrt (2 * Real.pi)) *
        polynomialKernel N x y := by
  simp only [hermiteKernel, hermiteMode_product]
  rw [← Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => hpoly k x * hpoly k y / (k.factorial : ℝ)) N

/-- Literal normalized Hermite CD, including the diagonal cross identity. -/
theorem hermite_christoffel_darboux_cross (n : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    (x-y) * hermiteKernel (n+1) x y =
      Real.sqrt ((n+1 : ℕ) : ℝ) *
        (hermiteMode (n+1) x * hermiteMode n y -
          hermiteMode n x * hermiteMode (n+1) y) := by
  have hn := sqrt_mul_hermiteNormalizer_succ n
  have hs := hermiteNormalizer_square n
  rw [hermiteKernel_eq_polynomialKernel]
  calc
    (x-y) * ((gaussianWeight x * gaussianWeight y / Real.sqrt (2 * Real.pi)) *
      polynomialKernel (n+1) x y) =
      (gaussianWeight x * gaussianWeight y / Real.sqrt (2 * Real.pi)) *
        ((x-y) * polynomialKernel (n+1) x y) := by ring
    _ = (gaussianWeight x * gaussianWeight y / Real.sqrt (2 * Real.pi)) *
        ((hpoly (n+1) x * hpoly n y - hpoly n x * hpoly (n+1) y) /
          (n.factorial : ℝ)) := by rw [christoffel_darboux_cross]
    _ = _ := by
      unfold hermiteMode
      have he : Real.sqrt ((n+1 : ℕ) : ℝ) *
          (gaussianWeight x * (hermiteNormalizer (n+1) * hpoly (n+1) x) *
            (gaussianWeight y * (hermiteNormalizer n * hpoly n y)) -
           gaussianWeight x * (hermiteNormalizer n * hpoly n x) *
            (gaussianWeight y * (hermiteNormalizer (n+1) * hpoly (n+1) y))) =
        gaussianWeight x * gaussianWeight y *
          ((Real.sqrt ((n+1 : ℕ) : ℝ) * hermiteNormalizer (n+1)) * hermiteNormalizer n) *
          (hpoly (n+1) x * hpoly n y - hpoly n x * hpoly (n+1) y) := by ring
      rw [he, hn, ← pow_two, hs]
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring

theorem hermite_christoffel_darboux (n : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/)
    (hxy : x ≠ y /- [standing] -/) :
    hermiteKernel (n+1) x y =
      Real.sqrt ((n+1 : ℕ) : ℝ) *
        (hermiteMode (n+1) x * hermiteMode n y -
          hermiteMode n x * hermiteMode (n+1) y) / (x-y) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).mpr
  simpa only [mul_comm] using hermite_christoffel_darboux_cross n x y

/-- The finite Hermite feature determinant, with Gaussian/factorial factors. -/
theorem hermite_mode_determinant (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    Matrix.det (fun i j : Fin N => hermiteMode j.val (x i)) =
      (∏ i : Fin N, gaussianWeight (x i)) *
      (∏ j : Fin N, hermiteNormalizer j.val) *
      (∏ i : Fin N, ∏ j ∈ Ioi i, (x j - x i)) := by
  change Matrix.det (Matrix.of (fun i j : Fin N =>
    gaussianWeight (x i) * (hermiteNormalizer j.val * hpoly j.val (x i)))) = _
  rw [Matrix.det_mul_column (fun i : Fin N => gaussianWeight (x i))
    (fun i j : Fin N => hermiteNormalizer j.val * hpoly j.val (x i))]
  change (∏ i : Fin N, gaussianWeight (x i)) *
    Matrix.det (Matrix.of (fun i j : Fin N => hermiteNormalizer j.val * hpoly j.val (x i))) = _
  rw [Matrix.det_mul_row (fun j : Fin N => hermiteNormalizer j.val)
    (fun i j : Fin N => hpoly j.val (x i))]
  change (∏ i : Fin N, gaussianWeight (x i)) *
    ((∏ j : Fin N, hermiteNormalizer j.val) * Matrix.det (fun i j : Fin N => hpoly j.val (x i))) = _
  rw [hermite_evaluation_determinant]
  ring

/-- Determinantal GUE eigenvalue density expression. Its identification with
the matrix pushforward and its unit integral remain separate analytic gaps. -/
noncomputable def hermiteDensity (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) : ℝ :=
  Matrix.det (fun i j : Fin N => hermiteKernel N (x i) (x j)) / (N.factorial : ℝ)

/-- Finite determinantal numerator is literally the Vandermonde square,
including every Gaussian weight and factorial normalization. -/
theorem hermite_density_formula (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) :
    hermiteDensity N x =
      ((∏ i : Fin N, gaussianWeight (x i)) *
      (∏ j : Fin N, hermiteNormalizer j.val) *
      (∏ i : Fin N, ∏ j ∈ Ioi i, (x j - x i))) ^ 2 / (N.factorial : ℝ) := by
  unfold hermiteDensity hermiteKernel
  rw [gram_determinant N (fun j y => hermiteMode j.val y), hermite_mode_determinant]

lemma hermite_density_nonneg (N : ℕ /- [definition] -/)
    (x : Fin N → ℝ /- [definition] -/) : 0 ≤ hermiteDensity N x := by
  rw [hermite_density_formula]
  positivity

/-- Every non-event binder of the density construction coexists with strict
positivity on distinct points in every growing dimension. -/
theorem hermite_density_all_binder_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ N : ℕ, 0 < hermiteDensity (N+1) (fun i => (i.val : ℝ))) := by
  refine ⟨fun K => ⟨K, Nat.lt_succ_self K⟩, fun N => ?_⟩
  rw [hermite_density_formula]
  have hw : 0 < ∏ i : Fin (N+1), gaussianWeight (i.val : ℝ) :=
    Finset.prod_pos (fun i _ => Real.exp_pos _)
  have hn : 0 < ∏ j : Fin (N+1), hermiteNormalizer j.val :=
    Finset.prod_pos (fun j _ => hermiteNormalizer_pos j.val)
  have hv : 0 < ∏ i : Fin (N+1), ∏ j ∈ Ioi i, ((j.val : ℝ) - (i.val : ℝ)) := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i.val < j.val := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
    exact sub_pos.mpr (by exact_mod_cast hij)
  exact div_pos (sq_pos_of_pos (mul_pos (mul_pos hw hn) hv))
    (by exact_mod_cast Nat.factorial_pos (N+1))

/-- Joint probe for every deterministic binder: actual Hermite functions,
dimension n+1 growing, distinct nonzero points and positive Gram determinant. -/
theorem hermite_all_binder_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, (0 : ℝ) ≠ n+1 ∧
      polynomialKernel (n+1) 0 (n+1) =
        (hpoly (n+1) 0 * hpoly n (n+1) - hpoly n 0 * hpoly (n+1) (n+1)) /
          ((n.factorial : ℝ) * (0-(n+1))) ) ∧
    (∀ N : ℕ, Matrix.det (fun i j : Fin (N+1) =>
      ∑ k : Fin (N+1), hpoly k.val (i.val : ℝ) * hpoly k.val (j.val : ℝ)) > 0) := by
  refine ⟨fun K => ⟨K, Nat.lt_succ_self K⟩, ?_, ?_⟩
  · intro n
    have hn : (0 : ℝ) ≠ n+1 := by positivity
    exact ⟨hn, christoffel_darboux n 0 (n+1) hn⟩
  · intro N
    rw [gram_determinant (N+1) (fun k x => hpoly k.val x), hermite_evaluation_determinant]
    have hV : Matrix.det (Matrix.vandermonde (fun i : Fin (N+1) => (i.val : ℝ))) ≠ 0 := by
      apply Matrix.det_vandermonde_ne_zero_iff.mpr
      intro i j h
      apply Fin.ext
      change (i.val : ℝ) = (j.val : ℝ) at h
      exact_mod_cast h
    rw [Matrix.det_vandermonde] at hV
    exact sq_pos_of_ne_zero hV

/-- The normalized CD and strict-density probes use the same growing Hermite
family; the off-diagonal standing premise is supplied, rather than re-taken. -/
theorem hermite_normalized_all_binder_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    (∀ n : ℕ, (0 : ℝ) ≠ n+1 ∧
      hermiteKernel (n+1) 0 (n+1) =
        Real.sqrt ((n+1 : ℕ) : ℝ) *
          (hermiteMode (n+1) 0 * hermiteMode n (n+1) -
            hermiteMode n 0 * hermiteMode (n+1) (n+1)) / (0-(n+1))) ∧
    (∀ N : ℕ, 0 < hermiteDensity (N+1) (fun i => (i.val : ℝ))) := by
  refine ⟨fun K => ⟨K, Nat.lt_succ_self K⟩, ?_,
    hermite_density_all_binder_joint_probe.2⟩
  intro n
  have hn : (0 : ℝ) ≠ n+1 := by positivity
  exact ⟨hn, hermite_christoffel_darboux n 0 (n+1) hn⟩

end RMTFoundations.TracyWidom.GUEHermite

#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_derivative_succ
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_three_term
#print axioms RMTFoundations.TracyWidom.GUEHermite.realHermite
#print axioms RMTFoundations.TracyWidom.GUEHermite.hpoly
#print axioms RMTFoundations.TracyWidom.GUEHermite.hpoly_zero
#print axioms RMTFoundations.TracyWidom.GUEHermite.hpoly_one
#print axioms RMTFoundations.TracyWidom.GUEHermite.hpoly_three_term
#print axioms RMTFoundations.TracyWidom.GUEHermite.polynomialKernel
#print axioms RMTFoundations.TracyWidom.GUEHermite.christoffel_darboux_cross
#print axioms RMTFoundations.TracyWidom.GUEHermite.christoffel_darboux
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_evaluation_determinant
#print axioms RMTFoundations.TracyWidom.GUEHermite.gram_determinant
#print axioms RMTFoundations.TracyWidom.GUEHermite.gram_determinant_nonneg
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.GUEHermite.gaussianWeight
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermiteNormalizer
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermiteMode
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermiteNormalizer_pos
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermiteKernel
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_mode_determinant
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermiteDensity
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_density_formula
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_density_nonneg
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_density_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermiteNormalizer_square
#print axioms RMTFoundations.TracyWidom.GUEHermite.sqrt_mul_hermiteNormalizer_succ
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermiteMode_product
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermiteKernel_eq_polynomialKernel
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_christoffel_darboux_cross
#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_christoffel_darboux

#print axioms RMTFoundations.TracyWidom.GUEHermite.hermite_normalized_all_binder_joint_probe
