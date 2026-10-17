import RMTFoundations.TracyWidom.OrderOneMonotone



set_option autoImplicit false

namespace RMTFoundations.TracyWidom.AiryCommutator

open RMTFoundations.Airy RMTFoundations.TWOneMonotone

/-- Exact kernel numerator identity, including the diagonal by antisymmetry. -/
theorem airy_kernel_multiplication_identity
    (x y : ℝ) -- [definition]
    : (x - y) * airyKernelIntegral x y =
      airyAiReal x * deriv airyAiReal y - deriv airyAiReal x * airyAiReal y := by
  by_cases h : x = y
  · subst y
    ring
  · rw [airyKernelIntegral_wronskian x y h]
    field_simp

/-- The common shift cancels in the multiplication commutator. -/
theorem shifted_airy_kernel_multiplication_identity
    (x y s : ℝ) -- [definition]
    : (x - y) * airyKernelIntegral (x + s) (y + s) =
      airyAiReal (x + s) * deriv airyAiReal (y + s) -
        deriv airyAiReal (x + s) * airyAiReal (y + s) := by
  simpa only [add_sub_add_right_eq_sub] using
    airy_kernel_multiplication_identity (x + s) (y + s)

/-- Exact finite weighted Airy-kernel commutator. This proves the matrix
identity without asserting a domain for the unbounded multiplication operator. -/
theorem finite_airy_multiplication_commutator
    (n : ℕ) -- [definition]
    (x w : Fin n → ℝ) -- [definition]
    (s : ℝ) -- [definition]
    : let K : Matrix (Fin n) (Fin n) ℝ := fun i j =>
        w i * airyKernelIntegral (x i + s) (x j + s) * w j
      Matrix.diagonal x * K - K * Matrix.diagonal x =
        Matrix.of (fun i j =>
          (w i * airyAiReal (x i + s)) * (w j * deriv airyAiReal (x j + s)) -
          (w i * deriv airyAiReal (x i + s)) * (w j * airyAiReal (x j + s))) := by
  dsimp only
  ext i j
  rw [Matrix.sub_apply]
  set_option backward.isDefEq.respectTransparency false in
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.of_apply]
  have h := shifted_airy_kernel_multiplication_identity (x i) (x j) s
  calc
    _ = w i * ((x i - x j) * airyKernelIntegral (x i + s) (x j + s)) * w j := by ring
    _ = _ := by rw [h]; ring

/-- A nondegenerate two-node, nonzero-weight instance exercises every binder. -/
theorem airy_commutator_joint_probe
    : ∃ x w : Fin 2 → ℝ, ∃ s : ℝ,
      x 0 ≠ x 1 ∧ (∀ i, w i ≠ 0) ∧ airyAiReal s ≠ 0 ∧
      (let K : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
        w i * airyKernelIntegral (x i + s) (x j + s) * w j
       Matrix.diagonal x * K - K * Matrix.diagonal x =
        Matrix.of (fun i j =>
          (w i * airyAiReal (x i + s)) * (w j * deriv airyAiReal (x j + s)) -
          (w i * deriv airyAiReal (x i + s)) * (w j * airyAiReal (x j + s)))) := by
  refine ⟨![0, 1], fun _ => 1, 0, ?_, ?_, airyAiReal_zero_pos.ne', ?_⟩
  · norm_num
  · intro i
    norm_num
  · exact finite_airy_multiplication_commutator 2 ![0, 1] (fun _ => 1) 0

end RMTFoundations.TracyWidom.AiryCommutator

#print axioms RMTFoundations.TracyWidom.AiryCommutator.airy_kernel_multiplication_identity
#print axioms RMTFoundations.TracyWidom.AiryCommutator.shifted_airy_kernel_multiplication_identity
#print axioms RMTFoundations.TracyWidom.AiryCommutator.finite_airy_multiplication_commutator
#print axioms RMTFoundations.TracyWidom.AiryCommutator.airy_commutator_joint_probe
