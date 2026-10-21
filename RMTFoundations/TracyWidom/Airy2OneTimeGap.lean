import RMTFoundations.TracyWidom.Airy2RouteObstruction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.Airy2OneTimeGap
open Filter
open scoped Topology
open RMTFoundations.TracyWidom.Airy2 RMTFoundations.Airy

/-- An auxiliary countermodel preserving every equal-time block exactly.
It is not a Hermite/Dyson kernel and is never used as a physical producer. -/
noncomputable def equalTimeOnlyKernel
    (t r x y : ℝ /- [definition] -/) : ℝ :=
  if r=t then extendedAiryKernel t t x y else 0

theorem equalTimeOnlyKernel_diagonal
    (t x y : ℝ /- [definition] -/) :
    equalTimeOnlyKernel t t x y = extendedAiryKernel t t x y := by
  simp [equalTimeOnlyKernel]

/-- Even exact one-time convergence leaves the distinct-time limit undetermined. -/
theorem one_time_convergence_does_not_determine_extended_limit :
    (∀ t x y : ℝ, Tendsto (fun _ : ℕ => equalTimeOnlyKernel t t x y)
      atTop (𝓝 (extendedAiryKernel t t x y))) ∧
    ¬ Tendsto (fun _ : ℕ => equalTimeOnlyKernel 1 0 1 1)
      atTop (𝓝 (extendedAiryKernel 1 0 1 1)) := by
  refine ⟨fun t x y => ?_,?_⟩
  · simpa only [equalTimeOnlyKernel_diagonal] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => extendedAiryKernel t t x y)
        atTop (𝓝 (extendedAiryKernel t t x y)))
  · intro h
    have hz : Tendsto (fun _ : ℕ => equalTimeOnlyKernel 1 0 1 1)
        atTop (𝓝 (0 : ℝ)) := by
      simpa [equalTimeOnlyKernel] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have he := tendsto_nhds_unique hz h
    exact (forward_diagonal_space_pos 1 0 1 (by norm_num) (by norm_num)).ne' he.symm

/-- All equal-time and distinct-time countermodel fields hold on nonzero physical
Airy reference data; only the auxiliary replacement is artificial. -/
theorem extended_limit_gap_joint_counterprobe :
    airyAiReal 0 ≠ 0 ∧ (0 : ℝ) < 1 ∧
    (∀ t x y : ℝ, equalTimeOnlyKernel t t x y = extendedAiryKernel t t x y) ∧
    (∀ t x y : ℝ, Tendsto (fun _ : ℕ => equalTimeOnlyKernel t t x y)
      atTop (𝓝 (extendedAiryKernel t t x y))) ∧
    ¬ Tendsto (fun _ : ℕ => equalTimeOnlyKernel 1 0 1 1)
      atTop (𝓝 (extendedAiryKernel 1 0 1 1)) := by
  exact ⟨airyAiReal_zero_pos.ne',by norm_num,equalTimeOnlyKernel_diagonal,
    one_time_convergence_does_not_determine_extended_limit⟩

end RMTFoundations.TracyWidom.Airy2OneTimeGap

#print axioms RMTFoundations.TracyWidom.Airy2OneTimeGap.equalTimeOnlyKernel
#print axioms RMTFoundations.TracyWidom.Airy2OneTimeGap.equalTimeOnlyKernel_diagonal
#print axioms RMTFoundations.TracyWidom.Airy2OneTimeGap.one_time_convergence_does_not_determine_extended_limit
#print axioms RMTFoundations.TracyWidom.Airy2OneTimeGap.extended_limit_gap_joint_counterprobe
