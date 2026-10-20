import RMTFoundations.TracyWidom.Airy2
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel
open MeasureTheory Set Filter
open RMTFoundations.Airy RMTFoundations.AiryKernel
/-- The formal candidate is real even before its absolute-convergence proof. -/
theorem airy2FredholmCandidate_real
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    airy2FredholmCandidate m times cuts =
      ((∑' n, kernelCoefficient (timeSpaceMeasure m)
        (shiftedExtendedKernel m times cuts) n * (-1 : ℝ)^n : ℝ) : ℂ) := by
  simpa only [airy2FredholmCandidate,Complex.ofReal_neg,Complex.ofReal_one] using
    kernelFredholm_real_coupling (timeSpaceMeasure m) (shiftedExtendedKernel m times cuts) (-1)

/-- A time-label permutation is a measurable equivalence of the actual disjoint union. -/
def timeLabelEquiv
    (m : ℕ /- [definition] -/)
    (e : Equiv.Perm (Fin m) /- [definition] -/) : TimeSpace m ≃ᵐ TimeSpace m where
  toEquiv := e.prodCongr (Equiv.refl ℝ)
  measurable_toFun := by
    change Measurable (fun p : TimeSpace m => (e p.1,p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : TimeSpace m => (e.symm p.1,p.2))
    fun_prop

/-- Labels carry counting measure; hence their permutations preserve the product measure. -/
theorem timeLabel_measurePreserving
    (m : ℕ /- [definition] -/)
    (e : Equiv.Perm (Fin m) /- [definition] -/) :
    MeasurePreserving (timeLabelEquiv m e) (timeSpaceMeasure m) (timeSpaceMeasure m) := by
  have hp : MeasurePreserving e (Measure.count : Measure (Fin m)) Measure.count := by
    refine ⟨by fun_prop,?_⟩
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs,
      Measure.count_apply (hs.preimage (by fun_prop)),Measure.count_apply hs]
    rw [← e.injective.encard_image]
    rw [Set.image_preimage_eq s e.surjective]
  exact hp.prod (MeasurePreserving.id halfLineMeasure)

/-- Relabeling all integration variables preserves each Fredholm coefficient. -/
theorem kernelCoefficient_timeLabel
    (m n : ℕ /- [definition] -/)
    (e : Equiv.Perm (Fin m) /- [definition] -/)
    (k : TimeSpace m → TimeSpace m → ℝ /- [definition] -/) :
    kernelCoefficient (timeSpaceMeasure m)
      (fun p q => k (timeLabelEquiv m e p) (timeLabelEquiv m e q)) n =
        kernelCoefficient (timeSpaceMeasure m) k n := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  unfold kernelCoefficient
  congr 1
  exact (measurePreserving_pi _ _ (fun _ : Fin n => timeLabel_measurePreserving m e)).integral_comp
    (MeasurableEquiv.piCongrRight (fun _ : Fin n => timeLabelEquiv m e)).measurableEmbedding
    (kernelMinor k n)

/-- The physical formal series is invariant under simultaneous time/cut permutations. -/
theorem airy2FredholmCandidate_permute
    (m : ℕ /- [definition] -/)
    (e : Equiv.Perm (Fin m) /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/) :
    airy2FredholmCandidate m (times ∘ e) (cuts ∘ e) =
      airy2FredholmCandidate m times cuts := by
  unfold airy2FredholmCandidate kernelFredholm kernelSeries
  apply tsum_congr
  intro n
  exact congrArg (fun v : ℝ => (v : ℂ)*(-1 : ℂ)^n)
    (kernelCoefficient_timeLabel m n e (shiftedExtendedKernel m times cuts))

/-- Real values and a nontrivial two-label swap coexist on physical data. -/
theorem relabel_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      airy2FredholmCandidate 2 (times ∘ Equiv.swap 0 1) (cuts ∘ Equiv.swap 0 1) =
        airy2FredholmCandidate 2 times cuts ∧
      (airy2FredholmCandidate 2 times cuts).im = 0 := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,airy2FredholmCandidate_permute _ _ _ _,?_⟩
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · rw [airy2FredholmCandidate_real]
    exact Complex.ofReal_im _

/-- The zero-dimensional candidate has the normalization required by an empty marginal. -/
theorem airy2FredholmCandidate_empty
    (times cuts : Fin 0 → ℝ /- [definition] -/) :
    airy2FredholmCandidate 0 times cuts = 1 := by
  letI : SigmaFinite (timeSpaceMeasure 0) := by unfold timeSpaceMeasure; infer_instance
  have hk : shiftedExtendedKernel 0 times cuts = fun _ _ => 0 := by
    funext p q
    exact p.1.elim0
  unfold airy2FredholmCandidate
  rw [hk]
  exact kernelFredholm_zero_kernel _ _

/-- Empty normalization and a nonempty physical two-time permutation jointly hold. -/
theorem empty_relabel_all_binder_joint_probe :
    airy2FredholmCandidate 0 (fun i => i.elim0) (fun i => i.elim0) = 1 ∧
    airyAiReal 0 ≠ 0 ∧
    airy2FredholmCandidate 2 ((fun i : Fin 2 => (i.val : ℝ)) ∘ Equiv.swap 0 1)
      ((fun i : Fin 2 => if i=0 then -1 else 1) ∘ Equiv.swap 0 1) =
      airy2FredholmCandidate 2 (fun i => (i.val : ℝ)) (fun i => if i=0 then -1 else 1) := by
  exact ⟨airy2FredholmCandidate_empty _ _,airyAiReal_zero_pos.ne',
    airy2FredholmCandidate_permute _ _ _ _⟩

end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_real
#print axioms RMTFoundations.TracyWidom.Airy2.timeLabelEquiv
#print axioms RMTFoundations.TracyWidom.Airy2.timeLabel_measurePreserving
#print axioms RMTFoundations.TracyWidom.Airy2.kernelCoefficient_timeLabel
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_permute
#print axioms RMTFoundations.TracyWidom.Airy2.relabel_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_empty
#print axioms RMTFoundations.TracyWidom.Airy2.empty_relabel_all_binder_joint_probe
