import RMTFoundations.TracyWidom.Airy2Continuity
import RMTFoundations.TracyWidom.Airy2Deletion
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel

/-- Uniform physical envelope whose constants depend on times only, for arbitrary thresholds. -/
theorem finiteTime_uniform_spatial_envelope
    (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ cuts p q,
      |shiftedExtendedKernel m times cuts p q| ≤
        C*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)) := by
  obtain ⟨a,ha,ha1,hgap⟩ := finiteTime_positive_rate m times
  obtain ⟨D,hD,hAi⟩ := Ai_slow_exponential_envelope
  let E : ℝ := D^2 * ∫ u, Real.exp (-(2*a)*u) ∂halfLineMeasure
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => Real.exp_nonneg _))
  refine ⟨a,E+1,ha,by linarith,?_⟩
  intro cuts p q
  exact (extendedAiryKernel_spatial_envelope D a _ _ _ _ hD.le ha
    (hAi a ha.le ha1) (hgap p.1 q.1)).trans
      (by dsimp [E]; gcongr; linarith)

/-- Sending one threshold to infinity deletes its actual physical kernel rows and columns.
The limit is the determinant on surviving labels, not a probability assertion. -/
theorem airy2FredholmCandidate_tendsto_remove_label
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/)
    (j : Fin m /- [definition] -/) :
    Tendsto (fun s : ℝ => airy2FredholmCandidate m times
      (fun i => cuts i + if i=j then s else 0)) atTop
      (𝓝 (kernelFredholm (timeSpaceMeasure m)
        (fun p q => if p.1≠j ∧ q.1≠j then shiftedExtendedKernel m times cuts p q else 0) (-1))) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  obtain ⟨a,C,ha,hC,hb⟩ := finiteTime_uniform_spatial_envelope m times
  let cs : ℝ → Fin m → ℝ := fun s i => cuts i + if i=j then s else 0
  have he : Tendsto (fun s : ℝ => Real.exp (-a*s)) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def,id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop ha tendsto_id)
  have heq : ∀ (s : ℝ) (p q : TimeSpace m),
      C*Real.exp (-a*(p.2+cs s p.1))*Real.exp (-a*(q.2+cs s q.1)) =
      (C*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1))) *
        ((if p.1=j then Real.exp (-a*s) else 1)*(if q.1=j then Real.exp (-a*s) else 1)) := by
    intro s p q
    dsimp [cs]
    split_ifs <;> simp only [add_zero, mul_add, neg_mul, Real.exp_add] <;> ring
  change Tendsto (fun s => kernelFredholm (timeSpaceMeasure m)
    (shiftedExtendedKernel m times (cs s)) (-1)) atTop _
  apply kernelFredholm_tendsto_of_minor_bound (timeSpaceMeasure m) atTop
    (fun s => shiftedExtendedKernel m times (cs s))
    (fun p q => if p.1≠j ∧ q.1≠j then shiftedExtendedKernel m times cuts p q else 0)
    (fun p => Real.exp (-a*(p.2+cuts p.1))) C hC.le
    (timeSpace_exponential_square_integrable m cuts a ha)
  · exact Eventually.of_forall (fun s => shiftedExtendedKernel_measurable m times (cs s))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    intro n x
    apply weighted_kernel_minor_bound_pow n (shiftedExtendedKernel m times (cs s)) C
      (fun p => Real.exp (-a*(p.2+cuts p.1))) x hC.le (fun _ => Real.exp_nonneg _)
    intro p q
    apply (hb (cs s) p q).trans
    have hp : Real.exp (-a*(p.2+cs s p.1)) ≤ Real.exp (-a*(p.2+cuts p.1)) := by
      apply Real.exp_le_exp.mpr
      dsimp [cs]
      split_ifs <;> nlinarith
    have hq : Real.exp (-a*(q.2+cs s q.1)) ≤ Real.exp (-a*(q.2+cuts q.1)) := by
      apply Real.exp_le_exp.mpr
      dsimp [cs]
      split_ifs <;> nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hq (Real.exp_nonneg _)
      (mul_nonneg hC.le (Real.exp_nonneg _))
  · intro p q
    by_cases hp : p.1=j
    · simp only [hp,ne_eq,not_true_eq_false,false_and,if_false]
      apply squeeze_zero_norm'
      · exact Eventually.of_forall (fun s => by
          simpa only [Real.norm_eq_abs,heq] using hb (cs s) p q)
      · simp only [hp,if_true]
        by_cases hq : q.1=j
        · simpa only [hp,hq,if_true,mul_zero] using (he.mul he).const_mul
            (C*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)))
        · simpa only [hp,hq,if_false,mul_one,mul_zero] using he.const_mul
            (C*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)))
    · by_cases hq : q.1=j
      · simp only [hq,ne_eq,not_true_eq_false,and_false,if_false]
        apply squeeze_zero_norm'
        · exact Eventually.of_forall (fun s => by
            simpa only [Real.norm_eq_abs,heq] using hb (cs s) p q)
        · simpa only [hp,hq,if_false,if_true,one_mul,mul_zero] using he.const_mul
            (C*Real.exp (-a*(p.2+cuts p.1))*Real.exp (-a*(q.2+cuts q.1)))
      · have hsame : ∀ s, shiftedExtendedKernel m times (cs s) p q =
            shiftedExtendedKernel m times cuts p q := by
          intro s
          simp [shiftedExtendedKernel,cs,hp,hq]
        simpa only [hp,hq,ne_eq,not_false_eq_true,and_self,if_true,hsame] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => shiftedExtendedKernel m times cuts p q)
            atTop (𝓝 (shiftedExtendedKernel m times cuts p q)))

/-- Removal and its non-event binders hold jointly on an actual nonzero two-time Airy model. -/
theorem removal_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      Tendsto (fun s : ℝ => airy2FredholmCandidate 2 times
        (fun i => cuts i + if i=(1 : Fin 2) then s else 0)) atTop
        (𝓝 (kernelFredholm (timeSpaceMeasure 2)
          (fun p q => if p.1≠(1 : Fin 2) ∧ q.1≠1 then shiftedExtendedKernel 2 times cuts p q else 0) (-1))) := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,airy2FredholmCandidate_tendsto_remove_label _ _ _ _⟩
  intro i j hij
  exact Nat.cast_lt.mpr hij

/-- A diverging threshold gives exactly the determinant on the surviving measured time slices. -/
theorem airy2FredholmCandidate_tendsto_remove_label_restrict
    (m : ℕ /- [definition] -/)
    (times cuts : Fin m → ℝ /- [definition] -/)
    (j : Fin m /- [definition] -/) :
    Tendsto (fun s : ℝ => airy2FredholmCandidate m times
      (fun i => cuts i + if i=j then s else 0)) atTop
      (𝓝 (kernelFredholm ((timeSpaceMeasure m).restrict {p : TimeSpace m | p.1≠j})
        (shiftedExtendedKernel m times cuts) (-1))) := by
  letI : SigmaFinite (timeSpaceMeasure m) := by unfold timeSpaceMeasure; infer_instance
  have hmask : kernelFredholm (timeSpaceMeasure m)
      (fun p q => if p.1≠j ∧ q.1≠j then shiftedExtendedKernel m times cuts p q else 0) (-1) =
      kernelFredholm ((timeSpaceMeasure m).restrict {p : TimeSpace m | p.1≠j})
        (shiftedExtendedKernel m times cuts) (-1) := by
    refine Eq.trans ?_ (kernelFredholm_mask_restrict (timeSpaceMeasure m)
      {p : TimeSpace m | p.1≠j} (by measurability) (shiftedExtendedKernel m times cuts) (-1))
    apply congrArg (fun f : TimeSpace m → TimeSpace m → ℝ =>
      kernelFredholm (timeSpaceMeasure m) f (-1))
    funext p q
    by_cases h : p.1≠j ∧ q.1≠j <;> simp [h]
  rw [← hmask]
  exact airy2FredholmCandidate_tendsto_remove_label m times cuts j

/-- For two times, removing the second label leaves the exact first-time TW2 marginal value. -/
theorem airy2FredholmCandidate_two_time_remove_second
    (times cuts : Fin 2 → ℝ /- [definition] -/) :
    Tendsto (fun s : ℝ => airy2FredholmCandidate 2 times
      (fun i => cuts i + if i=(1 : Fin 2) then s else 0)) atTop
      (𝓝 (RMTFoundations.TracyWidom.TW2 (cuts 0))) := by
  have hm : (fun p q : TimeSpace 2 => if p.1≠(1 : Fin 2) ∧ q.1≠1
      then shiftedExtendedKernel 2 times cuts p q else 0) =
      (fun p q : TimeSpace 2 => if p.1=(0 : Fin 2) ∧ q.1=0
        then shiftedExtendedKernel 2 times cuts p q else 0) := by
    funext p q
    rcases p with ⟨p,x⟩
    rcases q with ⟨q,y⟩
    fin_cases p <;> fin_cases q <;> simp
  simpa only [hm,removedLabels_Fredholm_eq_TW2] using
    airy2FredholmCandidate_tendsto_remove_label 2 times cuts 1

/-- Genuine physical mixed-threshold data instantiate both surviving-slice and TW2 limit conclusions. -/
theorem marginal_limit_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ ∃ times cuts : Fin 2 → ℝ,
      StrictMono times ∧ cuts 0 = -1 ∧ cuts 1 = 1 ∧
      Tendsto (fun s : ℝ => airy2FredholmCandidate 2 times
        (fun i => cuts i + if i=(1 : Fin 2) then s else 0)) atTop
        (𝓝 (RMTFoundations.TracyWidom.TW2 (-1))) := by
  refine ⟨airyAiReal_zero_pos.ne',fun i => (i.val : ℝ),fun i => if i=0 then -1 else 1,
    ?_,by norm_num,by norm_num,?_⟩
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · simpa using airy2FredholmCandidate_two_time_remove_second (fun i => (i.val : ℝ))
      (fun i => if i=0 then -1 else 1)

end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.finiteTime_uniform_spatial_envelope
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_tendsto_remove_label
#print axioms RMTFoundations.TracyWidom.Airy2.removal_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_tendsto_remove_label_restrict
#print axioms RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_two_time_remove_second
#print axioms RMTFoundations.TracyWidom.Airy2.marginal_limit_all_binder_joint_probe
