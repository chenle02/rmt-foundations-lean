import RMTFoundations.TracyWidom.HermiteAiryAmplitude
import Mathlib.Topology.Sequences
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteAiryCompact
open Complex Filter Topology MeasureTheory
open RMTFoundations.TracyWidom.HermiteCubicSaddle RMTFoundations.TracyWidom.HermiteCircleCoordinate
open RMTFoundations.TracyWidom.HermiteCircleDominated RMTFoundations.TracyWidom.HermiteAiryContour
open RMTFoundations.TracyWidom.HermiteAiryAmplitude RMTFoundations.TracyWidom.HermiteEdgeNormalization
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.Airy

lemma cut_circle_sequence_tendsto (a : ℕ → ℕ /- [definition] -/)
    (b : ℕ → ℝ /- [definition] -/)
    (x t : ℝ /- [definition] -/)
    (ha : Tendsto a atTop atTop /- [standing] -/)
    (hb : Tendsto b atTop (𝓝 x) /- [standing] -/) :
    Tendsto (fun n : ℕ => cutCircle (a n+1) (b n) t) atTop (𝓝 (verticalIntegrand 1 x t)) := by
  have hu := (circle_coordinate_tendsto 1 t).comp ha
  have hp := (circle_phase_tendsto 1 x t).comp ha
  have hbC : Tendsto (fun n : ℕ => (b n : ℂ)) atTop (𝓝 (x : ℂ)) :=
    (Complex.continuous_ofReal.tendsto x).comp hb
  have he := hp.add ((hbC.sub_const (x : ℂ)).mul hu)
  simp only [sub_self,zero_mul,add_zero,Function.comp_def] at he
  have hf : Tendsto (fun n : ℕ => saddlePhase (a n+1) (b n) (circleCoordinate (a n+1) 1 t))
      atTop (𝓝 ((x : ℂ)*(-1+Complex.I*t)-(-1+Complex.I*t)^3/3)) := by
    convert he using 1
    · funext n
      unfold saddlePhase
      push_cast
      ring
  have hExp := Complex.continuous_exp.continuousAt.tendsto.comp hf
  apply hExp.congr'
  filter_upwards [ha.eventually (circle_domain_exhausts t)] with n hn
  simp only [cutCircle,if_pos hn.le,Function.comp_apply]

lemma circle_integral_sequence_tendsto (a : ℕ → ℕ /- [definition] -/)
    (b : ℕ → ℝ /- [definition] -/)
    (x R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (ha : Tendsto a atTop atTop /- [standing] -/)
    (hb : Tendsto b atTop (𝓝 x) /- [standing] -/)
    (hbound : ∀ n : ℕ, |b n| ≤ R /- [standing] -/) :
    Tendsto (fun n : ℕ => (1/(2*Real.pi))*∫ t : ℝ, (cutCircle (a n+1) (b n) t).re)
      atTop (𝓝 (airyAiReal x)) := by
  have hs := ha.eventually (saddle_scale_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))
  have hRd : Tendsto (fun n : ℕ => R*saddleScale (a n+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (saddle_scale_tendsto.comp ha).const_mul R
  have hd := hRd.eventually (gt_mem_nhds zero_lt_one)
  have hg : Integrable (fun t : ℝ => Real.exp (R+4/3)*Real.exp (-1/Real.pi^2*t^2)) := by
    simpa only [neg_div] using (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1/Real.pi^2)).const_mul (Real.exp (R+4/3))
  have hh := tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => Real.exp (R+4/3)*Real.exp (-1/Real.pi^2*t^2))
    (Filter.Eventually.of_forall (fun n : ℕ => (cut_circle_aestronglyMeasurable (a n+1) (b n)).re))
    (by
      filter_upwards [hs,hd] with n hn hdn
      apply ae_of_all
      intro t
      have hbx : |b n| *saddleScale (a n+1) ≤ 1 := by
        exact le_trans (mul_le_mul_of_nonneg_right (hbound n) (saddle_scale_pos _ (by omega)).le) hdn.le
      have hc : ‖cutCircle (a n+1) (b n) t‖ ≤
          Real.exp (R+4/3)*Real.exp (-1/Real.pi^2*t^2) := by
        unfold cutCircle
        split_ifs with ht
        · exact le_trans (circle_phase_gaussian _ (by omega) (b n) t hn.le hbx ht)
            (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hbound n])) (Real.exp_pos _).le)
        · simp only [norm_zero]
          positivity
      exact le_trans (by simpa using Complex.abs_re_le_norm (cutCircle (a n+1) (b n) t)) hc)
    hg (ae_of_all _ (fun t => (Complex.continuous_re.tendsto _).comp
      (cut_circle_sequence_tendsto a b x t ha hb)))
  have hmul := hh.const_mul (1/(2*Real.pi))
  rw [← airy_vertical_integral 1 x zero_lt_one] at hmul
  exact hmul

/-- Actual Hermite convergence along every convergent compact-window sequence. -/
theorem hermite_edge_sequence_tendsto (a : ℕ → ℕ /- [definition] -/)
    (b : ℕ → ℝ /- [definition] -/)
    (x R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (ha : Tendsto a atTop atTop /- [standing] -/)
    (hb : Tendsto b atTop (𝓝 x) /- [standing] -/)
    (hbound : ∀ n : ℕ, |b n| ≤ R /- [standing] -/) :
    Tendsto (fun n : ℕ => edgeMode (a n+1) (b n)) atTop (𝓝 (airyAiReal x)) := by
  have hf : Tendsto (fun n : ℕ => saddlePrefactor (a n+1) (b n)) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [ha.eventually (saddle_prefactor_locally_uniform R hR ε hε)] with n hn
    simpa only [Real.dist_eq] using hn (b n) (hbound n)
  have hh := hf.mul (circle_integral_sequence_tendsto a b x R hR ha hb hbound)
  simp only [one_mul] at hh
  apply hh.congr'
  have hs := ha.eventually (saddle_scale_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))
  have hRd : Tendsto (fun n : ℕ => R*saddleScale (a n+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (saddle_scale_tendsto.comp ha).const_mul R
  filter_upwards [hs,hRd.eventually (gt_mem_nhds zero_lt_one)] with n hn hdn
  have hbx : |b n| *saddleScale (a n+1) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (hbound n) (saddle_scale_pos _ (by omega)).le) hdn.le
  exact (edge_mode_circle_integral _ (by omega) (b n) hn.le hbx).symm

/-- The actual Airy amplitude is locally uniform, rather than only pointwise. -/
theorem hermite_edge_locally_uniform (R : ℝ /- [definition] -/)
    (hR : 0 ≤ R /- [standing] -/)
    (ε : ℝ /- [definition] -/)
    (hε : 0 < ε /- [standing] -/) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x| ≤ R → |edgeMode (n+1) x-airyAiReal x| < ε := by
  classical
  by_contra h
  have hfreq : ∃ᶠ n : ℕ in atTop, ∃ x : ℝ,
      |x| ≤ R ∧ ε ≤ |edgeMode (n+1) x-airyAiReal x| := by
    have hh := Filter.not_eventually.mp h
    exact hh.mono fun n hn => by
      push_neg at hn
      exact hn
  obtain ⟨a,ha,hbad⟩ := exists_seq_forall_of_frequently hfreq
  choose b hbR hbErr using hbad
  have hbI : ∀ n : ℕ, b n ∈ Set.Icc (-R) R := fun n => abs_le.mp (hbR n)
  obtain ⟨x,hx,φ,hφmono,hφ⟩ := isCompact_Icc.tendsto_subseq hbI
  have haφ := ha.comp hφmono.tendsto_atTop
  have hconv := hermite_edge_sequence_tendsto (a ∘ φ) (b ∘ φ) x R hR haφ hφ
    (fun n => hbR (φ n))
  have hAi := (hasDerivAt_airyAiReal x).continuousAt.tendsto.comp hφ
  have hErr : Tendsto (fun n : ℕ => |edgeMode (a (φ n)+1) (b (φ n))-airyAiReal (b (φ n))|)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hconv.sub hAi).abs
  obtain ⟨n,hn⟩ := (hErr.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbErr (φ n))) hn

theorem airy_compact_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+1) ∧
    Tendsto (fun n : ℕ => edgeMode (n+1) 1) atTop (𝓝 (airyAiReal 1)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x| ≤ 3 →
      |edgeMode (n+1) x-airyAiReal x| < ε) ∧ 0 < airyAiReal 1 := by
  exact ⟨fun K => ⟨K,Nat.lt_succ_self K⟩,
    hermite_edge_sequence_tendsto id (fun _ => 1) 1 3 (by norm_num) tendsto_id
      tendsto_const_nhds (fun _ => by norm_num),
    fun ε hε => hermite_edge_locally_uniform 3 (by norm_num) ε hε,
    airyAiReal_pos_of_nonneg zero_le_one⟩
end RMTFoundations.TracyWidom.HermiteAiryCompact

#print axioms RMTFoundations.TracyWidom.HermiteAiryCompact.cut_circle_sequence_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteAiryCompact.circle_integral_sequence_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteAiryCompact.hermite_edge_sequence_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteAiryCompact.hermite_edge_locally_uniform
#print axioms RMTFoundations.TracyWidom.HermiteAiryCompact.airy_compact_joint_probe
