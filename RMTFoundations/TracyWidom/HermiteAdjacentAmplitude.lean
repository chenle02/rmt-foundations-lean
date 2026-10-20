import RMTFoundations.TracyWidom.HermiteAiryCompact
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteAdjacentAmplitude
open Filter Topology
open RMTFoundations.TracyWidom.HermiteAiryCompact RMTFoundations.Airy
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.TracyWidom.HermiteEdgeScale
open RMTFoundations.TracyWidom.HermiteEdgeODE RMTFoundations.TracyWidom.GUEHermite

/-- The same actual mode evaluated at any converging edge coordinate. -/
theorem hermite_edge_moving_point (b : ℕ → ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (hb : Tendsto b atTop (𝓝 x) /- [standing] -/) :
    Tendsto (fun n : ℕ => edgeMode (n+1) (b n)) atTop (𝓝 (airyAiReal x)) := by
  have hnear : ∀ᶠ n : ℕ in atTop, |b n| ≤ |x|+1 := by
    have he := (Metric.tendsto_nhds.mp hb) 1 zero_lt_one
    filter_upwards [he] with n hn
    have ht := abs_add_le (b n-x) x
    rw [sub_add_cancel] at ht
    rw [Real.dist_eq] at hn
    linarith
  have herr : Tendsto (fun n : ℕ => edgeMode (n+1) (b n)-airyAiReal (b n))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hnear,hermite_edge_locally_uniform (|x|+1) (by positivity) ε hε] with n hn hu
    simpa [Real.dist_eq] using hu (b n) hn
  have hAi := (hasDerivAt_airyAiReal x).continuousAt.tendsto.comp hb
  simpa using herr.add hAi

noncomputable def stepRatio (n : ℕ /- [definition] -/) : ℝ :=
  1+1/((n+1 : ℕ) : ℝ)
noncomputable def shiftedCoordinate (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  (2/(Real.sqrt (stepRatio n)+1))*((n+1 : ℕ) : ℝ)^(-1/3 : ℝ)+
    (stepRatio n)^(-1/6 : ℝ)*x

lemma stepRatio_pos (n : ℕ /- [definition] -/) : 0 < stepRatio n := by
  unfold stepRatio
  positivity
lemma stepRatio_mul (n : ℕ /- [definition] -/) :
    ((n+2 : ℕ) : ℝ) = ((n+1 : ℕ) : ℝ)*stepRatio n := by
  unfold stepRatio
  push_cast
  field_simp
  ring
lemma stepRatio_tendsto : Tendsto stepRatio atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n : ℕ => 1+1/((n+1 : ℕ) : ℝ)) atTop (𝓝 1)
  simpa [Function.comp_def,one_div] using (tendsto_inv_atTop_zero.comp hn).const_add 1
lemma shiftedCoordinate_tendsto (x : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => shiftedCoordinate n x) atTop (𝓝 x) := by
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp stepRatio_tendsto
  have hp := (Real.continuousAt_rpow_const 1 (-1/6 : ℝ) (Or.inl (by norm_num))).tendsto.comp stepRatio_tendsto
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hd := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/3 by norm_num)).comp hn
  have hc := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).div (hroot.add_const 1) (by norm_num : Real.sqrt (1 : ℝ)+1 ≠ 0)).mul hd
  simpa [shiftedCoordinate,Function.comp_def,div_eq_mul_inv] using hc.add (hp.mul_const x)

lemma step_edgePoint (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    edgePoint (n+2) x = edgePoint (n+1) (shiftedCoordinate n x) := by
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hr := stepRatio_pos n
  have hs : Real.sqrt ((n+2 : ℕ) : ℝ) =
      Real.sqrt ((n+1 : ℕ) : ℝ)*Real.sqrt (stepRatio n) := by
    rw [stepRatio_mul,Real.sqrt_mul hn.le]
  have hscale : edgeScale (n+2) = edgeScale (n+1)*(stepRatio n)^(-1/6 : ℝ) := by
    unfold edgeScale
    rw [stepRatio_mul,Real.mul_rpow hn.le hr.le]
  have hnroot := Real.sq_sqrt hn.le
  have hrroot := Real.sq_sqrt hr.le
  have hcenter : 2*Real.sqrt ((n+2 : ℕ) : ℝ)-2*Real.sqrt ((n+1 : ℕ) : ℝ) =
      edgeScale (n+1)*(2/(Real.sqrt (stepRatio n)+1))*((n+1 : ℕ) : ℝ)^(-1/3 : ℝ) := by
    rw [hs]
    have he : edgeScale (n+1)*((n+1 : ℕ) : ℝ)^(-1/3 : ℝ) =
        1/Real.sqrt ((n+1 : ℕ) : ℝ) := by
      rw [edgeScale,←Real.rpow_add hn,Real.sqrt_eq_rpow,one_div,←Real.rpow_neg hn.le]
      norm_num
    have hden : Real.sqrt (stepRatio n)+1 ≠ 0 := by positivity
    have hsq : Real.sqrt ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hratio : stepRatio n-1 = 1/((n+1 : ℕ) : ℝ) := by unfold stepRatio;ring
    calc
      _ = 2*Real.sqrt ((n+1 : ℕ) : ℝ)*(Real.sqrt (stepRatio n)-1) := by ring
      _ = 2*Real.sqrt ((n+1 : ℕ) : ℝ)*(stepRatio n-1)/(Real.sqrt (stepRatio n)+1) := by
        field_simp
        nlinarith [hrroot]
      _ = _ := by
        rw [hratio]
        calc
          _ = (edgeScale (n+1)*((n+1 : ℕ) : ℝ)^(-1/3 : ℝ))*(2/(Real.sqrt (stepRatio n)+1)) := by
            rw [he]
            field_simp
            nlinarith [hnroot]
          _ = _ := by ring
  unfold edgePoint shiftedCoordinate
  rw [hscale]
  linarith

lemma step_edgeAmplitude (n : ℕ /- [definition] -/) :
    edgeAmplitude (n+2) = (stepRatio n)^(1/12 : ℝ)*edgeAmplitude (n+1) := by
  unfold edgeAmplitude
  rw [stepRatio_mul,Real.mul_rpow (by positivity) (stepRatio_pos n).le,mul_comm]

/-- Neighboring degree n+1 at the physical center/scale of n+2. No new mode definition. -/
theorem adjacent_edge_tendsto (x : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => edgeAmplitude (n+2)*hermiteMode (n+1) (edgePoint (n+2) x))
      atTop (𝓝 (airyAiReal x)) := by
  have hp := (Real.continuousAt_rpow_const 1 (1/12 : ℝ) (Or.inl (by norm_num))).tendsto.comp stepRatio_tendsto
  have hh := hp.mul (hermite_edge_moving_point (fun n => shiftedCoordinate n x) x
    (shiftedCoordinate_tendsto x))
  simpa only [Real.one_rpow,one_mul] using hh.congr' (Filter.Eventually.of_forall (fun n => by
    rw [step_edgePoint,step_edgeAmplitude]
    unfold edgeMode affineMode edgePoint
    dsimp only [Function.comp_def]
    ring))

theorem adjacent_amplitude_joint_probe :
    (∀ K : ℕ, ∃ n : ℕ, K < n+2) ∧
    (∀ n : ℕ, 0 < stepRatio n ∧ 0 < edgeAmplitude (n+2) ∧
      0 < hermiteDensity (n+2) (fun i => (i.val : ℝ)) ∧
      edgePoint (n+2) 1 = edgePoint (n+1) (shiftedCoordinate n 1)) ∧
    Tendsto (fun n : ℕ => edgeAmplitude (n+2)*hermiteMode (n+1) (edgePoint (n+2) 1))
      atTop (𝓝 (airyAiReal 1)) ∧ 0 < airyAiReal 1 := by
  exact ⟨fun K => ⟨K,by omega⟩,fun n =>
    ⟨stepRatio_pos n,by unfold edgeAmplitude;positivity,
      hermite_density_all_binder_joint_probe.2 (n+1),step_edgePoint n 1⟩,
    adjacent_edge_tendsto 1,airyAiReal_pos_of_nonneg zero_le_one⟩
end RMTFoundations.TracyWidom.HermiteAdjacentAmplitude

#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.hermite_edge_moving_point
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.stepRatio
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.shiftedCoordinate
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.stepRatio_pos
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.stepRatio_mul
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.stepRatio_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.shiftedCoordinate_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.step_edgePoint
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.step_edgeAmplitude
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.adjacent_edge_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteAdjacentAmplitude.adjacent_amplitude_joint_probe
