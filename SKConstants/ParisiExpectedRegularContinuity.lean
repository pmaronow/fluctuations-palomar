module

public import SKConstants.ParisiUnboundedTimeGenerator

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma brownian_solution_L1_increment_ordered (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (s t : ℝ≥0) (hst : s≤t) :
    (∫ w, |b.solution W.driver t w-b.solution W.driver s w| ∂W.law) ≤
      Real.sqrt ((t:ℝ)-(s:ℝ))*normalFirstMoment+(b.bound:ℝ)*((t:ℝ)-(s:ℝ)) := by
  let := W.isProbability
  let h := t-s
  have he : s+h=t := add_tsub_cancel_of_le hst
  have hh : (h:ℝ)=(t:ℝ)-(s:ℝ) := NNReal.coe_sub hst
  have hi := ((W.brownian.integrable_eval t).sub (W.brownian.integrable_eval s)).abs
  change Integrable (fun w => |W.B t w-W.B s w|) W.law at hi
  have hsol := ((b.solution_integrable W t).sub (b.solution_integrable W s)).abs
  change Integrable (fun w => |b.solution W.driver t w-b.solution W.driver s w|) W.law at hsol
  have H : (∫ w, |b.solution W.driver t w-b.solution W.driver s w| ∂W.law) ≤
      ∫ w, |W.B t w-W.B s w|+(b.bound:ℝ)*((t:ℝ)-(s:ℝ)) ∂W.law := by
    apply integral_mono_ae hsol (hi.add (integrable_const _))
    filter_upwards [b.solution_increment W s h] with w hw
    have ht : (s:ℝ)+(h:ℝ)=(t:ℝ) := by exact_mod_cast he
    rw [he,ht] at hw
    change |b.solution W.driver t w-b.solution W.driver s w|≤|W.B t w-W.B s w|+(b.bound:ℝ)*((t:ℝ)-(s:ℝ))
    rw [hw]
    rw [show b.solution W.driver s w+(W.B t w-W.B s w)+b.displacement W s t w-b.solution W.driver s w=
      (W.B t w-W.B s w)+b.displacement W s t w by ring]
    exact (abs_add_le _ _).trans (add_le_add le_rfl
      (by simpa only [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))] using b.displacement_bound W s t w))
  rw [integral_add hi (integrable_const _)] at H
  have HG := increment_abs_first W.brownian.toIsPreBrownianReal s h
  rw [he,hh] at HG
  simpa only [HG,integral_const,probReal_univ,smul_eq_mul,one_mul] using H

lemma brownian_solution_L1_increment (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (s t : ℝ≥0) :
    (∫ w, |b.solution W.driver t w-b.solution W.driver s w| ∂W.law) ≤
      Real.sqrt |(t:ℝ)-(s:ℝ)| *normalFirstMoment+(b.bound:ℝ)*|(t:ℝ)-(s:ℝ)| := by
  rcases le_total s t with hst|hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))] using
      brownian_solution_L1_increment_ordered W b s t hst
  · simpa only [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hts))] using
      brownian_solution_L1_increment_ordered W b t s hts

lemma integrable_comp_lipschitz {P : Measure Ω} [IsFiniteMeasure P]
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {Y : Ω → ℝ}
    (hY : Integrable Y P) : Integrable (fun w => f (Y w)) P := by
  apply ((integrable_const ‖f 0‖).add (hY.norm.const_mul (L:ℝ))).mono'
    (hf.continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable)
  filter_upwards [] with w
  have H := hf.norm_sub_le (Y w) 0
  simp only [sub_zero] at H
  have HT := norm_add_le (f (Y w)-f 0) (f 0)
  rw [sub_add_cancel] at HT
  simp only [Real.norm_eq_abs] at H HT
  dsimp
  linarith

lemma expected_regular_modulus (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {F : ℝ → ℝ → ℝ} (L M : ℝ≥0)
    (hL : ∀ t, LipschitzWith L (F t))
    (hM : ∀ s t x, |F t x-F s x|≤(M:ℝ)*|t-s|) (s t : ℝ) :
    |(∫ w, F t (b.solution W.driver (Real.toNNReal t) w) ∂W.law)-
      (∫ w, F s (b.solution W.driver (Real.toNNReal s) w) ∂W.law)| ≤
      (L:ℝ)*(Real.sqrt |(Real.toNNReal t:ℝ)-(Real.toNNReal s:ℝ)| *normalFirstMoment+
        (b.bound:ℝ)*|(Real.toNNReal t:ℝ)-(Real.toNNReal s:ℝ)|)+(M:ℝ)*|t-s| := by
  let := W.isProbability
  have ht := integrable_comp_lipschitz (hL t) (b.solution_integrable W (Real.toNNReal t))
  have hs := integrable_comp_lipschitz (hL s) (b.solution_integrable W (Real.toNNReal s))
  have hdiff := ((b.solution_integrable W (Real.toNNReal t)).sub
    (b.solution_integrable W (Real.toNNReal s))).abs
  change Integrable (fun w => |b.solution W.driver (Real.toNNReal t) w-
    b.solution W.driver (Real.toNNReal s) w|) W.law at hdiff
  rw [←integral_sub ht hs]
  apply (abs_integral_le_integral_abs).trans
  calc
    _ ≤ ∫ w, (L:ℝ)*|b.solution W.driver (Real.toNNReal t) w-
        b.solution W.driver (Real.toNNReal s) w|+(M:ℝ)*|t-s| ∂W.law := by
      apply integral_mono (ht.sub hs).abs ((hdiff.const_mul _).add (integrable_const _))
      intro w
      have hl := (hL t).norm_sub_le
        (b.solution W.driver (Real.toNNReal t) w) (b.solution W.driver (Real.toNNReal s) w)
      have hm := hM s t (b.solution W.driver (Real.toNNReal s) w)
      simp only [Real.norm_eq_abs] at hl
      calc
        _ ≤ |F t (b.solution W.driver (Real.toNNReal t) w)-F t (b.solution W.driver (Real.toNNReal s) w)|+
          |F t (b.solution W.driver (Real.toNNReal s) w)-F s (b.solution W.driver (Real.toNNReal s) w)| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add hl hm
    _ ≤ _ := by
      rw [integral_add (hdiff.const_mul _) (integrable_const _),integral_const_mul,integral_const]
      simp only [probReal_univ,smul_eq_mul,one_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (brownian_solution_L1_increment W b _ _) L.coe_nonneg) le_rfl

lemma expected_regular_continuous (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {F : ℝ → ℝ → ℝ} (L M : ℝ≥0)
    (hL : ∀ t, LipschitzWith L (F t))
    (hM : ∀ s t x, |F t x-F s x|≤(M:ℝ)*|t-s|) :
    Continuous (fun t => ∫ w, F t (b.solution W.driver (Real.toNNReal t) w) ∂W.law) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have H : Tendsto (fun t : ℝ => (L:ℝ)*(Real.sqrt |(Real.toNNReal t:ℝ)-(Real.toNNReal s:ℝ)| *normalFirstMoment+
      (b.bound:ℝ)*|(Real.toNNReal t:ℝ)-(Real.toNNReal s:ℝ)|)+(M:ℝ)*|t-s|) (𝓝 s) (𝓝 0) := by
    have hn : Tendsto (fun t : ℝ => (Real.toNNReal t:ℝ)-(Real.toNNReal s:ℝ)) (𝓝 s) (𝓝 0) := by
      simpa only [Function.comp_def,sub_self] using ((NNReal.continuous_coe.comp continuous_real_toNNReal).continuousAt (x:=s)).tendsto.sub_const
        (Real.toNNReal s:ℝ)
    have hd : Tendsto (fun t : ℝ => t-s) (𝓝 s) (𝓝 0) := by
      simpa only [id_eq,sub_self] using (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 s) (𝓝 s)).sub_const s
    simpa only [sub_self,abs_zero,Real.sqrt_zero,zero_mul,mul_zero,add_zero] using
      (((hn.abs.sqrt.mul_const normalFirstMoment).add (hn.abs.const_mul (b.bound:ℝ))).const_mul (L:ℝ)).add
        (hd.abs.const_mul (M:ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ H
  exact Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs] using expected_regular_modulus W b L M hL hM s t)

end SKConstants.ParisiFullSupport
