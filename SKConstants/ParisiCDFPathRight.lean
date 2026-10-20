module

public import SKConstants.ParisiCDFGenerator

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic

lemma stieltjes_comp_right_continuous (α : StieltjesFunction ℝ)
    {g : ℝ → ℝ} (hg : Continuous g) (hm : Monotone g) (s : ℝ) :
    ContinuousWithinAt (fun r => α (g r)) (Ioi s) s := by
  have H : Tendsto g (𝓝[Ici s] s) (𝓝[Ici (g s)] (g s)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hg.tendsto s).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hm hr
  exact ((α.right_continuous _).tendsto.comp H).mono_left
    (nhdsWithin_mono _ Ioi_subset_Ici_self)

lemma continuous_along_path {F : ℝ → ℝ → ℝ}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    {g x : ℝ → ℝ} (hg : Continuous g) (hx : Continuous x) :
    Continuous (fun r => F (g r) (x r)) :=
  hF.comp (hg.prodMk hx)

lemma cdfTimeClamp_monotone : Monotone cdfTimeClamp := by
  intro a b hab
  exact max_le_max_left _ (min_le_min_right _ hab)

lemma finiteTemperatureCDFDrift_path_right_continuous
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) :
    ∀ᵐ w ∂W.law, ∀ s : ℝ,
      ContinuousWithinAt
        (fun r => (finiteTemperatureCDFDrift β α ha h1).pathDrift W r w) (Ioi s) s := by
  let b := finiteTemperatureCDFDrift β α ha h1
  let g : ℝ → ℝ := fun r => (Real.toNNReal r : ℝ)/β^2
  have hg : Continuous g := by
    exact (continuous_subtype_val.comp continuous_real_toNNReal).div_const _
  have hm : Monotone g := by
    intro r t hrt
    exact div_le_div_of_nonneg_right
      (Real.toNNReal_mono hrt) (sq_nonneg β)
  have hcg : Continuous (fun r => cdfTimeClamp (g r)) :=
    continuous_cdfTimeClamp.comp hg
  have hcm : Monotone (fun r => cdfTimeClamp (g r)) :=
    cdfTimeClamp_monotone.comp hm
  filter_upwards [b.solution_continuous_ae W] with w hw
  have hx : Continuous (fun r => b.solution W.driver (Real.toNNReal r) w) :=
    hw.comp continuous_real_toNNReal
  have hG := continuous_along_path
    (F := fun t x => scalarCDFGradient β α (cdfTimeClamp t)
      (Real.toNNReal (1-cdfTimeClamp t)) x)
    (continuous_clamped_CDFGradient β α ha h1) hg hx
  intro s
  exact (stieltjes_comp_right_continuous α hcg hcm s).mul
    hG.continuousAt.continuousWithinAt

end SKConstants.ParisiFullSupport
