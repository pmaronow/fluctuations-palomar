module
public import SKConstants.ParisiFiniteFeedbackLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem finite_transition_tilted_partial
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    {f g : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f) (hg : BoundedSmooth g)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N i : ℕ} (hi : i < N) (δ : ℝ≥0) (hδ : δ ≤ h) :
    (∫ w, g ((finiteFeedback hf hLip c h N 0).solution W.driver ((i:ℝ≥0)*h+δ) w) ∂W.law) =
      ∫ w, varianceTilted (c i) δ
        (varianceLogHeat (c i) ((h:ℝ)-δ) (backwardBoundary c h f N (i+1))) g
        ((finiteFeedback hf hLip c h N 0).solution W.driver ((i:ℝ≥0)*h) w) ∂W.law := by
  let F := backwardBoundary c h f N (i+1)
  have hF : RegularDatum F := cascade_regular hf hLip c h _ _
  have hFL : LipschitzWith 1 F := cascade_lipschitz hLip c h _ _
  have hfδ := regularDatum_varianceLogHeat hF hFL (c i).coe_nonneg ((h:ℝ)-δ)
  have hLδ := varianceLogHeat_lipschitz hFL (c i).coe_nonneg ((h:ℝ)-δ)
  have H := expected_transition_tiltedMean W (finiteFeedback hf hLip c h N 0)
    hfδ hLδ hg (c i).coe_nonneg (show (i:ℝ≥0)*h ≤ (i:ℝ≥0)*h+δ from le_add_of_nonneg_right bot_le)
    (fun t ht x => by
      have hti : t ∈ Ico ((i:ℝ)*h) (((i+1:ℕ):ℝ)*h) := by
        constructor
        · exact ht.1
        · have hhδ : (δ:ℝ) ≤ h := hδ
          simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast] at ht
          push_cast
          linarith [ht.2]
      rw [finiteFeedback_step hf hLip c h hi hti]
      congr 1
      have ha : 0 ≤ (((i:ℝ≥0)*h+δ:ℝ≥0):ℝ)-t := by exact sub_nonneg.mpr ht.2.le
      have hb : 0 ≤ (h:ℝ)-δ := sub_nonneg.mpr hδ
      have he : (((i+1:ℕ):ℝ)*h-t) = ((((i:ℝ≥0)*h+δ:ℝ≥0):ℝ)-t)+((h:ℝ)-δ) := by push_cast; ring
      rw [he,varianceLogHeat_add hFL (c i).coe_nonneg ha hb])
  have he : ((((i:ℝ≥0)*h+δ:ℝ≥0):ℝ)-(((i:ℝ≥0)*h:ℝ≥0):ℝ))=δ := by push_cast; ring
  simpa only [he,F] using H

end SKConstants.ParisiFullSupport
