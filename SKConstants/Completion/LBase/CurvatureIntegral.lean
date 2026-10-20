module

public import SKConstants.Completion.LBase.CurvatureCross
public import SKConstants.BrownianMartingaleIdentification
public import SKConstants.ParisiFullVarianceIntegral

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedLipschitzDrift.solution
set_option maxHeartbeats 400000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

lemma memLp_actualMagnetization (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0) :
    MemLp (actualParisiMagnetizationObservable W β T) 2 W.law :=
  (memLp_two_iff_integrable_sq (measurable_actualParisiMagnetizationObservable W β T).aestronglyMeasurable).2
    (by simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β T T)

lemma actual_curvature_energy_eq_terminal_secondMoment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    (∫ r in (0 : ℝ)..T, actualParisiFullSusceptibilitySquareExpected W β r) =
      ∫ w, (actualParisiMagnetizationObservable W β T w)^2 ∂W.law := by
  have H := actualParisiFullSusceptibilitySquareExpected_interval W β hβ 0 T bot_le
  have h0 := actualParisiFullOverlap_pre W β hβ 0 bot_le
  simp only [NNReal.coe_zero, zero_div] at h0 H
  rw [h0, sub_zero] at H
  exact H

theorem actual_curvature_leftSum_meanSquare_tendsto
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k * 2^l → (G.time l (i+1) : ℝ) - G.time l i ≤ δ l) :
    Tendsto (fun l => ∫ w, (actualCurvatureLeftSum W β G k l w -
      actualParisiMagnetizationObservable W β (G.time 0 k) w)^2 ∂W.law) atTop (𝓝 0) := by
  let X := actualParisiMagnetizationObservable W β (G.time 0 k)
  let S := actualCurvatureLeftSum W β G k
  have hS := fun l => memLp_actualCurvatureLeftSum W β G k l
  have hX := memLp_actualMagnetization W β (G.time 0 k)
  have hs := actual_curvature_leftSum_secondMoment_tendsto W β G k δ hδ hwidth
  have hc := actual_curvature_leftSum_crossMoment_tendsto W β hβ G k δ hδ hwidth
  rw [actual_curvature_energy_eq_terminal_secondMoment W β hβ] at hs hc
  change Tendsto (fun l => ∫ w, (S l w)^2 ∂W.law) atTop (𝓝 (∫ w, (X w)^2 ∂W.law)) at hs
  change Tendsto (fun l => ∫ w, X w * S l w ∂W.law) atTop (𝓝 (∫ w, (X w)^2 ∂W.law)) at hc
  have he (l : ℕ) : (∫ w, (S l w - X w)^2 ∂W.law) =
      (∫ w, (S l w)^2 ∂W.law) - 2 * (∫ w, X w * S l w ∂W.law) +
        ∫ w, (X w)^2 ∂W.law := by
    have hi := hX.integrable_mul (hS l)
    have hp : (fun w => (S l w - X w)^2) = fun w => (S l w)^2 - 2 * (X w * S l w) + (X w)^2 := by
      funext w
      ring
    rw [hp, integral_add (f := fun w => (S l w)^2 - 2 * (X w * S l w))
      (g := fun w => (X w)^2) ((hS l).integrable_sq.sub (hi.const_mul 2)) hX.integrable_sq,
      integral_sub (f := fun w => (S l w)^2) (g := fun w => 2 * (X w * S l w))
      (hS l).integrable_sq (hi.const_mul 2), integral_const_mul]
  change Tendsto (fun l => ∫ w, (S l w - X w)^2 ∂W.law) atTop (𝓝 0)
  simp_rw [he]
  convert (hs.sub (hc.const_mul 2)).add_const (∫ w, (X w)^2 ∂W.law) using 1
  ring

theorem actual_curvature_dyadic_meanSquare_tendsto
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    Tendsto (fun l => ∫ w, (actualCurvatureLeftSum W β (brownianDyadicGrid T) 1 l w -
      actualParisiMagnetizationObservable W β T w)^2 ∂W.law) atTop (𝓝 0) := by
  simpa only [brownianDyadicGrid_horizon] using actual_curvature_leftSum_meanSquare_tendsto W β hβ
    (brownianDyadicGrid T) 1 (brownianDyadicWidth T) (brownianDyadicWidth_tendsto T)
    (fun l i _ => brownianDyadicGrid_width_le T l i)

theorem actual_curvature_integral_eq_magnetization
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (T : ℝ≥0)
    (I : Ω → ℝ) (hI : MemLp I 2 W.law)
    (hIlim : Tendsto (fun l => ∫ w, (actualCurvatureLeftSum W β (brownianDyadicGrid T) 1 l w - I w)^2
      ∂W.law) atTop (𝓝 0)) :
    I =ᵐ[W.law] actualParisiMagnetizationObservable W β T := by
  have hs := fun l => memLp_actualCurvatureLeftSum W β (brownianDyadicGrid T) 1 l
  have he := tendsto_nhds_unique
    (tendsto_toLp_of_meanSquare hs hI hIlim)
    (tendsto_toLp_of_meanSquare hs (memLp_actualMagnetization W β T)
      (actual_curvature_dyadic_meanSquare_tendsto W β hβ T))
  exact (hI.toLp_eq_toLp_iff (memLp_actualMagnetization W β T)).mp he

theorem actual_curvature_integral_exists
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    ∃ I : Ω → ℝ, MemLp I 2 W.law ∧
      Tendsto (fun l => ∫ w, (actualCurvatureLeftSum W β (brownianDyadicGrid T) 1 l w - I w)^2
        ∂W.law) atTop (𝓝 0) ∧ I =ᵐ[W.law] actualParisiMagnetizationObservable W β T := by
  obtain ⟨J, hJ, _, hJlim⟩ := brownianContinuousLeftSum_exists_L2_limit (Measure.dirac ()) W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable (curvaturePastCoefficient β)
    (measurable_curvaturePastCoefficient β) 1 (curvaturePastCoefficient_norm_le β)
    (curvaturePastCoefficient_continuous_ae W β) (brownianDyadicGrid T) 1
    (brownianDyadicWidth T) (brownianDyadicWidth_tendsto T)
    (fun l d i _ => brownianDyadicGrid_left_le T l d i)
  let I := fun w => J ((), w)
  have hI : MemLp I 2 W.law := hJ.comp_measurePreserving (unitLift_measurePreserving W.law)
  have hIlim : Tendsto (fun l => ∫ w, (actualCurvatureLeftSum W β (brownianDyadicGrid T) 1 l w - I w)^2
      ∂W.law) atTop (𝓝 0) := by
    apply hJlim.congr'
    apply Filter.Eventually.of_forall
    intro l
    dsimp only
    rw [integral_unit_prod]
    exact integral_congr_ae ((rawCurvatureLeftSum_actual W β (brownianDyadicGrid T) 1 l).mono
      (fun w hw => congrArg (fun x : ℝ => (x - J ((), w))^2) hw))
  exact ⟨I, hI, hIlim, actual_curvature_integral_eq_magnetization W β hβ T I hI hIlim⟩

end SKConstants.Completion.LBase
