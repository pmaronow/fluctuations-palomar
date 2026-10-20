module

public import SKConstants.Completion.N9Q2.PosteriorMean
public import SKConstants.Completion.N9Q2.PicardRestart
public import SKConstants.Completion.N9Q2.ScalarMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N9Q2
open SKConstantsOAI.ZeroTemperatureSK M1 LFine
variable {Ω : Type*} [MeasurableSpace Ω]

theorem wiener_restarted_magnetization_mean (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0) (B D : ScalarContinuousPath a) :
    (∫ p, actualParisiFullMagnetization β (a+v)
      (restartedField W β hβ a v B D p)
      ∂(scalarPrimitiveBrownianPathLaw W v).prod (scalarPrimitiveBrownianPathLaw W v)) =
      fixedPastPosterior W β hβ a B D := by
  letI := W.isProbability
  let b := actualParisiFullScalarDrift β
  let f := actualParisiNegativeRhoStieltjes W β hβ
  let g := actualParisiSigmaStieltjes W β hβ
  let hf := continuous_actualParisiNegativeRhoStieltjes W β hβ
  let hg := continuous_actualParisiSigmaStieltjes W β hβ
  let x := scalarTwoDriverPicardPath b f g hf hg a (0,(B,D)) ⟨a,a.coe_nonneg,le_rfl⟩
  let J := scalarTwoDriverWeightedPath (shiftedCoefficient f hf a) (shiftedCoefficient g hg a)
    (continuous_shiftedCoefficient f hf a) (continuous_shiftedCoefficient g hg a) v
  let H : ScalarContinuousPath v → ℝ := fun p =>
    actualParisiFullMagnetization β (a+v)
      (scalarForwardPicardPath (SKConstants.BoundedLipschitzDrift.translated b a 0) v
        (x,p) ⟨v,v.coe_nonneg,le_rfl⟩)
  have hH : Measurable H :=
    (((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable).comp
        ((ContinuousMap.measurable_eval _).comp
          ((measurable_scalarForwardPicardPath _ v).comp (measurable_const.prodMk measurable_id)))
  have hJ : Measurable J := measurable_scalarTwoDriverWeightedPath _ _ _ _ v
  have hLaw : ((scalarPrimitiveBrownianPathLaw W v).prod
      (scalarPrimitiveBrownianPathLaw W v)).map J = scalarPrimitiveBrownianPathLaw W v := by
    apply weighted_wiener_law W
    intro s hs
    exact actualParisiStieltjesCoefficients_unit W β hβ ((a : ℝ)+s)
  have he : (fun p => actualParisiFullMagnetization β (a+v)
      (restartedField W β hβ a v B D p)) =ᵐ[
      (scalarPrimitiveBrownianPathLaw W v).prod (scalarPrimitiveBrownianPathLaw W v)]
      (fun p => H (J p)) := by
    filter_upwards [(measurePreserving_fst (μ := scalarPrimitiveBrownianPathLaw W v)
      (ν := scalarPrimitiveBrownianPathLaw W v)).quasiMeasurePreserving.ae
        (scalarPrimitiveBrownianPathLaw_zero_ae W v),
      (measurePreserving_snd (μ := scalarPrimitiveBrownianPathLaw W v)
      (ν := scalarPrimitiveBrownianPathLaw W v)).quasiMeasurePreserving.ae
        (scalarPrimitiveBrownianPathLaw_zero_ae W v)] with p hp hq
    exact congrArg (actualParisiFullMagnetization β (a+v))
      (twoDriverPicard_concat_restart b f g hf hg a v v le_rfl 0 B D p.1 p.2 hp hq)
  rw [integral_congr_ae he,← integral_map hJ.aemeasurable hH.aestronglyMeasurable,hLaw]
  have hPaths : scalarPrimitiveBrownianPathVersion W v =ᵐ[W.law] brownianFinitePath W v := by
    filter_upwards [scalarPrimitiveBrownianPathVersion_ae W v,brownianFinitePath_version W v]
      with w hp hq
    ext t
    exact (hp t).trans (hq t).symm
  unfold scalarPrimitiveBrownianPathLaw
  rw [Measure.map_congr hPaths,integral_map (measurable_brownianFinitePath W v).aemeasurable
    hH.aestronglyMeasurable]
  have hVersion : (fun w => H (brownianFinitePath W v w)) =ᵐ[W.law]
      (fun w => actualParisiFullMagnetization β (a+v) (actualParisiRestartField W β a x v w)) := by
    let past : ScalarContinuousPath a := ⟨fun _ => x,continuous_const⟩
    filter_upwards [boundedDriftRestartCallback_fresh_version W b a v past] with w hw
    exact congrArg (actualParisiFullMagnetization β (a+v)) (hw ⟨v,v.coe_nonneg,le_rfl⟩)
  rw [integral_congr_ae hVersion,restart_magnetization_mean W β hβ a v x]
  rfl

theorem freshPosteriorMean_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (hh : 0 < h) (n : ℕ) (B D : Fin n → ScalarContinuousPath a) :
    FreshPosteriorMeanStatement W β hβ a h f n B D := by
  apply (freshPosteriorMean_iff_wiener W β hβ a h f hh n B D).mpr
  intro i
  exact wiener_restarted_magnetization_mean W β hβ a (h+f) (B i) (D i)

theorem finePosteriorRestart_holds : Blueprint5.FinePosteriorRestartStatement := by
  intro Ω _ W β hβ a h f hh n B D
  exact freshPosteriorMean_holds W β hβ a h f hh n B D

end SKConstants.Completion.N9Q2
