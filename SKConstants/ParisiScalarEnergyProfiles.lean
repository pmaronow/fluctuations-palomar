module

public import SKConstants.ParisiPostEntropyDissipation
public import SKConstants.ParisiEquilibriumPressureBalance

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

def actualParisiFullSusceptibilityExpected (W : BrownianSystem Ω) (β v : ℝ) : ℝ :=
  ∫ w, actualParisiFullCurvature β v
    (actualParisiFullScalarProcess W β (Real.toNNReal v) w) ∂W.law

def actualParisiFullSusceptibilitySquareExpected (W : BrownianSystem Ω) (β v : ℝ) : ℝ :=
  ∫ w, (actualParisiFullCurvature β v
    (actualParisiFullScalarProcess W β (Real.toNNReal v) w))^2 ∂W.law

def actualParisiFullEntropyRateExpected (W : BrownianSystem Ω) (β v : ℝ) : ℝ :=
  ∫ w, (actualParisiFullCurvature β v
    (actualParisiFullScalarProcess W β (Real.toNNReal v) w))^2/
      (1-(actualParisiFullMagnetization β v
        (actualParisiFullScalarProcess W β (Real.toNNReal v) w))^2) ∂W.law

def actualParisiEnergyReference (W : BrownianSystem Ω) (β V : ℝ) : ℝ :=
  ∫ v in 0..V, Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v)*
    actualParisiFullSusceptibilityExpected W β v*actualParisiQueryRho W β v

def actualParisiEntropyReference (W : BrownianSystem Ω) (β V : ℝ) : ℝ :=
  (1/2:ℝ)*(∫ v in 0..V, (actualParisiQueryRho W β v)^2*
    actualParisiFullEntropyRateExpected W β v)

lemma actualParisiFullCurvature_abs_le_one (β v x : ℝ) : |actualParisiFullCurvature β v x|≤1 := by
  have H := actualParisiFullMagnetization_curvature_bounds β v x
  rw [abs_of_nonneg H.2.1]
  nlinarith [sq_nonneg (actualParisiFullMagnetization β v x)]

lemma actualParisiFullEntropyRate_bounds (β v x : ℝ) :
    0≤(actualParisiFullCurvature β v x)^2/(1-(actualParisiFullMagnetization β v x)^2) ∧
      (actualParisiFullCurvature β v x)^2/(1-(actualParisiFullMagnetization β v x)^2)≤1 := by
  have H := actualParisiFullMagnetization_curvature_bounds β v x
  have HS := actualParisiFullMagnetization_strict_bounds β v x
  have hd : 0<1-(actualParisiFullMagnetization β v x)^2 := by nlinarith
  refine ⟨div_nonneg (sq_nonneg _) hd.le, (div_le_iff₀ hd).mpr ?_⟩
  have hdef : 1-(actualParisiFullMagnetization β v x)^2≤1 := by nlinarith [sq_nonneg (actualParisiFullMagnetization β v x)]
  nlinarith

lemma actualParisiFullExpected_continuous (W : BrownianSystem Ω) (β : ℝ)
    {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) (C : ℝ)
    (hC : ∀ v x, |g v x|≤C) :
    Continuous (fun v => ∫ w, g v (actualParisiFullScalarProcess W β (Real.toNNReal v) w) ∂W.law) := by
  let := W.isProbability
  apply continuous_of_dominated (bound:=fun _ : Ω => C)
  · intro v
    have H := hg.measurable.comp
      ((measurable_const : Measurable (fun _ : Ω => v)).prodMk
        ((actualParisiFullScalarDrift β).solution_measurable W (Real.toNNReal v)))
    exact H.aestronglyMeasurable
  · intro v
    exact Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using hC v _)
  · exact integrable_const _
  · filter_upwards [(actualParisiFullScalarDrift β).solution_continuous_ae W] with w hw
    exact hg.comp (continuous_id.prodMk (hw.comp continuous_real_toNNReal))

theorem continuous_actualParisiFullSusceptibilityExpected (W : BrownianSystem Ω) (β : ℝ) :
    Continuous (actualParisiFullSusceptibilityExpected W β) :=
  actualParisiFullExpected_continuous W β (continuous_actualParisiFullCurvature β) 1
    (actualParisiFullCurvature_abs_le_one β)

theorem continuous_actualParisiFullSusceptibilitySquareExpected (W : BrownianSystem Ω) (β : ℝ) :
    Continuous (actualParisiFullSusceptibilitySquareExpected W β) := by
  unfold actualParisiFullSusceptibilitySquareExpected
  apply actualParisiFullExpected_continuous W β
    (g:=fun v x => (actualParisiFullCurvature β v x)^2)
    (by
      have H := (continuous_actualParisiFullCurvature β).pow 2
      change Continuous (fun p : ℝ×ℝ => (actualParisiFullCurvature β p.1 p.2)^2) at H
      exact H) 1
  intro v x
  have HP := pow_le_pow_left₀ (abs_nonneg _) (actualParisiFullCurvature_abs_le_one β v x) 2
  simpa only [abs_pow,one_pow] using HP

theorem continuous_actualParisiFullEntropyRateExpected (W : BrownianSystem Ω) (β : ℝ) :
    Continuous (actualParisiFullEntropyRateExpected W β) := by
  have Hcont : Continuous (fun p : ℝ×ℝ => (actualParisiFullCurvature β p.1 p.2)^2/
      (1-(actualParisiFullMagnetization β p.1 p.2)^2)) := by
    apply ((continuous_actualParisiFullCurvature β).pow 2).div
      (continuous_const.sub ((continuous_actualParisiFullMagnetization β).pow 2))
    intro p
    have H := actualParisiFullMagnetization_strict_bounds β p.1 p.2
    change 1-(actualParisiFullMagnetization β p.1 p.2)^2 ≠ 0
    nlinarith
  unfold actualParisiFullEntropyRateExpected
  apply actualParisiFullExpected_continuous W β
    (g:=fun v x => (actualParisiFullCurvature β v x)^2/
      (1-(actualParisiFullMagnetization β v x)^2)) Hcont 1
  intro v x
  have H := actualParisiFullEntropyRate_bounds β v x
  simpa only [abs_of_nonneg H.1] using H.2

theorem actualParisiEnergyIntegrand_intervalIntegrable (W : BrownianSystem Ω) (β A V : ℝ) :
    IntervalIntegrable (fun v => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v)*
      actualParisiFullSusceptibilityExpected W β v*actualParisiQueryRho W β v) volume A V :=
  (((continuous_actualParisiFullSusceptibilitySquareExpected W β).sqrt.mul
    (continuous_actualParisiFullSusceptibilityExpected W β)).mul
    (continuous_actualParisiQueryRho W β)).intervalIntegrable A V

theorem actualParisiEntropyIntegrand_intervalIntegrable (W : BrownianSystem Ω) (β A V : ℝ) :
    IntervalIntegrable (fun v => (actualParisiQueryRho W β v)^2*
      actualParisiFullEntropyRateExpected W β v) volume A V :=
  (((continuous_actualParisiQueryRho W β).pow 2).mul
    (continuous_actualParisiFullEntropyRateExpected W β)).intervalIntegrable A V

end SKConstants
