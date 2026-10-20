module

public import SKConstants.Completion.N9.ScalarBounds
public import SKConstants.Completion.LBase.HorizonBounds
public import SKConstants.Completion.N19.Stability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal Topology
namespace SKConstants.Completion.N19n
open GaussianProposal Blueprint LBase LQ
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem negativeRho_pathBound_le_two (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (H : ℝ≥0) :
    scalarStieltjesPathBound (actualParisiNegativeRhoStieltjes W β hβ) H ≤ 2 := by
  have h0 := actualParisiQueryRho_bounds W β hβ 0
  have hH := actualParisiQueryRho_bounds W β hβ H
  change |-actualParisiQueryRho W β 0| + |-actualParisiQueryRho W β H| +
    (-actualParisiQueryRho W β H - -actualParisiQueryRho W β 0) ≤ 2
  rw [abs_neg, abs_neg, abs_of_nonneg h0.1, abs_of_nonneg hH.1]
  linarith [h0.2]

theorem sigma_pathBound_le_two (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (H : ℝ≥0) :
    scalarStieltjesPathBound (actualParisiSigmaStieltjes W β hβ) H ≤ 2 := by
  have h0 := actualParisiQuerySigma_bounds W β hβ 0
  have hH := actualParisiQuerySigma_bounds W β hβ H
  change |actualParisiQuerySigma W β 0| + |actualParisiQuerySigma W β H| +
    (actualParisiQuerySigma W β H - actualParisiQuerySigma W β 0) ≤ 2
  rw [abs_of_nonneg h0.1, abs_of_nonneg hH.1]
  linarith [hH.2]

theorem actual_square_profile_exp_lower (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : 0 ≤ v) :
    curvatureLowerConstant β * Real.exp (-v) ≤
      actualParisiFullSusceptibilitySquareExpected W β v := by
  have hroot : Real.sqrt (1+v) ≤ Real.exp (v/2) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp v])
  have he : Real.exp (-v) ≤ Real.exp (-v/2) / Real.sqrt (1+v) := by
    apply (le_div_iff₀ (by positivity : 0 < Real.sqrt (1+v))).mpr
    calc
      _ ≤ Real.exp (-v) * Real.exp (v/2) :=
        mul_le_mul_of_nonneg_left hroot (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact (mul_le_mul_of_nonneg_left he (curvatureLowerConstant_pos β hβ).le).trans
    (actual_square_profile_temperature_lower W β hβ v hv)

theorem growing_incrementScale_lower (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ) (j : Fin q) :
    Real.sqrt ((δ : ℝ) * actualParisiFullSusceptibilitySquareExpected W β
      (scalarGrowingSourceHorizon δ q)) ≤
      scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
        (growingQueryTime δ) (j.val+1) := by
  rw [actualParisiGrowingIncrementScale_eq_posterior W β hβ δ hδ (j.val+1) (by omega)]
  simp only [Nat.add_sub_cancel]
  have hscale := N9.actualFineScale_endpoint_lower W β hβ δ hδ j.val
    (scalarGrowingSourceHorizon δ q)
    (NNReal.coe_le_coe.mpr ((growingQueryTime_strictMono δ hδ).monotone (by omega)))
  have hd : (δ : ℝ) ≤ meshDuration δ j.val := by
    have h := meshDuration_mono δ (Nat.zero_le j.val)
    simpa only [meshDuration_zero] using h
  have hr := (actualParisiFullSusceptibilitySquareExpected_bounds W β
    (scalarGrowingSourceHorizon δ q)).1
  have hp := mul_le_mul_of_nonneg_right hd hr
  have hs := (actualParisiPosteriorIntervalScale W β (growingQueryTime δ j.val)
    (growingQueryTime δ (j.val+1))).coe_nonneg
  have hsq := Real.sq_sqrt (mul_nonneg δ.coe_nonneg hr)
  change _ ≤ (LFine.actualFineScale W β δ j.val) ^ 2 at hscale
  change 0 ≤ LFine.actualFineScale W β δ j.val at hs
  change _ ≤ LFine.actualFineScale W β δ j.val
  nlinarith [Real.sqrt_nonneg ((δ : ℝ) *
    actualParisiFullSusceptibilitySquareExpected W β (scalarGrowingSourceHorizon δ q))]

theorem growing_incrementScale_lower_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ) :
    0 < Real.sqrt ((δ : ℝ) * actualParisiFullSusceptibilitySquareExpected W β
      (scalarGrowingSourceHorizon δ q)) := by
  apply Real.sqrt_pos.mpr
  exact mul_pos (NNReal.coe_pos.mpr hδ)
    (LBase.actual_square_profile_pos W β hβ _ (scalarGrowingSourceHorizon δ q).coe_nonneg)

end SKConstants.Completion.N19n
