module

public import SKConstants.Completion.LFine.ActualSchedule
public import SKConstants.Completion.LQ.ActualGrowingQuadrature
public import SKConstants.GaussianProposalScalarInitialState
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.N9
open SKConstantsOAI.ZeroTemperatureSK LFine LQ
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actual_square_profile_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    0 < actualParisiFullSusceptibilitySquareExpected W β t := by
  rw [actual_square_profile_eq W β hβ t ht]
  exact actualParisiContinuationR_pos W β _

theorem actualFineScale_square_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ) :
    (actualFineScale W β δ j)^2 =
      ∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j+1) : ℝ),
        actualParisiFullSusceptibilitySquareExpected W β v := by
  rw [actualFineScale_square W β hβ δ hδ j]
  exact (actualParisiFullSusceptibilitySquareExpected_interval W β hβ _ _
    ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ j))).symm

theorem actualFineScale_endpoint_lower (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ) (V : ℝ)
    (hV : (growingQueryTime δ (j+1) : ℝ) ≤ V) :
    meshDuration δ j * actualParisiFullSusceptibilitySquareExpected W β V ≤
      (actualFineScale W β δ j)^2 := by
  have hst : (growingQueryTime δ j : ℝ) ≤ (growingQueryTime δ (j+1) : ℝ) :=
    NNReal.coe_le_coe.mpr ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ j))
  have hVz : 0 ≤ V := (growingQueryTime δ (j+1)).coe_nonneg.trans hV
  have h := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ =>
      actualParisiFullSusceptibilitySquareExpected W β V) volume _ _)
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _)
    (fun v hv => actual_square_profile_antitone W β hβ
      ((growingQueryTime δ j).coe_nonneg.trans hv.1) hVz (hv.2.trans hV))
  rw [intervalIntegral.integral_const, smul_eq_mul,
    ← actualFineScale_square_integral W β hβ δ hδ j] at h
  simpa only [growingQueryTime_succ, NNReal.coe_add, add_sub_cancel_left,
    meshDuration] using h

theorem actualFineCellError_sum_le_endpoint (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (N : ℝ) (hN : 0 < N) :
    (∑ j : Fin K, fineCellError N (j.val+1) (actualFineScale W β δ j.val)
      (meshDuration δ j.val)) ≤
    fineScheduleError N K (meshTime δ (K+1))
      (1 / actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ (K+1))) := by
  have hr := actual_square_profile_pos W β hβ (growingQueryTime δ (K+1))
    (growingQueryTime δ (K+1)).coe_nonneg
  apply fineCellError_sum_le N hN K _ _ _ _ (by positivity)
    (fun j => actualFineScale_pos W β hβ δ hδ j.val)
    (fun j => (meshDuration_pos δ hδ j.val).le)
    (actualFineScale_square_sum_le_one W β hβ δ hδ K)
  · rw [growing_previous_duration_sum]
    exact meshTime_mono δ (Nat.le_succ K)
  · intro j
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ hr).mpr
    exact actualFineScale_endpoint_lower W β hβ δ hδ j.val _
      (NNReal.coe_le_coe.mpr ((growingQueryTime_strictMono δ hδ).monotone (by omega)))

theorem growingCell_sqrt_ratio_le_two (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ)
    (hsmall : meshDuration δ j ≤ 1/8) :
    Real.sqrt (meshDuration δ (j+1)) / Real.sqrt (meshDuration δ j) ≤ 2 := by
  have h := growingCell_sqrt_ratio_le δ hδ j (1/8) hsmall
  have he : Real.exp ((1/8 : ℝ)/8) ≤ 2 := by
    have hb := Real.exp_le_two_add_div_two_sub (x := ((1/8 : ℝ)/8))
      (by norm_num) (by norm_num)
    norm_num at hb ⊢
    linarith
  exact h.trans he

theorem actual_growing_mixed_scale_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ) (hsmall : meshDuration δ j ≤ 1/8) :
    β * Real.sqrt (meshDuration δ (j+1) *
      actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ (j+1))) ≤
      2*β*actualFineScale W β δ j := by
  have hp := meshDuration_pos δ hδ j
  have hq := meshDuration_pos δ hδ (j+1)
  have hr := (actualParisiFullSusceptibilitySquareExpected_bounds W β
    (growingQueryTime δ (j+1))).1
  have hs := actualFineScale_pos W β hβ δ hδ j
  have hratio := (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mp
    (growingCell_sqrt_ratio_le_two δ hδ j hsmall)
  have hdur : meshDuration δ (j+1) ≤ 4*meshDuration δ j := by
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq.le,
      Real.sqrt_nonneg (meshDuration δ j), Real.sqrt_nonneg (meshDuration δ (j+1))]
  have hscale := actualFineScale_endpoint_lower W β hβ δ hδ j _ le_rfl
  have hprod := mul_le_mul_of_nonneg_right hdur hr
  have hroot : Real.sqrt (meshDuration δ (j+1) *
      actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ (j+1))) ≤
      2*actualFineScale W β δ j := by
    nlinarith [Real.sq_sqrt (mul_nonneg hq.le hr),
      Real.sqrt_nonneg (meshDuration δ (j+1) *
        actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ (j+1)))]
  nlinarith [mul_le_mul_of_nonneg_left hroot (zero_lt_one.trans hβ).le]

def fineEnergyQuadratureConstant (β : ℝ) : ℝ :=
  1/β^2 + 33*Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ)+1)/2)

theorem fineEnergyQuadratureConstant_nonneg (β : ℝ) :
    0 ≤ fineEnergyQuadratureConstant β := by unfold fineEnergyQuadratureConstant; positivity

def fineEnergyBudget (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ) (N : ℝ) : ℝ :=
  (δ : ℝ) + (((K : ℝ)+1)*(1+(scalarGrowingSourceHorizon δ K : ℝ))+Real.sqrt K)/N +
    ((K : ℝ)+1)^2*(scalarGrowingSourceHorizon δ K : ℝ)/
      (actualParisiFullSusceptibilitySquareExpected W β (scalarGrowingSourceHorizon δ K)*N^2)

theorem fineEnergyBudget_eq_schedule (W : BrownianSystem Ω) (β : ℝ)
    (δ : ℝ≥0) (K : ℕ) (N : ℝ) :
    fineEnergyBudget W β δ K N = (δ : ℝ) +
      fineScheduleError N K (meshTime δ (K+1))
        (1/actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ (K+1))) := by
  simp only [fineEnergyBudget, fineScheduleError, meshTime, scalarGrowingSourceHorizon,
    div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem fineEnergy_sum_lower_of_cells (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (N : ℝ) (hN : 0 < N)
    (C : ℝ) (hC : 0 ≤ C) (energy : Fin K → ℝ)
    (hsmall : ∀ j ≤ K, (growingQueryDuration δ j : ℝ) ≤ 1/8)
    (hcell : ∀ j : Fin K,
      actualFineScale W β δ j.val *
        actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (j.val+1))
          (growingQueryTime δ (j.val+2)) -
        C*fineCellError N (j.val+1) (actualFineScale W β δ j.val) (meshDuration δ j.val) ≤ energy j) :
    actualParisiEnergyReference W β (scalarGrowingSourceHorizon δ K) -
      (fineEnergyQuadratureConstant β+C)*fineEnergyBudget W β δ K N ≤ ∑ j, energy j := by
  let S := fineScheduleError N K (meshTime δ (K+1))
    (1/actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ (K+1)))
  have hr := actual_square_profile_pos W β hβ (growingQueryTime δ (K+1))
    (growingQueryTime δ (K+1)).coe_nonneg
  have hS : 0 ≤ S := by
    dsimp [S,fineScheduleError]
    have hV := meshTime_nonneg δ (K+1)
    positivity
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcell j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hfinite : actualParisiGrowingEnergySum W β δ K =
      ∑ j : Fin K, actualFineScale W β δ j.val *
        actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (j.val+1))
          (growingQueryTime δ (j.val+2)) := by
    unfold actualParisiGrowingEnergySum actualFineScale
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [← hfinite] at hsum
  have herr := actualFineCellError_sum_le_endpoint W β hβ δ hδ K N hN
  have hsumerr := mul_le_mul_of_nonneg_left herr hC
  have hquad := actual_growing_energy_error W β hβ δ hδ K (fun i hi => by
    exact_mod_cast (hsmall i (by omega)).trans (by norm_num : (1/8 : ℝ) ≤ 1))
  change |actualParisiGrowingEnergySum W β δ K -
    actualParisiEnergyReference W β (scalarGrowingSourceHorizon δ K)| ≤
      fineEnergyQuadratureConstant β * (δ : ℝ) at hquad
  rw [fineEnergyBudget_eq_schedule]
  have hcross₁ := mul_nonneg hC δ.coe_nonneg
  have hcross₂ := mul_nonneg (fineEnergyQuadratureConstant_nonneg β) hS
  change _ - (fineEnergyQuadratureConstant β+C)*((δ : ℝ)+S) ≤ _
  change C*(∑ j : Fin K, fineCellError N (j.val+1)
    (actualFineScale W β δ j.val) (meshDuration δ j.val)) ≤ C*S at hsumerr
  have hquadLower := (abs_le.mp hquad).1
  nlinarith

end SKConstants.Completion.N9
