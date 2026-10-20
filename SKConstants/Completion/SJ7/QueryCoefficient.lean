module

public import SKConstants.Completion.LJ.RefinedResidual
public import SKConstants.Completion.LJ.GrowingLagBudget

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Filter Set
open scoped NNReal BigOperators Topology

namespace SKConstants.Completion.SJ7
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem growing_residualCoarseB_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (i : ℕ) :
    LJ.residualCoarseB W β (growingQueryTime δ) (i + 1) =
      LQ.posteriorScale (actualParisiFullSusceptibilitySquareExpected W β)
        (LQ.meshTime δ i) (LQ.meshTime δ (i + 1)) /
          Real.sqrt (LQ.meshDuration δ (i + 1)) := by
  simp only [LJ.residualCoarseB, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel, LJ.gridPosteriorScale]
  rw [actualParisiPosteriorIntervalScale_eq_sqrt_integral W β hβ _ _
    (growingQueryTime_strictMono δ hδ (Nat.lt_succ_self i)), growingQueryTime_sub]
  rfl

theorem growing_residualCoarseB_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (i : ℕ) {v : ℝ}
    (hv : v ∈ Icc (growingQueryTime δ (i + 1) : ℝ) (growingQueryTime δ (i + 2) : ℝ)) :
    |Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v) -
        LJ.residualCoarseB W β (growingQueryTime δ) (i + 1)| ≤
      (33 / 8 : ℝ) * (growingQueryDuration δ (i + 1) : ℝ) *
        Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ i)) := by
  rw [abs_sub_comm, growing_residualCoarseB_eq W β hβ δ hδ i]
  exact LQ.growing_coefficient_error (actualParisiFullSusceptibilitySquareExpected W β) δ hδ i
    (fun v _ => (actualParisiFullSusceptibilitySquareExpected_bounds W β v).1)
    (LQ.actual_square_profile_antitone W β hβ) (LQ.actual_square_profile_drop W β hβ)
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _) hv

theorem growing_residualCoarseB_sq_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (i : ℕ) (hsmall : growingQueryDuration δ i ≤ 1)
    {v : ℝ} (hv : v ∈ Icc (growingQueryTime δ (i + 1) : ℝ) (growingQueryTime δ (i + 2) : ℝ)) :
    (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v) -
      LJ.residualCoarseB W β (growingQueryTime δ) (i + 1)) ^ 2 ≤
      ((33 / 8 : ℝ) ^ 2 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)) * (δ : ℝ) ^ 2 := by
  have hG := growing_residualCoarseB_error W β hβ δ hδ i hv
  have hs := pow_le_pow_left₀ (abs_nonneg _) hG 2
  rw [sq_abs, mul_pow, mul_pow,
    Real.sq_sqrt (actualParisiFullSusceptibilitySquareExpected_bounds W β (growingQueryTime δ i)).1] at hs
  have hg := LQ.mesh_adjacent_profile_square_le (actualParisiFullSusceptibilitySquareExpected W β)
    (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) (Real.exp_pos _).le δ i
    (LQ.actual_square_profile_tail W β hβ _ (growingQueryTime δ i).coe_nonneg) (by exact_mod_cast hsmall)
  have he : Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * Real.exp (1 / 2) =
      Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hg
  calc
    _ ≤ (33 / 8 : ℝ) ^ 2 *
        (actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ i) *
          (growingQueryDuration δ (i + 1) : ℝ) ^ 2) := by nlinarith [hs]
    _ ≤ (33 / 8 : ℝ) ^ 2 *
        (Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2) * (δ : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring

theorem growing_query_coefficient_sq_integral_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) :
    (∑ j ∈ Finset.range (K + 1),
      ∫ v in (growingQueryTime δ j : ℝ)..(growingQueryTime δ (j + 1) : ℝ),
        (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v) -
          LJ.residualCoarseB W β (growingQueryTime δ) j) ^ 2) ≤
      (1 + 8 * (33 / 8 : ℝ) ^ 2 *
        Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)) * δ := by
  let C := (33 / 8 : ℝ) ^ 2 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)
  have hC : 0 ≤ C := by positivity
  have haux : (∫ v in (growingQueryTime δ 0 : ℝ)..(growingQueryTime δ (0 + 1) : ℝ),
      (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v) -
        LJ.residualCoarseB W β (growingQueryTime δ) 0) ^ 2) ≤ δ := by
    simp only [LJ.residualCoarseB, ↓reduceIte, sub_zero,
      Real.sq_sqrt (actualParisiFullSusceptibilitySquareExpected_bounds W β _).1,
      growingQueryTime_zero, Nat.zero_add, NNReal.coe_zero]
    have ht1 : (growingQueryTime δ 1 : ℝ) = δ := LQ.meshTime_one δ
    rw [ht1]
    have h := intervalIntegral.integral_mono_on δ.coe_nonneg
      ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable 0 δ)
      (intervalIntegrable_const (c := (1 : ℝ)) (μ := volume))
      (fun v _ => (actualParisiFullSusceptibilitySquareExpected_bounds W β v).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] using h
  have hcell (i : ℕ) (hi : i < K) :
      (∫ v in (growingQueryTime δ (i + 1) : ℝ)..(growingQueryTime δ (i + 1 + 1) : ℝ),
        (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v) -
          LJ.residualCoarseB W β (growingQueryTime δ) (i + 1)) ^ 2) ≤ C * (δ : ℝ) ^ 2 := by
    have hST : (growingQueryTime δ (i + 1) : ℝ) ≤ growingQueryTime δ (i + 1 + 1) :=
      NNReal.coe_le_coe.mpr ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _))
    have hc : Continuous (fun v : ℝ =>
        (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v) -
          LJ.residualCoarseB W β (growingQueryTime δ) (i + 1)) ^ 2) :=
      ((continuous_actualParisiFullSusceptibilitySquareExpected W β).sqrt.sub continuous_const).pow 2
    have hb := intervalIntegral.integral_mono_on hST (hc.intervalIntegrable _ _)
      (intervalIntegrable_const (c := C * (δ : ℝ) ^ 2) (μ := volume))
      (fun v hv => growing_residualCoarseB_sq_le W β hβ δ hδ i (hsmall i (by omega)) hv)
    rw [intervalIntegral.integral_const, smul_eq_mul, growingQueryTime_sub] at hb
    exact hb.trans (mul_le_of_le_one_left (by positivity) (by exact_mod_cast hsmall (i + 1) (by omega)))
  rw [Finset.sum_range_succ']
  have hsum : (∑ i ∈ Finset.range K,
      ∫ v in (growingQueryTime δ (i + 1) : ℝ)..(growingQueryTime δ (i + 1 + 1) : ℝ),
        (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v) -
          LJ.residualCoarseB W β (growingQueryTime δ) (i + 1)) ^ 2) ≤ 8 * C * δ := by
    have hcount := growingQuery_finite_count_bound δ hδ (K + 1) hsmall
    have hK : (K : ℝ) * δ ≤ 8 := by
      have hKle : (K : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.le_succ K
      exact (mul_le_mul_of_nonneg_right hKle δ.coe_nonneg).trans hcount
    calc
      _ ≤ ∑ _i ∈ Finset.range K, C * (δ : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun i hi => hcell i (Finset.mem_range.mp hi))
      _ = (C * δ) * ((K : ℝ) * δ) := by simp; ring
      _ ≤ (C * δ) * 8 := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = _ := by ring
  dsimp only [C] at hsum
  nlinarith [hsum, haux]

end SKConstants.Completion.SJ7
