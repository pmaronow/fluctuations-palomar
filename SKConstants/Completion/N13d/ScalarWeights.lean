module

public import SKConstants.Completion.LGram.PopulationNorms
public import SKConstants.Completion.LBase.FullIdentities
public import SKConstants.Completion.LQ.ActualStoppingQuadrature
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal RealInnerProductSpace

namespace SKConstants.Completion.N13d
open SKConstantsOAI.ZeroTemperatureSK LGram LQ
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem populationTargetSpin_norm_sq (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t) (ht0 : t 0 = 0)
    (g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) (hH : t k ≤ H) :
    ‖populationTargetSpin W Z β hβ t g k H‖^2 = actualParisiFullOverlap W β (t k) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [populationTargetSpin_eq_scale W Z β hβ t ht g k H hH,
    actualParisiPosteriorIntervalScale_sq W β hβ _ _ (ht (Nat.lt_succ_self _))]
  change (∑ j : Fin k, (fun i : ℕ => actualParisiFullOverlap W β (t (i+1))-
    actualParisiFullOverlap W β (t i)) j.val) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => actualParisiFullOverlap W β (t (i+1))-
      actualParisiFullOverlap W β (t i)) k]
  have hsum := Finset.sum_range_sub (fun j => actualParisiFullOverlap W β (t j)) k
  have h0 := actualParisiFullOverlap_pre W β hβ 0 bot_le
  simp only [NNReal.coe_zero, zero_div] at h0
  simpa only [ht0, h0, sub_zero] using hsum

theorem populationTargetSpin_norm_sq_eq_defect
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (ht0 : t 0 = 0)
    (g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) (hH : t k ≤ H)
    (hpost : parisiEquilibriumPhysicalEndpoint β ≤ t k) :
    ‖populationTargetSpin W Z β hβ t g k H‖^2 =
      1-actualParisiFullSusceptibilityExpected W β (t k) := by
  rw [populationTargetSpin_norm_sq W Z β hβ t ht ht0 g k H hH,
    LBase.actual_post_susceptibility_eq_defect W β hβ (t k) hpost]
  ring

theorem populationTargetSpin_growing_coordinate_sq_le
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0)
    (hH : growingQueryTime δ k ≤ H) (j : Fin k) :
    (populationTargetSpin W Z β hβ (growingQueryTime δ) g k H j)^2 ≤
      Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)*(δ : ℝ) := by
  let t := growingQueryTime δ
  let r := actualParisiFullSusceptibilitySquareExpected W β
  have ht : StrictMono t := growingQueryTime_strictMono δ hδ
  have hst : (t j : ℝ) ≤ t (j+1) := NNReal.coe_le_coe.mpr (ht.monotone (Nat.le_succ _))
  have he : (populationTargetSpin W Z β hβ t g k H j)^2 =
      ∫ v in (t j : ℝ)..t (j+1), r v := by
    rw [populationTargetSpin_eq_scale W Z β hβ t ht g k H hH,
      actualParisiPosteriorIntervalScale_sq W β hβ _ _ (ht (Nat.lt_succ_self _)),
      actualParisiFullSusceptibilitySquareExpected_interval W β hβ _ _
        (ht.monotone (Nat.le_succ _))]
  have hi := intervalIntegral.integral_mono_on hst
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => r (t j)) volume _ _)
    (fun v hv => actual_square_profile_antitone W β hβ
      (t j).coe_nonneg ((t j).coe_nonneg.trans hv.1) hv.1)
  have hdt : (t (j+1) : ℝ)-(t j : ℝ) = (growingQueryDuration δ j : ℝ) := by
    simp only [t, growingQueryTime_succ, NNReal.coe_add, add_sub_cancel_left]
  rw [intervalIntegral.integral_const, smul_eq_mul, hdt] at hi
  rw [he]
  calc
    _ ≤ r (t j)*(δ : ℝ)*Real.exp ((t j : ℝ)/4) := by
      simpa only [growingQueryDuration_coe, t, mul_assoc, mul_comm, mul_left_comm] using hi
    _ ≤ Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)*(δ : ℝ)*
        Real.exp (-(t j : ℝ)/4) :=
      weighted_overshoot_scale r _ δ (t j)
        (actual_square_profile_tail W β hβ _ (t j).coe_nonneg)
    _ ≤ Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)*(δ : ℝ)*1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_one_iff.mpr (by have hh := (t j).coe_nonneg; linarith)
    _ = _ := mul_one _

end SKConstants.Completion.N13d
