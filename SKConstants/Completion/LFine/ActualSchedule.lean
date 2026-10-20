module

public import SKConstants.Completion.LFine.ScheduleSummation
public import SKConstants.ParisiFullVarianceIntegral
public import SKConstants.ParisiFullSpinRowMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SKConstants.Completion.LFine
open SKConstantsOAI.ZeroTemperatureSK LQ
variable {Ω : Type*} [MeasurableSpace Ω]

def actualFineScale (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (j : ℕ) : ℝ :=
  actualParisiPosteriorIntervalScale W β (growingQueryTime δ j) (growingQueryTime δ (j+1))

theorem actualFineScale_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ) : 0 < actualFineScale W β δ j :=
  NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ _ _
    (growingQueryTime_strictMono δ hδ (Nat.lt_succ_self j)))

theorem actualFineScale_square (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ) :
    (actualFineScale W β δ j)^2 =
      actualParisiFullOverlap W β (growingQueryTime δ (j+1)) -
        actualParisiFullOverlap W β (growingQueryTime δ j) :=
  actualParisiPosteriorIntervalScale_sq W β hβ _ _
    (growingQueryTime_strictMono δ hδ (Nat.lt_succ_self j))

theorem actualFineScale_square_sum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) :
    (∑ j : Fin K, (actualFineScale W β δ j.val)^2) =
      actualParisiFullOverlap W β (growingQueryTime δ K) := by
  have hzero : actualParisiFullOverlap W β 0 = 0 := by
    simpa only [NNReal.coe_zero, zero_div] using actualParisiFullOverlap_pre W β hβ 0 bot_le
  induction K with
  | zero => simp [growingQueryTime_zero, hzero]
  | succ K ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin K, (actualFineScale W β δ j.val)^2) + (actualFineScale W β δ K)^2 = _
    rw [ih, actualFineScale_square W β hβ δ hδ K]
    ring

theorem actualFineScale_square_sum_le_one (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) :
    (∑ j : Fin K, (actualFineScale W β δ j.val)^2) ≤ 1 := by
  let := W.isProbability
  rw [actualFineScale_square_sum W β hβ δ hδ K]
  unfold actualParisiFullOverlap
  have hi : Integrable (fun ω => (actualParisiMagnetizationObservable W β (growingQueryTime δ K) ω)^2)
      W.law := by
    simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β
      (growingQueryTime δ K) (growingQueryTime δ K)
  have hp (ω : Ω) : (actualParisiMagnetizationObservable W β (growingQueryTime δ K) ω)^2 ≤ 1 := by
    have h := actualParisiMagnetizationObservable_abs_le W β (growingQueryTime δ K) ω
    rcases abs_le.mp h with ⟨hlo,hhi⟩
    nlinarith
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono_ae hi (integrable_const 1) (ae_of_all _ hp)

theorem growing_previous_duration_sum (δ : ℝ≥0) (K : ℕ) :
    (∑ j : Fin K, meshDuration δ j.val) = meshTime δ K := by
  induction K with
  | zero => simp [meshTime_zero]
  | succ K ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin K, meshDuration δ j.val) + meshDuration δ K = _
    rw [ih, meshTime_succ]

theorem actualFineCellError_sum_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (N : ℝ) (hN : 0 < N) :
    (∑ j : Fin K, fineCellError N (j.val+1) (actualFineScale W β δ j.val) (meshDuration δ j.val)) ≤
      fineScheduleError N K (meshTime δ (K+1))
        (actualParisiPosteriorRowMGFProxy W β (growingQueryTime δ (K+1))) := by
  apply fineCellError_sum_le N hN K _ _ _ _ (NNReal.coe_nonneg _)
    (fun j => actualFineScale_pos W β hβ δ hδ j.val)
    (fun j => (meshDuration_pos δ hδ j.val).le)
    (actualFineScale_square_sum_le_one W β hβ δ hδ K)
  · rw [growing_previous_duration_sum]
    exact meshTime_mono δ (Nat.le_succ K)
  · intro j
    have hST := growingQueryTime_strictMono δ hδ (Nat.lt_succ_self j.val)
    have hTH := (growingQueryTime_strictMono δ hδ).monotone
      (show j.val+1 ≤ K+1 by omega)
    have h := NNReal.coe_le_coe.mpr (actualParisiPosteriorIntervalScale_duration_budget
      W β hβ _ _ _ hST hTH)
    rw [NNReal.coe_sub hST.le, NNReal.coe_mul, NNReal.coe_pow] at h
    simpa only [actualFineScale, meshDuration, growingQueryTime_succ, NNReal.coe_add,
      add_sub_cancel_left] using h

end SKConstants.Completion.LFine
