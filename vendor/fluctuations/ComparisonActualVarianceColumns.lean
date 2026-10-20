module

public import ComparisonSelectedVarianceEnergyLedger
public import ComparisonSelectedBinEnergyScore
public import ComparisonSideSquareColumn

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory ProbabilityTheory Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem physicalSelectedUnitEnergy_nonneg (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    {U : Type} [Fintype U] [DecidableEq U] (unit : Fin (steps.length+1) → U) (u : U) :
    0 ≤ physicalSelectedUnitEnergy n steps q0 J unit u := by
  unfold physicalSelectedUnitEnergy
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg (pathMassDifferences_nonneg steps ha i)
      (integral_nonneg (fun z=>physicalCutSusceptibility_nonneg n steps ha id i.val z))
  · exact le_rfl

theorem physical_actual_bin_variance_le_reciprocal_energy (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {δ width : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ width) (hstart : x 0=0) (hend : x K=width)
    (hx : ∀u:Fin K,x u < x (u.val+1)) :
    actualBinSideVariance n K steps q0 J unit x δ width ≤
      ∑u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u*
        ((max δ (x u))⁻¹+(max δ (width-x (u.val+1)))⁻¹) := by
  have hpq : δ ≤ width-δ := by linarith
  have hmono := unitPoints_monotoneOn x (fun u hu=>(hx ⟨u,hu⟩).le)
  have hleftB u : x (u:Fin K) ≤ width := by
    rw [←hend]
    exact hmono ⟨by omega,by omega⟩ ⟨by omega,le_rfl⟩ (by omega)
  have hrightA u : 0 ≤ x ((u:Fin K).val+1) := by
    rw [←hstart]
    exact hmono ⟨le_rfl,by omega⟩ ⟨by omega,by omega⟩ (by omega)
  have hL := physical_selected_weight_variance_integral_le_energy n steps ha q0 J unit
    (fun t u=>left 0 (x u.val) (x (u.val+1)) t) hpq (fun u=>by
      have h := left_continuousOn (a:=0) (b:=width) hδ (hx u)
      exact h.mono (by simpa only [zero_add] using Icc_subset_Icc le_rfl (by linarith : width-δ ≤ width)))
  have hR := physical_selected_weight_variance_integral_le_energy n steps ha q0 J unit
    (fun t u=>right width (x u.val) (x (u.val+1)) t) hpq (fun u=>
      (right_continuousOn (a:=0) hδ (hx u)).mono (Icc_subset_Icc hδ.le le_rfl))
  have hLc (u:Fin K) : (∫t in δ..width-δ,(left 0 (x u.val) (x (u.val+1)) t)^2) ≤ (max δ (x u))⁻¹ := by
    have hI : IntervalIntegrable (fun t=>(left 0 (x u.val) (x (u.val+1)) t)^2) volume δ width := by
      apply ContinuousOn.intervalIntegrable (μ:=volume)
      simpa [uIcc_of_le (by linarith : δ ≤ width),Pi.pow_def] using
        (left_continuousOn (a:=0) (b:=width) hδ (hx u)).pow 2
    have hm := intervalIntegral.integral_mono_interval le_rfl hpq
      (by linarith : width-δ ≤ width) (Filter.Eventually.of_forall (fun _=>sq_nonneg _)) hI
    exact hm.trans (by simpa only [zero_add,sub_zero] using
      left_square_column_le_reciprocal (a:=0) hδ (by linarith) (hx u) (hleftB u))
  have hRc (u:Fin K) : (∫t in δ..width-δ,(right width (x u.val) (x (u.val+1)) t)^2) ≤ (max δ (width-x (u.val+1)))⁻¹ := by
    have hI : IntervalIntegrable (fun t=>(right width (x u.val) (x (u.val+1)) t)^2) volume 0 (width-δ) := by
      apply ContinuousOn.intervalIntegrable (μ:=volume)
      simpa [uIcc_of_le (by linarith : 0 ≤ width-δ),Pi.pow_def] using
        (right_continuousOn (a:=0) hδ (hx u)).pow 2
    have hm := intervalIntegral.integral_mono_interval hδ.le hpq le_rfl
      (Filter.Eventually.of_forall (fun _=>sq_nonneg _)) hI
    exact hm.trans (right_square_column_le_reciprocal (a:=0) hδ (by linarith) (hx u) (hrightA u))
  have hLs := Finset.sum_le_sum (fun u (_:u∈(Finset.univ:Finset (Fin K)))=>
    mul_le_mul_of_nonneg_left (hLc u) (physicalSelectedUnitEnergy_nonneg n steps ha q0 J unit u))
  have hRs := Finset.sum_le_sum (fun u (_:u∈(Finset.univ:Finset (Fin K)))=>
    mul_le_mul_of_nonneg_left (hRc u) (physicalSelectedUnitEnergy_nonneg n steps ha q0 J unit u))
  unfold actualBinSideVariance selectedScoreVariance selectedLeftWeight selectedRightWeight
  exact (add_le_add (hL.trans hLs) (hR.trans hRs)).trans_eq (by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring)

end OAI.SKFluctuations.WholeUnitSideKernel
