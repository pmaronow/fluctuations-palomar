module

public import ComparisonActualGeneralResourceFullB0Readout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators

theorem actual_general_four_second_low_abs_le_of_full_B0
    {n i star U : ℕ} {as : List PositiveMass}
    (bf hf : ℝ→ℝ≥0) (ho : MassOrdered 0 as)
    (hU : U≤as.length) (hs : star<U)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (scale B : ℝ) (hB : 0≤B)
    (H0 : |scale*actualGeneralOriginalCenteredResourceB0 bf hf U st.term|≤B)
    (H1 : |scale*actualGeneralOriginalCenteredResourceB0 bf hf U (st.term.retarget 0)|≤B) :
    |scale*actualGeneralFourCategoryContrast bf hf U st .secondLow|≤2*B := by
  rw [actual_general_four_second_low_eq_two_full_resource_sources bf hf U hU ho hs st]
  rw [mul_sub]
  have Hring : scale*((1/2:ℝ)*actualGeneralOriginalCenteredResourceB0 bf hf U
      (st.term.retarget 0))=(1/2:ℝ)*(scale*
        actualGeneralOriginalCenteredResourceB0 bf hf U (st.term.retarget 0)):=by ring
  rw [Hring,sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul (1/2:ℝ),abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  apply (add_le_add H0 (mul_le_mul_of_nonneg_left H1 (by norm_num : (0:ℝ)≤1/2))).trans
  linarith only [hB]

end OAI.SKFluctuations.Cavity
