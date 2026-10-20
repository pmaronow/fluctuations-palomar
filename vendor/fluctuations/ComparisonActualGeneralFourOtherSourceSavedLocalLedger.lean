module

public import ComparisonActualGeneralFourCategories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
set_option maxHeartbeats 12000000

theorem actual_general_four_other_source_saved_local_ledger
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (d scale qga qg qsite qsecond Di Dstar I P R : ℝ)
    (Cga Cg Cl Cj C4 CY Ch Cgl Cjl Cd C2 : ℝ)
    (Hga : |(d⁻¹)^st.generation*actualGeneralFourGaContrast bf hf U st|≤
      scale*(Cga*qga*d^3+Cga*d*P))
    (Hg : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .gammaRetained|≤
      scale*(Cg*qg*d^3))
    (Hl0 : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .longitudinalLeft|≤
      scale*(Cl*d*P))
    (Hl1 : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .longitudinalRight|≤
      scale*(Cl*d*P))
    (Hj : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .jointLowTwoHigh|≤
      scale*(Cj*d*P))
    (H4 : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .fourGLowRestoration|≤
      scale*(C4*d*P))
    (Ht : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .higherTaylor|≤
      scale*(CY*(d*P+d^2*(Di+Dstar+I))))
    (Hh : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .gammaHighRestoration|≤
      scale*(Ch*d^2*R))
    (Hgl : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .gammaLowRestoration|≤
      scale*(Cgl*d^2*Dstar))
    (Hjl : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .jointLowRestoration|≤
      scale*(Cjl*d^2*Dstar))
    (Hd : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .deletedSite|≤
      scale*(Cd*qsite*d^3))
    (H2 : |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .secondLow|≤
      scale*(C2*qsecond*d^3)) :
    |(d⁻¹)^st.generation*actualGeneralFourOtherSourceErrorContrast bf hf U st|≤
      scale*(d^3*(Cga*qga+Cg*qg+Cd*qsite+C2*qsecond)+
        d^2*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)+
        d*P*(Cga+2*Cl+Cj+C4+CY)+d^2*R*Ch) := by
  have Htriangle : |(d⁻¹)^st.generation*actualGeneralFourOtherSourceErrorContrast bf hf U st|≤
      |(d⁻¹)^st.generation*actualGeneralFourGaContrast bf hf U st|+
        (nativeActualOtherSourceCategories.map (fun cat=>
          |(d⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st cat|)).sum:=by
    rw [actual_general_four_other_source_eq_Ga_add_categories,mul_add]
    apply (abs_add_le _ _).trans
    apply add_le_add le_rfl
    rw [←List.sum_map_mul_left]
    exact native_abs_sum_map_le _ _
  simp only [nativeActualOtherSourceCategories,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    at Htriangle
  apply Htriangle.trans
  calc
    _ ≤ scale*(Cga*qga*d^3+Cga*d*P)+scale*(Cg*qg*d^3)+
      scale*(Ch*d^2*R)+scale*(Cgl*d^2*Dstar)+scale*(C2*qsecond*d^3)+
      scale*(CY*(d*P+d^2*(Di+Dstar+I)))+scale*(Cj*d*P)+
      scale*(Cjl*d^2*Dstar)+scale*(Cl*d*P)+scale*(Cl*d*P)+
      scale*(C4*d*P)+scale*(Cd*qsite*d^3):=by
        linarith only [Hga,Hg,Hl0,Hl1,Hj,H4,Ht,Hh,Hgl,Hjl,Hd,H2]
    _ = _ := by ring

end OAI.SKFluctuations.Cavity
