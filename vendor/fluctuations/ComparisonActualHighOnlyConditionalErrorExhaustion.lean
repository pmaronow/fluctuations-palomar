module

public import ComparisonActualHighOnlyConditionalFiniteCover
public import ComparisonActualHighOnlyConditionalOpenRadiusError

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.cap_contact_error_exhaustion_high_only
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) :
    ∃F : ℕ→Finset (ordConnectedSection P.negativeSet),Monotone F ∧
      (∀t : ordConnectedSection P.negativeSet,∃j,t∈F j) ∧
      Tendsto (fun j=>∫u in 0..1,
        (A∩((⋃t : F j,Ioo (P.capFamily (F j) t).left (P.capFamily (F j) t).right)∪P.contactSet)).indicator
          (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) atTop
        (𝓝 (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
          (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)) := by
  have hH : ContinuousOn P.H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using P.hH.continuousOn
  let He := fun r=>P.H (projIcc (0:ℝ) 1 zero_le_one r)
  have hHe : Continuous He :=
    (continuousOn_iff_continuous_domRestrict.mp hH).comp continuous_projIcc
  have HR u : a.R u∈Icc (0:ℝ) 1 := a.shiftedNativeModel.R_bounds u
  have Heq u : He (a.R u)=P.H (a.R u) := by
    dsimp only [He]
    rw [projIcc_of_mem zero_le_one (HR u)]
  let : Countable (ordConnectedSection P.negativeSet) :=
    (wholeCap_representatives_countable P.negativeSet_open).to_subtype
  obtain ⟨F,hF,hcover⟩ := countable_finset_exhaustion (ordConnectedSection P.negativeSet)
  have hi : IntegrableOn a.comparisonErrorDensity (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp a.comparisonErrorDensity_intervalIntegrable
  have hRmeas : Measurable a.R := (omittedSweepQuantile_continuous zero_le_one
    ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha).measurable
  have H := NativeCapExhaustion.thermal_integral_tendsto P.negativeSet_open P.negativeSet_subset
    He a.R hHe.measurable hRmeas A hA a.comparisonErrorDensity hi F hF hcover
  have hfixed j u :
      (A∩NativeSelectedMask.fixedSupport (NativeCapExhaustion.left P.negativeSet (F j))
        (NativeCapExhaustion.right P.negativeSet (F j)) He).indicator (fun _=>(1:ℝ)) (a.R u)=
      (A∩((⋃t : F j,Ioo (P.capFamily (F j) t).left (P.capFamily (F j) t).right)∪P.contactSet)).indicator
        (fun _=>(1:ℝ)) (a.R u) := by
    rw [NativeCapExhaustion.fixedSupport_eq P.negativeSet_open P.negativeSet_subset,
      P.capFamily_union (F j)]
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,contactSet,
      mem_preimage,mem_singleton_iff,Heq,HR,true_and]
  have hfull u :
      (A∩(P.negativeSet∪{r | He r=0})).indicator (fun _=>(1:ℝ)) (a.R u)=
      (A∩(P.negativeSet∪P.contactSet)).indicator (fun _=>(1:ℝ)) (a.R u) := by
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,contactSet,
      mem_preimage,mem_singleton_iff,Heq,HR,true_and]
  simp_rw [hfixed,hfull] at H
  simp_rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one] at H
  exact ⟨F,hF,hcover,H⟩

theorem Potential.nonpositive_error_le_of_finite_budgets_high_only
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) {B : ℝ}
    (hFinite : ∀F : Finset (ordConnectedSection P.negativeSet),
      (∫u in 0..1,(A∩((⋃t : F,Ioo (P.capFamily F t).left (P.capFamily F t).right)∪P.contactSet)).indicator
        (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤ B) :
    (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
      (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤ B := by
  obtain ⟨F,_,_,H⟩ := P.cap_contact_error_exhaustion_high_only A hA
  exact le_of_tendsto H (Eventually.of_forall fun j=>hFinite (F j))

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
