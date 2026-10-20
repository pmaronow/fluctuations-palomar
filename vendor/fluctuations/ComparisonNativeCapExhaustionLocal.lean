module

public import ComparisonNativeCapExhaustion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 2200000
attribute [local instance] Classical.propDecidable
namespace NativeCapExhaustion
section Native
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem actual_local_finite_cap_thermal_exhaustion
    (α : inverseIntegralConstraints 0 0 k M)
    {U : Set ℝ} (hU : IsOpen U) (hUb : U⊆Icc (0:ℝ) 1)
    (H : ℝ→ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (A : Set ℝ) (hA : MeasurableSet A)
    (T : ℝ→ℝ) (hT : IntegrableOn T (Icc (0:ℝ) 1)) :
    ∃F : ℕ→Finset (ordConnectedSection U),Monotone F ∧
      (∀t:ordConnectedSection U,∃j,t∈F j) ∧
      Tendsto (fun j=>(wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
        (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real
        (U\wholeCapFiniteUnion U (F j))) atTop (𝓝 0) ∧
      Tendsto (fun j=>∫u in Icc (0:ℝ) 1,
        (A∩NativeSelectedMask.fixedSupport (left U (F j)) (right U (F j)) H).indicator
          (fun _=>(1:ℝ)) (comparisonSweepQuantile hc hk hkc hm hM α u)*T u) atTop
        (𝓝 (∫u in Icc (0:ℝ) 1,(A∩(U∪{r | H r=0})).indicator
          (fun _=>(1:ℝ)) (comparisonSweepQuantile hc hk hkc hm hM α u)*T u)) := by
  let He := fun r=>H (projIcc (0:ℝ) 1 zero_le_one r)
  have hHe : Continuous He :=
    (continuousOn_iff_continuous_domRestrict.mp hH).comp continuous_projIcc
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have heq u : He (R u)=H (R u) := by
    dsimp only [He]
    rw [projIcc_of_mem zero_le_one (show R u∈Icc (0:ℝ) 1 from comparisonSweepQuantile_bounds hc hk hkc hm hM α u)]
  obtain ⟨F,hF,hcover,htail,hthermal⟩ := actual_finite_cap_thermal_exhaustion
    hc hk hkc hm hM α hU hUb He hHe.measurable A hA T hT
  have hfixed j u :
      (A∩NativeSelectedMask.fixedSupport (left U (F j)) (right U (F j)) He).indicator
        (fun _=>(1:ℝ)) (R u)=
      (A∩NativeSelectedMask.fixedSupport (left U (F j)) (right U (F j)) H).indicator
        (fun _=>(1:ℝ)) (R u) := by
    have hp : (R u∈A∩NativeSelectedMask.fixedSupport (left U (F j)) (right U (F j)) He) ↔
        R u∈A∩NativeSelectedMask.fixedSupport (left U (F j)) (right U (F j)) H := by
      change (R u∈A ∧ ((∃t,R u∈Ioo (left U (F j) t) (right U (F j) t)) ∨ He (R u)=0)) ↔
        (R u∈A ∧ ((∃t,R u∈Ioo (left U (F j) t) (right U (F j) t)) ∨ H (R u)=0))
      rw [heq u]
    by_cases hu : R u∈A∩NativeSelectedMask.fixedSupport (left U (F j)) (right U (F j)) H
    · rw [indicator_of_mem hu,indicator_of_mem (hp.mpr hu)]
    · rw [indicator_of_notMem hu,indicator_of_notMem (fun h=>hu (hp.mp h))]
  have hfull u : (A∩(U∪{r | He r=0})).indicator (fun _=>(1:ℝ)) (R u)=
      (A∩(U∪{r | H r=0})).indicator (fun _=>(1:ℝ)) (R u) := by
    have hp : (R u∈A∩(U∪{r | He r=0})) ↔ R u∈A∩(U∪{r | H r=0}) := by
      change (R u∈A ∧ (R u∈U ∨ He (R u)=0)) ↔ (R u∈A ∧ (R u∈U ∨ H (R u)=0))
      rw [heq u]
    by_cases hu : R u∈A∩(U∪{r | H r=0})
    · rw [indicator_of_mem hu,indicator_of_mem (hp.mpr hu)]
    · rw [indicator_of_notMem hu,indicator_of_notMem (fun h=>hu (hp.mp h))]
  change Tendsto (fun j=>∫u in Icc (0:ℝ) 1,
      (A∩NativeSelectedMask.fixedSupport (left U (F j)) (right U (F j)) He).indicator
        (fun _=>(1:ℝ)) (R u)*T u) atTop
      (𝓝 (∫u in Icc (0:ℝ) 1,(A∩(U∪{r | He r=0})).indicator (fun _=>(1:ℝ)) (R u)*T u)) at hthermal
  simp_rw [hfixed,hfull] at hthermal
  exact ⟨F,hF,hcover,htail,hthermal⟩

theorem actual_local_full_thermal_le_of_finite_caps
    (α : inverseIntegralConstraints 0 0 k M)
    {U : Set ℝ} (hU : IsOpen U) (hUb : U⊆Icc (0:ℝ) 1)
    (H : ℝ→ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (A : Set ℝ) (hA : MeasurableSet A)
    (T : ℝ→ℝ) (hT : IntegrableOn T (Icc (0:ℝ) 1))
    {B : ℝ}
    (hfinite : ∀F : Finset (ordConnectedSection U),
      (∫u in Icc (0:ℝ) 1,
        (A∩NativeSelectedMask.fixedSupport (left U F) (right U F) H).indicator
          (fun _=>(1:ℝ)) (comparisonSweepQuantile hc hk hkc hm hM α u)*T u)≤B) :
    (∫u in Icc (0:ℝ) 1,(A∩(U∪{r | H r=0})).indicator
      (fun _=>(1:ℝ)) (comparisonSweepQuantile hc hk hkc hm hM α u)*T u)≤B := by
  obtain ⟨F,_,_,_,hlim⟩ := actual_local_finite_cap_thermal_exhaustion hc hk hkc hm hM
    α hU hUb H hH A hA T hT
  exact le_of_tendsto hlim (Eventually.of_forall (fun j=>hfinite (F j)))

end Native
end NativeCapExhaustion
end OAI.SKFluctuations.LaplaceWindowFormalization
