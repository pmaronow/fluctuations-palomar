module

public import ComparisonShiftedNativeBandCarrier
public import ComparisonNativeCapExhaustionLocal
public import ComparisonActualHighWallContactGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem thermal_mask_integrable (A : Set ℝ) (hA : MeasurableSet A) :
    IntervalIntegrable (fun u=>A.indicator (fun _=>1) (m.R u)*m.thermal u) volume 0 1 := by
  have hT:=physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf m.hbf m.hhf
  apply intervalIntegrable_bounded_measurable_mul
    ((measurable_const.indicator hA).comp m.R_continuous.measurable)
    (show (0:ℝ)≤1 by norm_num) _ hT
  intro u hu
  by_cases hs:m.R u∈A <;> simp [hs]

theorem thermal_nonneg {u : ℝ} (hu : u∈Ioc (0:ℝ) 1) : 0≤ m.thermal u :=
  sub_nonneg.mpr (orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf m.hbf m.hhf hu).2.2.1

theorem R_strictMonoOn : StrictMonoOn m.R (Icc m.u0 1) := by
  intro u hu v hv huv
  apply lt_of_not_ge
  intro h
  have H:=m.alpha.val.property.2 h
  rw [m.R_spec hv,m.R_spec hu] at H
  exact huv.not_ge H

def massSlice (lo hi : ℝ) : Set ℝ:=Ioo (m.R lo) (m.R hi)

theorem massSlice_quantile_mem {lo hi u : ℝ}
    (hlo : lo∈Icc m.u0 1) (hhi : hi∈Icc m.u0 1) (hu : u∈Icc (0:ℝ) 1) :
    m.R u∈m.massSlice lo hi ↔ u∈Ioo lo hi := by
  constructor
  · intro h
    exact ⟨lt_of_not_ge (fun H=>h.1.not_ge (m.R_monotone H)),
      lt_of_not_ge (fun H=>h.2.not_ge (m.R_monotone H))⟩
  · intro h
    have huHigh : u∈Icc m.u0 1:=⟨hlo.1.trans h.1.le,hu.2⟩
    exact ⟨m.R_strictMonoOn hlo huHigh h.1,m.R_strictMonoOn huHigh hhi h.2⟩

theorem massSlice_thermal_integral {lo hi : ℝ}
    (hlo : lo∈Icc m.u0 1) (hhi : hi∈Icc m.u0 1) (hlh : lo≤ hi) :
    (∫u in 0..1,(m.massSlice lo hi).indicator (fun _=>1) (m.R u)*m.thermal u)=
      ∫u in lo..hi,m.thermal u := by
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  have he : (∫u in Icc (0:ℝ) 1,(m.massSlice lo hi).indicator (fun _=>1) (m.R u)*m.thermal u)=
      ∫u in Icc (0:ℝ) 1,(Ioo lo hi).indicator m.thermal u := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only
    have hm:=m.massSlice_quantile_mem hlo hhi hu
    by_cases hp:u∈Ioo lo hi
    · rw [indicator_of_mem (hm.mpr hp),indicator_of_mem hp,one_mul]
    · rw [indicator_of_notMem (fun H=>hp (hm.mp H)),indicator_of_notMem hp,zero_mul]
  rw [he,setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (Ioo_subset_Icc_self.trans (Icc_subset_Icc (m.hu.1.trans hlo.1) hhi.2)),
    ←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hlh]

theorem cap_thermal_exhaustion {U : Set ℝ} (hU : IsOpen U) (hUb : U⊆Icc m.rmin 1)
    (H : ℝ→ℝ) (hH : ContinuousOn H (Icc m.rmin 1)) (A : Set ℝ) (hA : MeasurableSet A) :
    ∃F : ℕ→Finset (ordConnectedSection U),Monotone F ∧
      (∀t : ordConnectedSection U,∃j,t∈F j) ∧
      Tendsto (fun j=>∫u in 0..1,
        (A∩NativeSelectedMask.fixedSupport (NativeCapExhaustion.left U (F j))
          (NativeCapExhaustion.right U (F j)) H).indicator (fun _=>(1:ℝ)) (m.R u)*m.thermal u) atTop
        (𝓝 (∫u in 0..1,(A∩(U∪{r | H r=0})).indicator (fun _=>(1:ℝ)) (m.R u)*m.thermal u)) := by
  let He:=fun r=>H (projIcc m.rmin 1 m.hr r)
  have hHe : Continuous He:=(continuousOn_iff_continuous_domRestrict.mp hH).comp continuous_projIcc
  have heq u : He (m.R u)=H (m.R u):=by
    dsimp only [He]
    rw [projIcc_of_mem m.hr (m.R_bounds u)]
  let : Countable (ordConnectedSection U):=(wholeCap_representatives_countable hU).to_subtype
  obtain ⟨F,hF,hcover⟩:=countable_finset_exhaustion (ordConnectedSection U)
  have hT : IntegrableOn m.thermal (Icc (0:ℝ) 1):=by
    have ht:=physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf m.hbf m.hhf
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one (by simp)).mp ht
  have hlim:=NativeCapExhaustion.thermal_integral_tendsto hU hUb He m.R hHe.measurable
    m.R_continuous.measurable A hA m.thermal hT F hF hcover
  have hfixed j u :
      (A∩NativeSelectedMask.fixedSupport (NativeCapExhaustion.left U (F j))
        (NativeCapExhaustion.right U (F j)) He).indicator (fun _=>(1:ℝ)) (m.R u)=
      (A∩NativeSelectedMask.fixedSupport (NativeCapExhaustion.left U (F j))
        (NativeCapExhaustion.right U (F j)) H).indicator (fun _=>(1:ℝ)) (m.R u):=by
    simp only [indicator_apply,mem_inter_iff,NativeSelectedMask.fixedSupport,
      mem_ofPred_eq,heq]
  have hfull u : (A∩(U∪{r | He r=0})).indicator (fun _=>(1:ℝ)) (m.R u)=
      (A∩(U∪{r | H r=0})).indicator (fun _=>(1:ℝ)) (m.R u):=by
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,heq]
  simp_rw [hfixed,hfull] at hlim
  simp_rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one] at hlim
  exact ⟨F,hF,hcover,hlim⟩

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
