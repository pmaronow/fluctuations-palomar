module

public import ComparisonNativeOriginalHighTailEdgeBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem native_high_tail_integral_le_continuum_add_l1
    {f g : ℝ→ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) (hf0 : ∀u∈Icc (0:ℝ) 1,0≤f u)
    {q u : ℝ} (hq0 : 0≤q) (hqu : q≤u) (hu1 : u≤1) :
    (∫s in u..1,f s)≤(∫s in q..1,g s)+(∫s in 0..1,|f s-g s|) := by
  have hq1 : q≤1:=hqu.trans hu1
  have hsub : uIcc q 1⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hq1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hq0 le_rfl
  have hfq:=hf.mono_set hsub
  have hgq:=hg.mono_set hsub
  have hnonneg : 0≤ᵐ[volume.restrict (Ioc q 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hf0 s ⟨hq0.trans hs.1.le,hs.2⟩
  have Hmono:=intervalIntegral.integral_mono_interval hqu hu1 le_rfl hnonneg hfq
  have Hlocal : (∫s in q..1,|f s-g s|)≤(∫s in 0..1,|f s-g s|) :=
    intervalIntegral.integral_mono_interval hq0 hq1 le_rfl
      (ae_of_all _ (fun s=>abs_nonneg (f s-g s))) (hf.sub hg).abs
  have Hnorm:=intervalIntegral.abs_integral_le_integral_abs (μ:=volume) (f:=fun s=>f s-g s) hq1
  rw [intervalIntegral.integral_sub hfq hgq] at Hnorm
  have Hupper:=le_abs_self ((∫s in q..1,f s)-(∫s in q..1,g s))
  linarith only [Hmono,Hupper,Hnorm,Hlocal]

theorem native_original_high_second_edgeBudget_le_thermal_add_mesh
    (n : ℕ) (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {as : List PositiveMass} (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh q : ℝ} (hm : PartitionMesh mesh 0 as) (hq : q∈Icc (0:ℝ) 1)
    (U : ℕ) (hU : U≤as.length) (hqU : q≤partitionPoint 0 as U) :
    ClockTree.edgeBudget 0 as
      (fun j=>if j<U then 0 else (nativeOriginalCutLowErrorRadius n b h as j)^2)≤
      (∫s in q..1,orderedPathB (n+1) b h s-(orderedPathS (n+1) b h s)^2)+
        mesh*(3*physicalBApproximationConstant n b h+1) := by
  rw [native_original_high_second_edgeBudget_eq_integral n b h ho he U hU]
  have H:=native_high_tail_integral_le_continuum_add_l1
    (physicalSampledCutLowErrorSecond_intervalIntegrable n b h hb hh as ho hm)
    (physicalOrderedThermal_intervalIntegrable n b h hb hh)
    (fun u _=>physicalSampledCutLowErrorSecond_nonneg n b h as ho u)
    hq.1 hqU (partitionPoint_mem as ho U).2
  exact H.trans (add_le_add le_rfl (physicalSampledCutLowErrorSecond_l1_bound n b h hb hh as ho he hm))

end OAI.SKFluctuations.LaplaceWindowFormalization
