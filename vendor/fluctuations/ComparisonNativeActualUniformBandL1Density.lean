module

public import ComparisonNativeOriginalHighTailEdgeBudget
public import ComparisonNativeActualCutLowErrorDensityProducer

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 14000000

theorem native_band_edgeBudget_eq_interval_integral {as : List PositiveMass}
    (ho : MassOrdered 0 as) (U V : ℕ) (hUV : U ≤ V) (hV : V ≤ as.length)
    (f : ℕ→ℝ) :
    ClockTree.edgeBudget 0 as (fun j=>if j<U then 0 else if j<V then f j else 0)=
      (∫u in partitionPoint 0 as U..partitionPoint 0 as V,massStepFunction as f u) := by
  have Hfunc : (fun j=>(if j<U then f j else 0)+
      (if j<U then 0 else if j<V then f j else 0))=(fun j=>if j<V then f j else 0) := by
    funext j
    by_cases hjU : j<U
    · have hjV : j<V := lt_of_lt_of_le hjU hUV
      simp only [hjU,hjV,ite_true,add_zero]
    · simp only [hjU,ite_false,zero_add]
  have Hbudget := Cavity.actual_low_edgeBudget_linear as 0 1 1
    (fun j=>if j<U then f j else 0) (fun j=>if j<U then 0 else if j<V then f j else 0)
  simp only [one_mul] at Hbudget
  rw [Hfunc,native_low_edgeBudget_eq_prefix_integral ho V hV,
    native_low_edgeBudget_eq_prefix_integral ho U (hUV.trans hV)] at Hbudget
  have Hints := intervalIntegral.integral_add_adjacent_intervals
    (massStepFunction_intervalIntegrable as f 0 (partitionPoint 0 as U))
    (massStepFunction_intervalIntegrable as f (partitionPoint 0 as U) (partitionPoint 0 as V))
  linarith only [Hbudget,Hints]

theorem native_original_band_l1_edgeBudget_le_sampled_interval_add_site
    (n : ℕ) (b h : ℝ→ℝ≥0) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (U V : ℕ) (hUV : U ≤ V) (hV : V ≤ as.length) :
    ClockTree.edgeBudget 0 as
      (fun j=>if j<U then 0 else if j<V then nativeOriginalCutLowErrorRadius n b h as j+1/(n+1:ℕ) else 0) ≤
      (∫u in partitionPoint 0 as U..partitionPoint 0 as V,
        Real.sqrt (physicalSampledCutLowErrorSecond n b h as ho u))+1/(n+1:ℕ) := by
  let R:=nativeOriginalCutLowErrorRadius n b h as
  let site:=(1/(n+1:ℕ):ℝ)
  have HM:=Cavity.actual_low_edgeBudget_mono ho (show ∀j,j ≤ as.length→
      (if j<U then 0 else if j<V then R j+site else 0) ≤
        (1:ℝ)*(if j<U then 0 else if j<V then R j else 0)+site*1 by
    intro j _
    by_cases hjU : j<U
    · simp only [hjU,ite_true,mul_zero,zero_add,mul_one]
      positivity
    · by_cases hjV : j<V
      · simp only [hjU,hjV,ite_false,ite_true,one_mul,mul_one,le_refl]
      · simp only [hjU,hjV,ite_false,mul_zero,zero_add,mul_one]
        positivity)
  have HO : ClockTree.edgeBudget 0 as (fun _=>(1:ℝ))=1 := by
    rw [native_edgeBudget_eq_cells_add_terminal,he,sub_self,zero_mul,add_zero,massCellSum_const,he]
    norm_num
  have HR : massStepFunction as R=(fun u=>Real.sqrt (physicalSampledCutLowErrorSecond n b h as ho u)) := by
    funext u
    exact (physicalSampledCutLowErrorRadius_eq_massStepFunction n b h as ho u).symm
  rw [Cavity.actual_low_edgeBudget_linear,one_mul,HO,mul_one,
    native_band_edgeBudget_eq_interval_integral ho U V hUV hV R,HR] at HM
  exact HM

theorem native_original_band_l1_edgeBudget_le_thermal_add_mesh
    (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {as : List PositiveMass} (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as)
    (U V : ℕ) (hUV : U ≤ V) (hV : V ≤ as.length) :
    ClockTree.edgeBudget 0 as
      (fun j=>if j<U then 0 else if j<V then nativeOriginalCutLowErrorRadius n b h as j+1/(n+1:ℕ) else 0) ≤
      (∫u in partitionPoint 0 as U..partitionPoint 0 as V,
        Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))+
        2*Real.sqrt (mesh*(3*physicalBApproximationConstant n b h+1))+1/(n+1:ℕ) := by
  let F:=fun u=>Real.sqrt (physicalSampledCutLowErrorSecond n b h as ho u)
  let G:=fun u=>Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)
  have hqU : partitionPoint 0 as U∈Icc (0:ℝ) 1:=partitionPoint_mem as ho U
  have hqV : partitionPoint 0 as V∈Icc (0:ℝ) 1:=partitionPoint_mem as ho V
  have hqUV : partitionPoint 0 as U ≤ partitionPoint 0 as V:=partitionPoint_mono as ho hUV
  have hf : IntervalIntegrable F volume 0 1:=native_intervalIntegrable_sqrt_of_intervalIntegrable
    (physicalSampledCutLowErrorSecond_intervalIntegrable n b h hb hh as ho hm)
  have hg : IntervalIntegrable G volume 0 1:=native_intervalIntegrable_sqrt_of_intervalIntegrable
    (physicalOrderedThermal_intervalIntegrable n b h hb hh)
  have hpre : uIcc (0:ℝ) (partitionPoint 0 as U)⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hqU.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hqU.2
  have hband : uIcc (partitionPoint 0 as U) (partitionPoint 0 as V)⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hqUV,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hqU.1 hqV.2
  have HF:=intervalIntegral.integral_add_adjacent_intervals (hf.mono_set hpre) (hf.mono_set hband)
  have HG:=intervalIntegral.integral_add_adjacent_intervals (hg.mono_set hpre) (hg.mono_set hband)
  have HV:=physicalSampledCutLowError_integral_error n b h hb hh as ho he hm hqV
  have HU:=physicalSampledCutLowError_integral_error n b h hb hh as ho he hm hqU
  have HVupper:=(abs_le.mp HV).2
  have HUlower:=(abs_le.mp HU).1
  have Hraw:=native_original_band_l1_edgeBudget_le_sampled_interval_add_site n b h ho he U V hUV hV
  change (∫u in 0..partitionPoint 0 as V,F u)-(∫u in 0..partitionPoint 0 as V,G u) ≤ _ at HVupper
  change _ ≤ (∫u in 0..partitionPoint 0 as U,F u)-(∫u in 0..partitionPoint 0 as U,G u) at HUlower
  change _ ≤ (∫u in partitionPoint 0 as U..partitionPoint 0 as V,F u)+_ at Hraw
  change _ ≤ (∫u in partitionPoint 0 as U..partitionPoint 0 as V,G u)+_+_
  linarith only [HF,HG,HVupper,HUlower,Hraw]

theorem original_band_l1_density_on_all_final_nets
    (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    ∀ᶠjGrid : ℕ in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1)→
        let as:=finiteCutMasses us jGrid
        ∀U V : ℕ,U ≤ V→V ≤ as.length→
          ClockTree.edgeBudget 0 as
            (fun j=>if j<U then 0 else if j<V then nativeOriginalCutLowErrorRadius n b h as j+1/(n+1:ℕ) else 0) ≤
            (∫u in partitionPoint 0 as U..partitionPoint 0 as V,
              Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))+3/(n+1:ℕ) := by
  let A:=3*physicalBApproximationConstant n b h+1
  have Hlim : Tendsto (fun k=>Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A)) atTop (𝓝 0) := by
    simpa only [zero_mul,Real.sqrt_zero] using (uniformMasses_mesh_tendsto.mul_const A).sqrt
  have HE:=Hlim.eventually (eventually_le_nhds (by positivity : (0:ℝ) < 1/(n+1:ℕ)))
  filter_upwards [HE] with k hk
  intro us hus
  dsimp only
  intro U V hUV hV
  have H:=native_original_band_l1_edgeBudget_le_thermal_add_mesh n b h hb hh
    (finiteCutMasses_ordered us hus k) (finiteCutMasses_end us hus k)
    (finiteCutMasses_mesh us hus k) U V hUV hV
  change _ ≤ _+2*Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A)+1/(n+1:ℕ) at H
  have hsite : 2*(1/(n+1:ℕ):ℝ)+1/(n+1:ℕ)=3/(n+1:ℕ) := by ring
  linarith only [H,hk,hsite]

namespace NativeOverlapMinimum

theorem actual_original_band_l1_density_on_all_final_nets
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠjGrid : ℕ in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1)→
        let as:=finiteCutMasses us jGrid
        ∀U V : ℕ,U ≤ V→V ≤ as.length→
          ClockTree.edgeBudget 0 as
            (fun j=>if j<U then 0 else if j<V then nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ) else 0) ≤
            (∫u in partitionPoint 0 as U..partitionPoint 0 as V,
              Real.sqrt (orderedPathB (n+1) M.bf (M.hf) u-(orderedPathS (n+1) M.bf M.hf u)^2))+
              3/(n+1:ℕ) := by
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  exact original_band_l1_density_on_all_final_nets n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
