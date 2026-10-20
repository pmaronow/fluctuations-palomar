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

theorem native_original_high_l1_edgeBudget_le_sampled_tail_add_site
    (n : ℕ) (b h : ℝ→ℝ≥0) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) (U : ℕ) (hU : U ≤ as.length) :
    ClockTree.edgeBudget 0 as
      (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n b h as j+1/(n+1:ℕ)) ≤
      (∫u in partitionPoint 0 as U..1,Real.sqrt (physicalSampledCutLowErrorSecond n b h as ho u))+
        1/(n+1:ℕ) := by
  let R:=nativeOriginalCutLowErrorRadius n b h as
  let site:=(1/(n+1:ℕ):ℝ)
  have HM:=Cavity.actual_low_edgeBudget_mono ho (show ∀j,j ≤ as.length→
      (if j<U then 0 else R j+site) ≤ (1:ℝ)*(if j<U then 0 else R j)+site*1 by
    intro j _
    by_cases hj : j<U
    · simp only [hj,ite_true,mul_zero,zero_add,mul_one]
      positivity
    · simp only [hj,ite_false,one_mul,mul_one,le_refl])
  have HO : ClockTree.edgeBudget 0 as (fun _=>(1:ℝ))=1 := by
    rw [native_edgeBudget_eq_cells_add_terminal,he,sub_self,zero_mul,add_zero,massCellSum_const,he]
    norm_num
  have HR : massStepFunction as R=(fun u=>Real.sqrt (physicalSampledCutLowErrorSecond n b h as ho u)) := by
    funext u
    exact (physicalSampledCutLowErrorRadius_eq_massStepFunction n b h as ho u).symm
  rw [Cavity.actual_low_edgeBudget_linear,one_mul,HO,mul_one,
    native_high_edgeBudget_eq_tail_integral ho he U hU R,HR] at HM
  exact HM

theorem native_original_high_l1_edgeBudget_le_thermal_add_mesh
    (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {as : List PositiveMass} (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) (U : ℕ) (hU : U ≤ as.length) :
    ClockTree.edgeBudget 0 as
      (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n b h as j+1/(n+1:ℕ)) ≤
      (∫u in partitionPoint 0 as U..1,
        Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))+
        2*Real.sqrt (mesh*(3*physicalBApproximationConstant n b h+1))+1/(n+1:ℕ) := by
  let F:=fun u=>Real.sqrt (physicalSampledCutLowErrorSecond n b h as ho u)
  let G:=fun u=>Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)
  have hq : partitionPoint 0 as U∈Icc (0:ℝ) 1:=partitionPoint_mem as ho U
  have hf : IntervalIntegrable F volume 0 1:=native_intervalIntegrable_sqrt_of_intervalIntegrable
    (physicalSampledCutLowErrorSecond_intervalIntegrable n b h hb hh as ho hm)
  have hg : IntervalIntegrable G volume 0 1:=native_intervalIntegrable_sqrt_of_intervalIntegrable
    (physicalOrderedThermal_intervalIntegrable n b h hb hh)
  have hpre : uIcc (0:ℝ) (partitionPoint 0 as U)⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hq.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2
  have htail : uIcc (partitionPoint 0 as U) 1⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hq.2,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hq.1 le_rfl
  have HF:=intervalIntegral.integral_add_adjacent_intervals (hf.mono_set hpre) (hf.mono_set htail)
  have HG:=intervalIntegral.integral_add_adjacent_intervals (hg.mono_set hpre) (hg.mono_set htail)
  have Hwhole:=physicalSampledCutLowError_integral_error n b h hb hh as ho he hm
    (show (1:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have Hpre:=physicalSampledCutLowError_integral_error n b h hb hh as ho he hm hq
  have HW:=(abs_le.mp Hwhole).2
  have HP:=(abs_le.mp Hpre).1
  have Hraw:=native_original_high_l1_edgeBudget_le_sampled_tail_add_site n b h ho he U hU
  change (∫u in 0..1,F u)-(∫u in 0..1,G u) ≤ _ at HW
  change _ ≤ (∫u in 0..partitionPoint 0 as U,F u)-(∫u in 0..partitionPoint 0 as U,G u) at HP
  change _ ≤ (∫u in partitionPoint 0 as U..1,F u)+_ at Hraw
  change _ ≤ (∫u in partitionPoint 0 as U..1,G u)+_+_
  linarith only [HF,HG,HW,HP,Hraw]

theorem original_high_l1_density_on_all_final_nets
    (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    ∀ᶠjGrid : ℕ in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1)→
        let as:=finiteCutMasses us jGrid
        ∀U : ℕ,U ≤ as.length→
          ClockTree.edgeBudget 0 as
            (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n b h as j+1/(n+1:ℕ)) ≤
            (∫u in partitionPoint 0 as U..1,
              Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))+3/(n+1:ℕ) := by
  let A:=3*physicalBApproximationConstant n b h+1
  have Hlim : Tendsto (fun k=>Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A)) atTop (𝓝 0) := by
    simpa only [zero_mul,Real.sqrt_zero] using (uniformMasses_mesh_tendsto.mul_const A).sqrt
  have HE:=Hlim.eventually (eventually_le_nhds (by positivity : (0:ℝ) < 1/(n+1:ℕ)))
  filter_upwards [HE] with k hk
  intro us hus
  dsimp only
  intro U hU
  have H:=native_original_high_l1_edgeBudget_le_thermal_add_mesh n b h hb hh
    (finiteCutMasses_ordered us hus k) (finiteCutMasses_end us hus k)
    (finiteCutMasses_mesh us hus k) U hU
  change _ ≤ _+2*Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A)+1/(n+1:ℕ) at H
  have hsite : 2*(1/(n+1:ℕ):ℝ)+1/(n+1:ℕ)=3/(n+1:ℕ) := by ring
  linarith only [H,hk,hsite]

namespace NativeOverlapMinimum

theorem actual_original_high_l1_density_on_all_final_nets
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠjGrid : ℕ in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1)→
        let as:=finiteCutMasses us jGrid
        ∀U : ℕ,U ≤ as.length→
          ClockTree.edgeBudget 0 as
            (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)) ≤
            (∫u in partitionPoint 0 as U..1,
              Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))+
              3/(n+1:ℕ) := by
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  exact original_high_l1_density_on_all_final_nets n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
