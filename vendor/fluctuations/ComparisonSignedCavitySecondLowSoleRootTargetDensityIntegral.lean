module

public import ComparisonSignedCavitySecondLowInheritedMovingLiteralEntryBudget
public import ComparisonNativeActualCutLowErrorDensityProducer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false

theorem native_second_low_literal_moving_density_le_original_prefix_integral
    (n : ℕ) (b h : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (i U : ℕ) (hU : U≤as.length) :
    nativeSecondLowLiteralMovingEntryDensity n b h as i i U≤
      (∫u in 0..partitionPoint 0 as U,Real.sqrt (physicalSampledCutLowErrorSecond n b h as ho u))+
      partitionPoint 0 as U/(n+1:ℕ) := by
  let R:=nativeOriginalCutLowErrorRadius n b h as
  let site:=(1/(n+1:ℕ):ℝ)
  have HM:=actual_low_edgeBudget_mono ho (show ∀j,j≤as.length→
      nativeSecondLowMovingOriginalEntryRadius n b h as i i U j ≤ if j<U then R j+site else 0 by
    intro j _
    unfold nativeSecondLowMovingOriginalEntryRadius
    by_cases H : j<U
    · simp only [H,true_and,ite_true]
      split_ifs
      · exact le_rfl
      · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · simp only [H,false_and,ite_false,le_refl])
  have HE : (fun j=>if j<U then R j+site else 0)=
      (fun j=>(1:ℝ)*(if j<U then R j else 0)+site*(if j<U then (1:ℝ) else 0)):=by
    funext j
    split_ifs <;> ring
  have HO : edgeBudget 0 as (fun j=>if j<U then (1:ℝ) else 0)=partitionPoint 0 as U:=by
    rw [native_low_edgeBudget_eq_prefix_cells as 0 U hU,massCellSum_const,massPartition_take_end]
    simp
  have HR : massStepFunction as R=(fun u=>Real.sqrt (physicalSampledCutLowErrorSecond n b h as ho u)):=by
    funext u
    exact (physicalSampledCutLowErrorRadius_eq_massStepFunction n b h as ho u).symm
  change nativeSecondLowLiteralMovingEntryDensity n b h as i i U≤_ at HM
  rw [HE,actual_low_edgeBudget_linear,one_mul,HO,native_low_edgeBudget_eq_prefix_integral ho U hU,HR] at HM
  apply HM.trans_eq
  dsimp only [site]
  ring

theorem actual_second_low_literal_moving_density_target_integral_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Couter : ℝ) (hCouter : 0≤Couter) (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) :
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      ∀(i U : ℕ) (x : ℝ),U≤as.length → M.xs≤x → partitionPoint 0 as U≤Couter*x →
        nativeSecondLowLiteralMovingEntryDensity n M.bf M.hf as i i U≤
          (∫u in 0..min (Couter*x) 1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
            (orderedPathS (n+1) M.bf M.hf u)^2))+(1+Couter)*x/(n+1:ℕ) := by
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb:=toNNReal_monotoneOn had.1
  have hh:=toNNReal_monotoneOn had.2.1
  let A:=3*physicalBApproximationConstant n M.bf M.hf+1
  have Hlim : Tendsto (fun k=>Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A)) atTop (𝓝 0):=by
    have H:=(uniformMasses_mesh_tendsto.mul_const A).sqrt
    simpa only [zero_mul,Real.sqrt_zero] using H
  have HE:=Hlim.eventually (eventually_le_nhds (div_pos M.hxs (by positivity : 0<((n+1:ℕ):ℝ))))
  filter_upwards [HE] with k hk
  dsimp only
  intro i U x hU hxsx houter
  let as:=finiteCutMasses us k
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hm:partitionPoint 0 as U∈Icc (0:ℝ) 1:=partitionPoint_mem as ho U
  have hx : 0<x:=M.hxs.trans_le hxsx
  have hq : min (Couter*x) 1∈Icc (0:ℝ) 1:=⟨le_min (mul_nonneg hCouter hx.le) zero_le_one,min_le_right _ _⟩
  have Hcut : partitionPoint 0 as U ≤ min (Couter*x) 1:=le_min houter hm.2
  have HP:=native_second_low_literal_moving_density_le_original_prefix_integral n M.bf M.hf as ho i U hU
  have HF:=physicalSampledCutLowError_integral_error n M.bf M.hf hb hh as ho
    (finiteCutMasses_end us hus k) (finiteCutMasses_mesh us hus k) hm
  have Hupper:=(abs_le.mp HF).2
  have Hsample : (∫u in 0..partitionPoint 0 as U,
      Real.sqrt (physicalSampledCutLowErrorSecond n M.bf M.hf as ho u))≤
      (∫u in 0..partitionPoint 0 as U,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2))+M.xs/(n+1:ℕ):=by
    have HH:=Hupper
    change _≤Real.sqrt (((k+1:ℕ):ℝ)⁻¹*A) at HH
    linarith
  have HI:=native_intervalIntegrable_sqrt_of_intervalIntegrable (physicalOrderedThermal_intervalIntegrable n M.bf M.hf hb hh)
  have HIq:=HI.mono_set (by
    rw [uIcc_of_le hq.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2)
  have Hmono:=intervalIntegral.integral_mono_interval le_rfl hm.1 Hcut
    (ae_of_all _ (fun u=>Real.sqrt_nonneg (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))) HIq
  have Hsite : M.xs/(n+1:ℕ)+partitionPoint 0 as U/(n+1:ℕ)≤(1+Couter)*x/(n+1:ℕ):=by
    rw [←add_div]
    apply (div_le_div_of_nonneg_right (add_le_add hxsx houter) (by positivity : (0:ℝ)≤(n+1:ℕ))).trans_eq
    ring
  apply (HP.trans (add_le_add Hsample (le_refl (partitionPoint 0 as U/(n+1:ℕ))))).trans
  have HH:=add_le_add Hmono Hsite
  simpa only [add_assoc] using HH

end OAI.SKFluctuations.Cavity
