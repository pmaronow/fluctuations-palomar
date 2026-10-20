module

public import ComparisonSignedCavityActualLowErrorDensity

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem actual_minimum_current_low_fork_radius_le_original
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0<cl) (hAz : 0≤Az) (Temp : ℝ) (hTemp : 0≤Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0) (hxs1 : M.xs≤1)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (U : ℕ)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (hj : j≤as.length) (hjU : j<U) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let S:=fun k=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let K:=fun k=>h k+b k*S k
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
      (cutLowError n U b h K) j≤
      actualLowErrorComparisonConstant (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp*
        (nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)) := by
  dsimp only
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have hbond k (_hk : k≤as.length) : (M.bf (partitionPoint 0 as k):ℝ)≤Temp :=
    (M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho k)).2.1
  have Hfield:=(M.bare_source_clock_bounds hcl hAz Temp hb hh
    (partitionPoint_mem as ho as.length)).2.2.2
  have hCf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have Hsmall : (M.hf (partitionPoint 0 as as.length):ℝ)≤
      2*NativeOverlapMinimum.bareSourceClockConstant cl Az D := by
    have H:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as as.length≤2 by linarith [(partitionPoint_mem as ho as.length).2]) hCf
    exact Hfield.trans (by linarith only [H])
  have HS:=(physicalOrderedPathS_mem_unit n M.bf M.hf hbf hhf (partitionPoint_mem as ho as.length)).2
  have Hmul:=mul_le_mul_of_nonneg_left HS (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  have Hclock : (M.hf (partitionPoint 0 as as.length):ℝ)+
      (M.bf (partitionPoint 0 as as.length):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as as.length)+
      (M.bf (partitionPoint 0 as as.length):ℝ)+(M.hf (partitionPoint 0 as as.length):ℝ)≤
      4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp := by
    linarith [hbond as.length le_rfl]
  have H:=native_actual_low_error_radius_le_original n U M.bf M.hf hbf hhf ho hl ht hTemp hbond Hclock j hj
  simpa only [hjU,ite_true] using H

end OAI.SKFluctuations.Cavity
