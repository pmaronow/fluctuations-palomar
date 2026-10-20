module

public import ComparisonSignedCavityActualHighErrorTransport
public import ComparisonSignedCavityActualLowErrorDensity

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeOriginalHighErrorEnvelope (n U : ℕ) (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (Mclock Temp : ℝ) (j : ℕ) : ℝ :=
  if j<U then 0 else actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n bf hf as j+1/(n+1:ℕ))

theorem actual_minimum_current_high_error_radius_le_original
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (Temp : ℝ) (hTemp : 0 ≤ Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0) (hxs1 : M.xs ≤ 1)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (U : ℕ) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (hj : j ≤ as.length) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let S:=fun k=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let K:=fun k=>h k+b k*S k
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
      (cutTSlope n U 0 b h K) j ≤
      nativeOriginalHighErrorEnvelope n U M.bf M.hf as
        (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp j := by
  dsimp only
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have hbond k (_hk : k ≤ as.length) : (M.bf (partitionPoint 0 as k):ℝ) ≤ Temp:=
    (M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho k)).2.1
  have Hfield:=(M.bare_source_clock_bounds hcl hAz Temp hb hh
    (partitionPoint_mem as ho as.length)).2.2.2
  have hCf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have Hsmall : (M.hf (partitionPoint 0 as as.length):ℝ) ≤
      2*NativeOverlapMinimum.bareSourceClockConstant cl Az D:=by
    have H:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as as.length ≤ 2 by linarith [(partitionPoint_mem as ho as.length).2]) hCf
    exact Hfield.trans (by linarith only [H])
  have HS:=(physicalOrderedPathS_mem_unit n M.bf M.hf hbf hhf (partitionPoint_mem as ho as.length)).2
  have Hmul:=mul_le_mul_of_nonneg_left HS (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  have Hclock : (M.hf (partitionPoint 0 as as.length):ℝ)+
      (M.bf (partitionPoint 0 as as.length):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as as.length)+
      (M.bf (partitionPoint 0 as as.length):ℝ)+(M.hf (partitionPoint 0 as as.length):ℝ) ≤
      4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp:=by
    linarith [hbond as.length le_rfl]
  exact native_actual_high_error_radius_le_original n U M.bf M.hf hbf hhf ho hl ht hTemp hbond Hclock j hj

theorem native_forkCost_mono_on_clock {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) {f g : ℕ→ℝ} (hfg : ∀j,j ≤ as.length → f j ≤ g j) :
    T.forkCost f ≤ T.forkCost g := by
  induction T generalizing f g with
  | leaf=>exact le_refl _
  | step a T ih=>
    exact ih (fun j hj=>hfg (1+j) (by simp only [List.length_cons];omega))
  | fork T V ihT ihV=>
    exact add_le_add (add_le_add (hfg 0 (Nat.zero_le _)) (ihT hfg)) (ihV hfg)

theorem actual_minimum_current_high_profile_le_original
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (Temp : ℝ) (hTemp : 0 ≤ Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0) (hxs1 : M.xs ≤ 1)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    {e : ℝ} (he : 0 ≤ e) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let S:=fun k=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let K:=fun k=>h k+b k*S k
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
      (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp
    nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
      (cutTSlope n U 0 b h K) T e ≤
        T.forkCost (fun j=>(R j)^e)+ClockTree.edgeBudget 0 as (fun j=>(R j)^e) := by
  dsimp only
  rw [nativeWholeLawProfileCost_eq_budget n ho]
  have H (j : ℕ) (hj : j ≤ as.length):=Real.rpow_le_rpow
    (nativeWholeLawErrorRadius_nonneg n as _ _ j)
    (actual_minimum_current_high_error_radius_le_original M hcl hAz Temp hTemp hb hh hxs1 ho U hl ht j hj) he
  exact add_le_add (native_forkCost_mono_on_clock T H) (actual_low_edgeBudget_mono ho H)

end OAI.SKFluctuations.Cavity
