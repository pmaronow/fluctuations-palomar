module

public import ComparisonSignedCavityInheritedCanonicalSourceMoments
public import ComparisonSignedCavityActualHighErrorProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem native_small_source_continuum_square_clock_budget
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hCf : 0 ≤ Cf) (hsource : NativeActualSmallSourceClocks M Temp Cf)
    (hxs : M.xs ≤ 1) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    h as.length+b as.length*S as.length+b as.length+h as.length ≤ 4*Cf+2*Temp := by
  dsimp only
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hu:=partitionPoint_mem as ho as.length
  have HC:=hsource _ hu
  have Hfield : (M.hf (partitionPoint 0 as as.length):ℝ) ≤ 2*Cf:=by
    have H:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as as.length ≤ 2 by linarith [hu.2]) hCf
    exact HC.2.trans (by linarith only [H])
  have HS:=(physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu).2
  have Hmul:=mul_le_mul_of_nonneg_left HS (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  nlinarith [HC.1]

theorem actual_minimum_inherited_current_low_error_radius_le_original
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (U : ℕ)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (hj : j ≤ as.length) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let K:=fun k=>h k+b k*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K) j ≤
      if j<U then actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
        (nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)) else 0 := by
  dsimp only
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbond k (_hk : k ≤ as.length) : (M.bf (partitionPoint 0 as k):ℝ) ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho k)).1
  exact native_actual_low_error_radius_le_original n U M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) ho hl ht hTemp hbond
    (native_small_source_continuum_square_clock_budget M Temp Cf hCf hsource hxs as ho) j hj

theorem actual_minimum_inherited_current_high_error_radius_le_original
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (U : ℕ)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (hj : j ≤ as.length) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let K:=fun k=>h k+b k*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) j ≤
      nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp j := by
  dsimp only
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbond k (_hk : k ≤ as.length) : (M.bf (partitionPoint 0 as k):ℝ) ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho k)).1
  exact native_actual_high_error_radius_le_original n U M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) ho hl ht hTemp hbond
    (native_small_source_continuum_square_clock_budget M Temp Cf hCf hsource hxs as ho) j hj

theorem actual_minimum_inherited_current_high_profile_le_original
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    {e : ℝ} (he : 0 ≤ e) :
    let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
    let K:=fun k=>h k+b k*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as k)
    let q:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
    nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T e ≤
      T.forkCost (fun j=>(R j)^e)+ClockTree.edgeBudget 0 as (fun j=>(R j)^e) := by
  dsimp only
  rw [nativeWholeLawProfileCost_eq_budget n ho]
  have H (j : ℕ) (hj : j ≤ as.length):=Real.rpow_le_rpow
    (nativeWholeLawErrorRadius_nonneg n as _ _ j)
    (actual_minimum_inherited_current_high_error_radius_le_original M Temp Cf hTemp hCf
      hsource hxs ho U hl ht j hj) he
  exact add_le_add (native_forkCost_mono_on_clock T H) (actual_low_edgeBudget_mono ho H)

end OAI.SKFluctuations.Cavity
