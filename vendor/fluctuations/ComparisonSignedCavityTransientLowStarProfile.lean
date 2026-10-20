module

public import ComparisonSignedCavityTransientLowMovingDensity
public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_minimum_current_low_error_radius_le_original_fixed
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
      (cutLowError n U b h K) j ≤
      if j<U then actualLowErrorComparisonConstant
        (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp*
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ)) else 0 := by
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
  exact native_actual_low_error_radius_le_original n U M.bf M.hf hbf hhf ho hl ht hTemp hbond Hclock j hj

theorem native_transient_low_star_profile_le_fixed_radius (n U i star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U≤as.length) (hs : star<U) (law : ℕ→FullCoordinate n→ℝ)
    {rBound : ℕ} (hT : T.leaves≤rBound) :
    let R:=nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K .star)
    T.forkCost R+edgeBudget 0 as R≤
      (rBound:ℝ)*nativeWholeLawErrorRadius n as law (cutLowError n U b h K) star := by
  let R:=nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K .star)
  let d:=nativeWholeLawErrorRadius n as law (cutLowError n U b h K) star
  have hd : 0≤d:=nativeWholeLawErrorRadius_nonneg _ _ _ _ _
  have Hpoint j : R j≤d := by
    dsimp only [R,d]
    rw [native_transient_low_part_radius]
    dsimp only
    split_ifs with hh
    · rw [hh.2]
    · exact nativeWholeLawErrorRadius_nonneg _ _ _ _ _
  have HF:=T.native_forkCost_le_pair_bound R d (fun s t _=>Hpoint (T.splitIndex s t))
  have HEpoint j : R j≤d*(if j<U then 1 else 0) := by
    dsimp only [R]
    rw [native_transient_low_part_radius]
    dsimp only
    by_cases hpart : j≠i ∧ j=star
    · rcases hpart with ⟨hji,rfl⟩
      simp [hji,hs,d]
    · simp only [hpart,ite_false]
      exact mul_nonneg hd (by split_ifs <;> norm_num)
  have HE:=actual_low_edgeBudget_mono ho (fun j _=>HEpoint j)
  have HEscale:=actual_low_edgeBudget_linear as 0 d 0 (fun j=>if j<U then 1 else 0) (fun _=>0)
  simp only [mul_zero,add_zero,zero_mul] at HEscale
  rw [HEscale] at HE
  have HEmass:=mul_le_mul_of_nonneg_left (actual_low_edgeBudget_ones_le ho U hU) hd
  have HEfinal : edgeBudget 0 as R≤d:=HE.trans (by simpa only [mul_one] using HEmass)
  have Hleaf : (T.leaves:ℝ)≤rBound:=by exact_mod_cast hT
  have Hsum:=add_le_add HF HEfinal
  have HleafMul:=mul_le_mul_of_nonneg_right Hleaf hd
  change T.forkCost R+edgeBudget 0 as R≤(rBound:ℝ)*d
  nlinarith only [Hsum,HleafMul]

end OAI.SKFluctuations.Cavity
