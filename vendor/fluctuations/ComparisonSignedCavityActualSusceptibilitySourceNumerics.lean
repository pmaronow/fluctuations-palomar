module

public import ComparisonSignedCavityActualConstantJointSourceLimit
public import ComparisonSignedCavityActualHistorySusceptibilityCoefficient
public import ComparisonSignedCavityScalarSelectedBadHistoryContinuumRemainder
public import ComparisonSignedCavityUniformCenterRefinement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem susceptibility_from_literal_source_bound
    {S K G mean T chi W c Ck Cr : ℝ}
    (hW : 0 < W) (hc : 0 < c) (hS : c*W ≤ S)
    (hchi0 : 0 ≤ chi) (hchi1 : chi ≤ 1)
    (hK : |K-T*S| ≤ Ck*W^3)
    (hscalar : |G-chi^2*K| ≤ Cr*W^3)
    (hmesh : |mean-S| ≤ W^3) :
    |T*chi^2-1| ≤ ((Ck+Cr+1)/c)*W^2+|mean-G|/(c*W) := by
  have hS0 : 0 < S:=(mul_pos hc hW).trans_le hS
  have hchi2 : chi^2 ≤ 1:=by nlinarith
  have hCk : 0 ≤ Ck*W^3:=(abs_nonneg _).trans hK
  have HK : |chi^2*(T*S-K)| ≤ Ck*W^3:=by
    rw [abs_mul,abs_of_nonneg (sq_nonneg chi),abs_sub_comm (T*S) K]
    exact (mul_le_mul hchi2 hK (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)
  have Heq : (T*chi^2-1)*S=
      chi^2*(T*S-K)-(G-chi^2*K)-(mean-G)+(mean-S):=by ring
  have H1:=abs_add_le (chi^2*(T*S-K)-(G-chi^2*K)-(mean-G)) (mean-S)
  have H2:=abs_add_le (chi^2*(T*S-K)-(G-chi^2*K)) (-(mean-G))
  have H3:=abs_add_le (chi^2*(T*S-K)) (-(G-chi^2*K))
  simp only [abs_neg,←sub_eq_add_neg] at H2 H3
  have H : |T*chi^2-1| *S ≤ (Ck+Cr+1)*W^3+|mean-G|:=by
    rw [←abs_of_pos hS0,←abs_mul,Heq]
    nlinarith only [H1,H2,H3,HK,hscalar,hmesh]
  have Hlow:=mul_le_mul_of_nonneg_left hS (abs_nonneg (T*chi^2-1))
  have Hbound : |T*chi^2-1| ≤ ((Ck+Cr+1)*W^3+|mean-G|)/(c*W):=
    (le_div_iff₀ (mul_pos hc hW)).mpr (Hlow.trans H)
  convert Hbound using 1
  field_simp

theorem actual_minimum_continuum_susceptibility_mem_unit
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ)
    (hU0 : 0 < U) (hU : U ≤ as.length) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0∈Icc (0:ℝ) 1 := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterm : K as.length ≤ Temp:=
    (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans (M.inherited_total_clock_le htotal 1 (by norm_num))
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp [relocatedClock,hU0])
    (B:=Temp) (by simpa [relocatedClock,not_lt.mpr hU] using hterm)
  exact ⟨((Real.exp_pos (-4*Temp)).le.trans HH.1),HH.2⟩

theorem actual_minimum_joint_constant_source_eq_original_mean_gap
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let S:=nativePhysicalResourceCenter n M.bf M.hf as
    nativeActualConstantJointStarSource n as star U b h K S=
      finitePhysicalMean (n+1) as b h star-nativeOriginalScalarPairMean as K star := by
  dsimp only
  apply native_actual_constant_joint_source_eq_original_mean_gap n as star U hs hU ho
  · exact native_continuum_mixed_clock_eq_original_center n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  · exact fun _=>NNReal.coe_nonneg _
  · exact fun _=>NNReal.coe_nonneg _
  · exact native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  · intro i j hij
    exact M.inherited_bf_monotone (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  · intro i j hij
    exact M.inherited_hf_monotone (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  · exact native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho

theorem actual_sharp_susceptibility_bound_by_joint_source
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Tstar L Cs Cr W : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) (hAz : 0 ≤ Az) (hW : 0 < W)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (w : ActualSlowWindowChoice) (hw : IsActualSharpCalibratedSlowWindow M W Tstar L Cs w)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hstar : w.star∈as)
    (U : ℕ) (hs : retainedMassPrefixIndex w.star.val as < U) (hU : U ≤ as.length)
    (hmesh : |finitePhysicalMean (n+1) as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
      (retainedMassPrefixIndex w.star.val as)-orderedPathS (n+1) M.bf M.hf w.star.val| ≤ W^3)
    (hscalar : let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeOriginalScalarPairMean as K (retainedMassPrefixIndex w.star.val as)-
        chi^2*K (retainedMassPrefixIndex w.star.val as)| ≤ Cr*W^3) :
    let c:=starMassBandConstant cu Az/cu
    let star:=retainedMassPrefixIndex w.star.val as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let S:=nativePhysicalResourceCenter n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |Tstar*chi^2-1| ≤ (((c+1)/4+Cr+1)/(3*c/4))*W^2+
      |nativeActualConstantJointStarSource n as star U b h K S|/((3*c/4)*W) := by
  dsimp only at hscalar ⊢
  have hc : 0 < starMassBandConstant cu Az/cu:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  obtain ⟨p,_,_,_,_,_,_,_,_,_,HS,_,_,_,_,_,_,HK,_⟩:=hw.1
  have HK' : |nativeContinuumMixedClock n M.bf M.hf as (retainedMassPrefixIndex w.star.val as)-
      Tstar*orderedPathS (n+1) M.bf M.hf w.star.val| ≤ ((starMassBandConstant cu Az/cu+1)/4)*W^3 := by
    rw [native_continuum_mixed_clock_retained_eq n M.bf M.hf as ho w.star hstar]
    exact HK
  rw [actual_minimum_joint_constant_source_eq_original_mean_gap M as ho _ U hs hU]
  exact susceptibility_from_literal_source_bound hW (by positivity) HS Hchi.1 Hchi.2 HK' hscalar hmesh

end OAI.SKFluctuations.Cavity
