module

public import ComparisonActualHighOnlyPullbackFourProducers
public import ComparisonActualHighOnlyCavityConsumerPrimitives
public import ComparisonActualHighOnlyComparableBandStarBond
public import ComparisonActualHighOnlySquareConsumerActualSharpFourTerminalAlong
public import ComparisonActualHighOnlyTargetRefinement

@[expose] public section
noncomputable section
set_option autoImplicit false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem actual_minimum_joint_constant_source_eq_original_mean_gap_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let S:=nativePhysicalResourceCenter n M.bf M.hf as
    nativeActualConstantJointStarSource n as star U b h K S=
      finitePhysicalMean (n+1) as b h star-nativeOriginalScalarPairMean as K star := by
  dsimp only
  refine native_actual_constant_joint_source_eq_original_mean_gap n as star U hs hU ho
    (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
    (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
    (nativeContinuumMixedClock n M.bf M.hf as)
    (nativePhysicalResourceCenter n M.bf M.hf as) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact native_continuum_mixed_clock_eq_original_center n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  · exact fun _=>NNReal.coe_nonneg _
  · exact fun _=>NNReal.coe_nonneg _
  · exact native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  · intro i j hij
    exact M.inherited_bf_monotone (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  · intro i j hij
    exact M.inherited_hf_monotone (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  · exact native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho

theorem actual_sharp_susceptibility_bound_by_joint_source_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Tstar L Cs Cr W : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) (hAz : 0 ≤ Az) (hW : 0 < W)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (w : ActualSlowWindowChoice) (hw : IsActualSharpCalibratedSlowWindow_high_only M W Tstar L Cs w)
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
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit_high_only M htotal as ho U (by omega) hU
  obtain ⟨p,_,_,_,_,_,_,_,_,_,HS,_,_,_,_,_,_,HK,_⟩:=hw.1
  have HK' : |nativeContinuumMixedClock n M.bf M.hf as (retainedMassPrefixIndex w.star.val as)-
      Tstar*orderedPathS (n+1) M.bf M.hf w.star.val| ≤ ((starMassBandConstant cu Az/cu+1)/4)*W^3 := by
    rw [native_continuum_mixed_clock_retained_eq n M.bf M.hf as ho w.star hstar]
    exact HK
  rw [actual_minimum_joint_constant_source_eq_original_mean_gap_high_only M as ho _ U hs hU]
  exact susceptibility_from_literal_source_bound hW (by positivity) HS Hchi.1 Hchi.2 HK' hscalar hmesh

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def nativeActualConstantSourceRetainedPart_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  let T:=ClockTree.single (S:=Spin n×Bool) as
  let s:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*K star*(nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) (g.embed s)+
    nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) g.mark)

def nativeActualConstantSourceTaylorPart_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  let T:=ClockTree.single (S:=Spin n×Bool) as
  let s:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  nativeActualJointRestoredForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark

theorem nativeActualConstantSourceRemainder_eq_parts_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) :
    nativeActualConstantSourceRemainder_high_only M as star U=
      nativeActualConstantSourceRetainedPart_high_only M as star U+
      nativeActualConstantSourceMeanPart_high_only M as star U+
      nativeActualConstantSourceTaylorPart_high_only M as star U := rfl

theorem actual_constant_source_retained_part_abs_le_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp R E : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length)
    (hK : nativeContinuumMixedClock n M.bf M.hf as star ≤ R)
    (hL : let T:=ClockTree.single (S:=Spin n×Bool) as
      let g:=nativeFreshAtSlot T 0 (singleSlot as) star
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      ∀a : g.tree.Slot,|nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) a| ≤ E) :
    |nativeActualConstantSourceRetainedPart_high_only M as star U| ≤ 2*R*E := by
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit_high_only M htotal as ho U (by omega) hU
  have HK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho star
  have hR : 0 ≤ R:=HK.trans hK
  unfold nativeActualConstantSourceRetainedPart_high_only
  dsimp only at hL ⊢
  rw [abs_mul,abs_mul,abs_of_nonneg Hchi.1,abs_of_nonneg HK]
  let g:=nativeFreshAtSlot (ClockTree.single (S:=Spin n×Bool) as) 0 (singleSlot as) star
  have HL:= (abs_add_le _ _).trans (add_le_add (hL (g.embed (singleSlot as))) (hL g.mark))
  have HC:=mul_le_mul Hchi.2 hK HK (by norm_num : (0:ℝ) ≤ 1)
  simp only [one_mul] at HC
  have H:=mul_le_mul HC HL (abs_nonneg _) hR
  nlinarith only [H]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

def nativeActualConstantSourceErrorEnvelope_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  ((List.range depth).map (fun j=>
    |nativeActualFourOtherSourceErrorSum_high_only M U W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)|/(Real.exp (-4*Temp)*cK*W)+
    |nativeActualFourFirstHighErrorSum_high_only M U W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)|)).sum

theorem nativeActualConstantSourceKnownEnvelope_le_coarse_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp cK gamma sharpSaving terminalSaving W : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (hW : 0<W) (hcK : 0<cK) (hgamma : 0≤gamma) (hterminal : 0≤terminalSaving) (depth : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let bstar:=(M.bf (partitionPoint 0 as star):ℝ)
    nativeActualConstantSourceKnownEnvelope_high_only M hs hU W Temp cK gamma sharpSaving terminalSaving depth≤
      bstar*W*((depth:ℝ)*(|1-bstar*chi^2| *(6*((n+1:ℕ):ℝ)^(-sharpSaving/2)*(M.xs^2/W))/
          (Real.exp (-4*Temp)*cK*W))+(6*(depth:ℝ)+13)*M.xs^2+
        nativeActualConstantSourceErrorEnvelope_high_only M hs hU W Temp cK depth)+
      |nativeActualConstantSourceRemainder_high_only M as star U| := by
  dsimp only
  let N:=((n+1:ℕ):ℝ)
  let eps:=N^(-gamma)
  let den:=Real.exp (-4*Temp)*cK*W
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let bstar:=(M.bf (partitionPoint 0 as star):ℝ)
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  let other:=fun j=>|nativeActualFourOtherSourceErrorSum_high_only M U W
    (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)|/den+
    |nativeActualFourFirstHighErrorSum_high_only M U W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)|
  let pair:=|1-bstar*chi^2| *(6*N^(-sharpSaving/2)*(M.xs^2/W))/den
  have hN : 1≤N:=by dsimp only [N];exact_mod_cast (show 1≤n+1 by omega)
  have heps : 0≤eps:=Real.rpow_nonneg (zero_le_one.trans hN) _
  have heps1 : eps≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hgamma)
  have hp d : eps^d≤1:=pow_le_one₀ heps heps1
  have hN6 : N^(-(1:ℝ)/6)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hNt : N^(-terminalSaving)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hden : 0<den:=by dsimp only [den];positivity
  have hNs : 0≤N^(-sharpSaving/2):=Real.rpow_nonneg (zero_le_one.trans hN) _
  have hNx : 0≤N^(-(1:ℝ)/6):=Real.rpow_nonneg (zero_le_one.trans hN) _
  have Hpair d : (|1-bstar*chi^2| *(6*(N^(-sharpSaving/2)*eps^(1+d)*(M.xs^2/W))))/den≤pair:=by
    apply div_le_div_of_nonneg_right _ hden.le
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp (1+d)) hNs)
      (div_nonneg (sq_nonneg M.xs) hW.le)
    nlinarith
  have Hfrozen d : 6*(N^(-(1:ℝ)/6)*M.xs^2*eps^(1+d+1))≤6*M.xs^2:=by
    have H:=mul_le_mul_of_nonneg_left (hp (1+d+1)) (mul_nonneg hNx (sq_nonneg M.xs))
    have HN:=mul_le_mul_of_nonneg_right hN6 (sq_nonneg M.xs)
    nlinarith
  have Hinitial : N^(-(1:ℝ)/6)*M.xs^2*eps≤M.xs^2:=by
    have H:=mul_le_mul_of_nonneg_left heps1 (mul_nonneg hNx (sq_nonneg M.xs))
    have HN:=mul_le_mul_of_nonneg_right hN6 (sq_nonneg M.xs)
    nlinarith
  have Hterminal : 12*(N^(-terminalSaving)*M.xs^2)≤12*M.xs^2:=by
    nlinarith [mul_le_mul_of_nonneg_right hNt (sq_nonneg M.xs)]
  have Hsum : ((List.range depth).map (fun j=>
      (|1-bstar*chi^2| *(6*(N^(-sharpSaving/2)*eps^(1+j)*(M.xs^2/W)))+
        |nativeActualFourOtherSourceErrorSum_high_only M U W
          (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)|)/den+
      6*(N^(-(1:ℝ)/6)*M.xs^2*eps^(1+j+1))+
      |nativeActualFourFirstHighErrorSum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)|)).sum≤
      (depth:ℝ)*(pair+6*M.xs^2)+((List.range depth).map other).sum:=by
    calc
      _≤((List.range depth).map (fun j=>(pair+6*M.xs^2)+other j)).sum:=by
        apply List.sum_le_sum
        intro j _
        rw [add_div]
        dsimp only [other]
        linarith [Hpair j,Hfrozen j]
      _=_:=by rw [List.sum_map_add];simp;ring
  unfold nativeActualConstantSourceKnownEnvelope_high_only
  dsimp only
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (NNReal.coe_nonneg _) hW.le)
  change _≤(depth:ℝ)*pair+(6*(depth:ℝ)+13)*M.xs^2+((List.range depth).map other).sum
  change _+12*(N^(-terminalSaving)*M.xs^2)+N^(-(1:ℝ)/6)*M.xs^2*eps≤_
  nlinarith

end OAI.SKFluctuations.Cavity

