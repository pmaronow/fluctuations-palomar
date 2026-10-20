module

public import ComparisonSignedCavityActualConstantJointFourIteration
public import ComparisonSignedCavityActualSusceptibilitySourceNumerics
public import ComparisonSignedCavityInheritedRetainedConstantLongitudinalAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def nativeActualConstantSourceRetainedPart
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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

def nativeActualConstantSourceMeanPart
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi^2*b star*(finitePhysicalMean (n+1) as b h star-
    finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)

def nativeActualConstantSourceTaylorPart
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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

theorem nativeActualConstantSourceRemainder_eq_parts
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) :
    nativeActualConstantSourceRemainder M as star U=
      nativeActualConstantSourceRetainedPart M as star U+
      nativeActualConstantSourceMeanPart M as star U+
      nativeActualConstantSourceTaylorPart M as star U := rfl

theorem actual_constant_source_retained_part_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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
    |nativeActualConstantSourceRetainedPart M as star U| ≤ 2*R*E := by
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  have HK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho star
  have hR : 0 ≤ R:=HK.trans hK
  unfold nativeActualConstantSourceRetainedPart
  dsimp only at hL ⊢
  rw [abs_mul,abs_mul,abs_of_nonneg Hchi.1,abs_of_nonneg HK]
  let g:=nativeFreshAtSlot (ClockTree.single (S:=Spin n×Bool) as) 0 (singleSlot as) star
  have HL:= (abs_add_le _ _).trans (add_le_add (hL (g.embed (singleSlot as))) (hL g.mark))
  have HC:=mul_le_mul Hchi.2 hK HK (by norm_num : (0:ℝ) ≤ 1)
  simp only [one_mul] at HC
  have H:=mul_le_mul HC HL (abs_nonneg _) hR
  nlinarith only [H]

theorem actual_constant_source_mean_part_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length)
    (hmesh : let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      |finitePhysicalMean (n+1) as b h star-nativePhysicalResourceCenter n M.bf M.hf as star| ≤
        1/(n+1:ℕ)) :
    |nativeActualConstantSourceMeanPart M as star U| ≤ 2*Temp/(n+1:ℕ) := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let mean:=finitePhysicalMean (n+1) as b h star
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  have Hmean0 : 0 ≤ mean:=finitePhysicalMean_nonneg (n+1) as b h star
  have Hmean1 : mean ≤ 1:=finitePhysicalMean_le_one (n+1) ho b h star
  have Hb : b star ≤ Temp:=by
    have H:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho star)
    dsimp only [b]
    linarith [(M.hf (partitionPoint 0 as star)).coe_nonneg]
  have Hb0 : 0 ≤ b star:=NNReal.coe_nonneg _
  have Hchi2 : chi^2 ≤ 1:=by change chi∈Icc (0:ℝ) 1 at Hchi;nlinarith [Hchi.1,Hchi.2]
  have Hcoef : chi^2*b star ≤ Temp:=by nlinarith
  have HE : |mean-mean/(n+1:ℕ)-S star| ≤ 2/(n+1:ℕ):=by
    have HH:=abs_add_le (mean-S star) (-(mean/(n+1:ℕ)))
    simp only [abs_neg,←sub_eq_add_neg] at HH
    rw [abs_of_nonneg (div_nonneg Hmean0 (by positivity))] at HH
    have Hdiv:=div_le_div_of_nonneg_right Hmean1 (show (0:ℝ) ≤ (n+1:ℕ) by positivity)
    change |mean-S star| ≤ 1/(n+1:ℕ) at hmesh
    have Heq : mean-mean/(n+1:ℕ)-S star=mean-S star-mean/(n+1:ℕ):=by ring
    rw [Heq,show (2:ℝ)/(n+1:ℕ)=1/(n+1:ℕ)+1/(n+1:ℕ) by ring]
    exact HH.trans (add_le_add hmesh Hdiv)
  change |chi^2*b star*(mean-mean/(n+1:ℕ)-S star)| ≤ _
  rw [abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg _) Hb0)]
  have H:=mul_le_mul Hcoef HE (abs_nonneg _) (Hb0.trans Hb)
  convert H using 1
  ring

end OAI.SKFluctuations.Cavity
