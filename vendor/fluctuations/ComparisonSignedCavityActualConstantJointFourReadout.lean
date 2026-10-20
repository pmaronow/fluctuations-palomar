module

public import ComparisonSignedCavityActualConstantJointSourceLimit
public import ComparisonSignedCavityActualConstantStarFourCalibration
public import ComparisonSignedCavityActualOriginalClockGCarrier
public import ComparisonSignedCavityActualSusceptibilitySourceNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

def nativeActualConstantSourceChildren
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) (hs : star<U) (hU : U≤as.length) :
    List (NativeActualResourceState (Spin n×Bool) as 0 star) :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  (base.projection (hs.le.trans hU)).reweight chi::
    nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU) .highRow base

theorem nativeActualConstantSourceChildren_valid
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length)
    (Q : NativeActualResourceState (Spin n×Bool) as 0 star)
    (hQ : Q∈nativeActualConstantSourceChildren M as star U hs hU) :
    NativeActualResourceGenerated 0 star U [] Q.generation Q.tree Q.term := by
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  have Hbase : NativeActualResourceGenerated 0 star U [] base.generation base.tree base.term:=
    .physical (.constant as hU)
  rcases List.mem_cons.mp hQ with rfl|hQ
  · exact (Hbase.projection (hs.le.trans hU)).reweight _
  · exact nativeActualResourceStep_valid _ hs (hs.le.trans hU) .highRow base Hbase Q hQ

theorem nativeActualConstantSourceChildren_generation
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length)
    (Q : NativeActualResourceState (Spin n×Bool) as 0 star)
    (hQ : Q∈nativeActualConstantSourceChildren M as star U hs hU) : Q.generation=1 := by
  rcases List.mem_cons.mp hQ with rfl|hQ
  · rfl
  · exact nativeActualResourceStep_generation _ hs (hs.le.trans hU) .highRow _ Q hQ

theorem nativeActualConstantSourceChildren_leaves
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length)
    (Q : NativeActualResourceState (Spin n×Bool) as 0 star)
    (hQ : Q∈nativeActualConstantSourceChildren M as star U hs hU) : Q.tree.leaves≤3 := by
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  have hb : base.tree.leaves≤1:=by rw [show base.tree=ClockTree.single (S:=Spin n×Bool) as from rfl,ClockTree.single_leaves_exact]
  rcases List.mem_cons.mp hQ with rfl|hQ
  · change (base.projection (hs.le.trans hU)).tree.leaves≤3
    exact nativeActualResourceStep_leaves_le
      (nativeOriginalHighRowGamma U (nativeContinuumMixedClock n M.bf M.hf as))
      hs (hs.le.trans hU) .projection base _ hb (List.mem_singleton_self _)
  · exact nativeActualResourceStep_leaves_le _ hs (hs.le.trans hU) .highRow base Q hb hQ

theorem actual_minimum_constant_source_children_response
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤as.length) :
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let s:=singleSlot as
    let g:=nativeFreshAtSlot T 0 s star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let S:=nativePhysicalResourceCenter n M.bf M.hf as
    let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
    chi*nativeOriginalLongitudinalPairing n 0 q 0 U K b S g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
      nativeOriginalFreshPartnerLResponse n 0 q 0 U K b S T s star (fun _ c d=>A c d)=
    W*((nativeActualConstantSourceChildren M as star U hs hU).map
      (nativeActualMinimumFourStateResponse M U W)).sum := by
  dsimp only
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hzero (σ : base.tree.Assignment) : base.term.value (fullWeight n) (fullFeature n)
      0 q (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) S 0 σ=1:=by
    simp [base,nativeActualConstantState,NativeResourceTerm.value,NativeResourceTerm.scalar,
      NativeResourceTerm.ofLive,nativeResourceConstant,NativeGeneratedTest.value,
      nativeGeneratedEdgeProduct,NativeGeneratedTest.edges]
  have HH:=nativeOriginalClockHighStep_response ho hs hU base K b S 0 q 0 0 q 0 W
  dsimp only at HH
  simp_rw [Hzero,one_mul] at HH
  simp only [base,nativeActualConstantState,Nat.zero_add,pow_one] at HH
  have HP:=actual_minimum_constant_star_response_eq_original M as W star U (hs.le.trans hU)
  dsimp only at HP
  have HR:=nativeOriginalClockResourceResponse_reweight
    (base.projection (hs.le.trans hU)).term ho U 1 K b S chi 0 q 0 0 q 0 W
  change nativeActualMinimumFourStateResponse M U W
      ((base.projection (hs.le.trans hU)).reweight chi)=
    chi*nativeActualMinimumFourStateResponse M U W (base.projection (hs.le.trans hU)) at HR
  rw [HP] at HR
  unfold nativeActualConstantSourceChildren
  simp only [List.map_cons,List.sum_cons]
  rw [HR]
  change _=W*(chi*(W⁻¹*_)+_)
  change ((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
      .highRow base).map (nativeActualMinimumFourStateResponse M U W)).sum= _ at HH
  rw [HH]
  simp only [base,nativeActualConstantState] at *
  have HA : (fun (_ : (ClockTree.single (S:=Spin n×Bool) as).Assignment) c d=>
      deletedOverlap n (joinSpin d) (joinSpin c)-S star)=
      (fun _ c d=>deletedOverlap n (joinSpin c) (joinSpin d)-S star):=by
    funext σ c d
    simp only [deletedOverlap, mul_comm]
  rw [HA]
  dsimp only [chi,K,b,h,S,q,NativeResourceTerm.ofLive,nativeResourceConstant]
  field_simp

theorem nativeActualConstantSourceChildren_coefficient_variation
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U≤as.length) :
    ((nativeActualConstantSourceChildren M as star U hs hU).map
      (fun Q=>|Q.term.coefficient|)).sum≤6 := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  have Hrow:=nativeActualResourceStep_coefficient_variation_le ho (nativeOriginalHighRowGamma U K)
    (fun st p _=>nativeOriginalHighRowGamma_abs_le_one ho U K st p)
    hs (hs.le.trans hU) .highRow base
    (show base.tree.leaves≤1 by simp only [base,nativeActualConstantState,single_leaves_exact,le_refl])
  have Hcoef : base.term.coefficient=1:=rfl
  rw [Hcoef] at Hrow
  norm_num only [abs_one,NativeActualExpansionOp.coefficientCost,Nat.cast_one,mul_one,one_mul] at Hrow
  unfold nativeActualConstantSourceChildren
  simp only [List.map_cons,List.sum_cons,NativeActualResourceState.reweight,
    NativeResourceTerm.reweight,NativeActualResourceState.projection,NativeResourceTerm.projection,
    nativeActualConstantState,NativeResourceTerm.ofLive,mul_one]
  change |chi|+_≤6
  rw [abs_of_nonneg Hchi.1]
  have Hchi1 : chi≤1:=Hchi.2
  change chi+((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    .highRow base).map (fun Q=>|Q.term.coefficient|)).sum≤6
  linarith

end OAI.SKFluctuations.Cavity
