module

public import ComparisonSignedCavityActualConstantMeanExchange
public import ComparisonSignedCavityActualMinimumOriginalOneStep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_minimum_constant_gap_eq_twice_old_longitudinal
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i
    finitePhysicalMean (n+1) as b h i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      chi^2*b i*(finitePhysicalMean (n+1) as b h i-
        finitePhysicalMean (n+1) as b h i/(n+1:ℕ)-C i)+
      2*b i*chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_hf_monotone hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKC : ∀j,K j=h j+b j*C j:=native_continuum_mixed_clock_eq_original_center n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have H:=actual_original_constant_gap_eq_twice_old_longitudinal n as i U hi hU ho b h K C
    hKC hb hh hK hbm hhm hKm
  dsimp only at H
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1 :=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  rw [HQ] at H
  exact H

end OAI.SKFluctuations.Cavity
