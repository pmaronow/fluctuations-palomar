module

public import ComparisonSignedCavityActualResourceHighTaylorReadout
public import ComparisonSignedCavityActualFreshPairMomentResourceLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

def nativeActualOriginalFreshResourceHigherHighPart
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (part : Fin 3) (l t : ℝ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeActualHigherHighPart part n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1)) (g.embed P.live.test.target) g.mark l t

theorem native_actual_original_fresh_resource_HIGH_part_eq_two_resources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (part : Fin 3) (l t : ℝ) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    nativeActualOriginalFreshResourceHigherHighPart M U P part l t=
      nativeActualResourceHigherHighPart M U (P.retarget 0) part (g.embed P.live.test.target) g.mark l t+
      nativeActualResourceHigherHighPart M U (P.retarget 0).freeze part (g.embed P.live.test.target) g.mark l t := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have HQ : cutFullVariance n q U 1 1 b h K=qfull:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have HP : (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1))=
      fun σ=>(P.retarget 0).value (fullWeight n) (fullFeature n) 0 qfull
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ+
        (P.retarget 0).freeze.value (fullWeight n) (fullFeature n) 0 qfull
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ:=by
    funext σ
    have H:=native_actual_centered_fresh_resource_readout (U:=U) q b h K C T P ho σ
    dsimp only at H
    rw [HQ] at H
    exact H
  unfold nativeActualOriginalFreshResourceHigherHighPart nativeActualResourceHigherHighPart
  dsimp only
  change nativeActualHigherHighPart part n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1)) (g.embed P.live.test.target) g.mark l t=_
  rw [HP,native_actual_higher_HIGH_part_add_test]

theorem native_actual_original_fresh_resource_HIGH_part_eq_centered_retarget
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (part : Fin 3) (l t : ℝ) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    nativeActualOriginalFreshResourceHigherHighPart M U P part l t=
      nativeActualOriginalCenteredResourceHigherHighPart M U (P.retarget 0) part
        (g.embed P.live.test.target) g.mark l t := by
  dsimp only
  rw [native_actual_original_fresh_resource_HIGH_part_eq_two_resources M U P ho,
    native_actual_original_centered_resource_HIGH_part_eq_two_resources M U (P.retarget 0) ho]

end OAI.SKFluctuations.Cavity
