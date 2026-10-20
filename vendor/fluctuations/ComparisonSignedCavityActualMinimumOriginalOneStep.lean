module

public import ComparisonSignedCavityOriginalPhysicalClock
public import ComparisonSignedCavityContinuumMixedClock
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_minimum_original_pair_eq_longitudinal_step
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let s:=P₀.live.test.target
    let g:=nativeFreshAtSlot T 0 s star
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T P
    let Pg:=fun σ=>Pc (g.restRestrict σ)
    let Q:=fun σ=>Pc (T.cavityAssignment σ).1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C star
    (1-b star*chi^2)*nativeActualOriginalFreshPairMoment n q U b h K C T Pc s star=
      chi*K star*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree
          (fun σ=>Pg (g.tree.cavityAssignment σ).1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree
          (fun σ=>Pg (g.tree.cavityAssignment σ).1) g.mark)+
      b star*(chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree
        (fun σ=>Q (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
        nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b C T s star
          (fun σ c d=>Q σ*A c d))+
      nativeActualOriginalOneStepError n q U b h K C T Pc s star := by
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
  have hq : ∀i,Monotone (fun j=>q j i) := by
    intro i
    cases i with
    | inl i=>exact hbm
    | inr i=>exact hhm
  have hq0 : ∀j i,0 ≤ q j i := by
    intro j i
    cases i with
    | inl i=>exact hb j
    | inr i=>exact hh j
  have H:=actual_generated_original_pair_eq_longitudinal_step hP hi hs ho q b h K C hKC P
    hq0 hq hb hh hK hbm hhm hKm
  dsimp only at H
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1 :=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  rw [HQ] at H
  exact H

end OAI.SKFluctuations.Cavity
