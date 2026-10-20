module

public import ComparisonActualHighOnlyPullbackFourProducers
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyRawResourcePairBudget
public import ComparisonActualHighOnlyLowSharpRadiusCompatibleSourceAlong
public import ComparisonActualHighOnlyCriticalScaleNumerics
public import ComparisonSignedCavityActualMinimumTwoFreshRecursion
public import ComparisonSignedCavityActualMinimumFourResourceSource
public import ComparisonSignedCavityActualMinimumFourResourceRecursion
public import ComparisonSignedCavityActualFourResourceForest
public import ComparisonSignedCavityActualFourResourceIteration
public import ComparisonSignedCavityActualFourGContinuumTerminalFromPairs
public import ComparisonSignedCavityActualCenteredFourTerminalLaw
public import ComparisonSignedCavityActualClockTerminalGAtom
public import ComparisonSignedCavityActualClockFrozenGResourcePairing
public import ComparisonSignedCavityActualConstantStarFourCalibration
public import ComparisonSignedCavityActualConstantJointFourReadout
public import ComparisonSignedCavityActualConstantJointFourIteration
public import ComparisonSignedCavityActualFirstHighSourceSplit
public import ComparisonSignedCavityActualFourResidualDecomposition
public import ComparisonSignedCavityActualFourFirstHighDecomposition
public import ComparisonSignedCavityActualFourCollectiveIteration
public import ComparisonSignedCavityActualFourFirstHighIteration
public import ComparisonSignedCavityActualConstantJointFourNumerics
public import ComparisonSignedCavityActualOriginalContinuumWeights
public import ComparisonSignedCavityActualInheritedContinuumGWeights
public import ComparisonSignedCavityActualFourGContinuumWeights
public import ComparisonSignedCavityActualFourForestNumerics
public import ComparisonSignedCavityActualFourFreshPairContrast
public import ComparisonSignedCavityActualInheritedClockGAtom
public import ComparisonSignedCavityActualInheritedClockFrozenGResourcePairing
public import ComparisonSignedCavityActualInheritedClockMeanSaving
public import ComparisonSignedCavityActualInheritedFrozenMeanCorrection
public import ComparisonSignedCavityActualTerminalDepth
public import ComparisonSignedCavityActualMixedTerminalDepth

@[expose] public section
noncomputable section
set_option linter.unusedVariables false

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_minimum_original_longitudinal_eq_two_fresh_subtraction_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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
    chi*K star*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C T Q s=
      nativeOriginalPairRecursionDefect n q U b h K C T Pc s star-
      (1/2:ℝ)*nativeOriginalPairRecursionDefect n q U b h K C g.tree Pg g.mark star-
      nativeOriginalPairRecursionChildren n q U b h K C T Pc s star+
      (1/2:ℝ)*nativeOriginalPairRecursionChildren n q U b h K C g.tree Pg g.mark star := by
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
  have H:=actual_original_longitudinal_eq_two_fresh_subtraction hP hi hs ho q b h K C hKC P
    hq0 hq hb hh hK hbm hhm hKm
  dsimp only at H
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1 :=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  rw [HQ] at H
  exact H

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_minimum_centered_resource_four_source_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let P:=nativeActualResourceRestValue st.term v₀ q₀ x₀ C
    let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀
    let Fc:=fun σ=>F σ-st.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull F 0
    let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
    let s:=st.term.live.test.target
    let g:=nativeFreshAtSlot st.tree 0 s star
    let Pg:=fun σ=>Pc (g.restRestrict σ)
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    chi*K star*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C st.tree Fc s=
      nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
      (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree Pg g.mark star+
      nativeOriginalFourResourceFunctional n 0 qfull 0 U K b C st.tree Fc s star := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term v₀ q₀ x₀ C
  let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀
  let Fc:=fun σ=>F σ-st.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull F 0
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  have HQ : cutFullVariance n qr U 1 1 b h K=qfull:=
    native_full_endpoint_clock_mixed_independent n qr U 1 b h K
      (finitePhysicalMixedClock (n+1) as b h)
  have HF : (fun σ=>Pc (st.tree.cavityAssignment σ).1)=Fc := by
    have H:=native_actual_resource_original_centered_readout st.term v₀ q₀ x₀ C qr U b h K
    dsimp only at H
    rw [HQ] at H
    exact H
  have Hfresh : (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1))=
      fun σ=>Fc (g.restrict σ) := by
    funext σ
    rw [←g.restRestrict_actual]
    exact congrFun HF (g.restrict σ)
  have HE:=actual_minimum_original_longitudinal_eq_two_fresh_subtraction_high_only M hP hi hs ho P
  dsimp only at HE
  change _=nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star-
    nativeOriginalPairRecursionChildren n qr U b h K C st.tree Pc s star+
    (1/2:ℝ)*nativeOriginalPairRecursionChildren n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star at HE
  rw [nativeOriginalPairRecursionChildren_eq_functional,
    nativeOriginalPairRecursionChildren_eq_functional,HQ,HF,Hfresh] at HE
  change _=nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star+
    nativeOriginalFourResourceFunctional n 0 qfull 0 U K b C st.tree Fc s star
  unfold nativeOriginalFourResourceFunctional
  dsimp only
  linear_combination HE

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

def nativeActualOriginalFourResourceDefect_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

private theorem four_source_normalize_high_only (a d L D G : ℝ) (hd : d≠0)
    (H : d*L=D+G) : a*L=a/d*D+a/d*G := by
  calc
    a*L=(a/d)*(d*L) := by field_simp
    _=(a/d)*(D+G) := by rw [H]
    _=a/d*D+a/d*G := by ring

theorem actual_minimum_centered_resource_four_recursion_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W≠0)
    (hstarK : 0 < nativeContinuumMixedClock n M.bf M.hf as star) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let F:=nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W
    let G:=nativeOriginalClockFourGStepResponse hs hP.highCut_le_length K b C 0 qfull 0 0 qfull 0 W
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    F st+F st.freeze=(W⁻¹)^st.generation/(chi*K star)*nativeActualOriginalFourResourceDefect_high_only M U st+
      G st+G st.freeze := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hchi : 0 < chi:=(Real.exp_pos _).trans_le Hchi.1
  have hd : chi*K star≠0:=(mul_pos hchi hstarK).ne'
  have Hsrc:=actual_minimum_centered_resource_four_source_high_only M st hP hi hs ho 0 qfull 0
  dsimp only at Hsrc
  have Hleft:=nativeOriginalClockStateResponse_centered_value ho U K b C 0 qfull 0 W st
  have Hright:=nativeOriginalClockFourGStepResponse_centered_value ho hs hP.highCut_le_length
    K b C 0 qfull 0 W hW st
  dsimp only at Hleft Hright
  rw [←Hleft,add_assoc,←Hright]
  apply four_source_normalize_high_only _ _ _ _ _ hd
  exact Hsrc

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

def nativeActualOriginalFourRecursionError_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let children:=nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGBranches
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) st
  (W⁻¹)^st.generation/(chi*K star)*nativeActualOriginalFourResourceDefect_high_only M U st-
    (children.map (fun Q=>nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W Q.freeze)).sum

theorem actual_minimum_centered_four_resource_level_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W≠0)
    (hstarK : 0 < nativeContinuumMixedClock n M.bf M.hf as star) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let F : NativeActualResourceState (Spin n×Bool) as i star→ℝ :=
    nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W
    let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)
    let zs:=xs.flatMap (fun Q=>[Q,Q.freeze])
    (zs.map F).sum=
      (zs.map (nativeActualOriginalFourRecursionError_high_only M hs hU W)).sum+
      ((zs.flatMap (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight)).map F).sum := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let F : NativeActualResourceState (Spin n×Bool) as i star→ℝ :=
    nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let zs:=xs.flatMap (fun Q=>[Q,Q.freeze])
  let G : NativeActualResourceState (Spin n×Bool) as i star→ℝ :=
    nativeOriginalClockFourGStepResponse hs hU K b C 0 qfull 0 0 qfull 0 W
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let E:=fun Q : NativeActualResourceState (Spin n×Bool) as i star=>
    (W⁻¹)^Q.generation/(chi*K star)*nativeActualOriginalFourResourceDefect_high_only M U Q
  let H:=fun Q : NativeActualResourceState (Spin n×Bool) as i star=>
    ((nativeActualWeightedBranchStep Γ hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight Q).map
      (fun R=>F R.freeze)).sum
  have Hzvalid : ∀Q∈zs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
    intro Q hQ
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with rfl|rfl
    · exact hxs _ hP
    · exact (hxs _ hP).freeze
  have Hsource : (zs.map (fun Q=>F Q+F Q.freeze)).sum=
      (zs.map (fun Q=>E Q+G Q+G Q.freeze)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro Q hQ
    exact actual_minimum_centered_resource_four_recursion_high_only M Q (Hzvalid Q hQ) hi hs ho W hW hstarK
  have HFzero:=nativeOriginalClock_centered_list_frozen_sum ho U K b C 0 qfull 0 0 qfull 0 W xs
  have HGzero:=nativeOriginalClockFourGStepResponse_centered_list_frozen_sum ho hs hU K b C
    0 qfull 0 0 qfull 0 W hW xs
  change (zs.map (fun Q=>F Q.freeze)).sum=0 at HFzero
  change (zs.map (fun Q=>G Q.freeze)).sum=0 at HGzero
  simp only [List.sum_map_add,HFzero,HGzero,add_zero] at Hsource
  have Hnext :
      ((zs.flatMap (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight)).map F).sum=
      (zs.map G).sum+(zs.map H).sum := by
    simp only [List.map_flatMap,native_sum_flatMap]
    have HQ (Q : NativeActualResourceState (Spin n×Bool) as i star) :
        ((nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
          nativeActualOriginalFourGCenteredBranches weight Q).map F).sum=G Q+H Q :=
      nativeOriginalClockFourGBranches_centered_response hs hU Q K b C 0 qfull 0 0 qfull 0 W
    simp_rw [HQ]
    exact List.sum_map_add
  change (zs.map F).sum=(zs.map (fun Q=>E Q-H Q)).sum+
    ((zs.flatMap (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
      nativeActualOriginalFourGCenteredBranches weight)).map F).sum
  rw [sum_map_sub_explicit,Hnext]
  linarith only [Hsource]

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualMinimumFourStateResponse_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (W : ℝ) (Q : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W Q

def nativeActualMinimumFourResidualSum_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ) (depth : ℕ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  ((List.range depth).map (fun j=>
    ((nativeActualMinimumFourCenteredForest_high_only M hs hU W j xs).map
      (nativeActualOriginalFourRecursionError_high_only M hs hU W)).sum)).sum

theorem actual_minimum_four_resource_forest_level_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W ≠ 0)
    (hstarK : 0 < nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    ((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth xs).map
      (nativeActualMinimumFourStateResponse_high_only M U W)).sum=
    ((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth xs).map
      (nativeActualOriginalFourRecursionError_high_only M hs hU W)).sum+
    ((nativeActualMinimumFourCenteredForest_high_only M hs hU W (depth+1) xs).map
      (nativeActualMinimumFourStateResponse_high_only M U W)).sum := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  obtain ⟨ys,hys⟩:=nativeActualFourCenteredForest_centered Γ hs (hs.le.trans hU) weight depth xs
  have Hv:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth xs hxs
  have Hy : ∀Q∈ys,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
    intro Q hQ
    apply Hv Q
    rw [hys]
    exact List.mem_flatMap.mpr ⟨Q,hQ,by simp⟩
  have H:=actual_minimum_centered_four_resource_level_high_only M ys Hy hi hs hU ho W hW hstarK
  change ((ys.flatMap (fun Q=>[Q,Q.freeze])).map
      (nativeActualMinimumFourStateResponse_high_only M U W)).sum=
    ((ys.flatMap (fun Q=>[Q,Q.freeze])).map
      (nativeActualOriginalFourRecursionError_high_only M hs hU W)).sum+
    (((ys.flatMap (fun Q=>[Q,Q.freeze])).flatMap
      (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight)).map
      (nativeActualMinimumFourStateResponse_high_only M U W)).sum at H
  rw [←hys] at H
  exact H

theorem actual_minimum_four_resource_finite_iteration_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W ≠ 0)
    (hstarK : 0 < nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    ((xs.flatMap (fun Q=>[Q,Q.freeze])).map
      (nativeActualMinimumFourStateResponse_high_only M U W)).sum=
    nativeActualMinimumFourResidualSum_high_only M hs hU W depth xs+
    ((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth xs).map
      (nativeActualMinimumFourStateResponse_high_only M U W)).sum := by
  induction depth with
  | zero=>simp [nativeActualMinimumFourResidualSum_high_only,nativeActualMinimumFourCenteredForest_high_only,
      nativeActualFourCenteredForest]
  | succ depth ih=>
    have H:=actual_minimum_four_resource_forest_level_high_only M xs hxs hi hs hU ho W hW hstarK depth
    rw [H] at ih
    simpa only [nativeActualMinimumFourResidualSum_high_only,List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,add_assoc] using ih

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

def nativeActualOriginalContinuumFourGFrontier_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (depth : ℕ) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
    (nativeOriginalClockFourGBranchBeta U K b parent tag)
  ((nativeActualWeightedFrontier (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGCenteredBranches weight depth
    (nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU)))).map
    (nativeOriginalClockStateResponse U K b C 0 q 0 0 q 0 W)).sum

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def nativeActualOriginalContinuumFrozenSeedFourGFrontier_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (depth : ℕ) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
    (nativeOriginalClockFourGBranchBeta U K b parent tag)
  ((nativeActualWeightedFrontier (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGCenteredBranches weight depth
    (nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))).freeze).map
    (nativeOriginalClockStateResponse U K b C 0 q 0 0 q 0 W)).sum

def nativeActualOriginalContinuumCenteredFourGFrontier_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (depth : ℕ) : ℝ :=
  ((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth
    [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))]).map
    (nativeActualMinimumFourStateResponse_high_only M U W)).sum

theorem native_actual_original_centered_four_G_frontier_eq_two_seeds_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (depth : ℕ) :
    nativeActualOriginalContinuumCenteredFourGFrontier_high_only M as W i star U hi hs hU depth=
      nativeActualOriginalContinuumFourGFrontier_high_only M as W i star U hi hs hU depth+
      nativeActualOriginalContinuumFrozenSeedFourGFrontier_high_only M as W i star U hi hs hU depth := by
  unfold nativeActualOriginalContinuumCenteredFourGFrontier_high_only
    nativeActualMinimumFourCenteredForest_high_only nativeActualMinimumFourStateResponse_high_only
    nativeActualOriginalContinuumFourGFrontier_high_only nativeActualOriginalContinuumFrozenSeedFourGFrontier_high_only
  exact nativeActualFourCenteredForest_singleton_response _ _ _ _ _ _ _

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

def nativeMinimumClockHighGAtom_high_only {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (U : ℕ) (a c e f : T.Slot) : T.Assignment→ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  nativeOriginalHighGAtom T U K b
    (nativePhysicalResourceCenter n M.bf M.hf as) a c e f

def NativeOriginalGMarkedWord.clockAtom_high_only {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (U : ℕ) (a : T.Slot) : g.tree.Assignment→ℝ :=
  nativeMinimumClockHighGAtom_high_only M K g.tree U
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

def nativeActualClockFrozenResourceGInsertion_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (U k : ℕ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) : ℝ :=
  ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*
    g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ*
          g.clockAtom_high_only M K U P.live.test.target σ)) x)).sum

 theorem nativeActualClockFrozenResourceGInsertion_eq_clock_response_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (U k : ℕ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    nativeActualClockFrozenResourceGInsertion_high_only M K P U k v₀ q₀ x₀ v q x W=
      nativeOriginalClockResourceResponse P U k K
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (nativePhysicalResourceCenter n M.bf M.hf as) v₀ q₀ x₀ v q x W := by
  have Hatom (g : NativeOriginalGMarkedWord T) :
      g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v₀ q₀
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ*g.clockAtom_high_only M K U P.live.test.target σ)) x=
        (W⁻¹)^k*g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>P.value (fullWeight n) (fullFeature n) v₀ q₀
            (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
            (nativePhysicalResourceCenter n M.bf M.hf as) x₀
            (g.p.restrict (g.r.restrict (g.z.restrict σ)))*g.clockAtom_high_only M K U P.live.test.target σ) x := by
    simp_rw [g.liftResource_value]
    rw [g.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  unfold nativeActualClockFrozenResourceGInsertion_high_only
  simp_rw [Hatom]
  unfold nativeOriginalClockResourceResponse
  have H:=nativeOriginalGMarkedWords_weighted_kernel_sum T
    (fun p r z=>z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ (p.restrict (r.restrict (z.restrict σ)))*
          nativeOriginalHighGAtom z.tree U
            K
            (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
            (nativePhysicalResourceCenter n M.bf M.hf as)
            (z.embed (r.embed (p.embed P.live.test.target)))
            (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x)
  conv_rhs =>
    unfold nativeOriginalLongitudinalPairing
    rw [←H,←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  simp only [NativeOriginalGMarkedWord.clockAtom_high_only,NativeOriginalGMarkedWord.tree,
    nativeMinimumClockHighGAtom_high_only]
  ring

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_minimum_constant_star_response_eq_original_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (star U : ℕ) (hstar : star≤ as.length) :
    let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection hstar
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 (singleSlot as) star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let S:=nativePhysicalResourceCenter n M.bf M.hf as
    let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
    nativeActualMinimumFourStateResponse_high_only M U W st=
      W⁻¹*nativeOriginalLongitudinalPairing n 0 q 0 U K b S g.tree
        (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) (singleSlot as)))
          (joinSpin (g.spin σ))-S star) (g.embed (singleSlot as)) := by
  dsimp only
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  have Hzero (σ : base.tree.Assignment) : base.term.value (fullWeight n) (fullFeature n)
      0 q (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) S 0 σ=1:=by
    simp [base,nativeActualConstantState,NativeResourceTerm.value,NativeResourceTerm.scalar,
      NativeResourceTerm.ofLive,nativeResourceConstant,NativeGeneratedTest.value,
      nativeGeneratedEdgeProduct,NativeGeneratedTest.edges]
  have H:=nativeOriginalClockResourceResponse_projection base.term U 0 K b S 0 q 0 0 q 0 W hstar
  dsimp only at H
  simp_rw [Hzero,one_mul] at H
  simpa only [nativeActualMinimumFourStateResponse_high_only,nativeOriginalClockStateResponse,
    NativeActualResourceState.projection,nativeActualConstantState,base,pow_one,
    nativeResourceConstant,NativeResourceTerm.ofLive,Nat.zero_add] using H

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

theorem actual_minimum_constant_source_children_response_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤ as.length) :
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
    W*((nativeActualConstantSourceChildren_high_only M as star U hs hU).map
      (nativeActualMinimumFourStateResponse_high_only M U W)).sum := by
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
  have HP:=actual_minimum_constant_star_response_eq_original_high_only M as W star U (hs.le.trans hU)
  dsimp only at HP
  have HR:=nativeOriginalClockResourceResponse_reweight
    (base.projection (hs.le.trans hU)).term ho U 1 K b S chi 0 q 0 0 q 0 W
  change nativeActualMinimumFourStateResponse_high_only M U W
      ((base.projection (hs.le.trans hU)).reweight chi)=
    chi*nativeActualMinimumFourStateResponse_high_only M U W (base.projection (hs.le.trans hU)) at HR
  rw [HP] at HR
  unfold nativeActualConstantSourceChildren_high_only
  simp only [List.map_cons,List.sum_cons]
  rw [HR]
  change _=W*(chi*(W⁻¹*_)+_)
  change ((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
      .highRow base).map (nativeActualMinimumFourStateResponse_high_only M U W)).sum= _ at HH
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

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

def nativeActualMinimumConstantJointSource_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  nativeActualConstantJointStarSource n as star U
    (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
    (nativeContinuumMixedClock n M.bf M.hf as) (nativePhysicalResourceCenter n M.bf M.hf as)

def nativeActualConstantSourceRemainder_high_only
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
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*K star*(nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) (g.embed s)+
    nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) g.mark)+
  chi^2*b star*(finitePhysicalMean (n+1) as b h star-
    finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)+
  nativeActualJointRestoredForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark

def nativeActualConstantSourceFrozenCorrection_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) (hs : star<U) (hU : U≤ as.length) (W : ℝ) : ℝ :=
  nativeActualConstantSourceRemainder_high_only M as star U-
    (M.bf (partitionPoint 0 as star):ℝ)*W*
      ((nativeActualConstantSourceChildren_high_only M as star U hs hU).map
        (fun Q=>nativeActualMinimumFourStateResponse_high_only M U W Q.freeze)).sum

theorem actual_minimum_constant_joint_source_eq_children_and_remainder_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤ as.length) :
    nativeActualMinimumConstantJointSource_high_only M as star U=
      (M.bf (partitionPoint 0 as star):ℝ)*W*
        ((nativeActualConstantSourceChildren_high_only M as star U hs hU).map
          (nativeActualMinimumFourStateResponse_high_only M U W)).sum+
      nativeActualConstantSourceRemainder_high_only M as star U := by
  have H:=actual_minimum_constant_source_children_response_high_only M as ho W hW star U hs hU
  dsimp only at H
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have Hq : finitePhysicalCavitySquareVariance n U as b h 1 1=
      cutFullVariance n q U 1 1 b h K:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h _ K
  change _+nativeOriginalFreshPartnerLResponse n 0 (finitePhysicalCavitySquareVariance n U as b h 1 1)
    0 U K b S _ _ star _= _ at H
  rw [Hq] at H
  unfold nativeActualMinimumConstantJointSource_high_only nativeActualConstantJointStarSource
    nativeActualConstantSourceRemainder_high_only
  dsimp only
  linear_combination (M.bf (partitionPoint 0 as star):ℝ)*H

theorem actual_minimum_constant_joint_source_eq_centered_children_and_correction_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤ as.length) :
    nativeActualMinimumConstantJointSource_high_only M as star U=
      (M.bf (partitionPoint 0 as star):ℝ)*W*
        (((nativeActualConstantSourceChildren_high_only M as star U hs hU).flatMap
          (fun Q=>[Q,Q.freeze])).map (nativeActualMinimumFourStateResponse_high_only M U W)).sum+
      nativeActualConstantSourceFrozenCorrection_high_only M as star U hs hU W := by
  rw [actual_minimum_constant_joint_source_eq_children_and_remainder_high_only M as ho W hW star U hs hU]
  unfold nativeActualConstantSourceFrozenCorrection_high_only
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,List.sum_map_add]
  ring

theorem actual_minimum_constant_joint_source_eq_finite_four_iteration_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤ as.length)
    (hstarK : 0<nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
    nativeActualMinimumConstantJointSource_high_only M as star U=
      (M.bf (partitionPoint 0 as star):ℝ)*W*
        (nativeActualMinimumFourResidualSum_high_only M hs hU W depth children+
          ((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth children).map
            (nativeActualMinimumFourStateResponse_high_only M U W)).sum)+
      nativeActualConstantSourceFrozenCorrection_high_only M as star U hs hU W := by
  dsimp only
  rw [actual_minimum_constant_joint_source_eq_centered_children_and_correction_high_only M as ho W hW star U hs hU]
  rw [actual_minimum_four_resource_finite_iteration_high_only M _
    (fun Q hQ=>nativeActualConstantSourceChildren_valid_high_only M hs hU Q hQ)
    (Nat.zero_le star) hs hU ho W hW hstarK depth]

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

theorem actual_minimum_one_step_eq_first_high_add_other_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalOneStepError n q U b h K C T P P₀.live.test.target star=
      chi*nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b C star 0) P+
      nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C T P P₀.live.test.target star := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_hf_monotone hu hv huv)) as ho
  apply native_original_one_step_eq_first_high_add_other hP hi hs ho
  · intro j i
    cases i <;> exact NNReal.coe_nonneg _
  · intro i
    cases i
    · exact hbm
    · exact hhm
  · exact fun j=>NNReal.coe_nonneg _
  · exact fun j=>NNReal.coe_nonneg _
  · exact native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  · exact hbm
  · exact hhm
  · exact native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualOriginalFourPairContrast_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalFreshPairMoment n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalFreshPairMoment n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def nativeActualOriginalFourSourceErrorContrast_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalOneStepError n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOneStepError n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def nativeActualOriginalFourFrozenChildCorrection_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤ as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let children:=nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGBranches
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) st
  (children.map (fun Q=>nativeActualMinimumFourStateResponse_high_only M U W Q.freeze)).sum

theorem native_actual_original_four_resource_defect_decomposition_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourResourceDefect_high_only M U st=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)*nativeActualOriginalFourPairContrast_high_only M U st-
        nativeActualOriginalFourSourceErrorContrast_high_only M U st := by
  unfold nativeActualOriginalFourResourceDefect_high_only nativeOriginalPairRecursionDefect
    nativeActualOriginalFourPairContrast_high_only nativeActualOriginalFourSourceErrorContrast_high_only
  dsimp only
  ring

theorem native_actual_original_four_recursion_error_decomposition_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤ as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourRecursionError_high_only M hs hU W st=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        ((W⁻¹)^st.generation*nativeActualOriginalFourPairContrast_high_only M U st)-
      (1/(chi*K star))*((W⁻¹)^st.generation*nativeActualOriginalFourSourceErrorContrast_high_only M U st)-
      nativeActualOriginalFourFrozenChildCorrection_high_only M hs hU W st := by
  unfold nativeActualOriginalFourRecursionError_high_only
  rw [native_actual_original_four_resource_defect_decomposition_high_only]
  dsimp only
  unfold nativeActualOriginalFourFrozenChildCorrection_high_only nativeActualMinimumFourStateResponse_high_only
  dsimp only
  ring

theorem actual_minimum_four_denominator_bounds_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤ as.length)
    (hstarK : cK*W≤ nativeContinuumMixedClock n M.bf M.hf as star) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    0<chi*K star ∧ chi≤1 ∧ Real.exp (-4*Temp)*cK*W≤ chi*K star := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterm : K as.length≤ Temp:=
    (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans (M.inherited_total_clock_le htotal 1 (by norm_num))
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp [relocatedClock,show 0<U by omega])
    (B:=Temp) (by simpa [relocatedClock,not_lt.mpr hU] using hterm)
  have hchi:=(Real.exp_pos (-4*Temp)).trans_le HH.1
  have hp : 0<K star:=(mul_pos hcK hW).trans_le hstarK
  refine ⟨mul_pos hchi hp,HH.2,?_⟩
  simpa only [mul_assoc] using mul_le_mul HH.1 hstarK (mul_pos hcK hW).le hchi.le

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

def nativeActualOriginalFourOtherSourceErrorContrast_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

theorem actual_minimum_four_source_error_eq_first_high_add_other_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) :
    nativeActualOriginalFourSourceErrorContrast_high_only M U st=
      nativeActualOriginalFourFirstHighContrast_high_only M U st+
      nativeActualOriginalFourOtherSourceErrorContrast_high_only M U st := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_minimum_one_step_eq_first_high_add_other_high_only M hP hi hs ho Pc
  have H1:=actual_minimum_one_step_eq_first_high_add_other_high_only M hP.retarget hi hs ho
    (fun σ=>Pc (g.restRestrict σ))
  change nativeActualOriginalOneStepError n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star =
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      nativeGammaProjectedFirstHighDisplacement g.tree g.mark star U q b h K
        (restCenteredFixedForkKernel n b C star 0) (fun σ=>Pc (g.restRestrict σ))+
    nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star at H1
  unfold nativeActualOriginalFourSourceErrorContrast_high_only nativeActualOriginalFourFirstHighContrast_high_only
    nativeActualOriginalFourOtherSourceErrorContrast_high_only
  dsimp only at H0 H1 ⊢
  rw [H0,H1]
  ring

theorem actual_minimum_four_recursion_error_first_high_decomposition_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (hU : U≤ as.length) (W : ℝ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourRecursionError_high_only M hs hU W st=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        ((W⁻¹)^st.generation*nativeActualOriginalFourPairContrast_high_only M U st)+
      nativeActualOriginalFourFirstHighError_high_only M U W st-
      (1/(chi*K star))*((W⁻¹)^st.generation*nativeActualOriginalFourOtherSourceErrorContrast_high_only M U st)-
      nativeActualOriginalFourFrozenChildCorrection_high_only M hs hU W st := by
  rw [native_actual_original_four_recursion_error_decomposition_high_only,
    actual_minimum_four_source_error_eq_first_high_add_other_high_only M st hP hi hs ho]
  unfold nativeActualOriginalFourFirstHighError_high_only
  dsimp only
  ring

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualFourPairSum_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourPairContrast_high_only M U Q)).sum

def nativeActualFourFrozenChildSum_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (nativeActualOriginalFourFrozenChildCorrection_high_only M hs hU W)).sum

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualFourOtherSourceErrorSum_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherSourceErrorContrast_high_only M U Q)).sum

def nativeActualFourFirstHighErrorSum_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (nativeActualOriginalFourFirstHighError_high_only M U W)).sum

theorem actual_minimum_four_recursion_error_sum_first_high_decomposition_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (hU : U ≤ as.length) (W : ℝ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    (xs.map (nativeActualOriginalFourRecursionError_high_only M hs hU W)).sum=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        nativeActualFourPairSum_high_only M U W xs+
      nativeActualFourFirstHighErrorSum_high_only M U W xs-
      (1/(chi*K star))*nativeActualFourOtherSourceErrorSum_high_only M U W xs-
        nativeActualFourFrozenChildSum_high_only M hs hU W xs := by
  dsimp only
  induction xs with
  | nil=>simp [nativeActualFourPairSum_high_only,nativeActualFourFirstHighErrorSum_high_only,
      nativeActualFourOtherSourceErrorSum_high_only,nativeActualFourFrozenChildSum_high_only]
  | cons Q xs ih=>
    have HQ:=hxs Q (by simp)
    have HT : ∀R∈xs,NativeActualResourceGenerated i star U seed R.generation R.tree R.term:=by
      intro R hR;exact hxs R (List.mem_cons_of_mem Q hR)
    simp only [List.map_cons,List.sum_cons]
    rw [actual_minimum_four_recursion_error_first_high_decomposition_high_only M Q HQ hi hs ho hU W,ih HT]
    simp only [nativeActualFourPairSum_high_only,nativeActualFourFirstHighErrorSum_high_only,
      nativeActualFourOtherSourceErrorSum_high_only,nativeActualFourFrozenChildSum_high_only,List.map_cons,List.sum_cons]
    ring

theorem actual_minimum_four_recursion_error_sum_first_high_abs_le_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK Bpair Bother Bfirst Bfrozen : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (Hpair : |nativeActualFourPairSum_high_only M U W xs| ≤ Bpair)
    (Hother : |nativeActualFourOtherSourceErrorSum_high_only M U W xs| ≤ Bother)
    (Hfirst : |nativeActualFourFirstHighErrorSum_high_only M U W xs| ≤ Bfirst)
    (Hfrozen : |nativeActualFourFrozenChildSum_high_only M hs hU W xs| ≤ Bfrozen) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (nativeActualOriginalFourRecursionError_high_only M hs hU W)).sum| ≤
      (|1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair+Bother)/
        (Real.exp (-4*Temp)*cK*W)+Bfrozen+Bfirst := by
  dsimp only
  rw [actual_minimum_four_recursion_error_sum_first_high_decomposition_high_only M xs hxs hi hs ho hU W]
  obtain ⟨_,_,hden⟩:=actual_minimum_four_denominator_bounds_high_only M htotal hW hcK ho hs hU hstarK
  have H:=four_collective_source_envelope
    (J:=1-(M.bf (partitionPoint 0 as star):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n M.bf M.hf as)))).H 0 0^2)
    (by positivity) hden Hpair Hother Hfrozen
  have HE (a b c d : ℝ) : a+b-c-d=(a-c-d)+b:=by ring
  rw [HE]
  exact (abs_add_le _ _).trans (add_le_add H Hfirst)

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

theorem actual_minimum_constant_joint_source_abs_le_of_four_budgets_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK terminal : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤ as.length)
    (hstarK : cK*W≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (Bpair Bother Bfirst Bfrozen : ℕ→ℝ)
    (Hpair : ∀j<depth,|nativeActualFourPairSum_high_only M U W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
        (nativeActualConstantSourceChildren_high_only M as star U hs hU))|≤ Bpair j)
    (Hother : ∀j<depth,|nativeActualFourOtherSourceErrorSum_high_only M U W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
        (nativeActualConstantSourceChildren_high_only M as star U hs hU))|≤ Bother j)
    (Hfirst : ∀j<depth,|nativeActualFourFirstHighErrorSum_high_only M U W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
        (nativeActualConstantSourceChildren_high_only M as star U hs hU))|≤ Bfirst j)
    (Hfrozen : ∀j<depth,|nativeActualFourFrozenChildSum_high_only M hs hU W
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W j
        (nativeActualConstantSourceChildren_high_only M as star U hs hU))|≤ Bfrozen j)
    (Hterminal : |((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth
      (nativeActualConstantSourceChildren_high_only M as star U hs hU)).map
        (nativeActualMinimumFourStateResponse_high_only M U W)).sum|≤ terminal) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualMinimumConstantJointSource_high_only M as star U|≤
      (M.bf (partitionPoint 0 as star):ℝ)*W*
        (((List.range depth).map (fun j=>
          (|1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair j+Bother j)/
            (Real.exp (-4*Temp)*cK*W)+Bfrozen j+Bfirst j)).sum+terminal)+
      |nativeActualConstantSourceFrozenCorrection_high_only M as star U hs hU W| := by
  dsimp only
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  have Hvalid : ∀Q∈children,NativeActualResourceGenerated 0 star U [] Q.generation Q.tree Q.term:=
    fun Q hQ=>nativeActualConstantSourceChildren_valid_high_only M hs hU Q hQ
  have Hlevel j (hj : j<depth):=
    actual_minimum_four_recursion_error_sum_first_high_abs_le_high_only M htotal hW hcK ho
      (Nat.zero_le star) hs hU hstarK
      (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)
      (nativeActualFourCenteredForest_valid _ hs (hs.le.trans hU) _ j children Hvalid)
      (Hpair j hj) (Hother j hj) (Hfirst j hj) (Hfrozen j hj)
  have Hres : |nativeActualMinimumFourResidualSum_high_only M hs hU W depth children|≤
      ((List.range depth).map (fun j=>
        (|1-(M.bf (partitionPoint 0 as star):ℝ)*
          (scalarTerminal.schedule (scalarBoundaryClocks as
            (relocatedClock U 0 (nativeContinuumMixedClock n M.bf M.hf as)))).H 0 0^2| *
          Bpair j+Bother j)/(Real.exp (-4*Temp)*cK*W)+Bfrozen j+Bfirst j)).sum := by
    unfold nativeActualMinimumFourResidualSum_high_only
    apply (native_abs_sum_map_le _ _).trans
    apply List.sum_le_sum
    intro j hj
    exact Hlevel j (List.mem_range.mp hj)
  rw [actual_minimum_constant_joint_source_eq_finite_four_iteration_high_only M as ho W hW.ne'
    star U hs hU ((mul_pos hcK hW).trans_le hstarK) depth]
  apply (abs_add_le _ _).trans
  apply add_le_add _ le_rfl
  rw [abs_mul,abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) hW.le)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (NNReal.coe_nonneg _) hW.le)
  exact (abs_add_le _ _).trans (add_le_add Hres Hterminal)

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem nativeOriginalClockGBranchBeta_bound_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    |nativeOriginalClockGBranchBeta U K (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) st tag| ≤ Temp := by
  let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
  obtain ⟨hlo,hhi⟩:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hU K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  have hchi : 0 ≤ chi:=(Real.exp_pos _).le.trans hlo
  have hb : (M.bf (partitionPoint 0 as star):ℝ) ≤ Temp := by
    have H:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho star)
    linarith [(M.hf (partitionPoint 0 as star)).coe_nonneg]
  unfold nativeOriginalClockGBranchBeta
  change |(if tag=0 then chi else 1)*(M.bf (partitionPoint 0 as star):ℝ)| ≤ Temp
  split_ifs with ht
  · rw [abs_of_nonneg (mul_nonneg hchi (NNReal.coe_nonneg _))]
    exact (mul_le_mul_of_nonneg_right hhi (NNReal.coe_nonneg _)).trans (by simpa using hb)
  · simpa only [one_mul,abs_of_nonneg (NNReal.coe_nonneg _)] using hb

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem actual_continuum_G_weight_bound_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp W cK : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    (hW : 0<W) (hcK : 0<cK)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i star U : ℕ} (hs : star<U) (hU : U≤ as.length)
    (hstarK : cK*W≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*cK) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterminal : K as.length≤ Temp :=
    (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans (M.inherited_total_clock_le htotal 1 (by norm_num))
  have hbeta:=nativeOriginalClockGBranchBeta_bound_high_only M htotal ho hs hU K hK hKm st tag
  have H:=native_full_gamma_recursion_coefficient_bound n st.tree ho 0 ho U (by omega)
    hU K hKm hK hterminal st.term.live.test.target hW hcK hstarK hbeta
  dsimp only at H ⊢
  unfold nativeOriginalClockParentWeight
  dsimp only
  rw [abs_mul,abs_of_pos hW]
  apply (mul_le_mul_of_nonneg_left H hW.le).trans
  apply le_of_eq
  field_simp

theorem actual_retained_continuum_G_weight_bound_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp W cK : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    (hW : 0<W) (hcK : 0<cK)
    (u : PositiveMass) (hclock : cK*W≤ actualMixedClock (n+1) M.bf M.hf u.val)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hu : u∈as)
    {i U : ℕ} (hs : retainedMassPrefixIndex u.val as<U) (hU : U≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex u.val as))
    (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*cK) := by
  apply actual_continuum_G_weight_bound_of_total_clock_high_only M htotal hW hcK as ho hs hU _ st tag
  rw [native_continuum_mixed_clock_retained_eq n M.bf M.hf as ho u hu]
  exact hclock

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem actual_continuum_four_G_weight_bound_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp W cK : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    (hW : 0<W) (hcK : 0<cK)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i star U : ℕ} (hs : star<U) (hU : U≤ as.length)
    (hstarK : cK*W≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*cK) := by
  apply nativeOriginalClockParentWeight_four_beta_abs_le
  intro j
  exact actual_continuum_G_weight_bound_of_total_clock_high_only M htotal hW hcK as ho hs hU hstarK st j

theorem actual_retained_continuum_four_G_weight_bound_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp W cK : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    (hW : 0<W) (hcK : 0<cK)
    (u : PositiveMass) (hclock : cK*W≤ actualMixedClock (n+1) M.bf M.hf u.val)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hu : u∈as)
    {i U : ℕ} (hs : retainedMassPrefixIndex u.val as<U) (hU : U≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex u.val as))
    (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*cK) := by
  apply nativeOriginalClockParentWeight_four_beta_abs_le
  intro j
  exact actual_retained_continuum_G_weight_bound_of_total_clock_high_only M htotal hW hcK u hclock as ho hu hs hU st j

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity LaplaceWindowFormalization
set_option maxHeartbeats 14000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 16000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

theorem actual_minimum_four_state_forest_abs_le_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK B : ℝ} (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (st : NativeActualResourceState (Spin n×Bool) as i star)
    {r : ℕ} (hr : st.tree.leaves ≤ r)
    (F : NativeActualResourceState (Spin n×Bool) as i star→ℝ) (hB : 0 ≤ B)
    (hF : ∀Q∈nativeActualMinimumFourCenteredForest_high_only M hs hU W depth [st],
      |F Q| ≤ |Q.term.coefficient| *B) :
    |((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth [st]).map F).sum| ≤
      2*|st.term.coefficient| *
        nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
          (Temp/(Real.exp (-4*Temp)*cK)) 3 r depth*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  exact nativeActualFourCenteredForest_singleton_abs_le ho (nativeOriginalHighRowGamma U K)
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    (fun Q tag=>nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag))
    (C:=Temp/(Real.exp (-4*Temp)*cK)) (by positivity)
    (fun Q tag=>actual_continuum_four_G_weight_bound_of_total_clock_high_only M htotal hW hcK as ho
      hs hU hstarK Q tag) depth st hr F hB hF

theorem actual_minimum_four_initial_forest_abs_le_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK B : ℝ} (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (F : NativeActualResourceState (Spin n×Bool) as i star→ℝ) (hB : 0 ≤ B)
    (hF : ∀Q∈nativeActualMinimumFourCenteredForest_high_only M hs hU W depth
      [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))],
      |F Q| ≤ |Q.term.coefficient| *B) :
    |((nativeActualMinimumFourCenteredForest_high_only M hs hU W depth
      [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))]).map F).sum| ≤
        nativeActualFourForestCost Temp cK depth*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  have H:=nativeActualFourCenteredForest_singleton_abs_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    weight (C:=Temp/(Real.exp (-4*Temp)*cK)) (by positivity)
    (fun Q tag=>actual_continuum_four_G_weight_bound_of_total_clock_high_only M htotal hW hcK as ho
      hs hU hstarK Q tag) depth
    (nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU)))
    (nativeActualInitialState_leaves_le as i star 0 (hi.trans (hs.le.trans hU))) F hB hF
  simpa only [nativeActualMinimumFourCenteredForest_high_only,nativeActualFourForestCost,
    nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,mul_one] using H

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star : ℕ}

def nativeActualOriginalCenteredResourceFreshPair_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=cutFullVariance n qr U 1 1 b h K
  nativeActualOriginalFreshPairMoment n qr U b h K C st.tree
    (nativeOriginalCenteredRestTest n qr U b h K st.tree
      (nativeActualResourceRestValue st.term 0 qfull 0 C)) st.term.live.test.target star

theorem native_actual_original_four_pair_contrast_eq_retarget_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (ho : MassOrdered 0 as) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeActualOriginalFourPairContrast_high_only M U st=
      nativeActualOriginalCenteredResourceFreshPair_high_only M U st-
        (1/2:ℝ)*nativeActualOriginalCenteredResourceFreshPair_high_only M U st.retarget := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n qr U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n qr U 1 b h K
      (finitePhysicalMixedClock (n+1) as b h)
  unfold nativeActualOriginalFourPairContrast_high_only nativeActualOriginalCenteredResourceFreshPair_high_only
  dsimp only [NativeActualResourceState.retarget]
  change _=_-(1/2:ℝ)*nativeActualOriginalFreshPairMoment n qr U b h K _ _
    (nativeOriginalCenteredRestTest n qr U b h K _
      (nativeActualResourceRestValue (st.term.retarget 0) 0 (cutFullVariance n qr U 1 1 b h K) 0 _))
      (st.term.retarget 0).live.test.target star
  rw [HQ,native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n qr U b h K st.tree ho]
  rfl

theorem native_actual_original_four_pair_contrast_abs_le_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (ho : MassOrdered 0 as) (st : NativeActualResourceState (Spin n×Bool) as i star)
    (W B : ℝ)
    (Hparent : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair_high_only M U st| ≤ B)
    (Hretarget : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair_high_only M U st.retarget| ≤ B) :
    |(W⁻¹)^st.generation*nativeActualOriginalFourPairContrast_high_only M U st| ≤ (3/2:ℝ)*B := by
  rw [native_actual_original_four_pair_contrast_eq_retarget_high_only M U ho]
  have Heq : (W⁻¹)^st.generation*
      (nativeActualOriginalCenteredResourceFreshPair_high_only M U st-
        (1/2:ℝ)*nativeActualOriginalCenteredResourceFreshPair_high_only M U st.retarget)=
      (W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair_high_only M U st+
        (-(1/2:ℝ))*((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair_high_only M U st.retarget) := by ring
  rw [Heq]
  have H:=abs_add_le ((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair_high_only M U st)
    ((-(1/2:ℝ))*((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair_high_only M U st.retarget))
  have Hhalf : |(-(1/2:ℝ))*((W⁻¹)^st.generation*
      nativeActualOriginalCenteredResourceFreshPair_high_only M U st.retarget)|=
      (1/2:ℝ)*|(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair_high_only M U st.retarget| := by
    rw [abs_mul]
    norm_num
  rw [Hhalf] at H
  exact H.trans (by linarith [Hparent,Hretarget])

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem native_minimum_clock_high_g_atom_abs_le_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hTemp : 0≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (a c e f : T.Slot) (σ : T.Assignment) :
    |nativeMinimumClockHighGAtom_high_only M K T U a c e f σ|≤2*Temp := by
  have Htotal:=M.inherited_total_clock_le htotal _
    (partitionPoint_mem as ho (T.splitIndex e f))
  have Hbond : (M.bf (partitionPoint 0 as (T.splitIndex e f)):ℝ)≤ Temp := by
    linarith [(M.hf (partitionPoint 0 as (T.splitIndex e f))).coe_nonneg]
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  change |nativeOriginalHighGAtom T U K b
    (nativePhysicalResourceCenter n M.bf M.hf as) a c e f σ|≤_
  exact native_original_high_g_atom_abs_le T ho U K b
    (nativePhysicalResourceCenter n M.bf M.hf as) a c e f hTemp
    (by rw [abs_of_nonneg (NNReal.coe_nonneg _)];exact Hbond)
    (native_physical_resource_center_abs_le_one n M.bf M.hf (M.bf_monotone)
      (M.hf_monotone) as ho _) σ

theorem native_minimum_clock_high_g_atom_second_moment_le_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hTemp : 0≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (a c e f : T.Slot) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(nativeMinimumClockHighGAtom_high_only M K T U a c e f σ)^2) x≤(2*Temp)^2 := by
  have hw:=T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x
  unfold ClockTree.disorderExpect
  calc
    _≤∑σ : T.Assignment,T.disorderWeight (fullWeight n) (fullFeature n) v q σ x*(2*Temp)^2 := by
      apply Finset.sum_le_sum
      intro σ _
      have H:=native_minimum_clock_high_g_atom_abs_le_of_total_clock_high_only M K hTemp htotal T ho U a c e f σ
      have Hsq:=(sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*Temp)).mpr H
      rw [sq_abs] at Hsq
      exact mul_le_mul_of_nonneg_left Hsq (hw.1 σ)
    _=(2*Temp)^2 := by rw [←Finset.sum_mul,hw.2,one_mul]

theorem NativeOriginalGMarkedWord.actual_clock_second_moment_le_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hTemp : 0≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (ho : MassOrdered 0 as) (U : ℕ) (a : T.Slot)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) :
    g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(g.clockAtom_high_only M K U a σ)^2) x≤(2*Temp)^2 :=
  native_minimum_clock_high_g_atom_second_moment_le_of_total_clock_high_only M K hTemp htotal g.tree ho U _ _ _ _ v q x

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem NativeOriginalGMarkedWord.actual_clock_frozen_normalized_resource_pairing_abs_le_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hTemp : 0≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (g : NativeOriginalGMarkedWord T)
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (a : T.Slot)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (y : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm₀ : P.PairMomentBudget (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) y A x W ε) :
    |g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ*g.clockAtom_high_only M K U a σ)) y|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp) := by
  exact hP.normalized_frozen_transported_terminal_pairing_abs_le (g.liftResource P)
    (g.liftResource_resources P) (g.liftResource_coefficient P)
    (fullWeight_pos n) (fullFeature n) ho v₀ q₀ x₀ v q
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) y A x W ε hA hx hW hε hi hstar
    (g.liftResource_pairMomentBudget P v₀ q₀ _ _ x₀ A x W ε hm₀)
    (g.liftResource_pairMomentBudget P v q _ _ y A x W ε hm).1
    (g.clockAtom_high_only M K U a) (2*Temp) (by positivity)
    (g.actual_clock_second_moment_le_of_total_clock_high_only M K hTemp htotal ho U a v q y)

theorem nativeActualClockFrozenResourceResponse_abs_le_of_total_clock_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hTemp : 0≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (r : ℕ) (hr : T.leaves≤ r)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (y : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm₀ : P.PairMomentBudget (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) y A x W ε) :
    |nativeOriginalClockResourceResponse P U k K
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (nativePhysicalResourceCenter n M.bf M.hf as) v₀ q₀ x₀ v q y W|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp)*
        nativeActualGInsertionCost r := by
  have hscale : 0≤ nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  rw [←nativeActualClockFrozenResourceGInsertion_eq_clock_response_high_only M K P ho]
  unfold nativeActualClockFrozenResourceGInsertion_high_only
  apply (nativeActualWeightedTerminalSum_abs_le _ _ _ (by
    intro g hg
    exact g.actual_clock_frozen_normalized_resource_pairing_abs_le_of_total_clock_high_only M K hTemp htotal hP ho
      P.live.test.target v₀ q₀ x₀ v q y A x W ε hA hx hW hε hi hstar hm₀ hm)).trans
  have HV:=mul_le_mul_of_nonneg_right (nativeOriginalGMarkedWords_variation_le T ho r hr)
    (show 0≤|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp) by positivity)
  simpa only [nativeActualGInsertionCost,mul_comm] using HV

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization ActualHighOnlyOverlapMinimum

theorem eventually_actual_inherited_original_clock_longitudinal_mean_saving_square_high_only
    (r : ℕ) (Bclock Temp : ℝ) (hTemp : 0 ≤ Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp) → M.h 0=0 →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →
      ∀ᶠk : ℕ in atTop,
        let as := finiteCutMasses us k
        let b := fun j => (M.bf (partitionPoint 0 as j):ℝ)
        let h := fun j => (M.hf (partitionPoint 0 as j):ℝ)
        ∀(K : ℕ→ℝ) (T : ClockTree (Spin n×Bool) as) (U : ℕ) (a : T.Slot),T.leaves ≤ r →
          |nativeOriginalLongitudinalMean T U K
            b h (nativePhysicalResourceCenter n M.bf M.hf as) a| ≤
              ((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2 := by
  let A := 8*(r:ℝ)*(r+1)*(r+2)*Temp
  have hA : 0 ≤ A := by dsimp [A];positivity
  have Hrate := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=(2:ℝ)/3+2*m) (s:=(1:ℝ)/3)
      (by linarith) 0 (2*A*C0^2))
  filter_upwards [Hrate] with n hn
  intro M htotal hroot0 us hus
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := M.bf_monotone
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := M.hf_monotone
  have hroot := M.inherited_zero_root_field hroot0
  let Cphys := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n+1) M.bf M.hf)
  have Hmesh := (uniformMasses_mesh_tendsto.mul_const Cphys).eventually
    (gt_mem_nhds (show (0:ℝ)*Cphys<1/(n+1:ℕ) by simpa only [zero_mul] using
      (show (0:ℝ)<1/(n+1:ℕ) by positivity)))
  filter_upwards [Hmesh] with k hk
  dsimp only
  let as := finiteCutMasses us k
  let b := fun j => (M.bf (partitionPoint 0 as j):ℝ)
  let h := fun j => (M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as := finiteCutMasses_ordered us hus k
  have Hcenter (j : ℕ) (hj : j ≤ as.length) :
      |finitePhysicalMean (n+1) as b h j-nativePhysicalResourceCenter n M.bf M.hf as j| ≤
        1/(n+1:ℕ) := by
    exact (finite_physical_mean_uniform_continuum_error n M.bf M.hf hbf hhf hroot as ho
      (finiteCutMasses_end us hus k) (by positivity) (finiteCutMasses_mesh us hus k) j hj).trans hk.le
  have Hbond (j : ℕ) (_hj : j ≤ as.length) : |b j| ≤ Temp := by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    have Htotal:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho j)
    linarith [(M.hf (partitionPoint 0 as j)).coe_nonneg]
  have Hnum := M.actual_terminal_power_over_scale hC0 (show 0 ≤ 2*A by positivity)
    (gamma:=1) 1
  simp only [Nat.cast_one,mul_one] at Hnum
  rw [show (1:ℝ)-(1:ℝ)/3+2*m=(2:ℝ)/3+2*m by ring] at Hnum
  have Hsave : 2*A/((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos M.hxs)).mp
    have Hnorm : (2*A/((n+1:ℕ):ℝ))/M.xs^2 ≤
        (2*A*C0^2)*((n+1:ℕ):ℝ)^(-((2:ℝ)/3+2*m)) := by
      simpa only [ActualHighOnlyComparisonData.N,Real.rpow_neg_one,div_eq_mul_inv,mul_assoc] using Hnum
    exact Hnorm.trans (by simpa only [pow_zero,mul_one,neg_div] using hn)
  intro K T U a hleaves
  have HM := native_original_longitudinal_mean_abs_le T ho U K
    b h (nativePhysicalResourceCenter n M.bf M.hf as) a hTemp (by positivity) Hbond Hcenter
  have Hpoly : 8*(T.leaves:ℝ)*(T.leaves+1)*(T.leaves+2)*Temp ≤ A := by
    dsimp only [A]
    have Hle : (T.leaves:ℝ) ≤ r := by exact_mod_cast hleaves
    gcongr
  apply HM.trans
  apply le_trans _ Hsave
  have HH := mul_le_mul_of_nonneg_right Hpoly
    (show (0:ℝ) ≤ 1/(n+1:ℕ)+1/(n+1:ℕ) by positivity)
  convert HH using 1
  ring

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Filter Set LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem eventually_actual_inherited_clock_frozen_resource_correction_high_only
    (r : ℕ) (Bclock Temp : ℝ) (hTemp : 0≤ Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)→M.h 0=0→
      ∀us : List PositiveMass,(∀u∈us,u.val≤1)→∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
        ∀(K : ℕ→ℝ) (i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P→T.leaves≤ r→
        ∀A x W ε : ℝ,0<A→0<x→0<W→0<ε→i ≤ star→star<as.length→
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as b h 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W ε→
        |nativeOriginalClockResourceResponse P.freeze U k K b
          (nativePhysicalResourceCenter n M.bf M.hf as)
          0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
          0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 W|≤
          (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k)*
            (((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2) := by
  filter_upwards [eventually_actual_inherited_original_clock_longitudinal_mean_saving_square_high_only r Bclock Temp
    hTemp hm hC0] with n hn
  intro M htotal hroot us hus
  filter_upwards [hn M htotal hroot us hus] with j hj
  dsimp only at hj ⊢
  intro K i star U k seed T P hP hT A x W ε hA hx hW hε hi hstar hbudget
  exact nativeOriginalClockResourceResponse_freeze_abs_le hP (finiteCutMasses_ordered us hus j)
    K _ _ _ A x W ε _ hA hx hW hε hi hstar hbudget (hj K T U P.live.test.target hT)

end OAI.SKFluctuations.Cavity

set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem exists_actual_terminal_depth_high_only
    (hm : 0 < m) (hC0 : 0<C0) {gamma : ℝ} (hgamma : 0<gamma) :
    ∃k : ℕ,0<k ∧ (1:ℝ)/3<(k:ℝ)*gamma ∧
      ∃saving : ℝ,0 < saving ∧ ∀C : ℝ,0≤ C →
        ∀ᶠn : ℕ in atTop,
          ∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
            C*a.data.N^(-gamma*(k:ℝ))≤ a.data.N^(-saving)*a.xs^2 := by
  obtain ⟨k,hk⟩:=exists_nat_gt (((1:ℝ)/3)/gamma)
  have hk0 : 0<k := by
    have H : (0:ℝ)<k := (by positivity : 0<((1:ℝ)/3)/gamma).trans hk
    exact_mod_cast H
  have hkg : (1:ℝ)/3<(k:ℝ)*gamma := (div_lt_iff₀ hgamma).mp hk
  let q:=gamma*(k:ℝ)-(1:ℝ)/3+2*m
  have hq : 0<q := by dsimp [q];nlinarith
  refine ⟨k,hk0,hkg,q/2,by positivity,?_⟩
  intro C hC
  have Hrate:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=q) (s:=q/2) (by linarith) 0 (C*C0^2))
  filter_upwards [Hrate] with n hn
  intro a
  apply (div_le_iff₀ (sq_pos_of_pos a.hxs)).mp
  apply (a.actual_terminal_power_over_scale hC0 hC k).trans
  simpa only [ActualHighOnlyComparisonData.N,pow_zero,mul_one,q] using hn

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighOnlyOverlapMinimum
open Hierarchy Hierarchy.ClockTree

theorem exists_actual_mixed_terminal_depth_high_only
    {m delta cl cu Az C0 Ct D Bclock gamma : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hgamma : 0 < gamma) :
    ∃depth : ℕ,0 < depth ∧ ∃saving : ℝ,0 < saving ∧
      ∀C : ℝ,0≤ C→∀ᶠn : ℕ in atTop,
        ∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        ∀ops : List NativeActualExpansionOp,depth≤ nativeActualExpansionMarkedCount ops→
          C*(a.data.N^(-gamma))^(nativeActualExpansionMarkedCount ops)≤
            a.data.N^(-saving)*a.xs^2 := by
  obtain ⟨depth,hd,_,saving,hs,H⟩:=exists_actual_terminal_depth_high_only
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hgamma
  refine ⟨depth,hd,saving,hs,?_⟩
  intro C hC
  filter_upwards [H C hC] with n hn
  intro a ops hops
  apply le_trans _ (hn a)
  apply mul_le_mul_of_nonneg_left _ hC
  rw [←Real.rpow_mul_natCast a.data.hN.le]
  apply Real.rpow_le_rpow_of_exponent_le
  · change (1:ℝ)≤(n+1:ℕ)
    exact_mod_cast (show 1≤ n+1 by omega)
  · have HO : (depth:ℝ)≤ nativeActualExpansionMarkedCount ops:=by exact_mod_cast hops
    nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighOnlyOverlapMinimum
