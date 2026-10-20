module

public import ComparisonSignedCavityActualFourResourceIteration
public import ComparisonSignedCavityActualFourGContinuumWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_original_longitudinal_eq_two_fresh_subtraction
    {n : ℕ}
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
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
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hbf hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hhf hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n bf hf
    hbf hhf as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n bf hf
    hbf hhf as ho
  have hKC : ∀j,K j=h j+b j*C j:=native_continuum_mixed_clock_eq_original_center n bf hf
    hbf hhf as ho
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

theorem actual_general_centered_resource_four_source
    {n : ℕ}
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
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
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
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
  have HE:=actual_general_original_longitudinal_eq_two_fresh_subtraction bf hf hbf hhf hP hi hs ho P
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

def actualGeneralFourResourceDefect
    {n : ℕ}
    (bf hf : ℝ → ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

private theorem actual_general_four_source_normalize (a d L D G : ℝ) (hd : d≠0)
    (H : d*L=D+G) : a*L=a/d*D+a/d*G := by
  calc
    a*L=(a/d)*(d*L) := by field_simp
    _=(a/d)*(D+G) := by rw [H]
    _=a/d*D+a/d*G := by ring

theorem actual_general_centered_resource_four_recursion
    {n : ℕ}
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W≠0)
    (hstarK : 0 < nativeContinuumMixedClock n bf hf as star) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let F:=nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W
    let G:=nativeOriginalClockFourGStepResponse hs hP.highCut_le_length K b C 0 qfull 0 0 qfull 0 W
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    F st+F st.freeze=(W⁻¹)^st.generation/(chi*K star)*actualGeneralFourResourceDefect bf hf U st+
      G st+G st.freeze := by
  dsimp only
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n bf hf hbf
    hhf as ho
  have hKm:=native_continuum_mixed_clock_monotone n bf hf hbf
    hhf as ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hchi : 0 < chi:=(Real.exp_pos _).trans_le Hchi.1
  have hd : chi*K star≠0:=(mul_pos hchi hstarK).ne'
  have Hsrc:=actual_general_centered_resource_four_source bf hf hbf hhf st hP hi hs ho 0 qfull 0
  dsimp only at Hsrc
  have Hleft:=nativeOriginalClockStateResponse_centered_value ho U K b C 0 qfull 0 W st
  have Hright:=nativeOriginalClockFourGStepResponse_centered_value ho hs hP.highCut_le_length
    K b C 0 qfull 0 W hW st
  dsimp only at Hleft Hright
  rw [←Hleft,add_assoc,←Hright]
  apply actual_general_four_source_normalize _ _ _ _ _ hd
  exact Hsrc

def actualGeneralFourRecursionError
    {n : ℕ}
    (bf hf : ℝ → ℝ≥0)
    {as : List PositiveMass} {i star U : ℕ}
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let children:=nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGBranches
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) st
  (W⁻¹)^st.generation/(chi*K star)*actualGeneralFourResourceDefect bf hf U st-
    (children.map (fun Q=>nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W Q.freeze)).sum

theorem actual_general_centered_four_resource_level
    {n : ℕ}
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    {as : List PositiveMass} {i star U : ℕ}
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W≠0)
    (hstarK : 0 < nativeContinuumMixedClock n bf hf as star) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let F : NativeActualResourceState (Spin n×Bool) as i star→ℝ :=
    nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W
    let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)
    let zs:=xs.flatMap (fun Q=>[Q,Q.freeze])
    (zs.map F).sum=
      (zs.map (actualGeneralFourRecursionError bf hf hs hU W)).sum+
      ((zs.flatMap (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight)).map F).sum := by
  dsimp only
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
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
    (W⁻¹)^Q.generation/(chi*K star)*actualGeneralFourResourceDefect bf hf U Q
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
    exact actual_general_centered_resource_four_recursion bf hf hbf hhf Q (Hzvalid Q hQ) hi hs ho W hW hstarK
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

section Iteration
variable {n : ℕ} {as : List PositiveMass} {i star U : ℕ}

def actualGeneralFourCenteredForest
    (bf hf : ℝ → ℝ≥0)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ) (depth : ℕ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    List (NativeActualResourceState (Spin n×Bool) as i star) :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  nativeActualFourCenteredForest (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) depth xs

def actualGeneralFourStateResponse
    (bf hf : ℝ → ℝ≥0)
    (U : ℕ) (W : ℝ) (Q : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W Q

def actualGeneralFourResidualSum
    (bf hf : ℝ → ℝ≥0)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ) (depth : ℕ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  ((List.range depth).map (fun j=>
    ((actualGeneralFourCenteredForest bf hf hs hU W j xs).map
      (actualGeneralFourRecursionError bf hf hs hU W)).sum)).sum

theorem actual_general_four_resource_forest_level
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W ≠ 0)
    (hstarK : 0 < nativeContinuumMixedClock n bf hf as star) (depth : ℕ) :
    ((actualGeneralFourCenteredForest bf hf hs hU W depth xs).map
      (actualGeneralFourStateResponse bf hf U W)).sum=
    ((actualGeneralFourCenteredForest bf hf hs hU W depth xs).map
      (actualGeneralFourRecursionError bf hf hs hU W)).sum+
    ((actualGeneralFourCenteredForest bf hf hs hU W (depth+1) xs).map
      (actualGeneralFourStateResponse bf hf U W)).sum := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
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
  have H:=actual_general_centered_four_resource_level bf hf hbf hhf ys Hy hi hs hU ho W hW hstarK
  change ((ys.flatMap (fun Q=>[Q,Q.freeze])).map
      (actualGeneralFourStateResponse bf hf U W)).sum=
    ((ys.flatMap (fun Q=>[Q,Q.freeze])).map
      (actualGeneralFourRecursionError bf hf hs hU W)).sum+
    (((ys.flatMap (fun Q=>[Q,Q.freeze])).flatMap
      (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight)).map
      (actualGeneralFourStateResponse bf hf U W)).sum at H
  rw [←hys] at H
  exact H

theorem actual_general_four_resource_finite_iteration
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W ≠ 0)
    (hstarK : 0 < nativeContinuumMixedClock n bf hf as star) (depth : ℕ) :
    ((xs.flatMap (fun Q=>[Q,Q.freeze])).map
      (actualGeneralFourStateResponse bf hf U W)).sum=
    actualGeneralFourResidualSum bf hf hs hU W depth xs+
    ((actualGeneralFourCenteredForest bf hf hs hU W depth xs).map
      (actualGeneralFourStateResponse bf hf U W)).sum := by
  induction depth with
  | zero=>simp [actualGeneralFourResidualSum,actualGeneralFourCenteredForest,
      nativeActualFourCenteredForest]
  | succ depth ih=>
    have H:=actual_general_four_resource_forest_level bf hf hbf hhf xs hxs hi hs hU ho W hW hstarK depth
    rw [H] at ih
    simpa only [actualGeneralFourResidualSum,List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,add_assoc] using ih

end Iteration

section Numerics
variable {n : ℕ} {as : List PositiveMass} {i star U : ℕ}

def actualGeneralFourPairContrast
    (bf hf : ℝ → ℝ≥0) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalFreshPairMoment n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalFreshPairMoment n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def actualGeneralFourSourceErrorContrast
    (bf hf : ℝ → ℝ≥0) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalOneStepError n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOneStepError n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def actualGeneralFourFrozenChildCorrection
    (bf hf : ℝ → ℝ≥0)
    (hs : star<U) (hU : U≤as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let children:=nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGBranches
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) st
  (children.map (fun Q=>actualGeneralFourStateResponse bf hf U W Q.freeze)).sum

theorem actual_general_four_resource_defect_decomposition
    (bf hf : ℝ → ℝ≥0) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    actualGeneralFourResourceDefect bf hf U st=
      (1-(bf (partitionPoint 0 as star):ℝ)*chi^2)*actualGeneralFourPairContrast bf hf U st-
        actualGeneralFourSourceErrorContrast bf hf U st := by
  unfold actualGeneralFourResourceDefect nativeOriginalPairRecursionDefect
    actualGeneralFourPairContrast actualGeneralFourSourceErrorContrast
  dsimp only
  ring

theorem actual_general_four_recursion_error_decomposition
    (bf hf : ℝ → ℝ≥0)
    (hs : star<U) (hU : U≤as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    actualGeneralFourRecursionError bf hf hs hU W st=
      (1-(bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        ((W⁻¹)^st.generation*actualGeneralFourPairContrast bf hf U st)-
      (1/(chi*K star))*((W⁻¹)^st.generation*actualGeneralFourSourceErrorContrast bf hf U st)-
      actualGeneralFourFrozenChildCorrection bf hf hs hU W st := by
  unfold actualGeneralFourRecursionError
  rw [actual_general_four_resource_defect_decomposition]
  dsimp only
  unfold actualGeneralFourFrozenChildCorrection actualGeneralFourStateResponse
  dsimp only
  ring

theorem actual_general_four_denominator_bounds
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n bf hf as star) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    0<chi*K star ∧ chi≤1 ∧ Real.exp (-4*Temp)*cK*W≤chi*K star := by
  dsimp only
  let K:=nativeContinuumMixedClock n bf hf as
  have hKm:=native_continuum_mixed_clock_monotone n bf hf hbf
    hhf as ho
  have hK0:=native_continuum_mixed_clock_nonneg n bf hf hbf
    hhf as ho
  have hterm : K as.length≤Temp:=
    (native_continuum_mixed_clock_terminal_le n bf hf hbf
      hhf as ho).trans (htotal 1 (by norm_num))
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp [relocatedClock,show 0<U by omega])
    (B:=Temp) (by simpa [relocatedClock,not_lt.mpr hU] using hterm)
  have hchi:=(Real.exp_pos (-4*Temp)).trans_le HH.1
  have hp : 0<K star:=(mul_pos hcK hW).trans_le hstarK
  refine ⟨mul_pos hchi hp,HH.2,?_⟩
  simpa only [mul_assoc] using mul_le_mul HH.1 hstarK (mul_pos hcK hW).le hchi.le

theorem actual_general_four_recursion_error_abs_le
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    {Temp W cK Bpair Bsource Bfrozen : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n bf hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (Hpair : |(W⁻¹)^st.generation*actualGeneralFourPairContrast bf hf U st|≤Bpair)
    (Hsource : |(W⁻¹)^st.generation*actualGeneralFourSourceErrorContrast bf hf U st|≤Bsource)
    (Hfrozen : |actualGeneralFourFrozenChildCorrection bf hf hs hU W st|≤Bfrozen) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |actualGeneralFourRecursionError bf hf hs hU W st|≤
      (|1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair+Bsource)/
        (Real.exp (-4*Temp)*cK*W)+Bfrozen := by
  dsimp only
  rw [actual_general_four_recursion_error_decomposition]
  obtain ⟨hd,_,hden⟩:=actual_general_four_denominator_bounds bf hf hbf hhf htotal hW hcK ho hs hU hstarK
  have hp:= (abs_nonneg _).trans Hpair
  have hs0:= (abs_nonneg _).trans Hsource
  have Hsub (a b : ℝ) : |a-b|≤|a|+|b| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  apply (Hsub _ _).trans
  apply (add_le_add (Hsub _ _) Hfrozen).trans
  simp only [abs_mul,abs_div,abs_of_pos hd,abs_one] at Hpair Hsource ⊢
  let defect:=1-(bf (partitionPoint 0 as star):ℝ)*
    (scalarTerminal.schedule (scalarBoundaryClocks as
      (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0^2
  have H1:=mul_le_mul_of_nonneg_left Hpair (div_nonneg (abs_nonneg defect) hd.le)
  have H2:=mul_le_mul_of_nonneg_left Hsource (div_nonneg zero_le_one hd.le)
  apply (add_le_add (add_le_add H1 H2) le_rfl).trans
  apply add_le_add _ le_rfl
  dsimp only [defect]
  calc
    _=(|1-(bf (partitionPoint 0 as star):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0^2| *Bpair+Bsource)/
      ((scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0*
          nativeContinuumMixedClock n bf hf as star) := by ring
    _≤_:=div_le_div_of_nonneg_left (by positivity) (by positivity) hden

theorem actual_general_four_recursion_error_abs_le_literal
    (bf hf : ℝ → ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0 : ℝ) 1))
    (hhf : MonotoneOn hf (Icc (0 : ℝ) 1))
    {Temp W cK : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n bf hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |actualGeneralFourRecursionError bf hf hs hU W st|≤
      (|1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *
          |(W⁻¹)^st.generation*actualGeneralFourPairContrast bf hf U st|+
        |(W⁻¹)^st.generation*actualGeneralFourSourceErrorContrast bf hf U st|)/
          (Real.exp (-4*Temp)*cK*W)+
        |actualGeneralFourFrozenChildCorrection bf hf hs hU W st| :=
  actual_general_four_recursion_error_abs_le bf hf hbf hhf htotal hW hcK ho hs hU
    hstarK st (le_refl _) (le_refl _) (le_refl _)

end Numerics
end OAI.SKFluctuations.Cavity
