module

public import ComparisonSignedCavityInheritedResourceGammaHighSecondWorking
public import ComparisonSignedCavityActualResourceGammaHighSecondProfileAlong
public import ComparisonActualHighOnlyPhysicalSourceProfiles
public import ComparisonActualHighOnlyFourReadoutPrimitives
public import ComparisonActualHighOnlyRawResourcePairBudget
public import ComparisonActualHighOnlyNearPairedGammaRows
public import ComparisonActualHighOnlyPairedFarGeneratedGammaRow

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 30000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem actual_minimum_inherited_rest_high_second_integral_L2_bound_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : ActualHighOnlySmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U rBound : ℕ) (hT : T.leaves ≤ rBound) (P : T.cavityLeft.Assignment→ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ))) (fun σ=>P σ^2) 0 ≤ C^2) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
    |nativeRestPayloadHighSecondIntegral n q U b h K T P| ≤
      nativeInheritedHighSecondL2Price rBound Temp Cf*C*(T.forkCost R+edgeBudget 0 as R) := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let V:=nativeInheritedHighSecondL2Price rBound Temp Cf
  have hV : 0 ≤ V:=nativeInheritedHighSecondL2Price_nonneg rBound Temp Cf hTemp
  have hR j : 0 ≤ R j := by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost : 0 ≤ T.forkCost R+edgeBudget 0 as R :=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    M.bf_monotone M.hf_monotone (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf M.bf_monotone M.hf_monotone) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  have Hjet t (ht : t∈Icc (0:ℝ) 1) :
      |cutFrozenLowHighJet n q U b h K T (fun σ=>P (T.cavityAssignment σ).1) 0 0 2 t| ≤
        V*C*(T.forkCost R+edgeBudget 0 as R) := by
    let law:=cutFullVariance n q U 0 t b h K
    let A:=cutTSlope n U 0 b h K
    have H:=cutFrozenLowHighJet_two_high_rest_L2_bound n q U b h K T ho P ht
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm hT hC
      (show 0 ≤ 2*Temp by positivity)
      (native_small_source_continuum_square_clock_budget_high_only M Temp Cf hCf hsource hxs as ho) hP
      (fun j _ σ τ=>native_centered_high_kernel_abs_le n U b h S
        (fun _=>NNReal.coe_nonneg _) Hb HS j σ τ)
      (nativeWholeLawErrorRadius_nonneg n as law A)
      (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    have Hprofile:=actual_minimum_inherited_current_high_profile_le_original_high_only M Temp Cf
      hTemp hCf hsource hxs T ho U (l:=0) (t:=t) (by norm_num) ht (e:=1) (by norm_num)
    dsimp only at Hprofile
    rw [nativeWholeLawProfileCost_eq_budget n ho] at Hprofile
    simp only [Real.rpow_one] at Hprofile
    have Hprice : pairForkVariation rBound*pairForkVariation (rBound+2)*(2*Temp)*
        (Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*C)=V*C := by
      dsimp only [V,nativeInheritedHighSecondL2Price]
      ring
    rw [Hprice] at H
    exact H.trans (mul_le_mul_of_nonneg_left Hprofile (mul_nonneg hV hC))
  have H:=weighted_unit_integral_abs_le (mul_nonneg (mul_nonneg hV hC) hcost) Hjet 1
  simpa only [pow_one,nativeRestPayloadHighSecondIntegral,V,q,K,b,h,S,R] using H

theorem actual_minimum_generated_Gamma_high_second_eq_paired_source_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    nativeGammaProjectedHighSecondRestoration T P₀.live.test.target star U q b h K A P=
      (1/2:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
        nativeRestPayloadHighSecondIntegral n q U b h K p.tree
          (nativeRestProjectedPairedTest T P₀.live.test.target star A P p))).sum := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.hf_monotone hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    M.bf_monotone M.hf_monotone as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf
    M.bf_monotone M.hf_monotone as ho
  have hq : ∀j₀,Monotone (fun j=>q j j₀) := by
    intro j₀
    cases j₀ with
    | inl j₀=>exact hbm
    | inr j₀=>exact hhm
  have hq0 : ∀j j₀,0 ≤ q j j₀ := by
    intro j j₀
    cases j₀ with
    | inl j₀=>exact hb j
    | inr j₀=>exact hh j
  exact native_actual_generated_Gamma_high_second_eq_paired_source hP hi hs ho q b h K A P
    hq0 hq hb hh hK hbm hhm hKm

theorem actual_minimum_rest_payload_high_second_integral_zero_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeRestPayloadHighSecondIntegral n q U b h K T (fun _=>0)=0 := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.hf_monotone hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    M.bf_monotone M.hf_monotone as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf
    M.bf_monotone M.hf_monotone as ho
  have hq : ∀j₀,Monotone (fun j=>q j j₀) := by
    intro j₀
    cases j₀ with
    | inl j₀=>exact hbm
    | inr j₀=>exact hhm
  have hq0 : ∀j j₀,0 ≤ q j j₀ := by
    intro j j₀
    cases j₀ with
    | inl j₀=>exact hb j
    | inr j₀=>exact hh j
  exact native_rest_payload_high_second_integral_zero n q U b h K T ho
    hq0 hq hb hh hK hbm hhm hKm

def nativeActualGeneratedHighSecond_high_only {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (star U : ℕ)
    (P : NativeGeneratedTest T) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  nativeGammaProjectedHighSecondRestoration T P.target star U
    (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h
    (nativeContinuumMixedClock n M.bf M.hf as) A
    (nativeRestGeneratedTestValue T P A (nativePhysicalResourceCenter n M.bf M.hf as))

theorem actual_minimum_generated_high_second_empty_live_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (hempty : P₀.live.test.edges=[]) :
    nativeActualGeneratedHighSecond_high_only M T star U P₀.live.test=0 := by
  unfold nativeActualGeneratedHighSecond_high_only
  dsimp only
  have HE (A : Spin n→Spin n→ℝ) (C : ℕ→ℝ) :
      nativeRestGeneratedTestValue T P₀.live.test A C=fun _=>1 := by
    funext σ
    simp only [nativeRestGeneratedTestValue,hempty,List.map_nil,List.prod_nil]
  rw [HE,actual_minimum_generated_Gamma_high_second_eq_paired_source_high_only M hP hi hs ho]
  simp only [native_rest_projected_paired_constant_zero,actual_minimum_rest_payload_high_second_integral_zero_high_only M _ ho U,
    mul_zero,List.map_const',List.sum_replicate,nsmul_zero]

private theorem gamma_high_second_native_actual_resource_canonical_product_eq_live_private
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (σ : T.Assignment) :
    ((nativeActualResourceCanonicalShape P hi hstar).canonicalHighOnlySource M
      (fun _=>NativeSourceFactorForm.centered)).product σ=
      P.test.value (fun u v=>deletedOverlap n (joinSpin u) (joinSpin v))
        (nativePhysicalResourceCenter n M.bf M.hf as) σ := by
  rw [P.value_eq_product_get]
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  apply Finset.prod_congr rfl
  intro e he
  simp only [ActualNaturalBoundaryShape.canonicalHighOnlySource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeActualResourceCanonicalShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul,nativePhysicalResourceCenter]
  rw [T.splitIndex_symm]
  ring

private theorem gamma_high_second_native_actual_resource_canonical_rest_product_eq_live_private
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : T.cavityLeft.Assignment) :
    ((nativeActualResourceCanonicalShape P hi hstar).canonicalHighOnlySource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P.test
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (nativePhysicalResourceCenter n M.bf M.hf as) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ:=by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=gamma_high_second_native_actual_resource_canonical_product_eq_live_private P hi hstar M τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_value_eq_full]
  rw [ht,H]
  unfold NativeGeneratedTest.value nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

theorem actual_minimum_generated_high_second_fixed_fork_kernel_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (star U : ℕ) (P : NativeGeneratedTest T) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    nativeGammaProjectedHighSecondRestoration T P.target star U q b h K
      (restCenteredFixedForkKernel n b C star 0) (nativeRestGeneratedTestValue T P A C)=
      b star*nativeActualGeneratedHighSecond_high_only M T star U P := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.hf_monotone hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    M.bf_monotone M.hf_monotone as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf
    M.bf_monotone M.hf_monotone as ho
  have hq : ∀j₀,Monotone (fun j=>q j j₀) := by
    intro j₀
    cases j₀ with
    | inl j₀=>exact hbm
    | inr j₀=>exact hhm
  have hq0 : ∀j j₀,0 ≤ q j j₀ := by
    intro j j₀
    cases j₀ with
    | inl j₀=>exact hb j
    | inr j₀=>exact hh j
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  have HA : restCenteredFixedForkKernel n b C star 0=
      (fun σ τ=>b star*A σ τ+(-b star*C star)) := by
    funext σ τ
    simp only [restCenteredFixedForkKernel,A,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
    ring
  rw [HA,native_gamma_high_second_affine_kernel T ho P.target star U q b h K A
    (nativeRestGeneratedTestValue T P A C) (b star) (-b star*C star)
    hq0 hq hb hh hK hbm hhm hKm]
  rfl

theorem actual_resource_gamma_second_restoration_normalized_profile_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < U)
    (high : Bool)
    {A x W price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W 1)
    (Hlive :
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let C:=nativePhysicalResourceCenter n M.bf M.hf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
      |nativeGammaProjectedSecondRestoration high T P.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b C star 0)
        (G.canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)).restProduct| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualResourceGammaSecondRestoration_high_only M U P high| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
  let scalar:=nativeActualResourceOriginalScalar_high_only M U P
  let F:=(G.canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)).restProduct
  have HE : nativeActualResourceGammaSecondRestoration_high_only M U P high=
      scalar*nativeGammaProjectedSecondRestoration high T P.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b C star 0) F := by
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let c:=-nativeOriginalRestTestExpectation n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
    have HP : nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)=
        (fun σ=>scalar*F σ+c) := by
      funext σ
      let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
      have Hτ : (T.cavityAssignment τ).1=σ := by simp only [τ,Equiv.apply_symm_apply]
      have Hlive:=gamma_high_second_native_actual_resource_canonical_product_eq_live_private P.live hi
        (hs.trans_le hP.highCut_le_length) M τ
      rw [ActualNaturalBoundaryShape.product_eq_restProduct,Hτ] at Hlive
      unfold nativeOriginalCenteredRestTest
      rw [←Hτ,native_actual_resource_rest_value_eq_full]
      change P.scalar (fullWeight n) (fullFeature n) 0 qfull
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0*
          P.live.test.value (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C τ-
          nativeOriginalRestTestExpectation n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)=_
      rw [←Hlive]
      rw [Hτ]
      change scalar*F σ- _=scalar*F σ+c
      rfl
    unfold nativeActualResourceGammaSecondRestoration_high_only
    dsimp only
    rw [HP]
    have hbm : Monotone b:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.bf_monotone hu hv huv) as ho
    have hhm : Monotone h:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.hf_monotone hu hv huv) as ho
    have HK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.bf_monotone M.hf_monotone as ho
    have HKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.bf_monotone M.hf_monotone as ho
    exact native_actual_generated_gamma_second_restoration_affine hP hi hs ho q b h K
      (restCenteredFixedForkKernel n b C star 0) F scalar c
      (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
      (by intro x;cases x <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm high
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as)
    A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
    zero_lt_one le_rfl hi (hs.trans_le hP.highCut_le_length) Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity
