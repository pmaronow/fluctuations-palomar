module

public import ComparisonSignedCavityActualFourFirstHighReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

def nativeActualOriginalOneStepWithoutFirstHigh (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  let Pg:=fun σ=>P (g.restRestrict σ)
  let Q:=fun σ=>P (T.cavityAssignment σ).1
  let qfull:=cutFullVariance n q U 1 1 b h K
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let A:=restCenteredFixedForkKernel n b S star 0
  chi*(nativeRetainedGammaProjectedDisplacement T s star U q K A P+
    nativeGammaProjectedHighSecondRestoration T s star U q b h K A P+
    nativeGammaProjectedLowSecondRestoration T s star U q b h K A P)+
  (chi/2)*nativeActualOriginalGProjectedResampling T s star U K b S 0 qfull 0
    (fun σ τ=>A σ.1 τ.1) Q+
  nativeActualOriginalForwardTaylorError n q U b h K S g.tree Pg (g.embed s) g.mark-
  (nativeOriginalSitePairExpectation n q U b h K g.tree Pg (g.embed s) g.mark-
    nativeActualOriginalFreshPairMoment n q U b h K S T P s star)

theorem native_original_one_step_eq_first_high_add_other
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b h K S : ℕ→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalOneStepError n q U b h K S T P P₀.live.test.target star=
      chi*nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b S star 0) P+
      nativeActualOriginalOneStepWithoutFirstHigh n q U b h K S T P P₀.live.test.target star := by
  have H:=native_actual_original_Gamma_pair_half_eq_rest_first_high_and_remainders
    hP hi hs ho q b h K (restCenteredFixedForkKernel n b S star 0) P hq0 hq hb hh hK hbm hhm hKm
  unfold nativeActualOriginalOneStepError nativeActualOriginalOneStepWithoutFirstHigh
  dsimp only
  linear_combination
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*H

theorem actual_minimum_one_step_eq_first_high_add_other
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
