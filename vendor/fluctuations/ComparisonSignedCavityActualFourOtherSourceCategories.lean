module

public import ComparisonSignedCavityActualFourFirstHighDecomposition
public import ComparisonSignedCavityActualFourGaSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

inductive NativeActualOtherSourceCategory where
  | gammaRetained | gammaHighRestoration | gammaLowRestoration
  | secondLow | higherTaylor | jointLowTwoHigh | jointLowRestoration
  | longitudinalLeft | longitudinalRight | fourGLowRestoration | deletedSite
  deriving DecidableEq, Repr

def nativeActualOtherSourceCategories : List NativeActualOtherSourceCategory :=
  [.gammaRetained,.gammaHighRestoration,.gammaLowRestoration,.secondLow,.higherTaylor,
    .jointLowTwoHigh,.jointLowRestoration,.longitudinalLeft,.longitudinalRight,
    .fourGLowRestoration,.deletedSite]

def nativeActualOriginalOtherSourceCategory (cat : NativeActualOtherSourceCategory) (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  let Pg:=fun σ=>P (g.restRestrict σ)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let A:=restCenteredFixedForkKernel n b C star 0
  match cat with
  | .gammaRetained=>chi*nativeRetainedGammaProjectedDisplacement T s star U q K A P
  | .gammaHighRestoration=>chi*nativeGammaProjectedHighSecondRestoration T s star U q b h K A P
  | .gammaLowRestoration=>chi*nativeGammaProjectedLowSecondRestoration T s star U q b h K A P
  | .secondLow=>(1/2:ℝ)*nativeRetainedCenteredCoefficient n q U b h K g.tree Pg [g.embed s,g.mark] 2 0
  | .higherTaylor=>nativeActualTaylorRemainder n q U b h K g.tree Pg (g.embed s) g.mark
  | .jointLowTwoHigh=>-nativeCenteredLowGammaHighSecondRemainder n q U b h K C g.tree Pg (g.embed s) g.mark
  | .jointLowRestoration=>-nativeCenteredLowGammaLowRestoration n q U b h K C g.tree Pg (g.embed s) g.mark
  | .longitudinalLeft=>-chi*K (g.tree.splitIndex (g.embed s) g.mark)*
      nativeOriginalLongitudinalRestoration n q U b h K C g.tree
        (fun σ=>Pg (g.tree.cavityAssignment σ).1) (g.embed s)
  | .longitudinalRight=>-chi*K (g.tree.splitIndex (g.embed s) g.mark)*
      nativeOriginalLongitudinalRestoration n q U b h K C g.tree
        (fun σ=>Pg (g.tree.cavityAssignment σ).1) g.mark
  | .fourGLowRestoration=>-nativeOriginalGKernelLowRestoration n q U b h K C g.tree Pg (g.embed s) g.mark
      (restCenteredLowKernel n U b C)
  | .deletedSite=>-(nativeOriginalSitePairExpectation n q U b h K g.tree Pg (g.embed s) g.mark-
      nativeActualOriginalFreshPairMoment n q U b h K C T P s star)

theorem native_actual_other_source_eq_Ga_add_categories (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) :
    nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C T P s star=
      nativeActualOriginalGaSource n q U b h K C T P s star+
      (nativeActualOtherSourceCategories.map
        (fun cat=>nativeActualOriginalOtherSourceCategory cat n q U b h K C T P s star)).sum := by
  simp only [nativeActualOtherSourceCategories,nativeActualOriginalOtherSourceCategory,
    nativeActualOriginalOneStepWithoutFirstHigh,nativeActualOriginalGaSource,
    nativeActualOriginalForwardTaylorError,nativeActualHigherAllocatedRemainder,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

def nativeActualOriginalFourOtherCategoryContrast
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (cat : NativeActualOtherSourceCategory) : ℝ :=
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
  nativeActualOriginalOtherSourceCategory cat n q U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOtherSourceCategory cat n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

theorem native_actual_four_other_source_eq_Ga_add_categories
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeActualOriginalFourOtherSourceErrorContrast M U st=
      nativeActualOriginalFourGaContrast M U st+
      (nativeActualOtherSourceCategories.map
        (nativeActualOriginalFourOtherCategoryContrast M U st)).sum := by
  unfold nativeActualOriginalFourOtherSourceErrorContrast nativeActualOriginalFourGaContrast
    nativeActualOriginalFourOtherCategoryContrast
  dsimp only
  rw [native_actual_other_source_eq_Ga_add_categories,native_actual_other_source_eq_Ga_add_categories]
  simp only [nativeActualOtherSourceCategories,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

end OAI.SKFluctuations.Cavity
