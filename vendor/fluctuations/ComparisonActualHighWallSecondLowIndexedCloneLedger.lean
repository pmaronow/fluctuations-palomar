module

public import ComparisonActualGeneralSecondLowCanonicalRow
public import ComparisonSignedCavitySecondLowClassifiedIndexedCloneLedgerLaw

@[expose] public section
noncomputable section
set_option maxHeartbeats 15000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
attribute [local instance] nativeSecondLowSlotFintype
private theorem classified_clock_expect_sum {S ι J : Type} [Fintype S] [Fintype ι] [Fintype J]
    {as : List PositiveMass} (T : ClockTree S as) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (F : J→T.Assignment→ℝ) (x : ι→ℝ) :
    T.expect w φ q (fun σ=>∑j:J,F j σ) x=∑j:J,T.expect w φ q (F j) x := by
  classical
  unfold ClockTree.expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

variable {n : ℕ} {pre mid tail : List PositiveMass}
variable {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {f c z : T.Slot}
variable {v : RestCoordinate n→ℝ} {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

theorem actual_high_wall_second_low_classified_canonical_two_LOW_read
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (ho : MassOrdered 0 (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (K : ℕ→ℝ)
    (hstar : pre.length+mid.length < U) (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (Hfc : T.splitIndex f c < U) (Hcz : T.splitIndex c z < U)
    (η : E.source.Ei.Assignment) (ζ : E.source.Es.Assignment) (δ : E.source.D.Assignment)
    (d : E.source.D.Slot) :
    ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor M.bf M.hf f (E.originalSlot d) (E.source.read η ζ δ)*
      ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor M.bf M.hf z (E.originalSlot d) (E.source.read η ζ δ)=
      (E.toWholeCSource ho).twoLow U
        (fun j=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)) K η ζ (E.source.D.atSlot δ d)+
        K (T.splitIndex f c)*K (T.splitIndex c z) := by
  obtain ⟨Hf,Hz⟩:=E.outside_splits_at_originalSlot hstar hU hT Hfc Hcz d
  rw [physical_unweighted_c_canonical_row_eq_LOW n U T M.bf M.hf f (E.originalSlot d) (by rwa [Hf]),
    physical_unweighted_c_canonical_row_eq_LOW n U T M.bf M.hf z (E.originalSlot d)
      (by rw [T.splitIndex_symm,Hz];exact Hcz)]
  rw [Hf,T.splitIndex_symm z (E.originalSlot d),Hz,E.outside_f_read,E.outside_z_read,
    E.read_at_originalSlot]
  dsimp only [NativeSecondLowClassifiedWholeCSource.twoLow,
    NativeSecondLowClassifiedRetainedWholeCSource.toWholeCSource]
  simp only [Hfc,Hcz,ite_true]
  have Hsymm (s t : Spin n) (j : ℕ) :
      restLowKernel n U (fun k=>(M.bf (partitionPoint 0 (pre++(mid++tail)) k):ℝ))
        (fun k=>(M.hf (partitionPoint 0 (pre++(mid++tail)) k):ℝ)) j s t=
      restLowKernel n U (fun k=>(M.bf (partitionPoint 0 (pre++(mid++tail)) k):ℝ))
        (fun k=>(M.hf (partitionPoint 0 (pre++(mid++tail)) k):ℝ)) j t s:=by
    simp only [restLowKernel,mul_comm]
  rw [Hsymm (E.outsideZ η ζ) (E.source.D.atSlot δ d) (T.splitIndex c z)]
  ring

theorem actual_high_wall_second_low_classified_indexed_NEW_ledger_eq_sum
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (ho : MassOrdered 0 (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U cut : ℕ) (q' : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (hstar : pre.length+mid.length < U) (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (Hfc : T.splitIndex f c < U) (Hcz : T.splitIndex c z < U)
    (r : ((RestCoordinate n→ℝ)×(RestCoordinate n→ℝ))×(RestCoordinate n→ℝ)) :
    nativeExteriorIndexedNewCloneSquareSum E.source.Ei E.source.Es E.source.D
      (restWeight n) (restFeature n) (cut-(pre.length+mid.length))
      (fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+j))
      (fun j=>cumulativeIncrements (q' 0) (fun k=>q' (k+1)) (pre.length+(mid.length+j)))
      ((E.toWholeCSource ho).twoLow U
        (fun j=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)) K)
      (exteriorForestIRoot r,exteriorForestStarRoot r)=
      ∑d:E.source.D.Slot,nativeSecondLowClassifiedCloneConditional E d cut q'
        (fun σ τ=>(
          ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor M.bf M.hf f (E.originalSlot d) σ*
            ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor M.bf M.hf z (E.originalSlot d) σ-
          ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor M.bf M.hf f (E.originalSlot d) τ*
            ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor M.bf M.hf z (E.originalSlot d) τ)^2) r := by
  dsimp only [nativeExteriorIndexedNewCloneSquareSum,nativeRetainedNewCloneSquareSum,
    nativeSecondLowClassifiedCloneConditional,NativeClassifiedWholeRetainedSource.retainedCloneConditional]
  simp_rw [classified_clock_expect_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply congrArg (fun F=>E.source.Ei.expect (restWeight n) (restFeature n) _ F _)
  funext η
  apply congrArg (fun F=>E.source.Es.expect (restWeight n) (restFeature n) _ F _)
  funext ζ
  apply congrArg (fun Q=>nativeRetainedCloneCutMean (restWeight n) (restFeature n) E.source.D d
    (cut-(pre.length+mid.length)) _ Q _)
  funext δ δ'
  rw [actual_high_wall_second_low_classified_canonical_two_LOW_read E ho M U K hstar hU hT Hfc Hcz,
    actual_high_wall_second_low_classified_canonical_two_LOW_read E ho M U K hstar hU hT Hfc Hcz]
  ring

end OAI.SKFluctuations.Cavity
