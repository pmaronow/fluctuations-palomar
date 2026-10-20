module

public import ComparisonSignedCavitySecondLowActualConstantResourceStarOnlyB0SavingAlong
public import ComparisonSignedCavitySecondLowActualHistoryFullHalfRetargetB0ModulusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

def ActualConstantResourceStarOnlyFullHalfB0SavingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Couter Rmacro Cx : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    ∀(mid tail : List PositiveMass),as=mid++tail → mid.length=retainedMassPrefixIndex (w n).star.val as →
    ∀(U : ℕ) (_hU : U ≤ (mid++tail).length)
      (st : NativeActualResourceState (Spin (dim n)×Bool) (mid++tail) 0 mid.length),
      NativeActualResourceGenerated 0 mid.length U [] st.generation st.tree st.term → st.generation ≤ degree →
      0 < mid.length → mid.length < U → st.tree.leaves ≤ rBound →
      partitionPoint 0 as U ≤ Couter*W n → partitionPoint 0 as mid.length ≤ Cmass*W n →
      4*W n ≤ (M n).R (partitionPoint 0 as U) →
      (M n).z ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).R (partitionPoint 0 as mid.length) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
    ∀(sourceMass : ℝ) (hsourceMass : 0 < sourceMass),Cx*(M n).xs ≤ sourceMass → partitionPoint 0 as U=sourceMass →
      (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us) →
    |((W n)⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U st .secondLow| ≤
      |st.term.coefficient| *eps n*W n*(M n).xs^2

theorem actual_constant_resource_star_only_full_half_B0_from_resource_rows_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree rBound : ℕ) (Cmass Couter Rmacro Cx : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hrows : ActualConstantResourceStarOnlyFullB0SavingOnEveryFinalNetAlong degree (rBound+1)
      Cmass Couter Rmacro Cx eps dim M W w) :
    ActualConstantResourceStarOnlyFullHalfB0SavingOnEveryFinalNetAlong degree rBound
      Cmass Couter Rmacro Cx (fun n=>(3/2:ℝ)*eps n) dim M W w := by
  filter_upwards [Hrows] with n hn
  intro L us hus hstar hret hmesh
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hg
  dsimp only at hg ⊢
  intro mid tail hparts hindex U hU st hP hdegree hmid hs hT houter hms Hhigh Hz Hrs
    sourceMass hsourceMass HCx HsourceMass Hnodes
  let as:=mid++tail
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target mid.length
  let B:=|st.term.coefficient| *eps n*W n*(M n).xs^2
  have hgLeaf : g.tree.leaves ≤ rBound+1:=by
    have H:=st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target mid.length)
    omega
  have H0:=hg mid tail hparts hindex U st.generation st.tree hU st.term hP hdegree hmid hs
    (hT.trans (by omega)) houter hms Hhigh Hz Hrs sourceMass hsourceMass HCx HsourceMass Hnodes
  have H1:=hg mid tail hparts hindex U st.generation g.tree hU (st.term.retarget 0) hP.retarget hdegree
    hmid hs hgLeaf houter hms Hhigh Hz Hrs sourceMass hsourceMass HCx HsourceMass Hnodes
  have ho:MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
  have H:=native_actual_original_full_four_second_low_abs_le (M n) U hU ho hs st (W n) B
    H0 (by simpa only [NativeResourceTerm.retarget] using H1)
  exact H.trans_eq (by dsimp only [B];ring)

end OAI.SKFluctuations.Cavity
