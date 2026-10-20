module

public import ComparisonSignedCavityActualCenteredResourceLongitudinalRestoration
public import ComparisonSignedCavityActualFourOtherSourceCategories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

def nativeActualLongitudinalCategory (right : Bool) : NativeActualOtherSourceCategory :=
  if right then .longitudinalRight else .longitudinalLeft

def nativeActualOriginalFourLongitudinalError
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (right : Bool) : ℝ :=
  (W⁻¹)^st.generation*(nativeActualOriginalFreshResourceLongitudinalRestoration M U st.term right-
    (1/2:ℝ)*nativeActualOriginalFreshResourceLongitudinalRestoration M U (st.term.retarget 0) right)

theorem native_actual_four_longitudinal_contrast_eq_resources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as)
    (hstar : star ≤ as.length) (right : Bool) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourOtherCategoryContrast M U st (nativeActualLongitudinalCategory right)=
      -chi*K star*(nativeActualOriginalFreshResourceLongitudinalRestoration M U st.term right-
        (1/2:ℝ)*nativeActualOriginalFreshResourceLongitudinalRestoration M U (st.term.retarget 0) right) := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  have hsplit (T : ClockTree (Spin n×Bool) as) (s : T.Slot) :
      (nativeFreshAtSlot T 0 s star).tree.splitIndex ((nativeFreshAtSlot T 0 s star).embed s)
        (nativeFreshAtSlot T 0 s star).mark=star:=by
    rw [ClockTree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hstar]
  cases right <;>
    unfold nativeActualLongitudinalCategory nativeActualOriginalFourOtherCategoryContrast
      nativeActualOriginalOtherSourceCategory nativeActualOriginalFreshResourceLongitudinalRestoration <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> rw [Hread] <;>
    dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,
      NativeGeneratedTest.retarget] <;>
    simp only [hsplit] <;> ring_nf <;> rfl

theorem actual_four_longitudinal_error_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (right : Bool)
    {B : ℝ} (hB : 0 ≤ B)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration M U st.term right| ≤ B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration M U (st.term.retarget 0) right| ≤ B) :
    |nativeActualOriginalFourLongitudinalError M U W st right| ≤ 2*B := by
  have H:=abs_sub_le ((W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration M U st.term right) 0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration M U (st.term.retarget 0) right))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at H
  have HE : nativeActualOriginalFourLongitudinalError M U W st right=
      (W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration M U st.term right-
        (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceLongitudinalRestoration M U (st.term.retarget 0) right):=by
    unfold nativeActualOriginalFourLongitudinalError
    ring
  rw [HE]
  linarith

end OAI.SKFluctuations.Cavity
