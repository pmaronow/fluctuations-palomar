module

public import ComparisonSignedCavityGeneratedBaseFactorization

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_edge_cuts {S : Type} {as : List PositiveMass}
    {T : ClockTree S as} (P : NativeGeneratedTest T) {i star : ℕ}
    (hP : NativeGeneratedTestAncestry i star P) (e : T.Slot×T.Slot) (he : e∈P.edges) :
    T.splitIndex e.1 e.2=i ∨ T.splitIndex e.1 e.2=star := by
  simp only [NativeGeneratedTest.edges,List.mem_append,List.mem_map] at he
  rcases he with (he|⟨c,hc,rfl⟩)|⟨c,hc,rfl⟩
  · exact hP.exterior_cuts e he
  · exact Or.inr (hP.teeth_star c hc)
  · exact hP.incoming_cuts c hc

def nativeGeneratedCompleteShape (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length) :
    ActualNaturalBoundaryShape n P.edges.length T where
  α:=fun _=>0
  β:=fun _=>1
  i:=fun e=>(P.edges.get e).2
  j:=fun e=>(P.edges.get e).1
  distinct:=by
    intro e heq
    have H:=native_generated_edge_cuts P hP (P.edges.get e) (List.get_mem _ e)
    rw [←heq,T.splitIndex_self] at H
    omega
  lowInGrid:=fun e=>T.splitIndex_le_clockLength _ _

theorem native_generated_complete_canonical_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (σ : T.Assignment) :
    ((nativeGeneratedCompleteShape n P hP hi hstar).canonicalMinimumSource M
      (fun _=>NativeSourceFactorForm.centered)).product σ =
      nativeGeneratedEdgeProduct T (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) P.edges σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [←List.prod_ofFn]
  unfold nativeGeneratedEdgeProduct
  conv_rhs => rw [←List.ofFn_get P.edges,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext e
  simp only [ActualNaturalBoundaryShape.canonicalMinimumSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeGeneratedCompleteShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul]
  rw [T.splitIndex_symm]
  dsimp only [Function.comp_apply]
  ring

def nativeGeneratedCompleteInitial {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T) (i : ℕ) :
    Finset (Fin P.edges.length) :=
  Finset.univ.filter (fun e=>T.splitIndex (P.edges.get e).1 (P.edges.get e).2=i)

theorem native_generated_complete_source_mass (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length) (Cmass x W : ℝ)
    (hmi : partitionPoint 0 as i ≤ Cmass*x) (hms : partitionPoint 0 as star ≤ Cmass*W)
    (e : Fin P.edges.length) :
    (nativeGeneratedCompleteShape n P hP hi hstar).sourceLowMass e ≤
      Cmass*sourceFactorScale x W (nativeGeneratedCompleteInitial P i) e := by
  classical
  have H:=native_generated_edge_cuts P hP (P.edges.get e) (List.get_mem _ e)
  simp only [ActualNaturalBoundaryShape.sourceLowMass,nativeGeneratedCompleteShape]
  rw [T.splitIndex_symm]
  by_cases he : T.splitIndex (P.edges.get e).1 (P.edges.get e).2=i
  · simpa only [nativeGeneratedCompleteInitial,sourceFactorScale,Finset.mem_filter,
      Finset.mem_univ,true_and,he,ite_true] using hmi
  · have hs : T.splitIndex (P.edges.get e).1 (P.edges.get e).2=star:=H.resolve_left he
    have hsi : star ≠ i:=fun H=>he (hs.trans H)
    simpa only [nativeGeneratedCompleteInitial,sourceFactorScale,Finset.mem_filter,
      Finset.mem_univ,true_and,he,ite_false,hs,hsi] using hms

theorem native_generated_complete_canonical_rest_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : T.cavityLeft.Assignment) :
    ((nativeGeneratedCompleteShape n P hP hi hstar).canonicalMinimumSource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ := by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=native_generated_complete_canonical_product n P hP hi hstar M τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_value_eq_full]
  rw [ht,H]
  unfold nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
