module

public import ComparisonSignedCavityCanonicalExteriorPayload
public import ComparisonSignedCavityCanonicalMarkedOldProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeGeneratedExteriorShape (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length) :
    ActualNaturalBoundaryShape n P.exterior.length T where
  α:=fun _=>0
  β:=fun _=>1
  i:=fun e=>(P.exterior.get e).2
  j:=fun e=>(P.exterior.get e).1
  distinct:=by
    intro e heq
    have H:=hP.exterior_cuts (P.exterior.get e) (List.get_mem _ e)
    rw [←heq,T.splitIndex_self] at H
    omega
  lowInGrid:=fun e=>T.splitIndex_le_clockLength _ _

theorem native_generated_exterior_shape_labels_low (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length) (j : Fin P.exterior.length×Bool) :
    T.cavityLeft.splitIndex (T.cavityLeftSlot P.target)
      ((nativeGeneratedExteriorShape n P hP hi hstar).restLabels j) ≤ star := by
  have H:=hP.exterior_departure (P.exterior.get j.1) (List.get_mem _ j.1)
  rcases j with ⟨e,b⟩
  cases b <;> simp only [ActualNaturalBoundaryShape.restLabels,nativeGeneratedExteriorShape,
    Bool.false_eq_true,ite_false,ite_true,ClockTree.cavityLeft_splitIndex] <;> tauto

theorem native_generated_exterior_canonical_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (σ : T.Assignment) :
    ((nativeGeneratedExteriorShape n P hP hi hstar).canonicalMinimumSource M
      (fun _=>NativeSourceFactorForm.centered)).product σ =
      nativeGeneratedEdgeProduct T (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) P.exterior σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [←List.prod_ofFn]
  unfold nativeGeneratedEdgeProduct
  conv_rhs => rw [←List.ofFn_get P.exterior,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext e
  simp only [ActualNaturalBoundaryShape.canonicalMinimumSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeGeneratedExteriorShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul]
  rw [T.splitIndex_symm]
  dsimp only [Function.comp_apply]
  ring

theorem native_generated_exterior_marked_labels_low (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star U : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < U) (hlen : U ≤ as.length)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hc : U ≤ T.splitIndex c P.target)
    (j : Fin P.exterior.length×Bool) :
    p.tree.cavityLeft.splitIndex (p.tree.cavityLeftSlot (p.embed c))
      (((nativeGeneratedExteriorShape n P hP hi (hstar.trans_le hlen)).retainOnMarked a p hp).restLabels j)
      ≤ star := by
  let G:=nativeGeneratedExteriorShape n P hP hi (hstar.trans_le hlen)
  have HL:=native_generated_exterior_shape_labels_low n P hP hi (hstar.trans_le hlen) j
  have HF : T.splitIndex P.target (if j.2 then G.j j.1 else G.i j.1) ≤ star := by
    simpa only [ActualNaturalBoundaryShape.restLabels,ClockTree.cavityLeft_splitIndex] using HL
  have HE:=T.splitIndex_low_eq_of_high c P.target _ hc (HF.trans_lt hstar)
  simp only [ActualNaturalBoundaryShape.restLabels,ActualNaturalBoundaryShape.retainOnMarked,
    ClockTree.cavityLeft_splitIndex]
  change p.tree.splitIndex (p.embed c) (if j.2 then p.embed (G.j j.1) else p.embed (G.i j.1)) ≤ star
  rw [←apply_ite p.embed,(T.markedAttach_embed_preserves a p hp).2,HE]
  exact HF

def nativeGeneratedExteriorInitial {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T) (i : ℕ) :
    Finset (Fin P.exterior.length) :=
  Finset.univ.filter (fun e=>T.splitIndex (P.exterior.get e).1 (P.exterior.get e).2=i)

theorem native_generated_exterior_source_mass (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length) (Cmass x W : ℝ)
    (hmi : partitionPoint 0 as i ≤ Cmass*x) (hms : partitionPoint 0 as star ≤ Cmass*W)
    (e : Fin P.exterior.length) :
    (nativeGeneratedExteriorShape n P hP hi hstar).sourceLowMass e ≤
      Cmass*sourceFactorScale x W (nativeGeneratedExteriorInitial P i) e := by
  classical
  have H:=hP.exterior_cuts (P.exterior.get e) (List.get_mem _ e)
  simp only [ActualNaturalBoundaryShape.sourceLowMass,nativeGeneratedExteriorShape]
  rw [T.splitIndex_symm]
  by_cases he : T.splitIndex (P.exterior.get e).1 (P.exterior.get e).2=i
  · simpa only [nativeGeneratedExteriorInitial,sourceFactorScale,Finset.mem_filter,
      Finset.mem_univ,true_and,he,ite_true] using hmi
  · have hs : T.splitIndex (P.exterior.get e).1 (P.exterior.get e).2=star:=H.resolve_left he
    have hsi : star ≠ i:=fun H=>he (hs.trans H)
    simpa only [nativeGeneratedExteriorInitial,sourceFactorScale,Finset.mem_filter,
      Finset.mem_univ,true_and,he,ite_false,hs,hsi] using hms

end OAI.SKFluctuations.Cavity
