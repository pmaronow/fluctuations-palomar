module

public import ComparisonSignedCavityActualResourceRecursion

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

abbrev NativeActualWeightedBranches := List (ℕ×List NativeActualExpansionOp)

def nativeActualWeightedBranchStep
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (st : NativeActualResourceState S as i star) : List (NativeActualResourceState S as i star) :=
  branches.flatMap (fun b=>(nativeActualResourceExpansion Γ hs hl b.2 st).map
    (fun Q=>Q.reweight (weight st b.1)))

def nativeActualWeightedFrontier
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ) :
    ℕ→NativeActualResourceState S as i star→List (NativeActualResourceState S as i star)
  | 0,st=>[st]
  | depth+1,st=>(nativeActualWeightedFrontier Γ hs hl branches weight depth st).flatMap
      (nativeActualWeightedBranchStep Γ hs hl branches weight)

def nativeActualWeightedResidualSum
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (E : NativeActualResourceState S as i star→ℝ) (depth : ℕ)
    (st : NativeActualResourceState S as i star) : ℝ :=
  ((List.range depth).map (fun j=>
    ((nativeActualWeightedFrontier Γ hs hl branches weight j st).map E).sum)).sum

theorem nativeActualWeightedBranchStep_valid
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (st : NativeActualResourceState S as i star) {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualWeightedBranchStep Γ hs hl branches weight st) :
    NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
  obtain ⟨b,hb,hQ⟩:=List.mem_flatMap.mp hQ
  obtain ⟨P,hP,rfl⟩:=List.mem_map.mp hQ
  exact (nativeActualResourceExpansion_valid Γ hs hl b.2 st hst P hP).reweight _

theorem nativeActualWeightedFrontier_valid
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (st : NativeActualResourceState S as i star) {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualWeightedFrontier Γ hs hl branches weight depth st) :
    NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
  induction depth generalizing Q with
  | zero=>obtain rfl:=List.mem_singleton.mp hQ;exact hst
  | succ depth ih=>
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    exact nativeActualWeightedBranchStep_valid Γ hs hl branches weight P (ih P hP) Q hQ

theorem nativeActualWeightedBranchStep_generation
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (increment : ℕ) (hinc : ∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)
    (st Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualWeightedBranchStep Γ hs hl branches weight st) :
    Q.generation=st.generation+increment := by
  obtain ⟨b,hb,hQ⟩:=List.mem_flatMap.mp hQ
  obtain ⟨P,hP,rfl⟩:=List.mem_map.mp hQ
  simpa only [NativeActualResourceState.reweight,hinc b hb] using
    nativeActualResourceExpansion_generation Γ hs hl b.2 st P hP

theorem nativeActualWeightedFrontier_generation
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (increment : ℕ) (hinc : ∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)
    (depth : ℕ) (st Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualWeightedFrontier Γ hs hl branches weight depth st) :
    Q.generation=st.generation+depth*increment := by
  induction depth generalizing Q with
  | zero=>obtain rfl:=List.mem_singleton.mp hQ;simp
  | succ depth ih=>
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    have HP:=ih P hP
    have HQ:=nativeActualWeightedBranchStep_generation Γ hs hl branches weight increment hinc P Q hQ
    simp only [Nat.succ_mul]
    omega

theorem nativeActualWeightedFrontier_telescoping
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (F E : NativeActualResourceState S as i star→ℝ) (depth : ℕ)
    (st : NativeActualResourceState S as i star)
    (hstep : ∀j<depth,∀Q∈nativeActualWeightedFrontier Γ hs hl branches weight j st,
      F Q=E Q+((nativeActualWeightedBranchStep Γ hs hl branches weight Q).map F).sum) :
    F st=nativeActualWeightedResidualSum Γ hs hl branches weight E depth st+
      ((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map F).sum := by
  induction depth with
  | zero=>simp [nativeActualWeightedResidualSum,nativeActualWeightedFrontier]
  | succ depth ih=>
    have HI:=ih (fun j hj Q hQ=>hstep j (by omega) Q hQ)
    have Hlevel : ((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map F).sum=
        ((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map E).sum+
        ((nativeActualWeightedFrontier Γ hs hl branches weight (depth+1) st).map F).sum := by
      calc
        _=((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map (fun Q=>
          E Q+((nativeActualWeightedBranchStep Γ hs hl branches weight Q).map F).sum)).sum := by
            congr 1
            apply List.map_congr_left
            intro Q hQ
            exact hstep depth (by omega) Q hQ
        _=_ := by
          simp only [List.sum_map_add,nativeActualWeightedFrontier,List.map_flatMap,native_sum_flatMap]
    rw [Hlevel] at HI
    simpa only [nativeActualWeightedResidualSum,List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,add_assoc] using HI

end OAI.SKFluctuations.Hierarchy.ClockTree
