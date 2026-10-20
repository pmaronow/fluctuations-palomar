module

public import ComparisonSignedCavityActualExpansionTerminal
public import ComparisonSignedCavityActualGInsertionTerminal

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

def nativeActualResourceBranchStep
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (st : NativeActualResourceState S as i star) : List (NativeActualResourceState S as i star) :=
  branches.flatMap (fun ops=>nativeActualResourceExpansion Γ hs hl ops st)

def nativeActualResourceFrontier
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp)) :
    ℕ→NativeActualResourceState S as i star→List (NativeActualResourceState S as i star)
  | 0,st=>[st]
  | depth+1,st=>(nativeActualResourceFrontier Γ hs hl branches depth st).flatMap
      (nativeActualResourceBranchStep Γ hs hl branches)

def nativeActualResourceResidualSum
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (E : NativeActualResourceState S as i star→ℝ) (depth : ℕ)
    (st : NativeActualResourceState S as i star) : ℝ :=
  ((List.range depth).map (fun j=>
    ((nativeActualResourceFrontier Γ hs hl branches j st).map E).sum)).sum

theorem nativeActualResourceBranchStep_valid
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (st : NativeActualResourceState S as i star) {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceBranchStep Γ hs hl branches st) :
    NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
  obtain ⟨ops,hops,hQ⟩:=List.mem_flatMap.mp hQ
  exact nativeActualResourceExpansion_valid Γ hs hl ops st hst Q hQ

theorem nativeActualResourceFrontier_valid
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (depth : ℕ) (st : NativeActualResourceState S as i star) {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceFrontier Γ hs hl branches depth st) :
    NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
  induction depth generalizing Q with
  | zero=>obtain rfl:=List.mem_singleton.mp hQ;exact hst
  | succ depth ih=>
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    exact nativeActualResourceBranchStep_valid Γ hs hl branches P (ih P hP) Q hQ

theorem nativeActualResourceBranchStep_generation
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (increment : ℕ) (hinc : ∀ops∈branches,nativeActualExpansionMarkedCount ops=increment)
    (st Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceBranchStep Γ hs hl branches st) :
    Q.generation=st.generation+increment := by
  obtain ⟨ops,hops,hQ⟩:=List.mem_flatMap.mp hQ
  simpa only [hinc ops hops] using nativeActualResourceExpansion_generation Γ hs hl ops st Q hQ

theorem nativeActualResourceFrontier_generation
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (increment : ℕ) (hinc : ∀ops∈branches,nativeActualExpansionMarkedCount ops=increment)
    (depth : ℕ) (st Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceFrontier Γ hs hl branches depth st) :
    Q.generation=st.generation+depth*increment := by
  induction depth generalizing Q with
  | zero=>obtain rfl:=List.mem_singleton.mp hQ;simp
  | succ depth ih=>
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    have HP:=ih P hP
    have HQ:=nativeActualResourceBranchStep_generation Γ hs hl branches increment hinc P Q hQ
    simp only [Nat.succ_mul]
    omega

theorem nativeActualResourceFrontier_telescoping
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (F E : NativeActualResourceState S as i star→ℝ) (depth : ℕ)
    (st : NativeActualResourceState S as i star)
    (hstep : ∀j<depth,∀Q∈nativeActualResourceFrontier Γ hs hl branches j st,
      F Q=E Q+((nativeActualResourceBranchStep Γ hs hl branches Q).map F).sum) :
    F st=nativeActualResourceResidualSum Γ hs hl branches E depth st+
      ((nativeActualResourceFrontier Γ hs hl branches depth st).map F).sum := by
  induction depth with
  | zero=>simp [nativeActualResourceResidualSum,nativeActualResourceFrontier]
  | succ depth ih=>
    have HI:=ih (fun j hj Q hQ=>hstep j (by omega) Q hQ)
    have Hlevel : ((nativeActualResourceFrontier Γ hs hl branches depth st).map F).sum=
        ((nativeActualResourceFrontier Γ hs hl branches depth st).map E).sum+
        ((nativeActualResourceFrontier Γ hs hl branches (depth+1) st).map F).sum := by
      calc
        _=((nativeActualResourceFrontier Γ hs hl branches depth st).map (fun Q=>
          E Q+((nativeActualResourceBranchStep Γ hs hl branches Q).map F).sum)).sum := by
            congr 1
            apply List.map_congr_left
            intro Q hQ
            exact hstep depth (by omega) Q hQ
        _=_ := by
          simp only [List.sum_map_add,nativeActualResourceFrontier,List.map_flatMap,native_sum_flatMap]
    rw [Hlevel] at HI
    simpa only [nativeActualResourceResidualSum,List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,add_assoc] using HI

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeActualGResourceResponse
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (W : ℝ) (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  nativeActualResourceGInsertion M st.term U st.generation v q x₀ W

theorem nativeActualGResourceResponse_finite_recursion_of_step_identity
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (W : ℝ) (E : NativeActualResourceState (Spin n×Bool) as i star→ℝ) (depth : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (hstep : ∀j<depth,∀Q∈nativeActualResourceFrontier Γ hs hl branches j st,
      nativeActualGResourceResponse M U v q x₀ W Q=E Q+
        ((nativeActualResourceBranchStep Γ hs hl branches Q).map
          (nativeActualGResourceResponse M U v q x₀ W)).sum) :
    nativeActualGResourceResponse M U v q x₀ W st=
      nativeActualResourceResidualSum Γ hs hl branches E depth st+
      ((nativeActualResourceFrontier Γ hs hl branches depth st).map
        (nativeActualGResourceResponse M U v q x₀ W)).sum :=
  nativeActualResourceFrontier_telescoping Γ hs hl branches _ E depth st hstep

end OAI.SKFluctuations.Cavity
