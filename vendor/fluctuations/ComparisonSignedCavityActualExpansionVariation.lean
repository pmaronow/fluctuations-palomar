module

public import ComparisonSignedCavityActualResourceVariation

@[expose] public section

noncomputable section
set_option maxHeartbeats 11000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

def NativeActualExpansionOp.coefficientCost (r : ℕ) : NativeActualExpansionOp → ℝ
  | .center=>2
  | .reweight c=>|c|
  | .retarget=>1
  | .projection=>1
  | .highRow=>4*(r:ℝ)+1

def nativeActualExpansionVariation : ℕ → List NativeActualExpansionOp → ℝ
  | _,[]=>1
  | r,op::ops=>op.coefficientCost r*nativeActualExpansionVariation (r+2) ops

theorem nativeActualExpansionVariation_nonneg (r : ℕ) (ops : List NativeActualExpansionOp) :
    0≤nativeActualExpansionVariation r ops := by
  induction ops generalizing r with
  | nil=>exact zero_le_one
  | cons op ops ih=>
    apply mul_nonneg _ (ih _)
    cases op <;> simp only [NativeActualExpansionOp.coefficientCost] <;> positivity

theorem nativeActualResourceStep_leaves_le
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (op : NativeActualExpansionOp)
    (st Q : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r)
    (hQ : Q∈nativeActualResourceStep Γ hs hl op st) : Q.tree.leaves≤r+2 := by
  have Hfresh : (nativeFreshAtSlot st.tree 0 st.term.live.test.target star).tree.leaves≤r+2 := by
    have H:=st.tree.markedAttach_leaves 0 _ (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target star)
    omega
  cases op with
  | center=>
    simp only [nativeActualResourceStep,List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with rfl|rfl
    · omega
    · change st.tree.leaves≤r+2;omega
  | reweight c=>
    obtain rfl:=List.mem_singleton.mp hQ
    change st.tree.leaves≤r+2;omega
  | retarget=>obtain rfl:=List.mem_singleton.mp hQ;exact Hfresh
  | projection=>obtain rfl:=List.mem_singleton.mp hQ;exact Hfresh
  | highRow=>
    obtain ⟨p,hp,hQ⟩:=List.mem_flatMap.mp hQ
    split_ifs at hQ with hh
    · obtain rfl:=List.mem_singleton.mp hQ
      have h1:=st.tree.markedAttach_leaves 0 p.val p.property
      have h2:=p.val.tree.markedAttach_leaves 0 _
        (nativeFreshAtSlot_mem p.val.tree 0 (p.val.embed st.term.live.test.target) star)
      change (nativeFreshAtSlot p.val.tree 0 (p.val.embed st.term.live.test.target) star).tree.leaves≤r+2
      omega
    · cases hQ

theorem nativeActualResourceStep_coefficient_variation_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (op : NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r) :
    ((nativeActualResourceStep Γ hs hl op st).map (fun Q=>|Q.term.coefficient|)).sum≤
      |st.term.coefficient| *op.coefficientCost r := by
  cases op with
  | center=>
    simp [nativeActualResourceStep,NativeActualResourceState.freeze,NativeResourceTerm.freeze,
      NativeActualExpansionOp.coefficientCost,mul_two]
  | reweight c=>
    simp [nativeActualResourceStep,NativeActualResourceState.reweight,NativeResourceTerm.reweight,
      NativeActualExpansionOp.coefficientCost,abs_mul,mul_comm]
  | retarget=>
    simp [nativeActualResourceStep,NativeActualResourceState.retarget,NativeResourceTerm.retarget,
      NativeActualExpansionOp.coefficientCost]
  | projection=>
    simp [nativeActualResourceStep,NativeActualResourceState.projection,NativeResourceTerm.projection,
      NativeActualExpansionOp.coefficientCost]
  | highRow=>
    have H:=nativeActualHighExpansion_coefficient_variation_le ho Γ hΓ hs hl 1 st hr
    simpa [nativeActualResourceExpansion,nativeHighSwitchForkVariation,
      NativeActualExpansionOp.coefficientCost] using H

theorem nativeActualResourceExpansion_coefficient_variation_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (ops : List NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r) :
    ((nativeActualResourceExpansion Γ hs hl ops st).map (fun Q=>|Q.term.coefficient|)).sum≤
      |st.term.coefficient| *nativeActualExpansionVariation r ops := by
  induction ops generalizing st r with
  | nil=>simp [nativeActualResourceExpansion,nativeActualExpansionVariation]
  | cons op ops ih=>
    rw [nativeActualResourceExpansion]
    simp only [List.map_flatMap,native_sum_flatMap]
    have HI:=List.sum_le_sum (fun Q hQ=>ih Q (nativeActualResourceStep_leaves_le Γ hs hl op st Q hr hQ))
    apply HI.trans
    rw [List.sum_map_mul_right]
    have H:=mul_le_mul_of_nonneg_right
      (nativeActualResourceStep_coefficient_variation_le ho Γ hΓ hs hl op st hr)
      (nativeActualExpansionVariation_nonneg (r+2) ops)
    simpa only [nativeActualExpansionVariation,mul_assoc] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
