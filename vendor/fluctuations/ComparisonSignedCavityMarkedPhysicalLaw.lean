module

public import ComparisonSignedCavityPhysicalTransport
public import CavityTerminalResamplingTree
public import CavityFiniteProfileClipping
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockMassIntegral

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type*}

theorem splitIndex_cavityLeft {as : List PositiveMass} (T : ClockTree (S×B) as)
    (s t : T.Slot) :
    T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot t)=T.splitIndex s t := by
  induction T with
  | leaf => rfl
  | step a T ih => exact congrArg (1+·) (ih s t)
  | fork T V ihT ihV => cases s <;> cases t <;>
      first | rfl | exact ihT _ _ | exact ihV _ _

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeIncomingNewSlot {n : ℕ} {as : List PositiveMass}
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as)) :
    p.tree.cavityLeft.Slot := p.tree.cavityLeftSlot p.mark

def nativeIncomingOldSlot {n : ℕ} {as : List PositiveMass}
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as)) :
    p.tree.cavityLeft.Slot :=
  p.tree.cavityLeftSlot (p.embed (ClockTree.singleSlot (S := Spin n×Bool) as))

def nativeIncomingPairSplit {n : ℕ} {as : List PositiveMass}
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as)) : ℕ :=
  p.tree.cavityLeft.splitIndex (nativeIncomingNewSlot p) (nativeIncomingOldSlot p)

theorem native_incoming_pair_split_eq_original {n : ℕ} {as : List PositiveMass}
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as)) :
    nativeIncomingPairSplit p=
      p.tree.splitIndex p.mark (p.embed (ClockTree.singleSlot (S := Spin n×Bool) as)) := by
  exact p.tree.splitIndex_cavityLeft _ _

private theorem physical_clockTree_pair_eq_conditional_fork (n : ℕ)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (T : ClockTree (Spin n) as) (q : ℕ → FeatureIndex n → ℝ≥0)
    (s t : T.Slot) (hst : s≠t) (Q : Spin n → Spin n → ℝ)
    (x : FeatureIndex n → ℝ) :
    T.expect (uniformWeight n) (finiteFeature n) q
      (fun σ=>Q (T.atSlot σ s) (T.atSlot σ t)) x=
      ∫ z, conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as q) (fun _ : Unit=>x) (T.splitIndex s t)
        (terminalPairTest (clockSteps as q) Q) ((),z)
        ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (clockSteps as q) x := by
  rw [T.expect_pairAtSlot (uniformWeight_pos n) (finiteFeature n) ho q s t hst Q x,
    ClockTree.pairMean_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n) as ho]
  symm
  exact integral_terminal_fork_fixed_root (uniformWeight_pos n) (finiteFeature n)
    (clockSteps as q) (clockSteps_ordered ho q) (fun _ : Unit=>x) () _
    (by simpa only [length_clockSteps] using T.splitIndex_le_clockLength s t) Q

theorem native_marked_rest_pair_eq_conditional_fork (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hst : nativeIncomingNewSlot p≠nativeIncomingOldSlot p)
    (Q : Spin n → Spin n → ℝ) :
    p.tree.cavityLeft.expect (restWeight n) (restFeature n) q
      (fun σ=>Q (p.restSpin σ) (nativeAttachmentOld p σ)) x=
      ∫ z, conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as (fun j=>restFiniteVariance n (q j)))
        (fun _ : Unit=>restFiniteState n x) (nativeIncomingPairSplit p)
        (terminalPairTest (clockSteps as (fun j=>restFiniteVariance n (q j))) Q) ((),z)
        ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n)
          (clockSteps as (fun j=>restFiniteVariance n (q j))) (restFiniteState n x) := by
  rw [restFinite_clockTree_expect n hn]
  exact physical_clockTree_pair_eq_conditional_fork n ho p.tree.cavityLeft
    (fun j=>restFiniteVariance n (q j)) (nativeIncomingNewSlot p) (nativeIncomingOldSlot p)
    hst Q (restFiniteState n x)

theorem native_incoming_projection_fourth_eq_conditional_fork (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hst : nativeIncomingNewSlot p≠nativeIncomingOldSlot p) :
    nativeIncomingProjectionFourth n q x center p=
      ((n:ℝ)/(n+1 : ℕ))^4*
      ∫ z, conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as (fun j=>restFiniteVariance n (q j)))
        (fun _ : Unit=>restFiniteState n x) (nativeIncomingPairSplit p)
        (terminalPairTest (clockSteps as (fun j=>restFiniteVariance n (q j)))
          (fun σ τ=>(physicalProjectedBoundaryOverlap n
              (clockSteps as (fun j=>restFiniteVariance n (q j))) σ (restFiniteState n x)-
            physicalProjectedBoundaryOverlap n
              (clockSteps as (fun j=>restFiniteVariance n (q j))) τ (restFiniteState n x))^4))
        ((),z) ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n)
          (clockSteps as (fun j=>restFiniteVariance n (q j))) (restFiniteState n x) := by
  rw [native_incoming_projection_fourth_eq_physical n hn ho q x center p]
  congr 1
  exact physical_clockTree_pair_eq_conditional_fork n ho p.tree.cavityLeft
    (fun j=>restFiniteVariance n (q j)) (nativeIncomingNewSlot p) (nativeIncomingOldSlot p)
    hst (fun σ τ=>(physicalProjectedBoundaryOverlap n
        (clockSteps as (fun j=>restFiniteVariance n (q j))) σ (restFiniteState n x)-
      physicalProjectedBoundaryOverlap n
        (clockSteps as (fun j=>restFiniteVariance n (q j))) τ (restFiniteState n x))^4)
    (restFiniteState n x)

theorem native_incoming_anchor_fourth_eq_conditional_fork (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (E : ClockTree (Spin n) as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hst : nativeIncomingNewSlot p≠nativeIncomingOldSlot p) :
    nativeIncomingAnchorFourth n E H s q x p=
      ((n:ℝ)/(n+1 : ℕ))^4*
      ∫ z, conditionalForkTest (uniformWeight n) (finiteFeature n)
        (clockSteps as (fun j=>restFiniteVariance n (q j)))
        (fun _ : Unit=>restFiniteState n x) (nativeIncomingPairSplit p)
        (terminalPairTest (clockSteps as (fun j=>restFiniteVariance n (q j)))
          (fun σ τ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-
              WithLp.toLp 2 (normalizedSpin n σ))
            (physicalWeightedExteriorAnchor n
              (E.realize (fun j=>restFiniteVariance n (q j)))
              (fun η=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (q j))).symm η))
              (E.slotEquiv (fun j=>restFiniteVariance n (q j)) s) (restFiniteState n x)))^4))
        ((),z) ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n)
          (clockSteps as (fun j=>restFiniteVariance n (q j))) (restFiniteState n x) := by
  rw [native_incoming_anchor_fourth_eq_physical n hn E H s q x p]
  congr 1
  exact physical_clockTree_pair_eq_conditional_fork n ho p.tree.cavityLeft
    (fun j=>restFiniteVariance n (q j)) (nativeIncomingNewSlot p) (nativeIncomingOldSlot p)
    hst (fun σ τ=>(inner ℝ (WithLp.toLp 2 (normalizedSpin n τ)-
        WithLp.toLp 2 (normalizedSpin n σ))
      (physicalWeightedExteriorAnchor n
        (E.realize (fun j=>restFiniteVariance n (q j)))
        (fun η=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (q j))).symm η))
        (E.slotEquiv (fun j=>restFiniteVariance n (q j)) s) (restFiniteState n x)))^4)
    (restFiniteState n x)

theorem native_incoming_projection_fourth_zero_of_coincident (n : ℕ)
    {as : List PositiveMass} (q : ℕ → RestCoordinate n → ℝ≥0)
    (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hst : nativeIncomingNewSlot p=nativeIncomingOldSlot p) :
    nativeIncomingProjectionFourth n q x center p=0 := by
  have he (σ : p.tree.cavityLeft.Assignment) : p.restSpin σ=nativeAttachmentOld p σ :=
    congrArg (p.tree.cavityLeft.atSlot σ) hst
  unfold nativeIncomingProjectionFourth nativeIncomingProjectionDifference ClockTree.expect
  simp only [he,sub_self,zero_pow (by norm_num : (4:ℕ)≠0),mul_zero,Finset.sum_const_zero]

theorem native_incoming_anchor_fourth_zero_of_coincident (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hst : nativeIncomingNewSlot p=nativeIncomingOldSlot p) :
    nativeIncomingAnchorFourth n E H s q x p=0 := by
  have he (σ : p.tree.cavityLeft.Assignment) : p.restSpin σ=nativeAttachmentOld p σ :=
    congrArg (p.tree.cavityLeft.atSlot σ) hst
  unfold nativeIncomingAnchorFourth nativeIncomingAnchorDifference ClockTree.expect
  simp only [he,sub_self,inner_zero_left,zero_pow (by norm_num : (4:ℕ)≠0),
    mul_zero,Finset.sum_const_zero]

end OAI.SKFluctuations.Cavity
