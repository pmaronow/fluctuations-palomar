module

public import ComparisonSignedCavityObservedFreshAnchorSource
public import ComparisonSignedCavityObservedSameFreshAnchorSource
public import ComparisonSignedCavityForestFullFreshRestTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def NativeActualFullFreshAnchorLaw (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot)
    (a : ℝ) (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ) : Prop :=
    let p:=nativeFreshAtSlot T a b (pre.length+mid.length)
    let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
    let qs:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j))
    ∃(A : ClockTree (Spin n) (mid++tail)) (Bold D : ClockTree (Spin n) tail)
      (read : A.Assignment → Bold.Assignment → D.Assignment → T.cavityLeft.Assignment)
      (td de : D.Slot),
      (∀η β δ,T.cavityLeft.atSlot (read η β δ) (T.cavityLeftSlot s)=D.atSlot δ td) ∧
      (∀η β δ,T.cavityLeft.atSlot (read η β δ) (T.cavityLeftSlot e)=D.atSlot δ de) ∧
      pre.length+mid.length+D.splitIndex td de=T.splitIndex s e ∧
      (∀Z : T.cavityLeft.Assignment → ℝ,
        p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q (fun σ=>
          Z (p.restRestrict σ)*
            (deletedOverlap n (joinSpin (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s),false))
                (joinSpin (p.restSpin σ,false))-
              deletedOverlap n (joinSpin (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot e),false))
                (joinSpin (p.restSpin σ,false)))) x=
          ∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
            Bold.expect (restWeight n) (restFeature n) qs (fun β=>
              D.expect (restWeight n) (restFeature n) qs (fun δ=>Z (read η β δ)*inner ℝ
                (WithLp.toLp 2 (normalizedSpin n (D.atSlot δ td))-
                  WithLp.toLp 2 (normalizedSpin n (D.atSlot δ de)))
                (nativeWeightedExteriorAnchor n (single tail) (fun _=>1) (singleSlot tail) qs
                  (twinPrefixBRoot z))) (twinPrefixDRoot z)) (twinPrefixBRoot z))
                    (twinPrefixSharedRoot z)
            ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)

theorem native_full_fresh_anchor_source_transport (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ)
    (hLaw : NativeActualFreshAnchorLaw n pre mid tail T.cavityLeft
      (T.cavityLeftSlot s) (T.cavityLeftSlot e) (T.cavityLeftSlot b) a v q x) :
    NativeActualFullFreshAnchorLaw n pre mid tail T s e b a v q x := by
  unfold NativeActualFreshAnchorLaw at hLaw
  obtain ⟨A,Bold,D,read,td,de,htD,htE,hSplit,hResidual⟩:=hLaw
  unfold NativeActualFullFreshAnchorLaw
  refine ⟨A,Bold,D,read,td,de,htD,htE,?_,?_⟩
  · simpa only [cavityLeft_splitIndex] using hSplit
  · intro Z
    rw [nativeFreshAtSlot_full_rest_disorder_transport T a b (pre.length+mid.length)
      (restWeight_pos n) (restFeature n) ho v q (fun σ f=>Z σ*
        (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false))
          (joinSpin (f,false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false))
          (joinSpin (f,false)))) x]
    exact hResidual Z

theorem native_physical_generated_observed_full_fresh_anchor_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativePhysicalResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c b : T.Slot) (hh : U ≤ p.tree.splitIndex p.mark (p.embed c))
    (hcb : T.splitIndex c b=pre.length)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ) :
    NativeActualFullFreshAnchorLaw n pre mid tail p.tree (p.embed c) p.mark (p.embed b) a₀ v q x := by
  exact native_full_fresh_anchor_source_transport n pre mid tail p.tree (p.embed c) p.mark (p.embed b) ho v q x
    (native_physical_generated_observed_fresh_anchor_source n pre mid tail hP hmid hU a p hp c b hh hcb ho v q x)

def NativeActualFullSameFreshAnchorLaw (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot)
    (a : ℝ) (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ) : Prop :=
    let p:=nativeFreshAtSlot T a b (pre.length+mid.length)
    let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
    let qs:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j))
    ∃(A : ClockTree (Spin n) (mid++tail)) (Bold D : ClockTree (Spin n) tail)
      (read : A.Assignment → Bold.Assignment → D.Assignment → T.cavityLeft.Assignment)
      (td de : D.Slot),
      (∀η β δ,T.cavityLeft.atSlot (read η β δ) (T.cavityLeftSlot s)=D.atSlot δ td) ∧
      (∀η β δ,T.cavityLeft.atSlot (read η β δ) (T.cavityLeftSlot e)=D.atSlot δ de) ∧
      pre.length+mid.length+D.splitIndex td de=T.splitIndex s e ∧
      (∀Z : T.cavityLeft.Assignment → ℝ,
        p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q (fun σ=>
          Z (p.restRestrict σ)*
            (deletedOverlap n (joinSpin (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s),false))
                (joinSpin (p.restSpin σ,false))-
              deletedOverlap n (joinSpin (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot e),false))
                (joinSpin (p.restSpin σ,false)))) x=
          ∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
            Bold.expect (restWeight n) (restFeature n) qs (fun β=>
              D.expect (restWeight n) (restFeature n) qs (fun δ=>Z (read η β δ)*inner ℝ
                (WithLp.toLp 2 (normalizedSpin n (D.atSlot δ td))-
                  WithLp.toLp 2 (normalizedSpin n (D.atSlot δ de)))
                (nativeWeightedExteriorAnchor n (single tail) (fun _=>1) (singleSlot tail) qs
                  (exteriorForestStarRoot z))) (exteriorForestStarRoot z)) (exteriorForestStarRoot z))
                    (exteriorForestIRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)

theorem native_full_fresh_same_anchor_source_transport (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ)
    (hLaw : NativeActualSameFreshAnchorLaw n pre mid tail T.cavityLeft
      (T.cavityLeftSlot s) (T.cavityLeftSlot e) (T.cavityLeftSlot b) a v q x) :
    NativeActualFullSameFreshAnchorLaw n pre mid tail T s e b a v q x := by
  unfold NativeActualSameFreshAnchorLaw at hLaw
  obtain ⟨A,Bold,D,read,td,de,htD,htE,hSplit,hResidual⟩:=hLaw
  unfold NativeActualFullSameFreshAnchorLaw
  refine ⟨A,Bold,D,read,td,de,htD,htE,?_,?_⟩
  · simpa only [cavityLeft_splitIndex] using hSplit
  · intro Z
    rw [nativeFreshAtSlot_full_rest_disorder_transport T a b (pre.length+mid.length)
      (restWeight_pos n) (restFeature n) ho v q (fun σ f=>Z σ*
        (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false))
          (joinSpin (f,false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false))
          (joinSpin (f,false)))) x]
    exact hResidual Z

theorem native_physical_generated_observed_full_same_fresh_anchor_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativePhysicalResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c b : T.Slot) (hh : U ≤ p.tree.splitIndex p.mark (p.embed c))
    (hcb : T.splitIndex c b=pre.length+mid.length)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ) :
    NativeActualFullSameFreshAnchorLaw n pre mid tail p.tree (p.embed c) p.mark (p.embed b) a₀ v q x := by
  exact native_full_fresh_same_anchor_source_transport n pre mid tail p.tree (p.embed c) p.mark (p.embed b) ho v q x
    (native_physical_generated_observed_same_fresh_anchor_source n pre mid tail hP hmid hU a p hp c b hh hcb ho v q x)

end OAI.SKFluctuations.Cavity
