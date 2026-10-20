module

public import ComparisonSignedCavityForestObservedSameFreshLaw
public import ComparisonSignedCavityTwinFreshAnchor

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_same_conditional_fresh_anchor_difference (n : ℕ)
    {ias tas : List PositiveMass} (A : ClockTree (Spin n) ias)
    (Bold Fresh D : ClockTree (Spin n) tas) (s : Fresh.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (Z : A.Assignment → Bold.Assignment → D.Assignment → ℝ)
    (old new : D.Assignment → Spin n) (xi xs : RestCoordinate n → ℝ) :
    nativeExteriorForestConditionalTest A (Bold.fork Fresh) D (restWeight n) (restFeature n) qi qs
      (fun η β δ => Z η β.1 δ*
        (deletedOverlap n (joinSpin (old δ,false)) (joinSpin (Fresh.atSlot β.2 s,false))-
          deletedOverlap n (joinSpin (new δ,false)) (joinSpin (Fresh.atSlot β.2 s,false)))) xi xs =
    A.expect (restWeight n) (restFeature n) qi (fun η =>
      Bold.expect (restWeight n) (restFeature n) qs (fun β =>
        D.expect (restWeight n) (restFeature n) qs (fun δ => Z η β δ*inner ℝ
          (WithLp.toLp 2 (normalizedSpin n (old δ))-WithLp.toLp 2 (normalizedSpin n (new δ)))
          (nativeWeightedExteriorAnchor n Fresh (fun _ => 1) s qs xs)) xs) xs) xi := by
  rw [nativeExteriorForestConditionalTest_eq_joint]
  simp only [ClockTree.expect_fork]
  apply congrArg (fun R=>A.expect (restWeight n) (restFeature n) qi R xi)
  funext η
  exact native_joint_old_fresh_anchor_difference n Bold Fresh D s qs qs qs xs xs (Z η) old new

def NativeActualSameFreshAnchorLaw (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n) (pre++(mid++tail))) (s e b : T.Slot)
    (a : ℝ) (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ) : Prop :=
    let p:=nativeFreshAtSlot T a b (pre.length+mid.length)
    let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
    let qs:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j))
    ∃(A : ClockTree (Spin n) (mid++tail)) (Bold D : ClockTree (Spin n) tail)
      (read : A.Assignment → Bold.Assignment → D.Assignment → T.Assignment)
      (td de : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ td) ∧
      (∀η β δ,T.atSlot (read η β δ) e=D.atSlot δ de) ∧
      pre.length+mid.length+D.splitIndex td de=T.splitIndex s e ∧
      (∀Z : T.Assignment → ℝ,
        p.tree.disorderExpect (restWeight n) (restFeature n) v q (fun σ=>
          Z (p.restrict σ)*
            (deletedOverlap n (joinSpin (T.atSlot (p.restrict σ) s,false))
                (joinSpin (p.spin σ,false))-
              deletedOverlap n (joinSpin (T.atSlot (p.restrict σ) e,false))
                (joinSpin (p.spin σ,false)))) x=
          ∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
            Bold.expect (restWeight n) (restFeature n) qs (fun β=>
              D.expect (restWeight n) (restFeature n) qs (fun δ=>Z (read η β δ)*inner ℝ
                (WithLp.toLp 2 (normalizedSpin n (D.atSlot δ td))-
                  WithLp.toLp 2 (normalizedSpin n (D.atSlot δ de)))
                (nativeWeightedExteriorAnchor n (single tail) (fun _=>1) (singleSlot tail) qs
                  (exteriorForestStarRoot z))) (exteriorForestStarRoot z)) (exteriorForestStarRoot z))
                    (exteriorForestIRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)

theorem native_actual_fresh_same_arm_anchor_source (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n) (pre++(mid++tail))) (s e b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hlen : U ≤ pre.length+mid.length+tail.length)
    (hsb : T.splitIndex s b=pre.length+mid.length) (hse : U ≤ T.splitIndex s e)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ) :
    NativeActualSameFreshAnchorLaw n pre mid tail T s e b a v q x := by
  have hFactory:=native_actual_fresh_same_arm_disorder_factory pre mid tail T s b hmid hU hlen hT hsb
    (restWeight_pos n) (restFeature n) ho v q x
  unfold NativeActualFreshSameArmLaw at hFactory
  obtain ⟨A,Bold,D,read,tb,td,htB,htD,hHigh,hExact,hConditional⟩:=hFactory
  obtain ⟨de,htE,hSplit⟩:=hHigh e (lt_of_lt_of_le hU hse)
  unfold NativeActualSameFreshAnchorLaw
  refine ⟨A,Bold,D,read,td,de,htD,htE,hSplit,?_⟩
  intro Z
  rw [hConditional (fun σ f=>Z σ*
    (deletedOverlap n (joinSpin (T.atSlot σ s,false)) (joinSpin (f,false))-
      deletedOverlap n (joinSpin (T.atSlot σ e,false)) (joinSpin (f,false))))]
  simp_rw [htD,htE]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have hAnchor:=native_same_conditional_fresh_anchor_difference n A Bold (single tail) D
    (singleSlot tail)
    (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
    (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
    (fun η β δ=>Z (read η β δ))
    (fun δ=>D.atSlot δ td) (fun δ=>D.atSlot δ de)
    (exteriorForestIRoot z) (exteriorForestStarRoot z)
  simpa only [single_atSlot] using hAnchor

theorem native_physical_generated_observed_same_fresh_anchor_source
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
    NativeActualSameFreshAnchorLaw n pre mid tail p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot p.mark)
      (p.tree.cavityLeftSlot (p.embed b)) a₀ v q x := by
  have hSource:=hP.persistentLowForks.observedRestHigh (by omega) hU a p hp c hh
  have hSplit : p.tree.cavityLeft.splitIndex
      (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot (p.embed b))=pre.length+mid.length := by
    rw [cavityLeft_splitIndex,(T.markedAttach_embed_preserves a p hp).2,hcb]
  have hHigh : U ≤ p.tree.cavityLeft.splitIndex
      (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot p.mark) := by
    rw [cavityLeft_splitIndex,p.tree.splitIndex_symm]
    exact hh
  have hlen : U ≤ pre.length+mid.length+tail.length := by
    have H:=hHigh.trans (p.tree.cavityLeft.splitIndex_le_clockLength
      (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot p.mark))
    simpa only [List.length_append,Nat.add_assoc] using H
  exact native_actual_fresh_same_arm_anchor_source n pre mid tail p.tree.cavityLeft
    (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot p.mark)
    (p.tree.cavityLeftSlot (p.embed b)) hmid hU hSource hlen hSplit hHigh ho v q x

end OAI.SKFluctuations.Cavity
