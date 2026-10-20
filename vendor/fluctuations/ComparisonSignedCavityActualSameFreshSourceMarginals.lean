module

public import ComparisonSignedCavityActualFreshSourceMarginals

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_same_conditional_old_test (n : ℕ)
    {ias tail : List PositiveMass} (A : ClockTree (Spin n) ias) (Bold D : ClockTree (Spin n) tail)
    {a : ℝ} (ho : MassOrdered a tail) (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (G : A.Assignment → Bold.Assignment → D.Assignment → ℝ)
    (xi xs : RestCoordinate n → ℝ) :
    nativeExteriorForestConditionalTest A (Bold.fork (single tail)) D (restWeight n) (restFeature n)
      qi qs (fun η β δ=>G η β.1 δ) xi xs=
    A.expect (restWeight n) (restFeature n) qi (fun η=>
      Bold.expect (restWeight n) (restFeature n) qs (fun β=>
        D.expect (restWeight n) (restFeature n) qs (G η β) xs) xs) xi := by
  rw [nativeExteriorForestConditionalTest_eq_joint]
  simp only [expect_fork]
  simp_rw [expect_const (restWeight_pos n) (restFeature n) (single tail) ho qs]

def NativeActualFullSameFreshAnchorMomentLaw (n : ℕ) (pre mid tail : List PositiveMass)
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
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x) ∧
      (∀G : T.cavityLeft.Assignment → ℝ,
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q G x=
          ∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
            Bold.expect (restWeight n) (restFeature n) qs (fun β=>
              D.expect (restWeight n) (restFeature n) qs (fun δ=>G (read η β δ))
                (exteriorForestStarRoot z)) (exteriorForestStarRoot z)) (exteriorForestIRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)

theorem native_actual_full_same_fresh_anchor_with_old_moments
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length+mid.length) (hse : U≤T.splitIndex s e)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    NativeActualFullSameFreshAnchorMomentLaw n pre mid tail T s e b a v q x := by
  have hS : T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot b)=pre.length+mid.length := by
    simpa only [cavityLeft_splitIndex] using hsb
  have hE : U≤T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot e) := by
    simpa only [cavityLeft_splitIndex] using hse
  have hlen : U≤pre.length+mid.length+tail.length := by
    have H:=hE.trans (T.cavityLeft.splitIndex_le_clockLength (T.cavityLeftSlot s) (T.cavityLeftSlot e))
    simpa only [List.length_append,Nat.add_assoc] using H
  have hFactory:=native_actual_fresh_same_arm_disorder_factory pre mid tail T.cavityLeft
    (T.cavityLeftSlot s) (T.cavityLeftSlot b) hmid hU hlen hT.cavityLeft hS
    (restWeight_pos n) (restFeature n) ho v q x
  unfold NativeActualFreshSameArmLaw at hFactory
  obtain ⟨A,Bold,D,read,tb,td,htB,htD,hHigh,hExact,hConditional⟩:=hFactory
  obtain ⟨de,htE,hSplit⟩:=hHigh (T.cavityLeftSlot e) (lt_of_lt_of_le hU hE)
  unfold NativeActualFullSameFreshAnchorMomentLaw
  refine ⟨A,Bold,D,read,td,de,htD,htE,?_,?_,?_⟩
  · simpa only [cavityLeft_splitIndex] using hSplit
  · intro Z
    rw [nativeFreshAtSlot_full_rest_disorder_transport T a b (pre.length+mid.length)
      (restWeight_pos n) (restFeature n) ho v q (fun σ f=>Z σ*
        (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false)) (joinSpin (f,false))-
          deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false)) (joinSpin (f,false)))) x]
    rw [hConditional (fun σ f=>Z σ*
      (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false)) (joinSpin (f,false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false)) (joinSpin (f,false))))]
    simp_rw [htD,htE]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    have H:=native_same_conditional_fresh_anchor_difference n A Bold (single tail) D (singleSlot tail)
      (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
      (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
      (fun η β δ=>Z (read η β δ)) (fun δ=>D.atSlot δ td) (fun δ=>D.atSlot δ de)
      (exteriorForestIRoot z) (exteriorForestStarRoot z)
    simpa only [single_atSlot] using H
  · intro G
    let p:=nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot b) (pre.length+mid.length)
    have HM:=native_marked_disorder_marginal T.cavityLeft ho p
      (nativeFreshAtSlot_mem T.cavityLeft a (T.cavityLeftSlot b) (pre.length+mid.length))
      (restWeight_pos n) (restFeature n) v q G x
    rw [←HM,hConditional (fun σ _=>G σ)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z=>native_same_conditional_old_test n A Bold D ho.suffix_end.suffix_end _ _
      (fun η β δ=>G (read η β δ)) (exteriorForestIRoot z) (exteriorForestStarRoot z))

end OAI.SKFluctuations.Cavity
