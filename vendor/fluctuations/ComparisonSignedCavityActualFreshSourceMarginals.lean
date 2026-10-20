module

public import ComparisonSignedCavityObservedFullFreshAnchorSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι]

theorem native_marked_expect_marginal {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (q : ℕ → ι → ℝ≥0) (G : T.Assignment → ℝ) (x : ι → ℝ) :
    p.tree.expect w φ q (fun σ=>G (p.restrict σ)) x=T.expect w φ q G x := by
  have hm : p.realize q∈(T.realize q).markedAttach a := by
    rw [←T.markedAttach_realize a q]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have H:=(T.realize q).markedAttach_preserves hw φ (clockSteps_ordered ho q)
    (p.realize q) hm (fun σ=>G ((T.assignmentEquiv q).symm σ)) x
  rw [p.tree.expect_realize,T.expect_realize]
  simpa only [MarkedPlacement.realize,Equiv.symm_apply_apply] using H

theorem native_marked_disorder_marginal {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (G : T.Assignment → ℝ) (x : ι → ℝ) :
    p.tree.disorderExpect w φ v q (fun σ=>G (p.restrict σ)) x=T.disorderExpect w φ v q G x := by
  rw [p.tree.disorderExpect_integral hw φ ho,T.disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>native_marked_expect_marginal T ho p hp hw φ _ G (x+y))

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_twin_conditional_old_test (n : ℕ)
    {ias tail : List PositiveMass} (A : ClockTree (Spin n) ias) (Bold D : ClockTree (Spin n) tail)
    {a : ℝ} (ho : MassOrdered a tail) (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (G : A.Assignment → Bold.Assignment → D.Assignment → ℝ)
    (xi xB xD : RestCoordinate n → ℝ) :
    nativeTwinForestConditionalTest A (Bold.fork (single tail)) D (restWeight n) (restFeature n)
      qi qs (fun η β δ=>G η β.1 δ) xi xB xD=
    A.expect (restWeight n) (restFeature n) qi (fun η=>
      Bold.expect (restWeight n) (restFeature n) qs (fun β=>
        D.expect (restWeight n) (restFeature n) qs (G η β) xD) xB) xi := by
  unfold nativeTwinForestConditionalTest
  simp only [expect_fork]
  simp_rw [expect_const (restWeight_pos n) (restFeature n) (single tail) ho qs]

def NativeActualFullFreshAnchorMomentLaw (n : ℕ) (pre mid tail : List PositiveMass)
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
            ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x) ∧
      (∀G : T.cavityLeft.Assignment → ℝ,
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q G x=
          ∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
            Bold.expect (restWeight n) (restFeature n) qs (fun β=>
              D.expect (restWeight n) (restFeature n) qs (fun δ=>G (read η β δ))
                (twinPrefixDRoot z)) (twinPrefixBRoot z)) (twinPrefixSharedRoot z)
            ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)

theorem native_actual_full_fresh_anchor_with_old_moments
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length) (hse : U≤T.splitIndex s e)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    NativeActualFullFreshAnchorMomentLaw n pre mid tail T s e b a v q x := by
  have hS : T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot b)=pre.length := by
    simpa only [cavityLeft_splitIndex] using hsb
  have hE : U≤T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot e) := by
    simpa only [cavityLeft_splitIndex] using hse
  have hFactory:=native_actual_fresh_two_arm_disorder_factory pre mid tail T.cavityLeft
    (T.cavityLeftSlot s) (T.cavityLeftSlot b) hmid hU hT.cavityLeft hS
    (restWeight_pos n) (restFeature n) ho v q x
  unfold NativeActualFreshTwoArmLaw at hFactory
  obtain ⟨A,Bold,D,read,tb,td,htB,htD,hHigh,hExact,hConditional⟩:=hFactory
  obtain ⟨de,htE,hSplit⟩:=hHigh (T.cavityLeftSlot e) (lt_of_lt_of_le hU hE)
  unfold NativeActualFullFreshAnchorMomentLaw
  refine ⟨A,Bold,D,read,td,de,htD,htE,?_,?_,?_⟩
  · simpa only [cavityLeft_splitIndex] using hSplit
  · intro Z
    rw [nativeFreshAtSlot_full_rest_disorder_transport T a b (pre.length+mid.length)
      (restWeight_pos n) (restFeature n) ho v q (fun σ f=>Z σ*
        (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false)) (joinSpin (f,false))-
          deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false)) (joinSpin (f,false)))) x]
    rw [hExact (fun σ f=>Z σ*
      (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false)) (joinSpin (f,false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false)) (joinSpin (f,false))))]
    simp_rw [htD,htE]
    have H:=native_twin_source_fresh_anchor_difference n pre mid A Bold (single tail) D
      (singleSlot tail) ho v q (fun η β δ=>Z (read η β δ))
      (fun δ=>D.atSlot δ td) (fun δ=>D.atSlot δ de) x
    simpa only [single_atSlot] using H
  · intro G
    let p:=nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot b) (pre.length+mid.length)
    have HM:=native_marked_disorder_marginal T.cavityLeft ho p
      (nativeFreshAtSlot_mem T.cavityLeft a (T.cavityLeftSlot b) (pre.length+mid.length))
      (restWeight_pos n) (restFeature n) v q G x
    rw [←HM,hConditional (fun σ _=>G σ)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z=>native_twin_conditional_old_test n A Bold D ho.suffix_end.suffix_end _ _
      (fun η β δ=>G (read η β δ)) (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z))

end OAI.SKFluctuations.Cavity
