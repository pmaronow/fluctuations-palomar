module

public import ComparisonSignedCavitySecondLowJointErrorAllocation
public import ComparisonSignedCavityForestObservedHighGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 24000000

theorem native_second_low_joint_rest_test_final_slots (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} (P : T.cavityLeft.Assignment→ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (τ : t.tree.cavityLeft.Assignment) :
    let f:=t.embed (s.embed (r.embed p.mark))
    let c:=t.embed (s.embed r.mark)
    let e:=t.embed s.mark
    let d:=t.mark
    nativeSecondLowJointRestTest n U b h K P p r s t τ=
      nativeSecondLowOldTest P p r s t τ*
        (restLowKernel n U b h (t.tree.splitIndex f c)
            (t.tree.cavityLeft.atSlot τ (t.tree.cavityLeftSlot f))
            (t.tree.cavityLeft.atSlot τ (t.tree.cavityLeftSlot c))*
          restLowKernel n U b h (t.tree.splitIndex e d)
            (t.tree.cavityLeft.atSlot τ (t.tree.cavityLeftSlot e))
            (t.tree.cavityLeft.atSlot τ (t.tree.cavityLeftSlot d))-
          nativeSecondLowScalarValue U K (t.tree.splitIndex f c)*
            nativeSecondLowScalarValue U K (t.tree.splitIndex e d)) := by
  dsimp only
  rw [native_second_low_joint_rest_test_product]
  simp only [MarkedPlacement.restSpin,MarkedPlacement.restRestrict_at,
    (s.tree.markedAttach_embed_preserves 0 t ht).2,
    (r.tree.markedAttach_embed_preserves 0 s hs).2,nativeSecondLowOldTest]

theorem native_second_low_joint_rest_word_abs_le (n : ℕ) (hn : 0<n)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (hU : U≤as.length) (Hfc : r.tree.splitIndex (r.embed p.mark) r.mark<U)
    (Hed : t.tree.splitIndex (t.embed s.mark) t.mark<U)
    {C : ℝ} (hC : 0≤C) (E R : ℕ→ℝ) (hE : ∀j,0≤E j) (hR : ∀j,0<R j)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q (fun τ=>|P τ|^4) 0≤C^4)
    (hError : ∀j,j< U→(pairClock as j).disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>(nativeSecondLowErrorKernel n U b h K j (pairSpin as j τ).1 (pairSpin as j τ).2)^2) 0≤(E j)^2)
    (hRaw : ∀j,j< U→(pairClock as j).disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>|restLowKernel n U b h j (pairSpin as j τ).1 (pairSpin as j τ).2|^4) 0≤(R j)^4) :
    |t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeSecondLowJointRestTest n U b h K P p r s t) 0|≤
      C*(E (r.tree.splitIndex (r.embed p.mark) r.mark)*R (t.tree.splitIndex (t.embed s.mark) t.mark)+
        |nativeSecondLowScalarValue U K (r.tree.splitIndex (r.embed p.mark) r.mark)| *
          E (t.tree.splitIndex (t.embed s.mark) t.mark)) := by
  let f:=t.tree.cavityLeftSlot (t.embed (s.embed (r.embed p.mark)))
  let c:=t.tree.cavityLeftSlot (t.embed (s.embed r.mark))
  let e:=t.tree.cavityLeftSlot (t.embed s.mark)
  let d:=t.tree.cavityLeftSlot t.mark
  have Hfcs : t.tree.cavityLeft.splitIndex f c=r.tree.splitIndex (r.embed p.mark) r.mark := by
    rw [cavityLeft_splitIndex,(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
  have Heds : t.tree.cavityLeft.splitIndex e d=t.tree.splitIndex (t.embed s.mark) t.mark := by
    rw [cavityLeft_splitIndex]
  have Hneq (u v : t.tree.cavityLeft.Slot) (H : t.tree.cavityLeft.splitIndex u v<U) : u≠v := by
    intro HH
    rw [HH,t.tree.cavityLeft.splitIndex_self] at H
    omega
  have Hfcn : f≠c:=Hneq f c (Hfcs ▸ Hfc)
  have Hedn : e≠d:=Hneq e d (Heds ▸ Hed)
  have HPold : t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun τ=>|nativeSecondLowOldTest P p r s t τ|^4) 0≤C^4 := by
    rw [native_second_low_old_test_moment_preserved n q U b h K T ho P 4 p hp r hr s hs t ht]
    exact hP
  have H:=native_second_low_product_difference_from_pair_moments n hn t.tree.cavityLeft ho q
    (nativeSecondLowOldTest P p r s t) (restLowKernel n U b h) (nativeSecondLowScalarValue U K)
    f c e d Hfcn Hedn hC (hE (t.tree.cavityLeft.splitIndex f c))
    (hE (t.tree.cavityLeft.splitIndex e d)) (hR (t.tree.cavityLeft.splitIndex e d)) HPold
    (by rw [Hfcs];exact hError _ Hfc)
    (by rw [Heds];exact hError _ Hed)
    (by rw [Heds];exact hRaw _ Hed)
  have Heq : nativeSecondLowJointRestTest n U b h K P p r s t=
      fun τ=>nativeSecondLowOldTest P p r s t τ*
        (restLowKernel n U b h (t.tree.cavityLeft.splitIndex f c)
          (t.tree.cavityLeft.atSlot τ f) (t.tree.cavityLeft.atSlot τ c)*
        restLowKernel n U b h (t.tree.cavityLeft.splitIndex e d)
          (t.tree.cavityLeft.atSlot τ e) (t.tree.cavityLeft.atSlot τ d)-
        nativeSecondLowScalarValue U K (t.tree.cavityLeft.splitIndex f c)*
          nativeSecondLowScalarValue U K (t.tree.cavityLeft.splitIndex e d)) := by
    funext τ
    dsimp only [f,c,e,d]
    simpa only [cavityLeft_splitIndex] using native_second_low_joint_rest_test_final_slots n U b h K P p r s hs t ht τ
  rw [Heq]
  simpa only [Hfcs,Heds] using H

end OAI.SKFluctuations.Cavity
