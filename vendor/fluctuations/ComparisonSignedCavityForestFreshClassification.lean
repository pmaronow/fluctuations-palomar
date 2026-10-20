module

public import ComparisonSignedCavityForestFreshProjectionGrouping

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_star_arm_fresh_classification (mid tail : List PositiveMass)
    (T : ClockTree S (mid++tail)) (s : T.Slot) {U : ℕ}
    (hmid : 0 < mid.length) (hU : mid.length<U)
    (hT : NativePersistentLowForks 0 mid.length U T)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (mid++tail)) :
    ∃(E : ClockTree S (mid++tail)) (D : ClockTree S tail)
      (read : E.Assignment → D.Assignment → T.Assignment) (target : D.Slot)
      (embed : T.Slot → (E.fork (exteriorPrepend mid D)).Slot),
      NativePersistentLowForks 0 mid.length U E ∧
      (∀η σ,T.atSlot (read η σ) s=D.atSlot σ target) ∧
      (∀c,T.splitIndex s c=0 → ∃e : E.Slot,∀η σ,T.atSlot (read η σ) c=E.atSlot η e) ∧
      (∀c,mid.length≤T.splitIndex s c → ∃d : D.Slot,
        (∀η σ,T.atSlot (read η σ) c=D.atSlot σ d) ∧
        mid.length+D.splitIndex target d=T.splitIndex s c) ∧
      (∀η σ c,T.atSlot (read η σ) c=(E.fork (exteriorPrepend mid D)).atSlot
        (η,(exteriorPrependAssignmentEquiv mid D).symm σ) (embed c)) ∧
      (∀c d,(E.fork (exteriorPrepend mid D)).splitIndex (embed c) (embed d)=T.splitIndex c d) ∧
      (embed s=Sum.inr ((exteriorPrependSlotEquiv mid D).symm target)) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → S → ℝ) (x : ι → ℝ),
        nativeTrunkProjectedMean w φ T s mid.length q Q x=
          (E.fork (exteriorPrepend mid (D.fork (single tail)))).expect w φ q (fun σ=>
            let z:=exteriorPrependAssignmentEquiv mid (D.fork (single tail)) σ.2
            Q (read σ.1 z.1) (singleEquiv (S:=S) tail z.2)) x) := by
  have Hmiddle:=native_group_occupied_shares_middle mid T s hU hT
  have hE:=nativeGroupRootForest_exterior_lowForks T s hT
  have hProjected : ∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → S → ℝ) (x : ι → ℝ),
      nativeTrunkProjectedMean w φ T s mid.length q Q x=
        (nativeGroupRootForest T s).exterior.expect w φ q (fun η=>
          nativeTrunkProjectedMean w φ (nativeGroupRootForest T s).occupied
            (nativeGroupRootForest T s).target mid.length q
            (fun σ d=>Q ((nativeGroupRootForest T s).read η σ) d) x) x :=
    fun q Q x=>nativeGroupRootForest_trunk_projected T s mid.length hmid hw φ ho q Q x
  have hTarget:=fun η σ=>(nativeGroupRootForest T s).read_target η σ
  have hHigh:=fun c hc=>(nativeGroupRootForest T s).read_high_relative c hc
  have has : mid++tail≠[] := by
    intro H
    have HM:=congrArg List.length (List.append_eq_nil_iff.mp H).1
    simp only [List.length_nil] at HM
    omega
  have hOutside:=fun c hc=>(nativeGroupRootForest T s).read_exterior_relative has c hc
  generalize hg:nativeGroupRootForest T s=g at Hmiddle hE hProjected hTarget hHigh hOutside
  rcases g with ⟨E,Di,ti,readi,ei,oi,hti,hoi,hri,hsi,hio,hfree⟩
  obtain ⟨D,hD⟩:=native_exists_prepend_of_trunk_split mid Di ti Hmiddle
  subst Di
  let d:=exteriorPrependSlotEquiv mid D ti
  let R:=fun η σ=>readi η ((exteriorPrependAssignmentEquiv mid D).symm σ)
  refine ⟨E,D,R,d,ei,hE,?_,?_,?_,?_,hsi,?_,?_⟩
  · intro η σ
    rw [hTarget,exteriorPrepend_atSlot]
    simp only [Equiv.apply_symm_apply]
    rfl
  · intro c hc
    obtain ⟨e,he⟩:=hOutside c hc
    exact ⟨e,fun η σ=>he η _⟩
  · intro c hc
    obtain ⟨di,hr,hs⟩:=hHigh c (by omega)
    refine ⟨exteriorPrependSlotEquiv mid D di,?_,?_⟩
    · intro η σ
      rw [hr,exteriorPrepend_atSlot]
      simp only [Equiv.apply_symm_apply]
    · simpa only [exteriorPrepend_splitIndex] using hs
  · intro η σ c
    exact hri η _ c
  · have H : ei s=Sum.inr ti := by
      calc
        _=ei (oi ti):=congrArg ei hti.symm
        _=Sum.inr ti:=hoi ti
    simpa only [d,Equiv.symm_apply_apply] using H
  · intro q Q x
    rw [hProjected,expect_fork]
    apply congrArg (fun F=>E.expect w φ q F x)
    funext η
    have H:=exteriorPrepend_trunk_projected_eq_fresh_tail mid D d hw φ ho q
      (fun σ fresh=>Q (readi η σ) fresh) x
    change nativeTrunkProjectedMean w φ (exteriorPrepend mid D)
      ((exteriorPrependSlotEquiv mid D).symm d) mid.length q
      (fun σ fresh=>Q (readi η σ) fresh) x =
      (exteriorPrepend mid (D.fork (single tail))).expect w φ q (fun σ=>
        let z:=exteriorPrependAssignmentEquiv mid (D.fork (single tail)) σ
        Q (readi η ((exteriorPrependAssignmentEquiv mid D).symm z.1))
          (singleEquiv (S:=S) tail z.2)) x at H
    simpa only [d,R,Equiv.symm_apply_apply] using H

end OAI.SKFluctuations.Cavity
