module

public import ComparisonSignedCavityForestFreshClassification

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_two_arm_fresh_factory
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(A : ClockTree S (mid++tail)) (Bold D : ClockTree S tail)
      (read : A.Assignment → Bold.Assignment → D.Assignment → T.Assignment)
      (targetB : Bold.Slot) (targetD : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) b=Bold.atSlot β targetB) ∧
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ targetD) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η β δ,T.atSlot (read η β δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex targetD d=T.splitIndex s c) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → S → ℝ) (x : ι → ℝ),
        let V:=A.fork ((exteriorPrepend mid (Bold.fork (single tail))).fork (exteriorPrepend mid D))
        nativeTrunkProjectedMean w φ T b (pre.length+mid.length) q Q x=
          (exteriorPrepend pre V).expect w φ q (fun σ=>
            let z:=exteriorPrependAssignmentEquiv pre V σ
            let β:=exteriorPrependAssignmentEquiv mid (Bold.fork (single tail)) z.2.1
            let δ:=exteriorPrependAssignmentEquiv mid D z.2.2
            Q (read z.1 β.1 δ) (singleEquiv (S:=S) tail β.2)) x) := by
  have Hpre : ∀c,pre.length≤T.splitIndex b c := by
    intro c
    rcases hT b c with H|H|H <;> omega
  obtain ⟨Ti,hpre⟩:=native_exists_prepend_of_trunk_split pre T b Hpre
  subst T
  let si:=exteriorPrependSlotEquiv pre Ti s
  let bi:=exteriorPrependSlotEquiv pre Ti b
  have hTi:=NativePersistentLowForks.strip_prefix pre mid Ti hU hT
  have hbi : Ti.splitIndex si bi=0 := by
    have HS:=exteriorPrepend_splitIndex pre Ti s b
    dsimp only [si,bi] at *
    omega
  obtain ⟨Ei,Bold,RB,tb,emb,hEi,htB,hOutB,hHighB,hRead,hSplit,hTarget,hFreshB⟩:=
    native_star_arm_fresh_classification mid tail Ti bi hmid
      (by omega : mid.length<U-pre.length) hTi hw φ ho.suffix_end
  have hExterior (c : Ti.Slot) (hc : Ti.splitIndex bi c=0) :
      ∃e : Ei.Slot,emb c=Sum.inl e ∧ ∀η β,Ti.atSlot (RB η β) c=Ei.atSlot η e := by
    have H:=hSplit bi c
    rw [hTarget,hc] at H
    cases hd:emb c with
    | inl e=>
      refine ⟨e,rfl,?_⟩
      intro η β
      rw [hRead,hd]
      rfl
    | inr d=>
      simp only [hd,splitIndex,Sum.elim_inr] at H
      rw [exteriorPrepend_splitIndex] at H
      omega
  obtain ⟨es,hes,hsRead⟩:=hExterior si (by rw [splitIndex_symm];exact hbi)
  obtain ⟨A,D,RD,td,hA,htD,hOutD,hHighD,hLawD⟩:=native_star_arm_classification
    mid tail Ei es hmid (by omega : mid.length<U-pre.length) hEi hw φ ho.suffix_end
  let R:=fun η β δ=>(exteriorPrependAssignmentEquiv pre Ti).symm (RB (RD η δ) β)
  refine ⟨A,Bold,D,R,tb,td,?_,?_,?_,?_⟩
  · intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    exact htB (RD η δ) β
  · intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [hsRead]
    exact htD η δ
  · intro c hc
    have HS:=exteriorPrepend_splitIndex pre Ti s c
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : mid.length<Ti.splitIndex si ci := by dsimp only [si,ci] at *;omega
    have hHigh : U-pre.length≤Ti.splitIndex ci si := by
      rcases hTi si ci with H|H|H <;> rw [Ti.splitIndex_symm ci si] <;> omega
    have hzero : Ti.splitIndex bi ci=0 := by
      have Hz:=Ti.splitIndex_low_eq_of_high ci si bi hHigh
        (by rw [hbi];omega : Ti.splitIndex si bi<U-pre.length)
      rw [Ti.splitIndex_symm bi ci,Hz,hbi]
    obtain ⟨ec,hec,hcRead⟩:=hExterior ci hzero
    have hsplit : Ei.splitIndex es ec=Ti.splitIndex si ci := by
      have H:=hSplit si ci
      simpa only [hes,hec,splitIndex,Sum.elim_inl] using H
    obtain ⟨d,hr,hd⟩:=hHighD ec (by rw [hsplit];omega)
    refine ⟨d,?_,?_⟩
    · intro η β δ
      rw [exteriorPrepend_atSlot]
      simp only [R,Equiv.apply_symm_apply]
      rw [hcRead]
      exact hr η δ
    · dsimp only [si,ci] at *
      omega
  · intro q Q x
    let Bf:=exteriorPrepend mid (Bold.fork (single tail))
    let Df:=exteriorPrepend mid D
    let V:=A.fork (Bf.fork Df)
    let Rv : V.Assignment → Ti.Assignment:=fun σ=>
      let β:=exteriorPrependAssignmentEquiv mid (Bold.fork (single tail)) σ.2.1
      let δ:=exteriorPrependAssignmentEquiv mid D σ.2.2
      RB (RD σ.1 δ) β.1
    let fresh : V.Assignment → S:=fun σ=>singleEquiv (S:=S) tail
      (exteriorPrependAssignmentEquiv mid (Bold.fork (single tail)) σ.2.1).2
    have hCore : ∀(q' : ℕ → ι → ℝ≥0) (P : Ti.Assignment → S → ℝ) (y : ι → ℝ),
        nativeTrunkProjectedMean w φ Ti bi mid.length q' P y=
          V.expect w φ q' (fun σ=>P (Rv σ) (fresh σ)) y := by
      intro q' P y
      rw [hFreshB,expect_fork,hLawD]
      simp only [V,Rv,fresh,expect_fork]
      apply congrArg (fun F=>A.expect w φ q' F y)
      funext η
      exact native_expect_nested_commute Df Bf w φ q'
        (fun δ β=>P (RB (RD η (exteriorPrependAssignmentEquiv mid D δ))
          (exteriorPrependAssignmentEquiv mid (Bold.fork (single tail)) β).1)
          (singleEquiv (S:=S) tail (exteriorPrependAssignmentEquiv mid (Bold.fork (single tail)) β).2)) y
    have H:=exteriorPrepend_trunk_projected_map_congr pre Ti V bi mid.length Rv fresh hw φ ho hCore q Q x
    change nativeTrunkProjectedMean w φ (exteriorPrepend pre Ti)
      ((exteriorPrependSlotEquiv pre Ti).symm bi) (pre.length+mid.length) q Q x=
      (exteriorPrepend pre V).expect w φ q (fun σ=>
        let z:=exteriorPrependAssignmentEquiv pre V σ
        Q ((exteriorPrependAssignmentEquiv pre Ti).symm (Rv z)) (fresh z)) x at H
    simpa only [bi,R,Rv,fresh,V,Bf,Df,Equiv.symm_apply_apply] using H

end OAI.SKFluctuations.Cavity
