module

public import ComparisonSignedCavityForestObservedFreshLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_same_arm_fresh_factory
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hlen : U≤pre.length+mid.length+tail.length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length+mid.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(Ei : ClockTree S (mid++tail)) (Bold D : ClockTree S tail)
      (read : Ei.Assignment → Bold.Assignment → D.Assignment → T.Assignment)
      (targetB : Bold.Slot) (targetD : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) b=Bold.atSlot β targetB) ∧
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ targetD) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η β δ,T.atSlot (read η β δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex targetD d=T.splitIndex s c) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → S → ℝ) (x : ι → ℝ),
        nativeTrunkProjectedMean w φ T b (pre.length+mid.length) q Q x=
          (nativeExteriorForestTree pre mid Ei (Bold.fork (single tail)) D).expect w φ q
            (nativeExteriorForestRead pre mid Ei (Bold.fork (single tail)) D
              (fun η β δ=>Q (read η β.1 δ) (singleEquiv (S:=S) tail β.2))) x) := by
  have Hpre : ∀c,pre.length≤T.splitIndex b c := by
    intro c
    rcases hT b c with H|H|H <;> omega
  obtain ⟨Ti,hpre⟩:=native_exists_prepend_of_trunk_split pre T b Hpre
  subst T
  let si:=exteriorPrependSlotEquiv pre Ti s
  let bi:=exteriorPrependSlotEquiv pre Ti b
  have hTi:=NativePersistentLowForks.strip_prefix pre mid Ti hU hT
  have hbi : Ti.splitIndex bi si=mid.length := by
    have HS:=exteriorPrepend_splitIndex pre Ti s b
    rw [Ti.splitIndex_symm bi si]
    dsimp only [si,bi] at *
    omega
  obtain ⟨Ei,Ts,Ri,tb,emb,hEi,htB,hOutB,hHighB,hRead,hSplit,hTarget,hFreshI⟩:=
    native_star_arm_fresh_classification mid tail Ti bi hmid
      (by omega : mid.length<U-pre.length) hTi hw φ ho.suffix_end
  have hInside (c : Ti.Slot) (hc : mid.length≤Ti.splitIndex bi c) :
      ∃e : (exteriorPrepend mid Ts).Slot,emb c=Sum.inr e ∧
        ∀η β,Ti.atSlot (Ri η β) c=Ts.atSlot β (exteriorPrependSlotEquiv mid Ts e) := by
    have H:=hSplit bi c
    rw [hTarget] at H
    cases hd:emb c with
    | inl e=>simp only [hd,splitIndex,Sum.elim_inl,Sum.elim_inr] at H;omega
    | inr e=>
      refine ⟨e,rfl,?_⟩
      intro η β
      rw [hRead,hd]
      change (exteriorPrepend mid Ts).atSlot ((exteriorPrependAssignmentEquiv mid Ts).symm β) e=_
      rw [exteriorPrepend_atSlot]
      simp only [Equiv.apply_symm_apply]
  obtain ⟨sp,hsp,hsRead⟩:=hInside si (by omega)
  let ss:=exteriorPrependSlotEquiv mid Ts sp
  have hsb0 : Ts.splitIndex ss tb=0 := by
    have H:=hSplit si bi
    rw [hsp,hTarget] at H
    simp only [splitIndex,Sum.elim_inr] at H
    rw [exteriorPrepend_splitIndex] at H
    simp only [Equiv.apply_symm_apply] at H
    dsimp only [ss] at *
    rw [Ti.splitIndex_symm si bi,hbi] at H
    omega
  have htail : tail≠[] := by
    intro H
    have HL:=congrArg List.length H
    simp only [List.length_nil] at HL
    omega
  have hLawS : ∀(q : ℕ → ι → ℝ≥0) (Q : Ts.Assignment → ℝ) (x : ι → ℝ),
      Ts.expect w φ q Q x=
        ((nativeGroupRootForest Ts ss).exterior.fork (nativeGroupRootForest Ts ss).occupied).expect w φ q
          (fun σ=>Q ((nativeGroupRootForest Ts ss).read σ.1 σ.2)) x :=
    fun q Q x=>nativeGroupRootForest_expect Ts ss hw φ ho.suffix_end.suffix_end q Q x
  have hTargetS:=fun ζ σ=>(nativeGroupRootForest Ts ss).read_target ζ σ
  have hB:=(nativeGroupRootForest Ts ss).read_exterior_relative htail tb hsb0
  have hHighS:=fun c hc=>(nativeGroupRootForest Ts ss).read_high_relative c hc
  generalize hg:nativeGroupRootForest Ts ss=g at hLawS hTargetS hB hHighS
  rcases g with ⟨Bold,D,td,Rs,es,os,hts,hos,hrs,hss,hso,hfree⟩
  obtain ⟨tB,hB⟩:=hB
  let R:=fun η β δ=>(exteriorPrependAssignmentEquiv pre Ti).symm (Ri η (Rs β δ))
  refine ⟨Ei,Bold,D,R,tB,td,?_,?_,?_,?_⟩
  · intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [htB]
    exact hB β δ
  · intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [hsRead]
    exact hTargetS β δ
  · intro c hc
    have HS:=exteriorPrepend_splitIndex pre Ti s c
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : mid.length<Ti.splitIndex si ci := by dsimp only [si,ci] at *;omega
    have hbi' : mid.length≤Ti.splitIndex bi ci :=
      Ti.splitIndex_cut_trans mid.length bi si ci (by omega) (by omega)
    obtain ⟨cp,hcp,hcRead⟩:=hInside ci hbi'
    let cs:=exteriorPrependSlotEquiv mid Ts cp
    have hsc : mid.length+Ts.splitIndex ss cs=Ti.splitIndex si ci := by
      have H:=hSplit si ci
      rw [hsp,hcp] at H
      simpa only [splitIndex,Sum.elim_inr,exteriorPrepend_splitIndex,ss,cs] using H
    obtain ⟨d,hr,hd⟩:=hHighS cs (by omega)
    refine ⟨d,?_,?_⟩
    · intro η β δ
      rw [exteriorPrepend_atSlot]
      simp only [R,Equiv.apply_symm_apply]
      rw [hcRead]
      exact hr β δ
    · dsimp only [si,ci] at *
      omega
  · intro q Q x
    let Vs:=(Bold.fork (single tail)).fork D
    let Raug : Vs.Assignment → (Ts.fork (single tail)).Assignment:=fun σ=>(Rs σ.1.1 σ.2,σ.1.2)
    have hAug : ∀(q' : ℕ → ι → ℝ≥0) (F : (Ts.fork (single tail)).Assignment → ℝ) (y : ι → ℝ),
        (Ts.fork (single tail)).expect w φ q' F y=Vs.expect w φ q' (fun σ=>F (Raug σ)) y := by
      intro q' F y
      rw [expect_fork,hLawS]
      simp only [Vs,Raug,expect_fork]
      apply congrArg (fun f=>Bold.expect w φ q' f y)
      funext β
      exact native_expect_nested_commute D (single tail) w φ q'
        (fun δ fresh=>F (Rs β δ,fresh)) y
    let V:=Ei.fork (exteriorPrepend mid Vs)
    let Rv : V.Assignment → Ti.Assignment:=fun σ=>
      let z:=exteriorPrependAssignmentEquiv mid Vs σ.2
      Ri σ.1 (Rs z.1.1 z.2)
    let fresh : V.Assignment → S:=fun σ=>singleEquiv (S:=S) tail
      (exteriorPrependAssignmentEquiv mid Vs σ.2).1.2
    have hCore : ∀(q' : ℕ → ι → ℝ≥0) (P : Ti.Assignment → S → ℝ) (y : ι → ℝ),
        nativeTrunkProjectedMean w φ Ti bi mid.length q' P y=
          V.expect w φ q' (fun σ=>P (Rv σ) (fresh σ)) y := by
      intro q' P y
      rw [hFreshI,expect_fork]
      rw [expect_fork]
      apply congrArg (fun F=>Ei.expect w φ q' F y)
      funext η
      have H:=exteriorPrepend_expect_map_congr mid (Ts.fork (single tail)) Vs Raug hw φ ho.suffix_end
        hAug q' (fun σ=>let z:=exteriorPrependAssignmentEquiv mid (Ts.fork (single tail)) σ
          P (Ri η z.1) (singleEquiv (S:=S) tail z.2)) y
      simpa only [exteriorPrependRead,Raug,Rv,fresh,Equiv.apply_symm_apply] using H
    have H:=exteriorPrepend_trunk_projected_map_congr pre Ti V bi mid.length Rv fresh hw φ ho hCore q Q x
    change nativeTrunkProjectedMean w φ (exteriorPrepend pre Ti)
      ((exteriorPrependSlotEquiv pre Ti).symm bi) (pre.length+mid.length) q Q x=
      (exteriorPrepend pre V).expect w φ q (fun σ=>
        let z:=exteriorPrependAssignmentEquiv pre V σ
        Q ((exteriorPrependAssignmentEquiv pre Ti).symm (Rv z)) (fresh z)) x at H
    unfold nativeExteriorForestRead
    simpa only [bi,R,Rv,fresh,V,Vs,nativeExteriorForestTree,Equiv.symm_apply_apply] using H

end OAI.SKFluctuations.Cavity
