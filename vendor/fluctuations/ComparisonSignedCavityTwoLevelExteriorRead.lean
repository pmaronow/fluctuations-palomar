module

public import ComparisonSignedCavityForestExteriorSlotGeometry

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_two_level_forest_classification_with_exterior
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hlen : U≤pre.length+mid.length+tail.length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → D.Assignment → T.Assignment)
      (targetD : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ targetD) ∧
      (∀c,T.splitIndex s c=pre.length → ∃e : Ei.Slot,
        ∀η β δ,T.atSlot (read η β δ) c=Ei.atSlot η e) ∧
      (∀c,T.splitIndex s c=pre.length+mid.length → ∃e : Es.Slot,
        ∀η β δ,T.atSlot (read η β δ) c=Es.atSlot β e) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η β δ,T.atSlot (read η β δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex targetD d=T.splitIndex s c) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
        T.expect w φ q Q x=(nativeExteriorForestTree pre mid Ei Es D).expect w φ q
          (nativeExteriorForestRead pre mid Ei Es D (fun η β δ=>Q (read η β δ))) x) := by
  have Hpre : ∀c,pre.length≤T.splitIndex s c := by
    intro c
    rcases hT s c with H|H|H <;> omega
  obtain ⟨Ti,hpre⟩:=native_exists_prepend_of_trunk_split pre T s Hpre
  subst T
  let si:=exteriorPrependSlotEquiv pre Ti s
  have hTi:=NativePersistentLowForks.strip_prefix pre mid Ti hU hT
  obtain ⟨Ei,Ts,Ri,ts,hEi,htI,hOutI,hHighI,hLawI⟩:=native_star_arm_classification
    mid tail Ti si hmid (by omega : mid.length<U-pre.length) hTi hw φ ho.suffix_end
  have htail : tail≠[] := by
    intro H
    have HL:=congrArg List.length H
    simp only [List.length_nil] at HL
    omega
  have hLawS : ∀(q : ℕ → ι → ℝ≥0) (Q : Ts.Assignment → ℝ) (x : ι → ℝ),
      Ts.expect w φ q Q x=
        ((nativeGroupRootForest Ts ts).exterior.fork (nativeGroupRootForest Ts ts).occupied).expect w φ q
          (fun σ=>Q ((nativeGroupRootForest Ts ts).read σ.1 σ.2)) x :=
    fun q Q x=>nativeGroupRootForest_expect Ts ts hw φ ho.suffix_end.suffix_end q Q x
  have hTarget:=fun ζ σ=>(nativeGroupRootForest Ts ts).read_target ζ σ
  have hOutside:=fun c hc=>(nativeGroupRootForest Ts ts).read_exterior_relative htail c hc
  have hHigh:=fun c hc=>(nativeGroupRootForest Ts ts).read_high_relative c hc
  generalize hg:nativeGroupRootForest Ts ts=g at hLawS hTarget hOutside hHigh
  rcases g with ⟨Es,D,td,Rs,es,os,hts,hos,hrs,hss,hso,hfree⟩
  let R:=fun η β δ=>(exteriorPrependAssignmentEquiv pre Ti).symm (Ri η (Rs β δ))
  refine ⟨Ei,Es,D,R,td,?_,?_,?_,?_,?_⟩
  · intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [htI]
    exact hTarget β δ
  · intro c hc
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : Ti.splitIndex si ci=0 := by
      have HS:=exteriorPrepend_splitIndex pre Ti s c
      dsimp only [si,ci] at *
      omega
    obtain ⟨e,he⟩:=hOutI ci hci
    refine ⟨e,?_⟩
    intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    exact he η (Rs β δ)
  · intro c hc
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : Ti.splitIndex si ci=mid.length := by
      have HS:=exteriorPrepend_splitIndex pre Ti s c
      dsimp only [si,ci] at *
      omega
    obtain ⟨cs,hr,hs⟩:=hHighI ci hci.ge
    have hcs : Ts.splitIndex ts cs=0 := by omega
    obtain ⟨e,he⟩:=hOutside cs hcs
    refine ⟨e,?_⟩
    intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [hr]
    exact he β δ
  · intro c hc
    have HS:=exteriorPrepend_splitIndex pre Ti s c
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : mid.length<Ti.splitIndex si ci := by dsimp only [si,ci] at *;omega
    obtain ⟨cs,hr,hs⟩:=hHighI ci hci.le
    have hcs : 0<Ts.splitIndex ts cs := by omega
    obtain ⟨d,hr',hs'⟩:=hHigh cs hcs
    refine ⟨d,?_,?_⟩
    · intro η β δ
      rw [exteriorPrepend_atSlot]
      simp only [R,Equiv.apply_symm_apply]
      rw [hr]
      exact hr' β δ
    · dsimp only [si,ci] at *
      omega
  · intro q Q x
    let Rsv : (Es.fork D).Assignment → Ts.Assignment:=fun σ=>Rs σ.1 σ.2
    let V:=Ei.fork (exteriorPrepend mid (Es.fork D))
    let Rv : V.Assignment → Ti.Assignment:=fun σ=>Ri σ.1
      (exteriorPrependAssignmentEquiv mid Ts
        (exteriorPrependRead mid Ts (Es.fork D) Rsv σ.2))
    have hCore : ∀(q' : ℕ → ι → ℝ≥0) (P : Ti.Assignment → ℝ) (y : ι → ℝ),
        Ti.expect w φ q' P y=V.expect w φ q' (fun σ=>P (Rv σ)) y := by
      intro q' P y
      rw [hLawI,expect_fork]
      rw [expect_fork]
      apply congrArg (fun F=>Ei.expect w φ q' F y)
      funext η
      exact exteriorPrepend_expect_map_congr mid Ts (Es.fork D) Rsv hw φ ho.suffix_end
        hLawS q' (fun σ=>P (Ri η (exteriorPrependAssignmentEquiv mid Ts σ))) y
    have H:=exteriorPrepend_expect_map_congr pre Ti V Rv hw φ ho hCore q Q x
    unfold nativeExteriorForestRead
    simpa only [nativeExteriorForestTree,exteriorPrependRead,
      Rv,Rsv,R,V,Equiv.apply_symm_apply] using H

end OAI.SKFluctuations.Cavity
