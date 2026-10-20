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

theorem native_two_arm_forest_classification
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(A : ClockTree S (mid++tail)) (B D : ClockTree S tail)
      (read : A.Assignment → B.Assignment → D.Assignment → T.Assignment)
      (targetB : B.Slot) (targetD : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) b=B.atSlot β targetB) ∧
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ targetD) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η β δ,T.atSlot (read η β δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex targetD d=T.splitIndex s c) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
        let V:=A.fork ((exteriorPrepend mid B).fork (exteriorPrepend mid D))
        T.expect w φ q Q x=(exteriorPrepend pre V).expect w φ q
          (fun σ=>let z:=exteriorPrependAssignmentEquiv pre V σ
            Q (read z.1 (exteriorPrependAssignmentEquiv mid B z.2.1)
              (exteriorPrependAssignmentEquiv mid D z.2.2))) x) := by
  have Hpre : ∀c,pre.length≤T.splitIndex s c := by
    intro c
    rcases hT s c with H|H|H <;> omega
  obtain ⟨Ti,hpre⟩:=native_exists_prepend_of_trunk_split pre T s Hpre
  subst T
  let si:=exteriorPrependSlotEquiv pre Ti s
  let bi:=exteriorPrependSlotEquiv pre Ti b
  have hTi:=NativePersistentLowForks.strip_prefix pre mid Ti hU hT
  have hbi : Ti.splitIndex si bi=0 := by
    have HS:=exteriorPrepend_splitIndex pre Ti s b
    dsimp only [si,bi] at *
    omega
  obtain ⟨Ei,D,RD,td,hEi,htD,hOutD,hHighD,hLawD⟩:=native_star_arm_classification
    mid tail Ti si hmid (by omega : mid.length<U-pre.length) hTi hw φ ho.suffix_end
  obtain ⟨eb,hb⟩:=hOutD bi hbi
  obtain ⟨A,B,RB,tb,hA,htB,hOutB,hHighB,hLawB⟩:=native_star_arm_classification
    mid tail Ei eb hmid (by omega : mid.length<U-pre.length) hEi hw φ ho.suffix_end
  let R:=fun η β δ=>(exteriorPrependAssignmentEquiv pre Ti).symm (RD (RB η β) δ)
  refine ⟨A,B,D,R,tb,td,?_,?_,?_,?_⟩
  · intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [hb]
    exact htB η β
  · intro η β δ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    exact htD (RB η β) δ
  · intro c hc
    have HS:=exteriorPrepend_splitIndex pre Ti s c
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : mid.length<Ti.splitIndex si ci := by dsimp only [si,ci] at *;omega
    obtain ⟨d,hr,hd⟩:=hHighD ci hci.le
    refine ⟨d,?_,?_⟩
    · intro η β δ
      rw [exteriorPrepend_atSlot]
      simp only [R,Equiv.apply_symm_apply]
      exact hr (RB η β) δ
    · dsimp only [si,ci] at *
      omega
  · intro q Q x
    let V:=A.fork ((exteriorPrepend mid B).fork (exteriorPrepend mid D))
    let Rv : V.Assignment → Ti.Assignment:=fun σ=>
      RD (RB σ.1 (exteriorPrependAssignmentEquiv mid B σ.2.1))
        (exteriorPrependAssignmentEquiv mid D σ.2.2)
    have hCore : ∀(q' : ℕ → ι → ℝ≥0) (P : Ti.Assignment → ℝ) (y : ι → ℝ),
        Ti.expect w φ q' P y=V.expect w φ q' (fun σ=>P (Rv σ)) y := by
      intro q' P y
      rw [hLawD,expect_fork,hLawB]
      simp only [V,Rv,expect_fork]
    exact exteriorPrepend_expect_map_congr pre Ti V Rv hw φ ho hCore q Q x

end OAI.SKFluctuations.Cavity
