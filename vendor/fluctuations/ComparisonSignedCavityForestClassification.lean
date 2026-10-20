module

public import ComparisonSignedCavityForestPrefixGeometry

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_two_level_forest_classification_with_high
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → D.Assignment → T.Assignment) (target : D.Slot),
      (∀η ζ σ,T.atSlot (read η ζ σ) s=D.atSlot σ target) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c →
        ∃d : D.Slot,(∀η ζ σ,T.atSlot (read η ζ σ) c=D.atSlot σ d) ∧
          pre.length+mid.length+D.splitIndex target d=T.splitIndex s c) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
        T.expect w φ q Q x=(nativeExteriorForestTree pre mid Ei Es D).expect w φ q
          (nativeExteriorForestRead pre mid Ei Es D (fun η ζ σ=>Q (read η ζ σ))) x) := by
  have Hpre : ∀c,pre.length≤T.splitIndex s c := by
    intro c
    rcases hT s c with H|H|H <;> omega
  obtain ⟨Ti,hpre⟩:=native_exists_prepend_of_trunk_split pre T s Hpre
  subst T
  let si:=exteriorPrependSlotEquiv pre Ti s
  have hTi:=NativePersistentLowForks.strip_prefix pre mid Ti hU hT
  have Hmiddle:=native_group_occupied_shares_middle mid Ti si (U:=U-pre.length) (by omega) hTi
  have hLaw1 : ∀(q : ℕ → ι → ℝ≥0) (Q : Ti.Assignment → ℝ) (x : ι → ℝ),
      Ti.expect w φ q Q x=
        ((nativeGroupRootForest Ti si).exterior.fork (nativeGroupRootForest Ti si).occupied).expect w φ q
          (fun σ=>Q ((nativeGroupRootForest Ti si).read σ.1 σ.2)) x :=
    fun q Q x=>nativeGroupRootForest_expect Ti si hw φ ho.suffix_end q Q x
  have hTarget1 : ∀(η : (nativeGroupRootForest Ti si).exterior.Assignment)
      (σ : (nativeGroupRootForest Ti si).occupied.Assignment),
      Ti.atSlot ((nativeGroupRootForest Ti si).read η σ) si=
        (nativeGroupRootForest Ti si).occupied.atSlot σ (nativeGroupRootForest Ti si).target :=
    fun η σ=>(nativeGroupRootForest Ti si).read_target η σ
  have hHigh1 : ∀c,0<Ti.splitIndex si c →
      ∃d : (nativeGroupRootForest Ti si).occupied.Slot,
        (∀η σ,Ti.atSlot ((nativeGroupRootForest Ti si).read η σ) c=
          (nativeGroupRootForest Ti si).occupied.atSlot σ d) ∧
        (nativeGroupRootForest Ti si).occupied.splitIndex (nativeGroupRootForest Ti si).target d=
          Ti.splitIndex si c :=fun c hc=>(nativeGroupRootForest Ti si).read_high_relative c hc
  generalize hg1:nativeGroupRootForest Ti si=g at Hmiddle hLaw1 hTarget1 hHigh1
  rcases g with ⟨Ei,Di,ti,readi,ei,oi,hti,hoi,hri,hsi,hio,hfree⟩
  obtain ⟨Ts,hmid⟩:=native_exists_prepend_of_trunk_split mid Di ti Hmiddle
  subst Di
  let ss:=exteriorPrependSlotEquiv mid Ts ti
  have hLaw2 : ∀(q : ℕ → ι → ℝ≥0) (Q : Ts.Assignment → ℝ) (x : ι → ℝ),
      Ts.expect w φ q Q x=
        ((nativeGroupRootForest Ts ss).exterior.fork (nativeGroupRootForest Ts ss).occupied).expect w φ q
          (fun σ=>Q ((nativeGroupRootForest Ts ss).read σ.1 σ.2)) x :=
    fun q Q x=>nativeGroupRootForest_expect Ts ss hw φ ho.suffix_end.suffix_end q Q x
  have hTarget2 : ∀(ζ : (nativeGroupRootForest Ts ss).exterior.Assignment)
      (σ : (nativeGroupRootForest Ts ss).occupied.Assignment),
      Ts.atSlot ((nativeGroupRootForest Ts ss).read ζ σ) ss=
        (nativeGroupRootForest Ts ss).occupied.atSlot σ (nativeGroupRootForest Ts ss).target :=
    fun ζ σ=>(nativeGroupRootForest Ts ss).read_target ζ σ
  have hHigh2 : ∀c,0<Ts.splitIndex ss c →
      ∃d : (nativeGroupRootForest Ts ss).occupied.Slot,
        (∀ζ σ,Ts.atSlot ((nativeGroupRootForest Ts ss).read ζ σ) c=
          (nativeGroupRootForest Ts ss).occupied.atSlot σ d) ∧
        (nativeGroupRootForest Ts ss).occupied.splitIndex (nativeGroupRootForest Ts ss).target d=
          Ts.splitIndex ss c :=fun c hc=>(nativeGroupRootForest Ts ss).read_high_relative c hc
  generalize hg2:nativeGroupRootForest Ts ss=g2 at hLaw2 hTarget2 hHigh2
  rcases g2 with ⟨Es,D,td,reads,es,os,hts,hos,hrs,hss,hso,hfree2⟩
  let R:=fun η ζ σ=>(exteriorPrependAssignmentEquiv pre Ti).symm
    (readi η ((exteriorPrependAssignmentEquiv mid Ts).symm (reads ζ σ)))
  refine ⟨Ei,Es,D,R,td,?_,?_,?_⟩
  · intro η ζ σ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [hTarget1,exteriorPrepend_atSlot]
    simp only [Equiv.apply_symm_apply]
    exact hTarget2 ζ σ
  · intro c hc
    have HS:=exteriorPrepend_splitIndex pre Ti s c
    let ci:=exteriorPrependSlotEquiv pre Ti c
    have hci : 0<Ti.splitIndex si ci := by dsimp only [si,ci] at *;omega
    obtain ⟨di,hreadi,hspliti⟩:=hHigh1 ci hci
    have HI:=exteriorPrepend_splitIndex mid Ts ti di
    let cs:=exteriorPrependSlotEquiv mid Ts di
    have hcs : 0<Ts.splitIndex ss cs := by dsimp only [si,ci,ss,cs] at *;omega
    obtain ⟨d,hreads,hsplits⟩:=hHigh2 cs hcs
    refine ⟨d,?_,?_⟩
    · intro η ζ σ
      rw [exteriorPrepend_atSlot]
      simp only [R,Equiv.apply_symm_apply]
      rw [hreadi,exteriorPrepend_atSlot]
      simp only [Equiv.apply_symm_apply]
      exact hreads ζ σ
    · dsimp only [si,ci,ss,cs] at *
      omega
  · intro q Q x
    let Rs : (Es.fork D).Assignment → Ts.Assignment:=fun σ=>reads σ.1 σ.2
    let V:=Ei.fork (exteriorPrepend mid (Es.fork D))
    let Rv : V.Assignment → Ti.Assignment:=fun σ=>readi σ.1
      (exteriorPrependRead mid Ts (Es.fork D) Rs σ.2)
    have hCore : ∀(q' : ℕ → ι → ℝ≥0) (P : Ti.Assignment → ℝ) (y : ι → ℝ),
        Ti.expect w φ q' P y=V.expect w φ q' (fun σ=>P (Rv σ)) y := by
      intro q' P y
      rw [hLaw1,expect_fork]
      rw [expect_fork]
      apply congrArg (fun F=>Ei.expect w φ q' F y)
      funext η
      exact exteriorPrepend_expect_map_congr mid Ts (Es.fork D) Rs hw φ ho.suffix_end
        hLaw2 q' (fun σ=>P (readi η σ)) y
    have H:=exteriorPrepend_expect_map_congr pre Ti V Rv hw φ ho hCore q Q x
    exact H

theorem native_two_level_forest_classification
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → D.Assignment → T.Assignment) (target : D.Slot),
      (∀η ζ σ,T.atSlot (read η ζ σ) s=D.atSlot σ target) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
        T.expect w φ q Q x=(nativeExteriorForestTree pre mid Ei Es D).expect w φ q
          (nativeExteriorForestRead pre mid Ei Es D (fun η ζ σ=>Q (read η ζ σ))) x) := by
  obtain ⟨Ei,Es,D,R,d,ht,_,hl⟩:=native_two_level_forest_classification_with_high pre mid tail T s hU hT hw φ ho
  exact ⟨Ei,Es,D,R,d,ht,hl⟩

end OAI.SKFluctuations.Cavity
