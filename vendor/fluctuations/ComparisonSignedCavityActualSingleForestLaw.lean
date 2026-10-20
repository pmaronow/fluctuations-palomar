module

public import ComparisonSignedCavityActualTargetSingleton

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

theorem NativeTargetStarSingleton.strip_prefix (pre : List PositiveMass)
    {tail : List PositiveMass} {T : ClockTree S tail}
    {s : (exteriorPrepend pre T).Slot} {star : ℕ}
    (h : NativeTargetStarSingleton (exteriorPrepend pre T) s (pre.length+star)) :
    NativeTargetStarSingleton T (exteriorPrependSlotEquiv pre T s) star := by
  intro c hc
  have HS:=h ((exteriorPrependSlotEquiv pre T).symm c) (by
    rw [exteriorPrepend_splitIndex]
    simp only [Equiv.apply_symm_apply]
    omega)
  have H:=congrArg (exteriorPrependSlotEquiv pre T) HS
  simpa only [Equiv.apply_symm_apply] using H

theorem NativeTargetStarSingleton.group_occupied {as : List PositiveMass}
    {T : ClockTree S as} {s : T.Slot} {star : ℕ}
    (h : NativeTargetStarSingleton T s star) (g : NativeRootForestGrouping T s) :
    NativeTargetStarSingleton g.occupied g.target star := by
  intro c hc
  have HS0 : T.splitIndex s (g.occupiedEmbed c)=g.occupied.splitIndex g.target c :=
    (congrArg (fun z=>T.splitIndex z (g.occupiedEmbed c)) g.target_eq).symm.trans
      (g.occupied_splits g.target c)
  have HS : star<T.splitIndex s (g.occupiedEmbed c) := by
    rw [HS0]
    exact hc
  have H:=congrArg g.embed (h (g.occupiedEmbed c) HS)
  have Hs : g.embed s=Sum.inr g.target :=
    (congrArg g.embed g.target_eq).symm.trans (g.occupied_embed g.target)
  rw [g.occupied_embed,Hs] at H
  exact Sum.inr.inj H

theorem native_root_free_singleton_eq_single {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (hf : NativeRootForkFree T)
    (h : NativeTargetStarSingleton T s 0) : T=single as := by
  cases T with
  | leaf=>rfl
  | step b T=>
    apply native_eq_single_of_slots_singleton (T.step b) s
    intro c
    apply h c
    change 0<1+T.splitIndex s c
    omega
  | fork T V=>exact hf.elim

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_two_level_single_forest_classification
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hSingle : NativeTargetStarSingleton T s (pre.length+mid.length))
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(Ei : ClockTree S (mid++tail)) (Es : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → (single (S:=S) tail).Assignment → T.Assignment),
      (∀η ζ σ,T.atSlot (read η ζ σ) s=singleEquiv (S:=S) tail σ) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
        T.expect w φ q Q x=(nativeExteriorForestTree pre mid Ei Es (single tail)).expect w φ q
          (nativeExteriorForestRead pre mid Ei Es (single tail)
            (fun η ζ σ=>Q (read η ζ σ))) x) := by
  have Hpre : ∀c,pre.length≤T.splitIndex s c := by
    intro c
    rcases hT s c with H|H|H <;> omega
  obtain ⟨Ti,hpre⟩:=native_exists_prepend_of_trunk_split pre T s Hpre
  subst T
  let si:=exteriorPrependSlotEquiv pre Ti s
  have hSinglei:=hSingle.strip_prefix pre
  have hTi:=NativePersistentLowForks.strip_prefix pre mid Ti hU hT
  have Hmiddle:=native_group_occupied_shares_middle mid Ti si (U:=U-pre.length) (by omega) hTi
  have hDi:=hSinglei.group_occupied (nativeGroupRootForest Ti si)
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
  generalize hg1:nativeGroupRootForest Ti si=g at Hmiddle hDi hLaw1 hTarget1
  rcases g with ⟨Ei,Di,ti,readi,ei,oi,hti,hoi,hri,hsi,hio,hfree⟩
  obtain ⟨Ts,hmid⟩:=native_exists_prepend_of_trunk_split mid Di ti Hmiddle
  subst Di
  let ss:=exteriorPrependSlotEquiv mid Ts ti
  have hSingles:=hDi.strip_prefix mid (star:=0)
  have hD:=hSingles.group_occupied (nativeGroupRootForest Ts ss)
  have hEq:=native_root_free_singleton_eq_single
    (nativeGroupRootForest Ts ss).occupied (nativeGroupRootForest Ts ss).target
    (nativeGroupRootForest Ts ss).root_free hD
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
  generalize hg2:nativeGroupRootForest Ts ss=g2 at hEq hLaw2 hTarget2
  rcases g2 with ⟨Es,D,td,reads,es,os,hts,hos,hrs,hss,hso,hfree2⟩
  change D=single tail at hEq
  subst D
  let R:=fun η ζ σ=>(exteriorPrependAssignmentEquiv pre Ti).symm
    (readi η ((exteriorPrependAssignmentEquiv mid Ts).symm (reads ζ σ)))
  refine ⟨Ei,Es,R,?_,?_⟩
  · intro η ζ σ
    rw [exteriorPrepend_atSlot]
    simp only [R,Equiv.apply_symm_apply]
    rw [hTarget1,exteriorPrepend_atSlot]
    simp only [Equiv.apply_symm_apply]
    rw [hTarget2]
    change (single tail).atSlot σ td=singleEquiv (S:=S) tail σ
    rw [native_single_slot_eq tail td,single_atSlot]
  · intro q Q x
    let Rs : (Es.fork (single tail)).Assignment → Ts.Assignment:=fun σ=>reads σ.1 σ.2
    let V:=Ei.fork (exteriorPrepend mid (Es.fork (single tail)))
    let Rv : V.Assignment → Ti.Assignment:=fun σ=>readi σ.1
      (exteriorPrependRead mid Ts (Es.fork (single tail)) Rs σ.2)
    have hCore : ∀(q' : ℕ → ι → ℝ≥0) (P : Ti.Assignment → ℝ) (y : ι → ℝ),
        Ti.expect w φ q' P y=V.expect w φ q' (fun σ=>P (Rv σ)) y := by
      intro q' P y
      rw [hLaw1,expect_fork,expect_fork]
      apply congrArg (fun F=>Ei.expect w φ q' F y)
      funext η
      exact exteriorPrepend_expect_map_congr mid Ts (Es.fork (single tail)) Rs hw φ ho.suffix_end
        hLaw2 q' (fun σ=>P (readi η σ)) y
    exact exteriorPrepend_expect_map_congr pre Ti V Rv hw φ ho hCore q Q x

theorem native_actual_generated_single_forest_classification
    (pre mid tail : List PositiveMass) {T : ClockTree S (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hU : pre.length+mid.length<U)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(Ei : ClockTree S (mid++tail)) (Es : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → (single (S:=S) tail).Assignment → T.Assignment),
      (∀η ζ σ,T.atSlot (read η ζ σ) P.live.test.target=singleEquiv (S:=S) tail σ) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
        T.expect w φ q Q x=(nativeExteriorForestTree pre mid Ei Es (single tail)).expect w φ q
          (nativeExteriorForestRead pre mid Ei Es (single tail)
            (fun η ζ σ=>Q (read η ζ σ))) x) :=
  native_two_level_single_forest_classification pre mid tail T P.live.test.target hU
    (hP.persistentLowForks (by omega)) (hP.targetStarSingleton (by omega)) hw φ ho

end OAI.SKFluctuations.Cavity
