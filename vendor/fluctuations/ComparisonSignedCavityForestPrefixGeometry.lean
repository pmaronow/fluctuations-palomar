module

public import ComparisonSignedCavityForestRootGrouping

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

def exteriorPrependSlotEquiv (pre : List PositiveMass) {tail : List PositiveMass}
    (T : ClockTree S tail) : (exteriorPrepend pre T).Slot ≃ T.Slot :=
  match pre with
  | []=>Equiv.refl _
  | _::pre=>exteriorPrependSlotEquiv pre T

theorem exteriorPrepend_atSlot (pre : List PositiveMass) {tail : List PositiveMass}
    (T : ClockTree S tail) (σ : (exteriorPrepend pre T).Assignment)
    (s : (exteriorPrepend pre T).Slot) :
    (exteriorPrepend pre T).atSlot σ s=
      T.atSlot (exteriorPrependAssignmentEquiv pre T σ) (exteriorPrependSlotEquiv pre T s) := by
  induction pre with
  | nil=>rfl
  | cons b pre ih=>exact ih σ s

theorem exteriorPrepend_splitIndex (pre : List PositiveMass) {tail : List PositiveMass}
    (T : ClockTree S tail) (s t : (exteriorPrepend pre T).Slot) :
    (exteriorPrepend pre T).splitIndex s t=pre.length+
      T.splitIndex (exteriorPrependSlotEquiv pre T s) (exteriorPrependSlotEquiv pre T t) := by
  induction pre with
  | nil=>
    simp only [exteriorPrepend,exteriorPrependSlotEquiv,List.length_nil,Nat.zero_add]
    rfl
  | cons b pre ih=>
    have H:=ih s t
    change 1+(exteriorPrepend pre T).splitIndex s t=pre.length+1+
      T.splitIndex (exteriorPrependSlotEquiv pre T s) (exteriorPrependSlotEquiv pre T t)
    omega

theorem native_exists_prepend_of_trunk_split (pre : List PositiveMass) {tail : List PositiveMass}
    (T : ClockTree S (pre++tail)) (s : T.Slot)
    (h : ∀c,pre.length≤T.splitIndex s c) :
    ∃D : ClockTree S tail,T=exteriorPrepend pre D := by
  induction pre with
  | nil=>exact ⟨T,rfl⟩
  | cons b pre ih=>
    cases T with
    | step b T=>
      have hT : ∀c,pre.length≤T.splitIndex s c := by
        intro c
        have H:=h c
        change pre.length+1≤1+T.splitIndex s c at H
        omega
      obtain ⟨D,hD⟩:=ih T s hT
      exact ⟨D,congrArg (fun V : ClockTree S (pre++tail)=>V.step b) hD⟩
    | fork T V=>
      cases s with
      | inl s=>
        have H:=h (Sum.inr (nativeFirstSlot V))
        simp only [splitIndex,List.length_cons,Sum.elim_inl,Sum.elim_inr] at H
        omega
      | inr s=>
        have H:=h (Sum.inl (nativeFirstSlot T))
        simp only [splitIndex,List.length_cons,Sum.elim_inl,Sum.elim_inr] at H
        omega

theorem NativeRootForkFree.split_pos {as : List PositiveMass} {T : ClockTree S as}
    (h : NativeRootForkFree T) (has : as≠[]) (s t : T.Slot) : 0<T.splitIndex s t := by
  cases T with
  | leaf=>exact (has rfl).elim
  | step b T=>change 0<1+T.splitIndex s t;omega
  | fork T V=>exact h.elim

theorem NativePersistentLowForks.strip_prefix (pre mid : List PositiveMass)
    {tail : List PositiveMass} (T : ClockTree S (mid++tail)) {U : ℕ}
    (_hU : pre.length+mid.length<U)
    (h : NativePersistentLowForks pre.length (pre.length+mid.length) U (exteriorPrepend pre T)) :
    NativePersistentLowForks 0 mid.length (U-pre.length) T := by
  intro c d
  have H:=h ((exteriorPrependSlotEquiv pre T).symm c) ((exteriorPrependSlotEquiv pre T).symm d)
  rw [exteriorPrepend_splitIndex] at H
  simp only [Equiv.apply_symm_apply] at H
  rcases H with H|H|H
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem native_group_occupied_shares_middle (mid : List PositiveMass) {tail : List PositiveMass}
    (T : ClockTree S (mid++tail)) (s : T.Slot) {U : ℕ} (hU : mid.length<U)
    (h : NativePersistentLowForks 0 mid.length U T) :
    ∀c,mid.length≤(nativeGroupRootForest T s).occupied.splitIndex
      (nativeGroupRootForest T s).target c := by
  intro c
  by_cases hm : mid=[]
  · simp only [hm,List.length_nil,Nat.zero_le]
  · have has : mid++tail≠[] := by
      intro H
      have Hm:mid=[]:=List.append_eq_nil_iff.mp H |>.1
      exact hm Hm
    have H:=h ((nativeGroupRootForest T s).occupiedEmbed (nativeGroupRootForest T s).target)
      ((nativeGroupRootForest T s).occupiedEmbed c)
    rw [(nativeGroupRootForest T s).occupied_splits] at H
    have Hpos:=(nativeGroupRootForest T s).root_free.split_pos has
      (nativeGroupRootForest T s).target c
    rcases H with H|H|H
    · omega
    · omega
    · omega

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def exteriorPrependRead (pre : List PositiveMass) {tail : List PositiveMass}
    (T V : ClockTree S tail) (read : V.Assignment → T.Assignment) :
    (exteriorPrepend pre V).Assignment → (exteriorPrepend pre T).Assignment :=
  fun σ=>(exteriorPrependAssignmentEquiv pre T).symm
    (read (exteriorPrependAssignmentEquiv pre V σ))

theorem exteriorPrepend_expect_map_congr (pre : List PositiveMass) {tail : List PositiveMass}
    (T V : ClockTree S tail) (read : V.Assignment → T.Assignment)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++tail))
    (hLaw : ∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
      T.expect w φ q Q x=V.expect w φ q (fun σ=>Q (read σ)) x)
    (q : ℕ → ι → ℝ≥0) (Q : (exteriorPrepend pre T).Assignment → ℝ) (x : ι → ℝ) :
    (exteriorPrepend pre T).expect w φ q Q x=
      (exteriorPrepend pre V).expect w φ q (fun σ=>Q (exteriorPrependRead pre T V read σ)) x := by
  let P:=fun τ=>Q ((exteriorPrependAssignmentEquiv pre T).symm τ)
  have HS:=exteriorPrepend_expect pre hw φ T ho q P x
  have HT:=exteriorPrepend_expect pre hw φ V ho q (fun σ=>P (read σ)) x
  simp only [P,Equiv.symm_apply_apply] at HS
  rw [HS]
  change _=(exteriorPrepend pre V).expect w φ q
    (fun σ=>P (read (exteriorPrependAssignmentEquiv pre V σ))) x
  rw [HT]
  apply congrArg (fun B=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j)))) B x)
  funext y
  exact hLaw _ P y

end OAI.SKFluctuations.Hierarchy.ClockTree
