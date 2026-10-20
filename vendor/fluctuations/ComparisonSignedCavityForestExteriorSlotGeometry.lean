module

public import ComparisonSignedCavityForestPhysicalHistories

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

theorem native_single_persistentLowForks_of_terminal (as : List PositiveMass) (star U : ℕ)
    (h : as.length=0 ∨ as.length=star ∨ U≤as.length) :
    NativePersistentLowForks 0 star U (single (S:=S) as) := by
  intro c d
  have hc:=native_single_slot_eq as c
  have hd:=native_single_slot_eq as d
  subst c
  subst d
  simpa only [splitIndex_self] using h

theorem native_persistentLowForks_fork_zero {as : List PositiveMass}
    {T V : ClockTree S as} {star U : ℕ}
    (hT : NativePersistentLowForks 0 star U T) (hV : NativePersistentLowForks 0 star U V) :
    NativePersistentLowForks 0 star U (T.fork V) := by
  intro c d
  cases c with
  | inl c=>cases d with
    | inl d=>exact hT c d
    | inr d=>exact Or.inl rfl
  | inr c=>cases d with
    | inl d=>exact Or.inl rfl
    | inr d=>exact hV c d

theorem nativeGroupRootForest_exterior_lowForks {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) {star U : ℕ}
    (hT : NativePersistentLowForks 0 star U T) :
    NativePersistentLowForks 0 star U (nativeGroupRootForest T s).exterior := by
  induction T with
  | leaf=>exact native_single_persistentLowForks_of_terminal [] star U (Or.inl rfl)
  | @step b tail T ih=>
    apply native_single_persistentLowForks_of_terminal (b::tail) star U
    simpa only [splitIndex_self] using hT s s
  | fork T V ihT ihV=>
    have hL : NativePersistentLowForks 0 star U T:=fun c d=>hT (Sum.inl c) (Sum.inl d)
    have hR : NativePersistentLowForks 0 star U V:=fun c d=>hT (Sum.inr c) (Sum.inr d)
    cases s with
    | inl s=>exact native_persistentLowForks_fork_zero hR (ihT s hL)
    | inr s=>exact native_persistentLowForks_fork_zero hL (ihV s hR)

theorem NativeRootForestGrouping.read_exterior_relative {as : List PositiveMass}
    {T : ClockTree S as} {s : T.Slot} (g : NativeRootForestGrouping T s)
    (has : as≠[]) (c : T.Slot) (hc : T.splitIndex s c=0) :
    ∃e : g.exterior.Slot,∀η σ,T.atSlot (g.read η σ) c=g.exterior.atSlot η e := by
  have he : g.embed s=Sum.inr g.target := by
    calc
      _=g.embed (g.occupiedEmbed g.target):=congrArg g.embed g.target_eq.symm
      _=Sum.inr g.target:=g.occupied_embed g.target
  have H:=g.old_splits s c
  rw [he,hc] at H
  cases hd:g.embed c with
  | inl e=>
    refine ⟨e,?_⟩
    intro η σ
    rw [g.read_at,hd]
    rfl
  | inr d=>
    have HP:=g.root_free.split_pos has g.target d
    simp only [hd,splitIndex,Sum.elim_inr] at H
    omega

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_star_arm_classification (mid tail : List PositiveMass)
    (T : ClockTree S (mid++tail)) (s : T.Slot) {U : ℕ}
    (hmid : 0 < mid.length) (hU : mid.length<U)
    (hT : NativePersistentLowForks 0 mid.length U T)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (mid++tail)) :
    ∃(E : ClockTree S (mid++tail)) (D : ClockTree S tail)
      (read : E.Assignment → D.Assignment → T.Assignment) (target : D.Slot),
      NativePersistentLowForks 0 mid.length U E ∧
      (∀η σ,T.atSlot (read η σ) s=D.atSlot σ target) ∧
      (∀c,T.splitIndex s c=0 → ∃e : E.Slot,∀η σ,T.atSlot (read η σ) c=E.atSlot η e) ∧
      (∀c,mid.length≤T.splitIndex s c → ∃d : D.Slot,
        (∀η σ,T.atSlot (read η σ) c=D.atSlot σ d) ∧
        mid.length+D.splitIndex target d=T.splitIndex s c) ∧
      (∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
        T.expect w φ q Q x=(E.fork (exteriorPrepend mid D)).expect w φ q
          (fun σ=>Q (read σ.1 (exteriorPrependAssignmentEquiv mid D σ.2))) x) := by
  have Hmiddle:=native_group_occupied_shares_middle mid T s hU hT
  have hE:=nativeGroupRootForest_exterior_lowForks T s hT
  have hLaw : ∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
      T.expect w φ q Q x=((nativeGroupRootForest T s).exterior.fork (nativeGroupRootForest T s).occupied).expect w φ q
        (fun σ=>Q ((nativeGroupRootForest T s).read σ.1 σ.2)) x :=
    fun q Q x=>nativeGroupRootForest_expect T s hw φ ho q Q x
  have hTarget:=fun η σ=>(nativeGroupRootForest T s).read_target η σ
  have hHigh:=fun c hc=>(nativeGroupRootForest T s).read_high_relative c hc
  have has : mid++tail≠[] := by
    intro H
    have HM:=congrArg List.length (List.append_eq_nil_iff.mp H).1
    simp only [List.length_nil] at HM
    omega
  have hOutside:=fun c hc=>(nativeGroupRootForest T s).read_exterior_relative has c hc
  generalize hg:nativeGroupRootForest T s=g at Hmiddle hE hLaw hTarget hHigh hOutside
  rcases g with ⟨E,Di,ti,readi,ei,oi,hti,hoi,hri,hsi,hio,hfree⟩
  obtain ⟨D,hD⟩:=native_exists_prepend_of_trunk_split mid Di ti Hmiddle
  subst Di
  let d:=exteriorPrependSlotEquiv mid D ti
  let R:=fun η σ=>readi η ((exteriorPrependAssignmentEquiv mid D).symm σ)
  refine ⟨E,D,R,d,hE,?_,?_,?_,?_⟩
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
  · intro q Q x
    simpa only [R,Equiv.symm_apply_apply] using hLaw q Q x

end OAI.SKFluctuations.Cavity
