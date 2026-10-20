module

public import ComparisonSignedCavitySecondLowClassifiedWholeCloneDisorderLaw
public import ComparisonSignedCavityActualExteriorPayloadSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

structure NativeSecondLowClassifiedRetainedWholeCSource
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (f c z : T.Slot)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) where
  source : NativeClassifiedWholeRetainedSource pre mid tail T.cavityLeft (T.cavityLeftSlot c)
    (restWeight n) (restFeature n)
  outsideF : source.Ei.Assignment→source.Es.Assignment→Spin n
  outsideZ : source.Ei.Assignment→source.Es.Assignment→Spin n
  outside_f_read : ∀η ζ δ,T.cavityLeft.atSlot (source.read η ζ δ) (T.cavityLeftSlot f)=outsideF η ζ
  outside_z_read : ∀η ζ δ,T.cavityLeft.atSlot (source.read η ζ δ) (T.cavityLeftSlot z)=outsideZ η ζ

namespace NativeSecondLowClassifiedRetainedWholeCSource
variable {n : ℕ} {pre mid tail : List PositiveMass}
variable {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {f c z : T.Slot}
variable {v : RestCoordinate n→ℝ} {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

def toWholeCSource (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (ho : MassOrdered 0 (pre++(mid++tail))) :
    NativeSecondLowClassifiedWholeCSource n pre mid tail T f c z v q x where
  Ei:=E.source.Ei
  Es:=E.source.Es
  D:=E.source.D
  read:=E.source.read
  target:=E.source.target
  outsideF:=E.outsideF
  outsideZ:=E.outsideZ
  target_read:=E.source.target_read
  outside_f_read:=E.outside_f_read
  outside_z_read:=E.outside_z_read
  incoming_i:=E.source.incoming_i
  incoming_star:=E.source.incoming_star
  high:=E.source.high
  whole_law:=fun Q=>E.source.whole_law (restWeight_pos n) ho v q Q x

def originalSlot (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (d : E.source.D.Slot) : T.Slot:=T.cavityLeftSlot.symm (E.source.embedD d)

theorem originalSlot_cavity
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (d : E.source.D.Slot) : T.cavityLeftSlot (E.originalSlot d)=E.source.embedD d:=
  T.cavityLeftSlot.apply_symm_apply _

theorem originalSlot_injective
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x) :
    Function.Injective E.originalSlot:=by
  intro d e H
  have HH:=congrArg T.cavityLeftSlot H
  rw [E.originalSlot_cavity,E.originalSlot_cavity] at HH
  exact E.source.embed_injective HH

theorem originalSlot_target
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x) :
    E.originalSlot E.source.target=c:=by
  dsimp only [originalSlot]
  rw [E.source.embed_target]
  exact T.cavityLeftSlot.symm_apply_apply c

theorem occupied_leaves_le
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x) :
    E.source.D.leaves ≤ T.leaves:=by
  let :=nativeSecondLowSlotFintype E.source.D
  let :=nativeSecondLowSlotFintype T
  have H:=Fintype.card_le_of_injective E.originalSlot E.originalSlot_injective
  rw [native_second_low_slot_fintype_card_eq_leaves E.source.D,
    native_second_low_slot_fintype_card_eq_leaves T] at H
  exact H

theorem read_at_originalSlot
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (η : E.source.Ei.Assignment) (ζ : E.source.Es.Assignment) (δ : E.source.D.Assignment)
    (d : E.source.D.Slot) :
    T.cavityLeft.atSlot (E.source.read η ζ δ) (T.cavityLeftSlot (E.originalSlot d))=E.source.D.atSlot δ d:=by
  rw [E.originalSlot_cavity]
  exact E.source.read_at_embed η ζ δ d

theorem originalSlot_high
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    {U : ℕ} (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (d : E.source.D.Slot) : U ≤ T.splitIndex c (E.originalSlot d):=by
  have H:=E.source.occupied_high hstar hU hT.cavityLeft d
  have HS:=cavityLeft_splitIndex T c (E.originalSlot d)
  rw [E.originalSlot_cavity] at HS
  exact H.trans_eq HS

theorem outside_splits_at_originalSlot
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    {U : ℕ} (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (Hfc : T.splitIndex f c < U) (Hcz : T.splitIndex c z < U) (d : E.source.D.Slot) :
    T.splitIndex f (E.originalSlot d)=T.splitIndex f c ∧
      T.splitIndex (E.originalSlot d) z=T.splitIndex c z := by
  have HH : U ≤ T.splitIndex (E.originalSlot d) c:=by
    rw [T.splitIndex_symm]
    exact E.originalSlot_high hstar hU hT d
  constructor
  · have H:=T.splitIndex_low_eq_of_high (E.originalSlot d) c f HH
      (by rw [T.splitIndex_symm];exact Hfc)
    simpa only [T.splitIndex_symm] using H
  · exact T.splitIndex_low_eq_of_high (E.originalSlot d) c z HH Hcz

theorem two_low_at_each_occupied_slot
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (ho : MassOrdered 0 (pre++(mid++tail)))
    (P : T.cavityLeft.Assignment→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (hstar : pre.length+mid.length < U) (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (Hfc : T.splitIndex f c < U) (Hcz : T.splitIndex c z < U)
    (η : E.source.Ei.Assignment) (ζ : E.source.Es.Assignment) (δ : E.source.D.Assignment)
    (d : E.source.D.Slot) :
    nativeSecondLowUnweightedCOldPayload n U b h K T f (E.originalSlot d) z P (E.source.read η ζ δ)=
      (E.toWholeCSource ho).fullP P η ζ δ*(E.toWholeCSource ho).twoLow U b h K η ζ (E.source.D.atSlot δ d):=by
  obtain ⟨Hf,Hz⟩:=E.outside_splits_at_originalSlot hstar hU hT Hfc Hcz d
  unfold nativeSecondLowUnweightedCOldPayload
  rw [Hf,Hz,E.outside_f_read,E.outside_z_read,E.read_at_originalSlot]
  rfl

theorem whole_current_old_difference_read
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x)
    (ho : MassOrdered 0 (pre++(mid++tail)))
    (P : T.cavityLeft.Assignment→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (η : E.source.Ei.Assignment) (ζ : E.source.Es.Assignment) (δ : E.source.D.Assignment)
    (sc : Spin n) :
    P (E.source.read η ζ δ)*(restLowKernel n U b h (T.splitIndex f c)
      (T.cavityLeft.atSlot (E.source.read η ζ δ) (T.cavityLeftSlot f)) sc*
      restLowKernel n U b h (T.splitIndex c z) sc
        (T.cavityLeft.atSlot (E.source.read η ζ δ) (T.cavityLeftSlot z))-
      (if T.splitIndex f c < U then K (T.splitIndex f c) else 0)*
        (if T.splitIndex c z < U then K (T.splitIndex c z) else 0))-
      nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (E.source.read η ζ δ)=
    (E.toWholeCSource ho).fullP P η ζ δ*((E.toWholeCSource ho).twoLow U b h K η ζ sc-
      (E.toWholeCSource ho).twoLow U b h K η ζ (E.source.D.atSlot δ E.source.target)) := by
  dsimp only [toWholeCSource,NativeSecondLowClassifiedWholeCSource.fullP,
    NativeSecondLowClassifiedWholeCSource.twoLow]
  unfold nativeSecondLowUnweightedCOldPayload
  rw [E.outside_f_read,E.outside_z_read,E.source.target_read]
  ring

end NativeSecondLowClassifiedRetainedWholeCSource

theorem native_second_low_classified_retained_whole_c_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (f c z : T.Slot) (U : ℕ)
    (hmid : 0 < mid.length) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length) (ho : MassOrdered 0 (pre++(mid++tail)))
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (Hfc : T.splitIndex c f ≤ pre.length+mid.length)
    (Hcz : T.splitIndex c z ≤ pre.length+mid.length)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    Nonempty (NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x) := by
  obtain ⟨E⟩:=native_classified_whole_retained_source pre mid tail T.cavityLeft (T.cavityLeftSlot c)
    hmid hstar (by simpa only [List.length_append,Nat.add_assoc] using hU) hT.cavityLeft
    (restWeight_pos n) (restFeature n) ho
  let labels : Fin 2→T.cavityLeft.Slot:=![T.cavityLeftSlot f,T.cavityLeftSlot z]
  have hlow : ∀j,T.cavityLeft.splitIndex (T.cavityLeftSlot c) (labels j) ≤ pre.length+mid.length:=by
    intro j
    fin_cases j
    · change T.cavityLeft.splitIndex (T.cavityLeftSlot c) (T.cavityLeftSlot f) ≤ _
      simpa only [cavityLeft_splitIndex] using Hfc
    · change T.cavityLeft.splitIndex (T.cavityLeftSlot c) (T.cavityLeftSlot z) ≤ _
      simpa only [cavityLeft_splitIndex] using Hcz
  obtain ⟨outside,Hread⟩:=native_two_level_exterior_read_independent pre mid tail T.cavityLeft
    (T.cavityLeftSlot c) hstar hT.cavityLeft E.Ei E.Es E.D E.read E.incoming_i E.incoming_star labels hlow
  refine ⟨⟨E,fun η ζ=>outside η ζ 0,fun η ζ=>outside η ζ 1,?_,?_⟩⟩
  · intro η ζ δ
    exact Hread η ζ δ 0
  · intro η ζ δ
    exact Hread η ζ δ 1

theorem native_second_low_actual_fresh_occupied_post_f_classified_retained_whole_c_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s : T.Slot) (U : ℕ)
    (hmid : 0 < mid.length) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length) (ho : MassOrdered 0 (pre++(mid++tail)))
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree)
    (hp : p∈nativeHighMarkedRows (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree
      ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed s) (U-1) 0)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    Nonempty (NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail p.tree p.mark
      (p.embed ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed
        (nativeSecondLowFreshOccupiedOldSlot T s (pre.length+mid.length) U hU B)))
      (p.embed (nativeFreshAtSlot T 0 s (pre.length+mid.length)).mark) v q x) := by
  let g:=nativeFreshAtSlot T 0 s (pre.length+mid.length)
  let oldv:=nativeSecondLowFreshOccupiedOldSlot T s (pre.length+mid.length) U hU B
  obtain ⟨hp0,hpH⟩:=(mem_nativeHighMarkedRows g.tree (g.embed s) (U-1) 0 p).mp hp
  have HpH : U ≤ p.tree.splitIndex p.mark (p.embed (g.embed s)):=by
    rw [p.tree.splitIndex_symm]
    omega
  have Hp:NativePersistentLowForks pre.length (pre.length+mid.length) U p.tree:=
    (hT.freshStar 0 s).observedHigh (by omega) hstar 0 p hp0 (g.embed s) HpH
  have Hgeometry:=native_second_low_fresh_occupied_old_slot_low_forks T s pre.length
    (pre.length+mid.length) U hU (by omega) hT B
  have Hv : T.splitIndex s oldv ≤ pre.length+mid.length:=Hgeometry.2
  have Hfc : p.tree.splitIndex (p.embed (g.embed oldv)) p.mark ≤ pre.length+mid.length:=by
    have Hlow : p.tree.splitIndex (p.embed (g.embed s)) (p.embed (g.embed oldv)) < U:=by
      rw [(g.tree.markedAttach_embed_preserves 0 p hp0).2,(nativeFreshAtSlot_old_splits T 0 s _).2]
      exact Hv.trans_lt hstar
    rw [p.tree.splitIndex_symm]
    rw [p.tree.splitIndex_low_eq_of_high p.mark (p.embed (g.embed s)) (p.embed (g.embed oldv)) HpH Hlow,
      (g.tree.markedAttach_embed_preserves 0 p hp0).2,(nativeFreshAtSlot_old_splits T 0 s _).2]
    exact Hv
  have Hcz : p.tree.splitIndex (p.embed (g.embed oldv)) (p.embed g.mark) ≤ pre.length+mid.length:=by
    rw [(g.tree.markedAttach_embed_preserves 0 p hp0).2,g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact Nat.min_le_left _ _
  exact native_second_low_classified_retained_whole_c_source n pre mid tail p.tree p.mark _ _ U
    hmid hstar hU ho Hp Hfc Hcz v q x

theorem native_second_low_actual_resource_fresh_occupied_post_f_classified_retained_whole_c_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (s : T.Slot) (hmid : 0 < mid.length) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length) (ho : MassOrdered 0 (pre++(mid++tail)))
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree)
    (hp : p∈nativeHighMarkedRows (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree
      ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed s) (U-1) 0)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    Nonempty (NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail p.tree p.mark
      (p.embed ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed
        (nativeSecondLowFreshOccupiedOldSlot T s (pre.length+mid.length) U hU B)))
      (p.embed (nativeFreshAtSlot T 0 s (pre.length+mid.length)).mark) v q x) :=
  native_second_low_actual_fresh_occupied_post_f_classified_retained_whole_c_source n pre mid tail T s U
    hmid hstar hU ho (hP.persistentLowForks (by omega)) B p hp v q x

end OAI.SKFluctuations.Cavity
