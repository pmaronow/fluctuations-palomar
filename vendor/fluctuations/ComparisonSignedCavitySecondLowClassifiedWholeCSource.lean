module

public import ComparisonSignedCavityTwoLevelExteriorPayload
public import ComparisonSignedCavitySecondLowObservedFreshOccupiedSource
public import ComparisonSignedCavitySecondLowUnweightedCRowSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

structure NativeSecondLowClassifiedWholeCSource
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (f c z : T.Slot)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) where
  Ei : ClockTree (Spin n) (mid++tail)
  Es : ClockTree (Spin n) tail
  D : ClockTree (Spin n) tail
  read : Ei.Assignment→Es.Assignment→D.Assignment→T.cavityLeft.Assignment
  target : D.Slot
  outsideF : Ei.Assignment→Es.Assignment→Spin n
  outsideZ : Ei.Assignment→Es.Assignment→Spin n
  target_read : ∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) (T.cavityLeftSlot c)=D.atSlot δ target
  outside_f_read : ∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) (T.cavityLeftSlot f)=outsideF η ζ
  outside_z_read : ∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) (T.cavityLeftSlot z)=outsideZ η ζ
  incoming_i : ∀d,T.cavityLeft.splitIndex (T.cavityLeftSlot c) d=pre.length → ∃e : Ei.Slot,
    ∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) d=Ei.atSlot η e
  incoming_star : ∀d,T.cavityLeft.splitIndex (T.cavityLeftSlot c) d=pre.length+mid.length → ∃e : Es.Slot,
    ∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) d=Es.atSlot ζ e
  high : ∀d,pre.length+mid.length < T.cavityLeft.splitIndex (T.cavityLeftSlot c) d → ∃e : D.Slot,
    (∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) d=D.atSlot δ e) ∧
    pre.length+mid.length+D.splitIndex target e=T.cavityLeft.splitIndex (T.cavityLeftSlot c) d
  whole_law : ∀Q : T.cavityLeft.Assignment→ℝ,
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q Q x=
      ∫r,nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n)
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ δ=>Q (read η ζ δ)) (exteriorForestIRoot r) (exteriorForestStarRoot r)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x

theorem native_second_low_classified_whole_c_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (f c z : T.Slot)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (Hsource : NativeClassifiedExteriorPayloadLaw pre mid tail T.cavityLeft (T.cavityLeftSlot c)
      (restWeight n) (restFeature n) v q x)
    (Hfc : T.splitIndex c f ≤ pre.length+mid.length)
    (Hcz : T.splitIndex c z ≤ pre.length+mid.length) :
    Nonempty (NativeSecondLowClassifiedWholeCSource n pre mid tail T f c z v q x) := by
  obtain ⟨Ei,Es,D,R,d,ht,hi,hs,hh,hlaw,hext⟩:=Hsource
  let labels : Fin 2→T.cavityLeft.Slot:=![T.cavityLeftSlot f,T.cavityLeftSlot z]
  have hlow : ∀j,T.cavityLeft.splitIndex (T.cavityLeftSlot c) (labels j) ≤ pre.length+mid.length:=by
    intro j
    fin_cases j
    · change T.cavityLeft.splitIndex (T.cavityLeftSlot c) (T.cavityLeftSlot f) ≤ _
      simpa only [cavityLeft_splitIndex] using Hfc
    · change T.cavityLeft.splitIndex (T.cavityLeftSlot c) (T.cavityLeftSlot z) ≤ _
      simpa only [cavityLeft_splitIndex] using Hcz
  obtain ⟨outside,Hread,_⟩:=hext (Fin 2) labels hlow
  refine ⟨⟨Ei,Es,D,R,d,fun η ζ=>outside η ζ 0,fun η ζ=>outside η ζ 1,ht,?_,?_,hi,hs,hh,hlaw⟩⟩
  · intro η ζ δ
    exact Hread η ζ δ 0
  · intro η ζ δ
    exact Hread η ζ δ 1

namespace NativeSecondLowClassifiedWholeCSource
variable {n : ℕ} {pre mid tail : List PositiveMass}
variable {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {f c z : T.Slot}
variable {v : RestCoordinate n→ℝ} {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

def fullP (E : NativeSecondLowClassifiedWholeCSource n pre mid tail T f c z v q x)
    (P : T.cavityLeft.Assignment→ℝ) : E.Ei.Assignment→E.Es.Assignment→E.D.Assignment→ℝ:=
  fun η ζ δ=>P (E.read η ζ δ)

def twoLow (E : NativeSecondLowClassifiedWholeCSource n pre mid tail T f c z v q x)
    (U : ℕ) (b h K : ℕ→ℝ) : E.Ei.Assignment→E.Es.Assignment→Spin n→ℝ:=
  fun η ζ sc=>restLowKernel n U b h (T.splitIndex f c) (E.outsideF η ζ) sc*
    restLowKernel n U b h (T.splitIndex c z) sc (E.outsideZ η ζ)-
    (if T.splitIndex f c < U then K (T.splitIndex f c) else 0)*
      (if T.splitIndex c z < U then K (T.splitIndex c z) else 0)

theorem whole_two_low_read (E : NativeSecondLowClassifiedWholeCSource n pre mid tail T f c z v q x)
    (P : T.cavityLeft.Assignment→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (η : E.Ei.Assignment) (ζ : E.Es.Assignment) (δ : E.D.Assignment) (sc : Spin n) :
    P (E.read η ζ δ)*(restLowKernel n U b h (T.splitIndex f c)
      (T.cavityLeft.atSlot (E.read η ζ δ) (T.cavityLeftSlot f)) sc*
      restLowKernel n U b h (T.splitIndex c z) sc
        (T.cavityLeft.atSlot (E.read η ζ δ) (T.cavityLeftSlot z))-
      (if T.splitIndex f c < U then K (T.splitIndex f c) else 0)*
        (if T.splitIndex c z < U then K (T.splitIndex c z) else 0))=
      E.fullP P η ζ δ*E.twoLow U b h K η ζ sc := by
  rw [E.outside_f_read,E.outside_z_read]
  rfl

theorem old_payload_whole_law (E : NativeSecondLowClassifiedWholeCSource n pre mid tail T f c z v q x)
    (P : T.cavityLeft.Assignment→ℝ) (U : ℕ) (b h K : ℕ→ℝ) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q
      (nativeSecondLowUnweightedCOldPayload n U b h K T f c z P) x=
      ∫r,nativeExteriorForestConditionalTest E.Ei E.Es E.D (restWeight n) (restFeature n)
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ δ=>E.fullP P η ζ δ*E.twoLow U b h K η ζ (E.D.atSlot δ E.target))
        (exteriorForestIRoot r) (exteriorForestStarRoot r)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  rw [E.whole_law]
  have HR : (fun η ζ δ=>nativeSecondLowUnweightedCOldPayload n U b h K T f c z P (E.read η ζ δ))=
      fun η ζ δ=>E.fullP P η ζ δ*E.twoLow U b h K η ζ (E.D.atSlot δ E.target) := by
    funext η ζ δ
    unfold nativeSecondLowUnweightedCOldPayload
    rw [E.whole_two_low_read,E.target_read]
  rw [HR]

end NativeSecondLowClassifiedWholeCSource

theorem native_second_low_actual_fresh_occupied_post_f_classified_whole_c_source
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
    Nonempty (NativeSecondLowClassifiedWholeCSource n pre mid tail p.tree p.mark
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
  apply native_second_low_classified_whole_c_source n pre mid tail p.tree p.mark _ _ v q x
    (native_classified_source_exterior_payload pre mid tail p.tree.cavityLeft _ hmid hstar
      (by simpa only [List.length_append,Nat.add_assoc] using hU) Hp.cavityLeft
      (restWeight_pos n) (restFeature n) ho v q x) Hfc Hcz

end OAI.SKFluctuations.Cavity
