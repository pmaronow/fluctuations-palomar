module

public import ComparisonSignedCavitySecondLowClassifiedConditionalCFold
public import ComparisonSignedCavitySecondLowActualClassifiedRetainedCSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

structure NativeSecondLowClassifiedHighWholeCSource
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (f c z : T.Slot)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) where
  source : NativeClassifiedWholeHighRowSource pre mid tail T.cavityLeft (T.cavityLeftSlot c)
    (restWeight n) (restFeature n)
  outsideF : source.core.Ei.Assignment→source.core.Es.Assignment→Spin n
  outsideZ : source.core.Ei.Assignment→source.core.Es.Assignment→Spin n
  outside_f_read : ∀η ζ δ,T.cavityLeft.atSlot (source.core.read η ζ δ) (T.cavityLeftSlot f)=outsideF η ζ
  outside_z_read : ∀η ζ δ,T.cavityLeft.atSlot (source.core.read η ζ δ) (T.cavityLeftSlot z)=outsideZ η ζ

namespace NativeSecondLowClassifiedHighWholeCSource
variable {n : ℕ} {pre mid tail : List PositiveMass}
variable {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {f c z : T.Slot}
variable {v : RestCoordinate n→ℝ} {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

def toRetainedCSource (E : NativeSecondLowClassifiedHighWholeCSource n pre mid tail T f c z v q x) :
    NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v q x where
  source:=E.source.core
  outsideF:=E.outsideF
  outsideZ:=E.outsideZ
  outside_f_read:=E.outside_f_read
  outside_z_read:=E.outside_z_read

theorem c_replacement_value_eq_conditional_prefix
    (E : NativeSecondLowClassifiedHighWholeCSource n pre mid tail T f c z v q x)
    (U : ℕ) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length) (ho : MassOrdered 0 (pre++(mid++tail)))
    (qn : ℕ→RestCoordinate n→ℝ≥0) (P : T.cavityLeft.Assignment→ℝ)
    (Q : Spin n→Spin n→Spin n→ℝ) (y : RestCoordinate n→ℝ) :
    nativeSecondLowCReplacementValue T.cavityLeft (T.cavityLeftSlot c) U 0
      (restWeight n) (restFeature n) qn P (.slot (T.cavityLeftSlot f)) (.slot (T.cavityLeftSlot z)) Q y=
      prefixTest (clockSteps pre qn)
        (gaussianHierarchy (restWeight n) (restFeature n)
          (clockSteps (mid++tail) (fun j=>qn (pre.length+j))))
        (fun xi=>prefixTest (clockSteps mid (fun j=>qn (pre.length+j)))
          (gaussianHierarchy (restWeight n) (restFeature n)
            (clockSteps tail (fun j=>qn (pre.length+(mid.length+j)))))
          (nativeClassifiedConditionalCFold E.source.core.Ei E.source.core.Es E.source.core.D E.source.core.target
            (U-(pre.length+mid.length)) (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))
            (restWeight n) (restFeature n) (fun j=>qn (pre.length+j))
            (fun j=>qn (pre.length+(mid.length+j)))
            (fun η ζ δ=>P (E.source.core.read η ζ δ)) E.outsideF E.outsideZ Q xi) xi) y := by
  have HR:=E.source.high_joint_row_expect E.source.core.target U hstar 0 qn
    (fun σ new=>P σ*Q (T.cavityLeft.atSlot σ (T.cavityLeftSlot f)) new
      (T.cavityLeft.atSlot σ (T.cavityLeftSlot z))) y
  rw [E.source.core.embed_target] at HR
  have HO:=E.source.core.whole_expect qn
    (fun σ=>P σ*Q (T.cavityLeft.atSlot σ (T.cavityLeftSlot f))
      (T.cavityLeft.atSlot σ (T.cavityLeftSlot c)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot z))) y
  have Hrow : (fun σ new=>P (nativeClassifiedSourceRead pre mid E.source.core.Ei E.source.core.Es
      E.source.core.D E.source.core.read σ)*Q
      (T.cavityLeft.atSlot (nativeClassifiedSourceRead pre mid E.source.core.Ei E.source.core.Es
        E.source.core.D E.source.core.read σ) (T.cavityLeftSlot f)) new
      (T.cavityLeft.atSlot (nativeClassifiedSourceRead pre mid E.source.core.Ei E.source.core.Es
        E.source.core.D E.source.core.read σ) (T.cavityLeftSlot z)))=
      fun σ new=>nativeClassifiedSourceRead pre mid E.source.core.Ei E.source.core.Es E.source.core.D
        (fun η ζ δ=>P (E.source.core.read η ζ δ)*Q (E.outsideF η ζ) new (E.outsideZ η ζ)) σ := by
    funext σ new
    dsimp only [nativeClassifiedSourceRead]
    rw [E.outside_f_read,E.outside_z_read]
  rw [Hrow] at HR
  have Hold : (fun η ζ δ=>P (E.source.core.read η ζ δ)*Q
      (T.cavityLeft.atSlot (E.source.core.read η ζ δ) (T.cavityLeftSlot f))
      (T.cavityLeft.atSlot (E.source.core.read η ζ δ) (T.cavityLeftSlot c))
      (T.cavityLeft.atSlot (E.source.core.read η ζ δ) (T.cavityLeftSlot z)))=
      fun η ζ δ=>P (E.source.core.read η ζ δ)*Q (E.outsideF η ζ)
        (E.source.core.D.atSlot δ E.source.core.target) (E.outsideZ η ζ) := by
    funext η ζ δ
    rw [E.outside_f_read,E.outside_z_read,E.source.core.target_read]
  rw [Hold] at HO
  unfold nativeSecondLowCReplacementValue
  simp only [nativeSecondLowCSourceRows,show U≠0 by omega,ite_false,NativeSecondLowCReader.read]
  rw [HR,HO]
  exact native_classified_forest_c_replacement_eq_conditional_prefix pre mid tail E.source.core.Ei
    E.source.core.Es E.source.core.D E.source.core.target U hstar hU 0 (restWeight_pos n)
    (restFeature n) ho qn (fun η ζ δ=>P (E.source.core.read η ζ δ)) E.outsideF E.outsideZ Q y

theorem c_coupling_fold_eq_conditional_prefix
    (E : NativeSecondLowClassifiedHighWholeCSource n pre mid tail T f c z v q x)
    (U : ℕ) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length) (ho : MassOrdered 0 (pre++(mid++tail)))
    (Hcf : T.splitIndex c f < U) (Hcz : T.splitIndex c z < U)
    (qn : ℕ→RestCoordinate n→ℝ≥0) (P : T.cavityLeft.Assignment→ℝ)
    (Q : Spin n→Spin n→Spin n→ℝ) (y : RestCoordinate n→ℝ) :
    nativeSecondLowCCouplingFold (restWeight n) (restFeature n) T.cavityLeft (T.cavityLeftSlot c) U 0 qn P
      (.slot (T.cavityLeftSlot f)) (.slot (T.cavityLeftSlot z)) Q y=
      prefixTest (clockSteps pre qn)
        (gaussianHierarchy (restWeight n) (restFeature n)
          (clockSteps (mid++tail) (fun j=>qn (pre.length+j))))
        (fun xi=>prefixTest (clockSteps mid (fun j=>qn (pre.length+j)))
          (gaussianHierarchy (restWeight n) (restFeature n)
            (clockSteps tail (fun j=>qn (pre.length+(mid.length+j)))))
          (nativeClassifiedConditionalCFold E.source.core.Ei E.source.core.Es E.source.core.D E.source.core.target
            (U-(pre.length+mid.length)) (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))
            (restWeight n) (restFeature n) (fun j=>qn (pre.length+j))
            (fun j=>qn (pre.length+(mid.length+j)))
            (fun η ζ δ=>P (E.source.core.read η ζ δ)) E.outsideF E.outsideZ Q xi) xi) y := by
  rw [native_second_low_c_coupling_fold_eq_original (restWeight_pos n) (restFeature n) T.cavityLeft
    (T.cavityLeftSlot c) U ho hU (by omega) qn P (.slot (T.cavityLeftSlot f)) (.slot (T.cavityLeftSlot z))
    (by simpa only [NativeSecondLowCReader.low,cavityLeft_splitIndex] using Hcf)
    (by simpa only [NativeSecondLowCReader.low,cavityLeft_splitIndex] using Hcz)]
  exact E.c_replacement_value_eq_conditional_prefix U hstar hU ho qn P Q y

end NativeSecondLowClassifiedHighWholeCSource

theorem native_second_low_classified_high_whole_c_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (f c z : T.Slot) (U : ℕ)
    (hmid : 0 < mid.length) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length) (ho : MassOrdered 0 (pre++(mid++tail)))
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (Hfc : T.splitIndex c f ≤ pre.length+mid.length)
    (Hcz : T.splitIndex c z ≤ pre.length+mid.length)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    Nonempty (NativeSecondLowClassifiedHighWholeCSource n pre mid tail T f c z v q x) := by
  obtain ⟨E⟩:=native_classified_whole_high_row_source pre mid tail T.cavityLeft (T.cavityLeftSlot c)
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
    (T.cavityLeftSlot c) hstar hT.cavityLeft E.core.Ei E.core.Es E.core.D E.core.read E.core.incoming_i E.core.incoming_star labels hlow
  refine ⟨⟨E,fun η ζ=>outside η ζ 0,fun η ζ=>outside η ζ 1,?_,?_⟩⟩
  · intro η ζ δ
    exact Hread η ζ δ 0
  · intro η ζ δ
    exact Hread η ζ δ 1

theorem native_second_low_actual_fresh_occupied_post_f_classified_high_whole_c_source
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
    Nonempty (NativeSecondLowClassifiedHighWholeCSource n pre mid tail p.tree p.mark
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
  exact native_second_low_classified_high_whole_c_source n pre mid tail p.tree p.mark _ _ U
    hmid hstar hU ho Hp Hfc Hcz v q x

theorem native_second_low_actual_resource_fresh_occupied_post_f_classified_high_whole_c_source
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
    Nonempty (NativeSecondLowClassifiedHighWholeCSource n pre mid tail p.tree p.mark
      (p.embed ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed
        (nativeSecondLowFreshOccupiedOldSlot T s (pre.length+mid.length) U hU B)))
      (p.embed (nativeFreshAtSlot T 0 s (pre.length+mid.length)).mark) v q x) :=
  native_second_low_actual_fresh_occupied_post_f_classified_high_whole_c_source n pre mid tail T s U
    hmid hstar hU ho (hP.persistentLowForks (by omega)) B p hp v q x

end OAI.SKFluctuations.Cavity
