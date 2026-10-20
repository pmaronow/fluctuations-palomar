module

public import ComparisonSignedCavitySecondLowCanonicalFreshMiddleSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators
set_option maxHeartbeats 45000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_second_low_occupied_gamma_word_endpoint_block_zero
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a v z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Hv : U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed v))))
      (nativeSecondLowWordMiddle p r s t j))
    (HB : T.cutBlock U hU a=T.cutBlock U hU v ∨ T.cutBlock U hU z=T.cutBlock U hU v) :
    nativeSecondLowGammaWordValue n q U b h K P a z j p r s t=0 := by
  by_contra HZ
  have H:=native_second_low_occupied_gamma_word_final_high_support n q U b h K T ho hU P a v z j p r s t Hv HZ
  have HM (k l : Fin 4)
      (Hkl : U ≤ T.splitIndex (nativeSecondLowChronologicalTargets j a v z k)
        (nativeSecondLowChronologicalTargets j a v z l)) :
      U ≤ t.tree.splitIndex (nativeSecondLowFinalWordMarks p r s t k) (nativeSecondLowFinalWordMarks p r s t l) := by
    have Hold : U ≤ t.tree.splitIndex
        (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z k)))))
        (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z l))))) := by
      rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,(r.tree.markedAttach_embed_preserves 0 s hs).2,
        (p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
      exact Hkl
    have Hk : U ≤ t.tree.splitIndex (nativeSecondLowFinalWordMarks p r s t k)
        (t.embed (s.embed (r.embed (p.embed (nativeSecondLowChronologicalTargets j a v z k))))) := by
      rw [t.tree.splitIndex_symm]
      exact H k
    exact t.tree.splitIndex_cut_trans U _ _ _ (t.tree.splitIndex_cut_trans U _ _ _ Hk Hold) (H l)
  have Zfirst (HF : U ≤ t.tree.splitIndex (nativeSecondLowFinalWordMarks p r s t 0)
      (nativeSecondLowFinalWordMarks p r s t 1)) :
      nativeSecondLowGammaWordValue n q U b h K P a z j p r s t=0 := by
    change U ≤ t.tree.splitIndex (t.embed (s.embed (r.embed p.mark))) (t.embed (s.embed r.mark)) at HF
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,(r.tree.markedAttach_embed_preserves 0 s hs).2] at HF
    unfold nativeSecondLowGammaWordValue
    rw [native_second_low_joint_rest_test_zero_of_first_high n U b h K P p r s t HF]
    simp [ClockTree.disorderExpect]
  have Zsecond (HF : U ≤ t.tree.splitIndex (nativeSecondLowFinalWordMarks p r s t 2)
      (nativeSecondLowFinalWordMarks p r s t 3)) :
      nativeSecondLowGammaWordValue n q U b h K P a z j p r s t=0 := by
    change U ≤ t.tree.splitIndex (t.embed s.mark) t.mark at HF
    unfold nativeSecondLowGammaWordValue
    rw [native_second_low_joint_rest_test_zero_of_second_high n U b h K P p r s t HF]
    simp [ClockTree.disorderExpect]
  rcases HB with HB|HB
  · have HA:=(T.cutBlock_eq_iff U hU a v).mp HB
    fin_cases j
    all_goals first
      | exact HZ (Zfirst (HM 0 1 (by simpa [nativeSecondLowChronologicalTargets,T.splitIndex_symm] using HA)))
      | exact HZ (Zsecond (HM 2 3 (by simpa [nativeSecondLowChronologicalTargets,T.splitIndex_symm] using HA)))
  · have HB:=(T.cutBlock_eq_iff U hU z v).mp HB
    fin_cases j
    all_goals first
      | exact HZ (Zfirst (HM 0 1 (by simpa [nativeSecondLowChronologicalTargets,T.splitIndex_symm] using HB)))
      | exact HZ (Zsecond (HM 2 3 (by simpa [nativeSecondLowChronologicalTargets,T.splitIndex_symm] using HB)))

theorem native_second_low_occupied_gamma_endpoint_block_ledger_zero
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8)
    (B : T.CutBlock U hU) (HB : T.cutBlock U hU a=B ∨ T.cutBlock U hU z=B) :
    nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B=0 := by
  calc
    _=nativeSecondLowDoubleAverage T (fun _ r=>nativeSecondLowDoubleAverage r.tree (fun _ _=>0)):=by
      unfold nativeSecondLowOccupiedBlockGammaPathLedger
      apply native_second_low_double_average_congr
      intro p hp r hr
      apply native_second_low_double_average_congr
      intro s hs t ht
      split_ifs with HH
      · apply native_second_low_occupied_gamma_word_endpoint_block_zero n q U b h K T ho hU P a
          (nativeSecondLowOccupiedBlockRepresentative T U hU B) z j p hp r hr s hs t ht HH
        simpa only [native_second_low_occupied_block_representative_eq] using HB
      · rfl
    _=0:=by simp [nativeSecondLowDoubleAverage]

abbrev NativeSecondLowFreshOccupiedMiddleBlock {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (hU : U≤as.length) :=
  {B : (nativeFreshAtSlot T 0 s star).tree.CutBlock U hU //
    (nativeFreshAtSlot T 0 s star).tree.cutBlock U hU ((nativeFreshAtSlot T 0 s star).embed s)≠B ∧
    (nativeFreshAtSlot T 0 s star).tree.cutBlock U hU (nativeFreshAtSlot T 0 s star).mark≠B}

theorem native_second_low_fresh_occupied_middle_has_old_representative {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (hU : U≤as.length)
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU) :
    ∃v : T.Slot,nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s star).tree U hU B.val=
      (nativeFreshAtSlot T 0 s star).embed v := by
  rcases nativeFreshAtSlot_slot_coverage T 0 s star
    (nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s star).tree U hU B.val) with HR|HR
  · have HE:=native_second_low_occupied_block_representative_eq U hU B.val
    rw [HR] at HE
    exact False.elim (B.property.2 HE)
  · exact HR

def nativeSecondLowFreshOccupiedOldSlot {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (hU : U≤as.length)
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU) : T.Slot :=
  Classical.choose (native_second_low_fresh_occupied_middle_has_old_representative T s star U hU B)

theorem native_second_low_fresh_occupied_old_slot_exact {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (hU : U≤as.length)
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU) :
    nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s star).tree U hU B.val=
      (nativeFreshAtSlot T 0 s star).embed (nativeSecondLowFreshOccupiedOldSlot T s star U hU B) :=
  Classical.choose_spec (native_second_low_fresh_occupied_middle_has_old_representative T s star U hU B)

theorem native_second_low_fresh_occupied_old_slot_injective {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (hU : U≤as.length) :
    Function.Injective (nativeSecondLowFreshOccupiedOldSlot T s star U hU) := by
  intro B C H
  apply Subtype.ext
  calc
    B.val=(nativeFreshAtSlot T 0 s star).tree.cutBlock U hU
      (nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s star).tree U hU B.val):=
        (native_second_low_occupied_block_representative_eq U hU B.val).symm
    _=(nativeFreshAtSlot T 0 s star).tree.cutBlock U hU
      (nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s star).tree U hU C.val):=by
        rw [native_second_low_fresh_occupied_old_slot_exact,native_second_low_fresh_occupied_old_slot_exact,H]
    _=C.val:=native_second_low_occupied_block_representative_eq U hU C.val

theorem native_second_low_slot_fintype_card_eq_leaves {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) : @Fintype.card T.Slot (nativeSecondLowSlotFintype T)=T.leaves := by
  induction T with
  | leaf=>rfl
  | @step b as T ih=>exact ih
  | @fork as T V ihT ihV=>
    let :=nativeSecondLowSlotFintype T
    let :=nativeSecondLowSlotFintype V
    change Fintype.card (T.Slot⊕V.Slot)=T.leaves+V.leaves
    rw [Fintype.card_sum,ihT,ihV]

theorem native_second_low_fresh_occupied_middle_block_count {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (hU : U≤as.length) :
    Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s star U hU)≤T.leaves := by
  let :=nativeSecondLowSlotFintype T
  have H:=Fintype.card_le_of_injective (nativeSecondLowFreshOccupiedOldSlot T s star U hU)
    (native_second_low_fresh_occupied_old_slot_injective T s star U hU)
  rw [native_second_low_slot_fintype_card_eq_leaves T] at H
  exact H

theorem native_second_low_fresh_occupied_old_slot_low_forks {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (i star U : ℕ) (hU : U≤as.length)
    (hi : i ≤ star) (hT : NativePersistentLowForks i star U T)
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU) :
    let v:=nativeSecondLowFreshOccupiedOldSlot T s star U hU B
    (T.splitIndex v s=i ∨ T.splitIndex v s=star) ∧ T.splitIndex s v ≤ star := by
  dsimp only
  have HL : T.splitIndex s (nativeSecondLowFreshOccupiedOldSlot T s star U hU B)<U:=by
    have HE:=native_second_low_occupied_block_representative_eq U hU B.val
    rw [native_second_low_fresh_occupied_old_slot_exact] at HE
    have Hneq : (nativeFreshAtSlot T 0 s star).tree.cutBlock U hU ((nativeFreshAtSlot T 0 s star).embed s)≠
      (nativeFreshAtSlot T 0 s star).tree.cutBlock U hU
        ((nativeFreshAtSlot T 0 s star).embed (nativeSecondLowFreshOccupiedOldSlot T s star U hU B)):=by
      rw [HE]
      exact B.property.1
    have H:=cut_block_ne_split_lt (nativeFreshAtSlot T 0 s star).tree U hU _ _ Hneq
    rw [(nativeFreshAtSlot_old_splits T 0 s star).2] at H
    exact H
  have H:=hT s (nativeSecondLowFreshOccupiedOldSlot T s star U hU B)
  rw [T.splitIndex_symm] at H
  have HL' : T.splitIndex (nativeSecondLowFreshOccupiedOldSlot T s star U hU B) s<U:=by
    simpa only [T.splitIndex_symm] using HL
  constructor
  · rcases H with H|H|H
    · exact Or.inl H
    · exact Or.inr H
    · rw [T.splitIndex_symm] at H
      omega
  · rw [T.splitIndex_symm]
    rcases H with H|H|H <;> omega

end OAI.SKFluctuations.Cavity
