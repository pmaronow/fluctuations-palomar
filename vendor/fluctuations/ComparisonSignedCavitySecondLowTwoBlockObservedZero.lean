module

public import ComparisonSignedCavitySecondLowObservedPartition
public import ComparisonSignedCavitySecondLowUnobservedSourceEntry
public import CavityPairSlots

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

theorem native_second_low_path_middle_distinct_endpoints {α : Type*}
    (A B f c e d : α) (j : Fin 8) (hfc : f ≠ c) (hed : e ≠ d)
    (H : nativeSecondLowBlockPath j A B f c e d) :
    nativeSecondLowPathMiddle j f c e d ≠ A ∧ nativeSecondLowPathMiddle j f c e d ≠ B := by
  fin_cases j
  all_goals dsimp only [nativeSecondLowBlockPath,nativeSecondLowPathMiddle] at H ⊢
  all_goals rcases H with ⟨H1,H2,H3⟩
  all_goals subst_vars
  all_goals simp_all [ne_eq,eq_comm]

theorem native_second_low_observed_class_zero_of_two_old_blocks
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (hcover : ∀ v : T.Slot, U ≤ T.splitIndex a v ∨ U ≤ T.splitIndex z v) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K T hU P a z j true = 0 := by
  have Hzero (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
      (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
      (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0) :
      (if nativeSecondLowWordPath U hU a z p r s t j ∧
        (nativeSecondLowWordObserved U p r s t j ↔ true=true)
        then nativeSecondLowWordValue n q U b h K P a z p r s t else 0) = 0 := by
    split_ifs with Hsource
    · rcases Hsource with ⟨Hpath,Hobserved⟩
      have Hobs := Hobserved.mpr rfl
      by_contra HZ
      have Hfc : r.tree.splitIndex (r.embed p.mark) r.mark < U := by
        by_contra HH
        have HE := native_second_low_joint_rest_test_zero_of_first_high n U b h K P p r s t (not_lt.mp HH)
        apply HZ
        unfold nativeSecondLowWordValue
        rw [HE]
        simp [ClockTree.disorderExpect]
      have Hed : t.tree.splitIndex (t.embed s.mark) t.mark < U := by
        by_contra HH
        have HE := native_second_low_joint_rest_test_zero_of_second_high n U b h K P p r s t (not_lt.mp HH)
        apply HZ
        unfold nativeSecondLowWordValue
        rw [HE]
        simp [ClockTree.disorderExpect]
      let embed := fun v : T.Slot => t.embed (s.embed (r.embed (p.embed v)))
      let B := t.tree.cutBlock U hU
      have Hpres (v w : T.Slot) : t.tree.splitIndex (embed v) (embed w) = T.splitIndex v w := by
        dsimp only [embed]
        rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
          (r.tree.markedAttach_embed_preserves 0 s hs).2,
          (p.tree.markedAttach_embed_preserves 0 r hr).2,
          (T.markedAttach_embed_preserves 0 p hp).2]
      have Hf : B (t.embed (s.embed (r.embed p.mark))) ≠ B (t.embed (s.embed r.mark)) := by
        intro HE
        have HI := (t.tree.cutBlock_eq_iff U hU _ _).mp HE
        rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
          (r.tree.markedAttach_embed_preserves 0 s hs).2] at HI
        omega
      have He : B (t.embed s.mark) ≠ B t.mark := by
        intro HE
        have HI := (t.tree.cutBlock_eq_iff U hU _ _).mp HE
        omega
      have HM := native_second_low_path_middle_distinct_endpoints
        (B (embed a)) (B (embed z)) (B (t.embed (s.embed (r.embed p.mark))))
        (B (t.embed (s.embed r.mark))) (B (t.embed s.mark)) (B t.mark) j Hf He Hpath
      have Hmid : B (nativeSecondLowWordMiddle p r s t j) ≠ B (embed a) ∧
          B (nativeSecondLowWordMiddle p r s t j) ≠ B (embed z) := by
        rw [nativeSecondLowWordMiddle,nativeSecondLowPathMiddle_map B j _ _ _ _]
        exact HM
      obtain ⟨v,hv⟩ := Hobs
      have HV : B (embed v) = B (nativeSecondLowWordMiddle p r s t j) :=
        (t.tree.cutBlock_eq_iff U hU _ _).mpr hv
      rcases hcover v with HA | HB
      · have HE : B (embed a) = B (embed v) := (t.tree.cutBlock_eq_iff U hU _ _).mpr (Hpres a v ▸ HA)
        exact Hmid.1 (HE.trans HV).symm
      · have HE : B (embed z) = B (embed v) := (t.tree.cutBlock_eq_iff U hU _ _).mpr (Hpres z v ▸ HB)
        exact Hmid.2 (HE.trans HV).symm
    · rfl
  unfold nativeSecondLowClassLedger
  have HE : nativeSecondLowDoubleAverage T (fun p r => nativeSecondLowDoubleAverage r.tree
      (fun s t => if nativeSecondLowWordPath U hU a z p r s t j ∧
        (nativeSecondLowWordObserved U p r s t j ↔ true=true)
        then nativeSecondLowWordValue n q U b h K P a z p r s t else 0)) =
      nativeSecondLowDoubleAverage T (fun _ _ => 0) := by
    apply native_second_low_double_average_congr
    intro p hp r hr
    have HH := native_second_low_double_average_congr r.tree _ (fun _ _ => 0) (Hzero p hp r hr)
    simpa [nativeSecondLowDoubleAverage] using HH
  rw [HE]
  simp [nativeSecondLowDoubleAverage]

end OAI.SKFluctuations.Cavity
