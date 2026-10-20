module

public import ComparisonSignedCavitySecondLowOccupiedBlockPartition
public import ComparisonSignedCavitySecondLowEightGammaWordSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowOccupiedBlockGammaPathLedger
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8)
    (B : T.CutBlock U hU) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r => nativeSecondLowDoubleAverage r.tree (fun s t =>
    if U ≤ t.tree.splitIndex
      (t.embed (s.embed (r.embed (p.embed (nativeSecondLowOccupiedBlockRepresentative T U hU B)))))
      (nativeSecondLowWordMiddle p r s t j)
    then nativeSecondLowGammaWordValue n q U b h K P a z j p r s t else 0))

theorem native_second_low_observed_class_eq_occupied_gamma_ledgers
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ)
    (a z : T.Slot) (haz : T.splitIndex a z < U) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K T hU P a z j true =
      ∑ B : T.CutBlock U hU, nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B := by
  unfold nativeSecondLowClassLedger nativeSecondLowOccupiedBlockGammaPathLedger
  rw [←native_second_low_double_average_univ]
  apply native_second_low_double_average_congr
  intro p hp r hr
  rw [←native_second_low_double_average_univ]
  apply native_second_low_double_average_congr
  intro s hs t ht
  have HE : (if nativeSecondLowWordPath U hU a z p r s t j ∧
      (nativeSecondLowWordObserved U p r s t j ↔ true=true)
      then nativeSecondLowWordValue n q U b h K P a z p r s t else 0) =
      (if nativeSecondLowWordObserved U p r s t j then
        (if nativeSecondLowWordPath U hU a z p r s t j
          then nativeSecondLowWordValue n q U b h K P a z p r s t else 0) else 0) := by
    by_cases HP : nativeSecondLowWordPath U hU a z p r s t j
    <;> by_cases HO : nativeSecondLowWordObserved U p r s t j
    <;> simp only [HP,HO,iff_true,and_true,and_false,ite_true,ite_false,eq_self]
  rw [HE,native_second_low_word_observed_value_eq_occupied_blocks T U hU p hp r hr s hs t ht j]
  apply Finset.sum_congr rfl
  intro B _
  by_cases HB : U ≤ t.tree.splitIndex
      (t.embed (s.embed (r.embed (p.embed (nativeSecondLowOccupiedBlockRepresentative T U hU B)))))
      (nativeSecondLowWordMiddle p r s t j)
  · simp only [HB,ite_true]
    exact native_second_low_masked_word_eq_gamma_source n q U b h K T ho hU P a z haz p hp r hr s hs t ht j
  · simp only [HB,ite_false]

theorem native_second_low_joint_half_eq_occupied_observed_add_unobserved
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ)
    (a z : T.Slot) (haz : T.splitIndex a z < U) :
    nativeSecondLowJointLedger n q U b h K T P [a,z]/2 =
      (∑ j : Fin 8, (∑ B : T.CutBlock U hU,
        nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU P a z j B)/2) +
      (∑ j : Fin 8, nativeSecondLowClassLedger n q U b h K T hU P a z j false/2) := by
  rw [native_second_low_joint_ledger_half_eq_observed_unobserved n q U b h K T ho hU P a z haz]
  simp_rw [native_second_low_observed_class_eq_occupied_gamma_ledgers n q U b h K T ho hU P a z haz]

theorem native_second_low_constant_joint_half_eq_occupied_observed_add_unobserved
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (a z : T.Slot) (haz : T.splitIndex a z < U) :
    nativeSecondLowJointLedger n q U b h K T (fun _ => 1) [a,z]/2 =
      (∑ j : Fin 8, (∑ B : T.CutBlock U hU,
        nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K T hU (fun _ => 1) a z j B)/2) +
      (∑ j : Fin 8, nativeSecondLowClassLedger n q U b h K T hU (fun _ => 1) a z j false/2) :=
  native_second_low_joint_half_eq_occupied_observed_add_unobserved n q U b h K T ho hU (fun _ => 1) a z haz

end OAI.SKFluctuations.Cavity
