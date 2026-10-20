module

public import ComparisonSignedCavitySecondLowJointPathPartition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

theorem native_second_low_double_average_add {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (F G : (p : MarkedPlacement T)→MarkedPlacement p.tree→ℝ) :
    nativeSecondLowDoubleAverage T (fun p r=>F p r+G p r)=
      nativeSecondLowDoubleAverage T F+nativeSecondLowDoubleAverage T G := by
  unfold nativeSecondLowDoubleAverage
  simp only [mul_add,List.sum_map_add,add_div]

def nativeSecondLowClassLedger (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (j : Fin 8) (observed : Bool) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r=>nativeSecondLowDoubleAverage r.tree (fun s t=>
    if nativeSecondLowWordPath U hU a z p r s t j ∧
        (nativeSecondLowWordObserved U p r s t j ↔ observed=true)
      then nativeSecondLowWordValue n q U b h K P a z p r s t else 0))

theorem native_second_low_path_ledger_eq_observed_add_unobserved (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) :
    nativeSecondLowPathLedger n q U b h K T hU P a z j=
      nativeSecondLowClassLedger n q U b h K T hU P a z j true+
      nativeSecondLowClassLedger n q U b h K T hU P a z j false := by
  unfold nativeSecondLowPathLedger nativeSecondLowClassLedger
  rw [←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro p hp r hr
  rw [←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro s hs t ht
  by_cases H : nativeSecondLowWordPath U hU a z p r s t j
  <;> by_cases O : nativeSecondLowWordObserved U p r s t j
  <;> simp [H,O]

theorem native_second_low_joint_ledger_half_eq_observed_unobserved (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (haz : T.splitIndex a z<U) :
    nativeSecondLowJointLedger n q U b h K T P [a,z]/2=
      (∑j : Fin 8,nativeSecondLowClassLedger n q U b h K T hU P a z j true/2)+
      (∑j : Fin 8,nativeSecondLowClassLedger n q U b h K T hU P a z j false/2) := by
  rw [native_second_low_joint_ledger_half_eq_eight_paths n q U b h K T ho hU P a z haz]
  simp_rw [native_second_low_path_ledger_eq_observed_add_unobserved,add_div]
  exact Finset.sum_add_distrib

theorem actual_second_low_centered_half_eq_observed_unobserved (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (haz : T.splitIndex a z<U)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 2 0 0/2=
      (∑j : Fin 8,nativeSecondLowClassLedger n q U b h K T hU P a z j true/2)+
      (∑j : Fin 8,nativeSecondLowClassLedger n q U b h K T hU P a z j false/2) := by
  rw [actual_second_low_centered_eq_joint_ledger n q U b h K T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz]
  exact native_second_low_joint_ledger_half_eq_observed_unobserved n q U b h K T ho hU P a z haz

end OAI.SKFluctuations.Cavity
