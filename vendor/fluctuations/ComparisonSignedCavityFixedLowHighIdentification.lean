module

public import ComparisonSignedCavityOriginalFixedTwoHighBudget
public import ComparisonSignedCavityCenteredTransientHighThird

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem native_fixed_low_high_eq_frozen (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (P : T.Assignment→ℝ)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (k r : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    cutFrozenLowHighJet n q U b h K T P 0 k r t=
      nativeFixedLowHighProfile n q U b h K T P k r 1 0 t := by
  rw [cutFrozenLowHighJet_eq_profileJets n q U b h K T ho P 0 hq0 hq hb hh hK hbm hhm hKm k r ht]
  simp only [nativeFixedLowHighProfile,List.map_append,List.map_replicate]

end OAI.SKFluctuations.Cavity
