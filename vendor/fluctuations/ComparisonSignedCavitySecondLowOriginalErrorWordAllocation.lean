module

public import ComparisonSignedCavitySecondLowInitialPhysicalSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators NNReal
set_option maxHeartbeats 30000000

def nativeSecondLowFirstErrorWord (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  t.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
    (nativeOldInitialRowProduct n t.tree (nativeSecondLowOldTest P p r s t)
      (nativeSmallCutOldErrorRestKernel n U b h K)
      (t.embed (s.embed (r.embed p.mark))) (t.embed (s.embed r.mark))
      (fun k : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] k) (![1,0] k))
      ![t.embed s.mark,t.embed (s.embed (r.embed (p.embed a)))]
      ![t.mark,t.embed (s.embed (r.embed (p.embed z)))]) 0

def nativeSecondLowSecondErrorWord (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  t.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
    (nativeOldInitialRowProduct n t.tree (nativeSecondLowOldTest P p r s t)
      (nativeSmallCutOldErrorRestKernel n U b h K) (t.embed s.mark) t.mark
      (fun k : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] k) (![0,0] k))
      ![t.embed (s.embed (r.embed p.mark)),t.embed (s.embed (r.embed (p.embed a)))]
      ![t.embed (s.embed r.mark),t.embed (s.embed (r.embed (p.embed z)))]) 0

theorem native_second_low_original_word_eq_error_allocations
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    nativeSecondLowWordValue n q U b h K P a z p r s t=
      nativeSecondLowFirstErrorWord n q U b h K P a z p r s t+
      nativeSecondLowSecondErrorWord n q U b h K P a z p r s t := by
  rw [native_second_low_joint_word_eq_original_physical_payload n q U b h K T ho P a z p r s hs t ht,
    native_second_low_physical_QQKK_expect_eq_two_initial_products]
  rfl

end OAI.SKFluctuations.Cavity
