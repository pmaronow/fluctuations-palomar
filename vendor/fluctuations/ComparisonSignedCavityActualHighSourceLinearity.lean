module

public import CavityDiagonalHigherJets
public import ComparisonSignedCavityCenteredFixedLowHigh
public import ComparisonSignedCavityCenteredTransientHighThird

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

omit [Fintype S] [Nonempty S] in
theorem actual_profilePairTest_add {as : List PositiveMass} {T : ClockTree S as}
    (P Q : T.Assignment→ℝ) (K : ℕ→S→S→ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
    profilePairTest (fun σ=>P σ+Q σ) K p r=
      fun σ=>profilePairTest P K p r σ+profilePairTest Q K p r σ := by
  funext σ
  dsimp only [profilePairTest]
  ring

omit [Nonempty S] [Nonempty ι] in
theorem actual_disorderProfileJets_add (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (Ks : List (ℕ→S→S→ℝ)) (T : ClockTree S as) (P Q : T.Assignment→ℝ) :
    disorderProfileJets w φ v q x Ks T (fun σ=>P σ+Q σ)=
      disorderProfileJets w φ v q x Ks T P+disorderProfileJets w φ v q x Ks T Q := by
  induction Ks generalizing T with
  | nil=>simp only [disorderProfileJets,disorderExpect,mul_add,Finset.sum_add_distrib]
  | cons K Ks ih=>
    simp only [disorderProfileJets,actual_profilePairTest_add,ih,mul_add,List.sum_map_add]
    ring

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem actual_productJet3_add_right (g f h : Fin 4→ℝ) (k : Fin 4) :
    productJet3 g (fun i=>f i+h i) k=productJet3 g f k+productJet3 g h k := by
  fin_cases k <;> simp only [productJet3] <;> ring

theorem actual_productJet3_const_mul_right (g f : Fin 4→ℝ) (k : Fin 4) (c : ℝ) :
    productJet3 g (fun i=>c*f i) k=c*productJet3 g f k := by
  fin_cases k <;> simp only [productJet3] <;> ring

theorem actual_nativeFixedLowHighProfile_add_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ)
    (k r : ℕ) (s l t : ℝ) :
    nativeFixedLowHighProfile n q U b h K T (fun σ=>P σ+Q σ) k r s l t=
      nativeFixedLowHighProfile n q U b h K T P k r s l t+
      nativeFixedLowHighProfile n q U b h K T Q k r s l t := by
  exact actual_disorderProfileJets_add _ _ _ _ _ _ _ _ _

theorem actual_nativeFixedLowHighProfile_const_mul_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (k r : ℕ) (s l t c : ℝ) :
    nativeFixedLowHighProfile n q U b h K T (fun σ=>c*P σ) k r s l t=
      c*nativeFixedLowHighProfile n q U b h K T P k r s l t := by
  exact disorderProfileJets_const_mul _ _ _ _ _ _ _ _ _

theorem actual_nativeCenteredFixedLowHigh_add_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ)
    (a z : T.Slot) (k : Fin 4) (r : ℕ) (t : ℝ) :
    nativeCenteredFixedLowHigh n q U b h K T (fun σ=>P σ+Q σ) a z k r t=
      nativeCenteredFixedLowHigh n q U b h K T P a z k r t+
      nativeCenteredFixedLowHigh n q U b h K T Q a z k r t := by
  unfold nativeCenteredFixedLowHigh
  simp only [add_mul,actual_nativeFixedLowHighProfile_add_test,actual_productJet3_add_right]
  ring

theorem actual_nativeCenteredFixedLowHigh_const_mul_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (a z : T.Slot) (k : Fin 4) (r : ℕ) (t c : ℝ) :
    nativeCenteredFixedLowHigh n q U b h K T (fun σ=>c*P σ) a z k r t=
      c*nativeCenteredFixedLowHigh n q U b h K T P a z k r t := by
  unfold nativeCenteredFixedLowHigh
  simp only [mul_assoc,actual_nativeFixedLowHighProfile_const_mul_test,actual_productJet3_const_mul_right]
  ring

theorem actual_nativeTransientHighJet_add_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (k : ℕ) (l t : ℝ) :
    nativeTransientHighJet n q U b h K T (fun σ=>P σ+Q σ) x k l t=
      nativeTransientHighJet n q U b h K T P x k l t+
      nativeTransientHighJet n q U b h K T Q x k l t := by
  exact actual_disorderProfileJets_add _ _ _ _ _ _ _ _ _

theorem actual_nativeTransientHighJet_const_mul_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (k : ℕ) (l t c : ℝ) :
    nativeTransientHighJet n q U b h K T (fun σ=>c*P σ) x k l t=
      c*nativeTransientHighJet n q U b h K T P x k l t := by
  exact disorderProfileJets_const_mul _ _ _ _ _ _ _ _ _

theorem actual_nativeCenteredTransientHighThird_add_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ)
    (a z : T.Slot) (l t : ℝ) :
    nativeCenteredTransientHighThird n q U b h K T (fun σ=>P σ+Q σ) a z l t=
      nativeCenteredTransientHighThird n q U b h K T P a z l t+
      nativeCenteredTransientHighThird n q U b h K T Q a z l t := by
  unfold nativeCenteredTransientHighThird
  simp only [add_mul,actual_nativeTransientHighJet_add_test,actual_productJet3_add_right]
  ring

theorem actual_nativeCenteredTransientHighThird_const_mul_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (a z : T.Slot) (l t c : ℝ) :
    nativeCenteredTransientHighThird n q U b h K T (fun σ=>c*P σ) a z l t=
      c*nativeCenteredTransientHighThird n q U b h K T P a z l t := by
  unfold nativeCenteredTransientHighThird
  simp only [mul_assoc,actual_nativeTransientHighJet_const_mul_test,actual_productJet3_const_mul_right]
  ring

end OAI.SKFluctuations.Cavity
