module

public import ComparisonSignedCavityActualConstantTransientLowProfile
public import ComparisonSignedCavityActualHighSourceLinearity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem actual_nativeTransientLowErrorJet_add_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (k : ℕ) (l t : ℝ) :
    nativeTransientLowErrorJet n q U b h K T (fun σ=>P σ+Q σ) x k l t=
      nativeTransientLowErrorJet n q U b h K T P x k l t+
      nativeTransientLowErrorJet n q U b h K T Q x k l t := by
  exact actual_disorderProfileJets_add _ _ _ _ _ _ _ _ _

theorem actual_nativeTransientLowErrorJet_const_mul_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (x : FullCoordinate n→ℝ) (k : ℕ) (l t c : ℝ) :
    nativeTransientLowErrorJet n q U b h K T (fun σ=>c*P σ) x k l t=
      c*nativeTransientLowErrorJet n q U b h K T P x k l t := by
  exact disorderProfileJets_const_mul _ _ _ _ _ _ _ _ _

theorem actual_nativeActualCenteredThirdLowPart_add_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P Q : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (l t : ℝ) :
    nativeActualCenteredThirdLowPart n q U b h K T (fun σ=>P σ+Q σ) a z l t=
      nativeActualCenteredThirdLowPart n q U b h K T P a z l t+
      nativeActualCenteredThirdLowPart n q U b h K T Q a z l t := by
  unfold nativeActualCenteredThirdLowPart
  simp only [add_mul,actual_nativeTransientLowErrorJet_add_test,actual_productJet3_add_right]
  ring

theorem actual_nativeActualCenteredThirdLowPart_const_mul_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (l t c : ℝ) :
    nativeActualCenteredThirdLowPart n q U b h K T (fun σ=>c*P σ) a z l t=
      c*nativeActualCenteredThirdLowPart n q U b h K T P a z l t := by
  unfold nativeActualCenteredThirdLowPart
  simp only [mul_assoc,actual_nativeTransientLowErrorJet_const_mul_test,actual_productJet3_const_mul_right]
  ring

end OAI.SKFluctuations.Cavity
