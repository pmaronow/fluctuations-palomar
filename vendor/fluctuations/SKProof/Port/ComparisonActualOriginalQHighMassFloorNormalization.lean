module

public import ComparisonNativeActualHighMassFloorNormalization
public import SKProof.Port.ComparisonActualOriginalQHighMassCriticalRates

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_direct_test_floor_strong_rate
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs) :
    a.data.N^delta*(a.data.U^2*a.directTestWorkingScale^2/a.xs^4) ≤
      (Cs+1)^2*C0^6*a.data.N^(-(6*m-delta)) := by
  have hE := a.data.hE
  have hd := a.data.hd
  have hN := a.data.hN
  have hx := a.hxs
  have HW := a.canonical_direct_test_band_pos
  have Hcap := a.canonical_direct_test_cap_strong_rate hC0 hCs hsmall
  have Hcritical := a.canonical_high_mass_critical_ratio hC0
  have Hcap0 : 0 ≤ (a.data.E/a.data.d^3)*(a.directTestWorkingScale^2/a.xs^4) := by positivity
  have Hcritical0 : 0 ≤ a.data.d^3/(a.data.N^2*a.data.E^3) := by positivity
  have Hmul := mul_le_mul Hcap Hcritical Hcritical0
    (show 0 ≤ (Cs+1)^2*C0^3*a.data.N^(-3*m) by positivity)
  have he : ((a.data.E/a.data.d^3)*(a.directTestWorkingScale^2/a.xs^4))*
      (a.data.d^3/(a.data.N^2*a.data.E^3))=
      a.data.U^2*a.directTestWorkingScale^2/a.xs^4 := by
    unfold ActualHighWallData.U comparisonSmallMass
    field_simp
  rw [he] at Hmul
  have Hfinal := mul_le_mul_of_nonneg_left Hmul (Real.rpow_nonneg hN.le delta)
  have he₂ : a.data.N^delta*((Cs+1)^2*C0^3*a.data.N^(-3*m)*
      (C0^3*a.data.N^(-3*m)))=(Cs+1)^2*C0^6*a.data.N^(-(6*m-delta)) := by
    calc
      _ = (Cs+1)^2*C0^6*((a.data.N^delta*a.data.N^(-3*m))*a.data.N^(-3*m)) := by ring
      _ = (Cs+1)^2*C0^6*a.data.N^(delta+-3*m+-3*m) := by
        rw [←Real.rpow_add hN,←Real.rpow_add hN]
      _ = _ := by rw [show delta+-3*m+-3*m=-(6*m-delta) by ring]
  rw [he₂] at Hfinal
  exact Hfinal

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
