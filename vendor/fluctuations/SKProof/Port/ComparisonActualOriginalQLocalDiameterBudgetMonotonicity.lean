module

public import ComparisonNativeActualLocalDiameterBudgetMonotonicity
public import SKProof.Port.ComparisonActualOriginalQLocalDiameterBudgetDefinitions

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

theorem canonical_mass_reverse_at_diameter_mono
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {ell : ℕ} (hell : 2 < ell) {Q v d₁ d₂ : ℝ}
    (hv : 0 ≤ v) (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂) :
    a.canonicalMassReverseAtDiameter ell Q v d₁ ≤ a.canonicalMassReverseAtDiameter ell Q v d₂ := by
  have he : (2:ℝ) < ell := by exact_mod_cast hell
  have htheta : 0 ≤ ((ell:ℝ)-2)/((ell:ℝ)-1) := div_nonneg (by linarith) (by linarith)
  have hEven : 0 ≤ (2*Q)^(2*ell) := by rw [Nat.mul_comm 2 ell,pow_mul]; exact sq_nonneg _
  have hxs := a.hxs
  have hy : 0 ≤ a.canonicalMassHeight v := by unfold canonicalMassHeight; positivity
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd₁ hd htheta)
    (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)

theorem canonical_broad_mass_budget_at_diameter_mono
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {ell : ℕ} (hell : 2 < ell) {Q Lside cut v width d₁ d₂ : ℝ}
    (hv : 0 ≤ v) (hLside : 0 ≤ Lside) (hwidth : 0 ≤ width)
    (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂) :
    a.canonicalBroadMassBudgetAtDiameter ell Q Lside cut v width d₁ ≤
      a.canonicalBroadMassBudgetAtDiameter ell Q Lside cut v width d₂ := by
  have HR := a.canonical_mass_reverse_at_diameter_mono (Q:=Q) hell hv hd₁ hd
  have HD := pow_le_pow_left₀ hd₁ hd 2
  have HE := mul_le_mul_of_nonneg_left HD (show 0 ≤ (76+64*Lside)*width by positivity)
  have HH := mul_le_mul_of_nonneg_left HR (show 0 ≤ 32*width by positivity)
  unfold canonicalBroadMassBudgetAtDiameter nativeConditionalLedgerBudget
  dsimp only
  linarith only [HE,HH]

theorem canonical_ordinary_mass_budget_at_diameter_mono
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {ell : ℕ} (hell : 2 < ell) {Q Lside cut v d₁ d₂ : ℝ}
    (hv : 0 < v) (hLside : 0 ≤ Lside) (hd₁ : 0 ≤ d₁) (hd : d₁ ≤ d₂) :
    a.canonicalOrdinaryMassBudgetAtDiameter ell Q Lside cut v d₁ ≤
      a.canonicalOrdinaryMassBudgetAtDiameter ell Q Lside cut v d₂ := by
  have HR := a.canonical_mass_reverse_at_diameter_mono (Q:=Q) hell hv.le hd₁ hd
  have HD := pow_le_pow_left₀ hd₁ hd 2
  unfold canonicalOrdinaryMassBudgetAtDiameter
  have HF : 0 ≤ nativeBinScaleLoss Lside (108*32^2*(Real.log a.data.N)^2)
      (54*32^2*(Real.log a.data.N)^2) (16*v) (v/4)*(16*v) := by
    unfold nativeBinScaleLoss
    positivity
  have HH := mul_le_mul_of_nonneg_left (add_le_add HD HR) HF
  linarith only [HH]

theorem canonical_comparable_broad_mass_budget_at_diameter_mono
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    {ell : ℕ} (hell : 2 < ell) {Q Lside cut v width d1 d2 : ℝ}
    (hv : 0 ≤ v) (hLside : 0 ≤ Lside) (hwidth : 0 ≤ width)
    (hd1 : 0 ≤ d1) (hd : d1 ≤ d2) :
    a.canonicalComparableBroadMassBudgetAtDiameter ell Q Lside cut v width d1 ≤
      a.canonicalComparableBroadMassBudgetAtDiameter ell Q Lside cut v width d2 := by
  have HR:=a.canonical_mass_reverse_at_diameter_mono (Q:=Q) hell hv hd1 hd
  have HD:=pow_le_pow_left₀ hd1 hd 2
  have HE:=mul_le_mul_of_nonneg_left HD (show 0 ≤ (76+64*Lside)*width by positivity)
  have HH:=mul_le_mul_of_nonneg_left HR (show 0 ≤ 32*width by positivity)
  unfold canonicalComparableBroadMassBudgetAtDiameter nativeConditionalLedgerBudget
  linarith only [HE,HH]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
