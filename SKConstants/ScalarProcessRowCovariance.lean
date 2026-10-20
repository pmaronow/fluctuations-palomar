module

public import SKConstants.ScalarProcessRowMGFSecondMoment
public import SKConstants.EmpiricalCovariance
public import SKConstants.EmpiricalCovarianceVariance
public import Mathlib.Probability.Independence.Basic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ}

theorem measurable_scalarNormalizedPosteriorRow
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ T, Measurable (B T))
    (t : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) :
    Measurable (scalarNormalizedPosteriorRow z B t s) := by
  have hY (T : ℝ≥0) : Measurable (scalarHiddenContinuousField z B T) :=
    (measurable_const.add
      (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul_const (T : ℝ))).add
        ((hBm T).comp measurable_snd)
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  exact ((measurable_scalarTanh.comp (hY (t (i+1)))).sub
    (measurable_scalarTanh.comp (hY (t i)))).div_const _

def scalarPosteriorRowsLaw (P : Measure Ω) (z : ℝ) (n : ℕ) :
    Measure (Fin n → Bool × Ω) :=
  Measure.pi (fun _ : Fin n ↦ scalarHiddenBrownianLaw z P)

instance scalarPosteriorRowsLaw_isProbability
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (n : ℕ) :
    IsProbabilityMeasure (scalarPosteriorRowsLaw P z n) := by
  unfold scalarPosteriorRowsLaw
  infer_instance

def scalarNormalizedPosteriorRows (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) (i : Fin n) (ω : Fin n → Bool × Ω) :
    EuclideanSpace ℝ (Fin d) :=
  scalarNormalizedPosteriorRow z B t s (ω i)

theorem measurable_scalarNormalizedPosteriorRows
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ T, Measurable (B T))
    (t : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) (i : Fin n) :
    Measurable (scalarNormalizedPosteriorRows z B t s i) :=
  (measurable_scalarNormalizedPosteriorRow z B hBm t s).comp (measurable_pi_apply i)

theorem scalarNormalizedPosteriorRows_independent
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) :
    iIndepFun (scalarNormalizedPosteriorRows (n := n) z B t s)
      (scalarPosteriorRowsLaw P z n) := by
  change iIndepFun (fun (i : Fin n) (ω : Fin n → Bool × Ω) ↦
      scalarNormalizedPosteriorRow z B t s (ω i))
    (Measure.pi (fun _ : Fin n ↦ scalarHiddenBrownianLaw z P))
  exact iIndepFun_pi
    (μ := fun _ : Fin n ↦ scalarHiddenBrownianLaw z P)
    (X := fun _ : Fin n ↦ scalarNormalizedPosteriorRow z B t s)
    (fun _ ↦ aemeasurable_scalarNormalizedPosteriorRow P z B hB t s)

private theorem hasSubgaussianMGF_product_copy {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ) (K : ℝ≥0)
    (hF : HasSubgaussianMGF F K μ) (i : Fin n) :
    HasSubgaussianMGF (fun ω : Fin n → A ↦ F (ω i)) K
      (Measure.pi (fun _ : Fin n ↦ μ)) := by
  apply HasSubgaussianMGF.of_map (measurable_pi_apply i).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin n ↦ μ) i).map_eq]
  exact hF

theorem scalarNormalizedPosteriorRows_unit_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (s : Fin d → ℝ≥0) (hs : ∀ j, 0 < s j)
    (K : ℝ≥0) (hbudget : ∀ j : Fin d, t (j+1) - t j ≤ K * s j ^ 2)
    (i : Fin n) (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun ω ↦ ⟪scalarNormalizedPosteriorRows z B t s i ω, a⟫_ℝ)
      K (scalarPosteriorRowsLaw P z n) := by
  simpa only [scalarNormalizedPosteriorRows, scalarPosteriorRowsLaw] using
    hasSubgaussianMGF_product_copy (scalarHiddenBrownianLaw z P)
      (fun u ↦ ⟪scalarNormalizedPosteriorRow z B t s u, a⟫_ℝ) K
      (scalarNormalizedPosteriorRow_unit_hasSubgaussianMGF P z B hB t ht s hs K hbudget a ha) i

theorem scalarNormalizedPosteriorRows_covariance_operator_tail
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ T, Measurable (B T))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (s : Fin d → ℝ≥0) (hs : ∀ j, 0 < s j)
    (K : ℝ≥0) (hK : 0 < K)
    (hbudget : ∀ j : Fin d, t (j+1) - t j ≤ K * s j ^ 2)
    (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    (scalarPosteriorRowsLaw P z n).real
      {ω | 2 * η < ‖Concentration.centeredEmpiricalCovariance (scalarPosteriorRowsLaw P z n)
        (scalarNormalizedPosteriorRows z B t s) ω‖} ≤
      2 * (9 : ℝ) ^ d * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (128 * Real.exp 1 ^ 2 * (K : ℝ) ^ 2))
        (η / (16 * Real.exp 1 * (K : ℝ)))) := by
  apply Concentration.independent_empirical_covariance_operator_tail_explicit hn
    (scalarNormalizedPosteriorRows z B t s)
    (scalarNormalizedPosteriorRows_independent P z B hB.toIsPreBrownianReal t s)
    (measurable_scalarNormalizedPosteriorRows z B hBm t s) K hK
    (fun i a ha ↦ scalarNormalizedPosteriorRows_unit_hasSubgaussianMGF
      P z B hB t ht s hs K hbudget i a ha) η hη

def scalarPosteriorRowMGFProxy (R : ℝ) (V : ℝ≥0) : ℝ≥0 :=
  (Real.toNNReal (scalarCompactTailConstant R * scalarTailScale V))⁻¹

private theorem integral_product_copy {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ)
    (hF : AEStronglyMeasurable F μ) (i : Fin n) :
    (∫ ω : Fin n → A, F (ω i) ∂Measure.pi (fun _ : Fin n ↦ μ)) = ∫ u, F u ∂μ := by
  have heval := (measurePreserving_eval (fun _ : Fin n ↦ μ) i).map_eq
  have hMap : AEStronglyMeasurable F
      ((Measure.pi (fun _ : Fin n ↦ μ)).map (Function.eval i)) := by
    rwa [heval]
  rw [← integral_map (measurable_pi_apply i).aemeasurable hMap, heval]

theorem scalarActualPosteriorRows_secondMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ T, Measurable (B T))
    (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V)
    (i : Fin n) (a : EuclideanSpace ℝ (Fin d)) :
    (∫ ω, ⟪scalarNormalizedPosteriorRows z B t
        (fun j : Fin d ↦ scalarPosteriorIntervalScale z (t j) (t (j+1))) i ω, a⟫_ℝ ^ 2
      ∂scalarPosteriorRowsLaw P z n) = ‖a‖ ^ 2 := by
  let s : Fin d → ℝ≥0 := fun j ↦ scalarPosteriorIntervalScale z (t j) (t (j+1))
  have hSq : Measurable (fun u ↦ ⟪scalarNormalizedPosteriorRow z B t s u, a⟫_ℝ ^ 2) := by
    have hrow := measurable_scalarNormalizedPosteriorRow z B hBm t s
    fun_prop
  calc
    _ = ∫ u, ⟪scalarNormalizedPosteriorRow z B t s u, a⟫_ℝ ^ 2
        ∂scalarHiddenBrownianLaw z P := by
      simpa only [scalarNormalizedPosteriorRows, scalarPosteriorRowsLaw] using
        integral_product_copy (scalarHiddenBrownianLaw z P)
          (fun u ↦ ⟪scalarNormalizedPosteriorRow z B t s u, a⟫_ℝ ^ 2) hSq.aestronglyMeasurable i
    _ = _ := scalarActualNormalizedPosteriorRow_secondMoment P z B hB R hR hz t ht V ht1 htV a

theorem scalarActualPosteriorRows_covariance_operator_tail
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ T, Measurable (B T))
    (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V)
    (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    (scalarPosteriorRowsLaw P z n).real
      {ω | 2 * η < ‖Concentration.centeredEmpiricalCovariance (scalarPosteriorRowsLaw P z n)
        (scalarNormalizedPosteriorRows z B t
          (fun i : Fin d ↦ scalarPosteriorIntervalScale z (t i) (t (i+1)))) ω‖} ≤
      2 * (9 : ℝ) ^ d * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (128 * Real.exp 1 ^ 2 * (scalarPosteriorRowMGFProxy R V : ℝ) ^ 2))
        (η / (16 * Real.exp 1 * (scalarPosteriorRowMGFProxy R V : ℝ)))) := by
  let s : Fin d → ℝ≥0 := fun i ↦ scalarPosteriorIntervalScale z (t i) (t (i+1))
  have hSi (i : Fin d) : 1 ≤ (t i : ℝ) :=
    ht1.trans (NNReal.coe_le_coe.mpr (ht.monotone (Nat.zero_le _)))
  have hTi (i : Fin d) : t (i+1) ≤ V := (ht.monotone (by omega)).trans htV
  have hs (i : Fin d) : 0 < s i :=
    scalarPosteriorIntervalScale_pos P z B hB R hR hz (t i) (t (i+1)) V
      (hSi i) (ht (Nat.lt_succ_self _)) (hTi i)
  have hbudget (i : Fin d) : t (i+1) - t i ≤ scalarPosteriorRowMGFProxy R V * s i ^ 2 :=
    scalarPosteriorIntervalScale_budget P z B hB R hR hz (t i) (t (i+1)) V
      (hSi i) (ht.monotone (Nat.le_succ _)) (hTi i)
  have hVp : 0 < V := (NNReal.coe_pos.mp (by linarith : 0 < (t 0 : ℝ))).trans_le
    ((ht.monotone (Nat.zero_le d)).trans htV)
  have hK : 0 < scalarPosteriorRowMGFProxy R V :=
    inv_pos.mpr (Real.toNNReal_pos.mpr
      (mul_pos (scalarCompactTailConstant_pos R) (scalarTailScale_pos hVp)))
  exact scalarNormalizedPosteriorRows_covariance_operator_tail P z B hB hBm t ht.monotone
    s hs (scalarPosteriorRowMGFProxy R V) hK hbudget hn η hη

theorem scalarActualPosteriorRows_covariance_operator_variance_tail
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ T, Measurable (B T))
    (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V)
    (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    (scalarPosteriorRowsLaw P z n).real
      {ω | 2 * η < ‖Concentration.centeredEmpiricalCovariance (scalarPosteriorRowsLaw P z n)
        (scalarNormalizedPosteriorRows z B t
          (fun i : Fin d ↦ scalarPosteriorIntervalScale z (t i) (t (i+1)))) ω‖} ≤
      2 * (9 : ℝ) ^ d * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (64 * Concentration.squareVarianceScale (scalarPosteriorRowMGFProxy R V : ℝ) 1))
        (η / (8 * Concentration.squareVarianceScale (scalarPosteriorRowMGFProxy R V : ℝ) 1))) := by
  let s : Fin d → ℝ≥0 := fun i ↦ scalarPosteriorIntervalScale z (t i) (t (i+1))
  have hSi (i : Fin d) : 1 ≤ (t i : ℝ) :=
    ht1.trans (NNReal.coe_le_coe.mpr (ht.monotone (Nat.zero_le _)))
  have hTi (i : Fin d) : t (i+1) ≤ V := (ht.monotone (by omega)).trans htV
  have hs (i : Fin d) : 0 < s i :=
    scalarPosteriorIntervalScale_pos P z B hB R hR hz (t i) (t (i+1)) V
      (hSi i) (ht (Nat.lt_succ_self _)) (hTi i)
  have hbudget (i : Fin d) : t (i+1) - t i ≤ scalarPosteriorRowMGFProxy R V * s i ^ 2 :=
    scalarPosteriorIntervalScale_budget P z B hB R hR hz (t i) (t (i+1)) V
      (hSi i) (ht.monotone (Nat.le_succ _)) (hTi i)
  have hVp : 0 < V := (NNReal.coe_pos.mp (by linarith : 0 < (t 0 : ℝ))).trans_le
    ((ht.monotone (Nat.zero_le d)).trans htV)
  have hK : 0 < scalarPosteriorRowMGFProxy R V :=
    inv_pos.mpr (Real.toNNReal_pos.mpr
      (mul_pos (scalarCompactTailConstant_pos R) (scalarTailScale_pos hVp)))
  have hSecond (i : Fin n) (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1) :
      (∫ ω, ⟪scalarNormalizedPosteriorRows z B t s i ω, a⟫_ℝ ^ 2
        ∂scalarPosteriorRowsLaw P z n) ≤ 1 := by
    rw [scalarActualPosteriorRows_secondMoment P z B hB hBm R hR hz t ht V ht1 htV i a]
    nlinarith [norm_nonneg a]
  simpa only [mul_one] using
    Concentration.independent_empirical_covariance_operator_variance_tail hn
      (scalarNormalizedPosteriorRows z B t s)
      (scalarNormalizedPosteriorRows_independent P z B hB.toIsPreBrownianReal t s)
      (measurable_scalarNormalizedPosteriorRows z B hBm t s)
      (scalarPosteriorRowMGFProxy R V) hK
      (fun i a ha ↦ scalarNormalizedPosteriorRows_unit_hasSubgaussianMGF
        P z B hB t ht.monotone s hs (scalarPosteriorRowMGFProxy R V) hbudget i a ha)
      1 (by norm_num) hSecond η hη

end SKConstants
