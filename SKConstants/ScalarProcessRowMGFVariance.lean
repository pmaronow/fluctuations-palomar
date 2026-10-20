module
public import SKConstants.ScalarProcessRowMGF
public import SKConstants.ScalarProcessVarianceBalance

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma scalarTailScale_pos {t : ℝ≥0} (ht : 0 < t) : 0 < scalarTailScale t := by
  unfold scalarTailScale
  have htp : 0 < (t : ℝ) := NNReal.coe_pos.mpr ht
  positivity

lemma scalarTailScale_antitone_pos {S T : ℝ≥0} (hS : 0 < S) (hST : S ≤ T) :
    scalarTailScale T ≤ scalarTailScale S := by
  have hSp : 0 < (S : ℝ) := NNReal.coe_pos.mpr hS
  have hTp : 0 < (T : ℝ) := hSp.trans_le (NNReal.coe_le_coe.mpr hST)
  unfold scalarTailScale
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    have h := NNReal.coe_le_coe.mpr hST
    linarith
  · apply (inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_pos.mpr (by positivity))).mpr
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hST)
      (by positivity))
  · positivity
  · positivity

lemma scalarP_actual_interval_ge_compact {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (S T V : ℝ≥0) (hS : 1 ≤ (S : ℝ)) (hST : S ≤ T) (hTV : T ≤ V) :
    scalarCompactTailConstant R * scalarTailScale V * ((T : ℝ) - (S : ℝ)) ≤
      scalarP z S - scalarP z T := by
  have hSp : 0 < S := NNReal.coe_pos.mp (by linarith)
  have hTp : 0 < T := hSp.trans_le hST
  rw [scalarP_actual_interval_balance P z B hB S T hSp.ne' hTp.ne']
  have hc := continuous_scalarHiddenExpectedDefectSqReal P z B hB
  calc
    _ = ∫ s in (S : ℝ)..(T : ℝ), scalarCompactTailConstant R * scalarTailScale V := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on (NNReal.coe_le_coe.mpr hST)
        (intervalIntegrable_const) (hc.intervalIntegrable _ _)
      intro s hs
      have hsp : 0 < s := by linarith [hs.1]
      rw [scalarHiddenExpectedDefectSqReal_eq_scalarR P z B hB.toIsPreBrownianReal s hsp]
      have hst : S ≤ s.toNNReal := by
        apply NNReal.coe_le_coe.mp
        simpa only [Real.coe_toNNReal s hsp.le] using hs.1
      have hvt : s.toNNReal ≤ V := by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal s hsp.le]
        exact hs.2.trans (NNReal.coe_le_coe.mpr hTV)
      calc
        _ ≤ scalarCompactTailConstant R * scalarTailScale s.toNNReal :=
          mul_le_mul_of_nonneg_left (scalarTailScale_antitone_pos (hSp.trans_le hst) hvt)
            (scalarCompactTailConstant_pos R).le
        _ ≤ scalarR z s.toNNReal := scalarR_ge_compact_tailScale z R s.toNNReal
          (by rw [Real.coe_toNNReal s hsp.le]; linarith [hs.1]) hR hz

@[expose] def scalarPosteriorIntervalScale (z : ℝ) (S T : ℝ≥0) : ℝ≥0 :=
  NNReal.sqrt (Real.toNNReal (scalarP z S - scalarP z T))

lemma scalarPosteriorIntervalScale_pos {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (S T V : ℝ≥0) (hS : 1 ≤ (S : ℝ)) (hST : S < T) (hTV : T ≤ V) :
    0 < scalarPosteriorIntervalScale z S T := by
  have hVp : 0 < V := (NNReal.coe_pos.mp (by linarith : 0 < (S : ℝ))).trans_le
    (hST.le.trans hTV)
  have hlow := scalarP_actual_interval_ge_compact P z B hB R hR hz S T V hS hST.le hTV
  have hd : 0 < scalarP z S - scalarP z T :=
    (mul_pos (mul_pos (scalarCompactTailConstant_pos R) (scalarTailScale_pos hVp))
      (sub_pos.mpr (NNReal.coe_lt_coe.mpr hST))).trans_le hlow
  simpa only [scalarPosteriorIntervalScale, NNReal.sqrt_pos, Real.toNNReal_pos] using hd

lemma scalarPosteriorIntervalScale_budget {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (S T V : ℝ≥0) (hS : 1 ≤ (S : ℝ)) (hST : S ≤ T) (hTV : T ≤ V) :
    T - S ≤ (Real.toNNReal (scalarCompactTailConstant R * scalarTailScale V))⁻¹ *
      scalarPosteriorIntervalScale z S T ^ 2 := by
  have hVp : 0 < V := (NNReal.coe_pos.mp (by linarith : 0 < (S : ℝ))).trans_le
    (hST.trans hTV)
  have hc : 0 < scalarCompactTailConstant R * scalarTailScale V :=
    mul_pos (scalarCompactTailConstant_pos R) (scalarTailScale_pos hVp)
  have hlow := scalarP_actual_interval_ge_compact P z B hB R hR hz S T V hS hST hTV
  have hd : 0 ≤ scalarP z S - scalarP z T :=
    (mul_nonneg hc.le (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hST))).trans hlow
  rw [scalarPosteriorIntervalScale, NNReal.sq_sqrt]
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_sub hST, NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le,
    Real.coe_toNNReal _ hd]
  exact (le_inv_mul_iff₀ hc).mpr (by simpa [mul_comm] using hlow)

lemma scalarActualNormalizedPosteriorRow_unit_hasSubgaussianMGF {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) {d : ℕ} (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V) (a : EuclideanSpace ℝ (Fin d))
    (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF
      (fun u => ⟪scalarNormalizedPosteriorRow z B t
        (fun i : Fin d => scalarPosteriorIntervalScale z (t i) (t (i+1))) u, a⟫_ℝ)
      (Real.toNNReal (scalarCompactTailConstant R * scalarTailScale V))⁻¹
      (scalarHiddenBrownianLaw z P) := by
  apply scalarNormalizedPosteriorRow_unit_hasSubgaussianMGF P z B hB t ht.monotone
  · intro i
    apply scalarPosteriorIntervalScale_pos P z B hB R hR hz (t i) (t (i+1)) V
    · exact ht1.trans (NNReal.coe_le_coe.mpr (ht.monotone (Nat.zero_le _)))
    · exact ht (Nat.lt_succ_self _)
    · exact (ht.monotone (by omega)).trans htV
  · intro i
    apply scalarPosteriorIntervalScale_budget P z B hB R hR hz (t i) (t (i+1)) V
    · exact ht1.trans (NNReal.coe_le_coe.mpr (ht.monotone (Nat.zero_le _)))
    · exact ht.monotone (Nat.le_succ _)
    · exact (ht.monotone (by omega)).trans htV
  · exact ha

end SKConstants
