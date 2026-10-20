module

public import SKConstants.Completion.Blueprint.AssemblyFine

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.N20
open SKConstantsOAI.ZeroTemperatureSK Blueprint

theorem pinning_schedule_eventually (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < rankCount p.a p.f n ∧ 0 < meshSize p.a n ∧
      p.b * Real.log (n : ℝ) ≤ (readoutTime p.a p.b n : ℝ) ∧
      readoutTime p.a p.b n ≤ readoutTime p.a p.f n := by
  have hb0 := hb.1
  have hbf := hb.2.1
  have hf0 : 0 < p.f := lt_trans hb0 hbf
  have hfa : p.f / 4 ≤ p.a := hf.1.le
  have hba : p.b / 4 ≤ p.a := by linarith
  have ha1 : p.a < 1 := by linarith [hf.2.1]
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ (p.f - p.b) * Real.log (n : ℝ) :=
    (Filter.Tendsto.const_mul_atTop (sub_pos.mpr hbf)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [schedule_eventually p.a p.b hb0 hba ha1,
    schedule_eventually p.a p.f hf0 hfa ha1, hlog] with n hB hF hgap
  have hbT := horizon_bounds p.a p.b hb0 hba n hB.1 hB.2.1
  have hfT := horizon_bounds p.a p.f hf0 hfa n hF.1 hF.2.1
  have hn : 0 < n := by omega
  refine ⟨hn, hF.2.2, paperGrowingQueryMeshSize_pos p.a n hn, hbT.1, ?_⟩
  apply NNReal.coe_le_coe.mp
  change (scalarGrowingSourceHorizon (meshSize p.a n) (queryCount p.a p.b n) : ℝ) ≤
    (scalarGrowingSourceHorizon (meshSize p.a n) (queryCount p.a p.f n) : ℝ)
  nlinarith

theorem logarithmic_radius_budget (b r E : ℝ) (hb : 0 < b) (hr : r < b / 2)
    (S : ℕ → ℝ≥0) (hS : ∀ᶠ n : ℕ in atTop, b * Real.log (n : ℝ) ≤ S n) :
    ∀ᶠ n : ℕ in atTop,
      E + 1 ≤ (S n : ℝ) ∧
      64 * (n : ℝ) * Real.exp (-((S n : ℝ) - E) / 2) ≤ (sparseFieldRadius r n : ℝ) := by
  have hlog : ∀ᶠ n : ℕ in atTop, E + 1 ≤ b * Real.log (n : ℝ) :=
    (Filter.Tendsto.const_mul_atTop hb
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (E + 1))
  have hpow := constant_rpow_le_small_rpow (1 - b / 2) (1 - r)
    (64 * Real.exp (E / 2)) 1 (by linarith) (by positivity) (by norm_num)
  filter_upwards [hS, hlog, hpow, eventually_gt_atTop (0 : ℕ)] with n hS hnS hp hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨hnS.trans hS, ?_⟩
  have he : Real.exp (-((S n : ℝ) - E) / 2) ≤
      Real.exp (E / 2) * (n : ℝ) ^ (-b / 2) := by
    rw [Real.rpow_def_of_pos hnR, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hnPow : (n : ℝ) * (n : ℝ) ^ (-b / 2) = (n : ℝ) ^ (1 - b / 2) := by
    rw [show (1 : ℝ) - b / 2 = 1 + (-b / 2) by ring, Real.rpow_add hnR, Real.rpow_one]
  calc
    _ ≤ 64 * (n : ℝ) * (Real.exp (E / 2) * (n : ℝ) ^ (-b / 2)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (64 * Real.exp (E / 2)) * (n : ℝ) ^ (1 - b / 2) := by rw [← hnPow]; ring
    _ ≤ (n : ℝ) ^ (1 - r) := by simpa only [one_mul] using hp
    _ ≤ (sparseFieldRadius r n : ℝ) := Nat.le_ceil _

end SKConstants.N20
