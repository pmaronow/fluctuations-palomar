module

public import SKConstants.ScalarProcessContinuous
public import SKConstants.ScalarProcessSampledHistory

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def scalarUniformTime (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / ((n : ℝ≥0) + 1)

theorem scalarUniformTime_coe (n k : ℕ) :
    (scalarUniformTime n k : ℝ) = (k : ℝ) / ((n : ℝ) + 1) := by
  simp [scalarUniformTime]

theorem scalarUniformTime_zero (n : ℕ) : scalarUniformTime n 0 = 0 := by
  simp [scalarUniformTime]

theorem scalarUniformTime_monotone (n : ℕ) : Monotone (scalarUniformTime n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem brownianMeshVariance_scalarUniformTime (n k : ℕ) :
    brownianMeshVariance (scalarUniformTime n) k = 1 / ((n : ℝ≥0) + 1) := by
  apply NNReal.eq
  rw [brownianMeshVariance, NNReal.coe_sub (scalarUniformTime_monotone n (by omega))]
  simp only [scalarUniformTime_coe, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add,
    NNReal.coe_natCast, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem scalarEulerDrift_eq_grid_sum (f : ℝ → ℝ) (n m : ℕ)
    (hb : ∀ s, ‖f s‖ ≤ 1) :
    scalarEulerDrift f (scalarUniformTime n m : ℝ) n =
      ∑ k ∈ Finset.range m, (1 / ((n : ℝ) + 1)) * f (scalarUniformTime n k) := by
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have he : ((n : ℝ) + 1) * (scalarUniformTime n m : ℝ) = (m : ℝ) := by
    rw [scalarUniformTime_coe]
    field_simp
  rw [scalarEulerDrift_eq_finite_sum f (scalarUniformTime n m : ℝ)
    (scalarUniformTime n m).coe_nonneg n hb]
  rw [he, Nat.floor_natCast]
  simp only [scalarUniformTime_coe, sub_self, zero_mul, add_zero]

def scalarUniformObservationHistory {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) : Bool × Ω → ScalarObservationHistory m :=
  scalarSampledFieldHistory
    (fun k u => scalarHiddenContinuousField z B (scalarUniformTime n (k + 1)) u) m

theorem scalarUniformObservationHistory_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (n m : ℕ) :
    HasLaw (scalarUniformObservationHistory z B n m)
      (scalarObservationHistoryLaw z (brownianMeshVariance (scalarUniformTime n)) m)
      (scalarHiddenBrownianLaw z P) := by
  exact scalarBrownianPriorField_history_hasLaw hB z (scalarUniformTime n)
    (scalarUniformTime_monotone n) (scalarUniformTime_zero n) m

theorem scalarHistoryInnovationSum_uniform_eq {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) (u : Bool × Ω) (hzero : B 0 u.2 = 0) :
    scalarHistoryInnovationSum z (brownianMeshVariance (scalarUniformTime n)) m
        (scalarUniformObservationHistory z B n m u) =
      scalarEulerInnovation z B (scalarUniformTime n m) n u := by
  have hy : scalarHiddenContinuousField z B (scalarUniformTime n 0) u = z := by
    simp [scalarHiddenContinuousField, scalarUniformTime_zero, hzero]
  rw [scalarUniformObservationHistory, scalarHistoryInnovationSum_sampled
    (fun k => scalarHiddenContinuousField z B (scalarUniformTime n k)) z
    (brownianMeshVariance (scalarUniformTime n)) m u hy]
  unfold scalarEulerInnovation
  rw [scalarEulerDrift_eq_grid_sum _ n m (fun _ => norm_tanh_le_one _)]
  congr 2
  funext k
  rw [brownianMeshVariance_scalarUniformTime]
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
  congr 2
  simp only [scalarHiddenFieldReal, scalarHiddenContinuousField, Real.toNNReal_coe]

theorem scalarUniformTime_floor_eq (n : ℕ) (T : ℝ≥0) :
    scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ =
      (scalarLeftMeshSample n (T : ℝ)).toNNReal := by
  apply NNReal.eq
  rw [scalarUniformTime_coe, Real.coe_toNNReal',
    max_eq_left (scalarLeftMeshSample_nonneg n (T : ℝ))]
  rfl

theorem scalarHistoryInnovationSum_uniform_prefix_tendsto {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : Bool × Ω)
    (hcont : Continuous (fun t => B t u.2)) (hzero : B 0 u.2 = 0) :
    Tendsto (fun n => scalarHistoryInnovationSum z
      (brownianMeshVariance (scalarUniformTime n)) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
      (scalarUniformObservationHistory z B n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u))
      atTop (𝓝 (scalarContinuousInnovation z B T u)) := by
  simp_rw [scalarHistoryInnovationSum_uniform_eq z B _ _ u hzero, scalarUniformTime_floor_eq]
  exact scalarEulerInnovation_prefix_tendsto_path z B T u hcont

end SKConstants
