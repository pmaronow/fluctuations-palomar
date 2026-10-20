module

public import SKProof.MeanBiasStatement
public import QuantitativePaper.ShortVarianceMeanProposition
public import QuantitativeFollowup.ImprovedFluctuationPowerCalculus
public import Paper.ParisiPDEFormula

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace OAI.SKFluctuations.MeanBias

theorem disorderLaw_eq_couplingLaw (n : ℕ) :
    disorderLaw n = QuantitativePaper.couplingLaw n := rfl

theorem hamiltonian_eq_skHamiltonian (β : ℝ) (n : ℕ)
    (g : Disorder n) (σ : Spin n) :
    hamiltonian β n g σ = Paper.skHamiltonian β 0 g σ := by
  simp [hamiltonian, Paper.skHamiltonian, spinValue, Paper.spinSign]

theorem countingLogPartition_eq_logPartition (β : ℝ) (n : ℕ)
    (g : Disorder n) :
    countingLogPartition β n g = QuantitativePaper.logPartition n β g := by
  unfold countingLogPartition QuantitativePaper.logPartition Paper.skPartitionFunction
  simp_rw [hamiltonian_eq_skHamiltonian]

theorem partitionFunction_eq_counting (β : ℝ) (n : ℕ) (g : Disorder n) :
    partitionFunction β n g =
      (2 : ℝ) ^ (-(n : ℤ)) * Paper.skPartitionFunction β 0 g := by
  unfold partitionFunction Paper.skPartitionFunction
  simp_rw [hamiltonian_eq_skHamiltonian]

theorem freeEnergy_eq_logPartition_sub (β : ℝ) (n : ℕ) (g : Disorder n) :
    freeEnergy β n g = QuantitativePaper.logPartition n β g - (n : ℝ) * Real.log 2 := by
  have htwo : (2 : ℝ) ^ (-(n : ℤ)) ≠ 0 := by positivity
  rw [freeEnergy, partitionFunction_eq_counting,
    Real.log_mul htwo (Paper.skPartitionFunction_pos β 0 g).ne', Real.log_zpow]
  simp only [Int.cast_neg, Int.cast_natCast]
  unfold QuantitativePaper.logPartition
  ring

theorem freeEnergyVariance_eq_quantitative (β : ℝ) (n : ℕ) :
    freeEnergyVariance β n = QuantitativePaper.freeEnergyVariance n β := by
  have hF : freeEnergy β n = fun g =>
      QuantitativePaper.logPartition n β g - (n : ℝ) * Real.log 2 :=
    funext (freeEnergy_eq_logPartition_sub β n)
  unfold freeEnergyVariance QuantitativePaper.freeEnergyVariance
  rw [hF, disorderLaw_eq_couplingLaw]
  exact variance_sub_const
    (QuantitativePaper.continuous_logPartition n β).aestronglyMeasurable _

theorem countingPressure_eq_pressure (β : ℝ) (n : ℕ) :
    countingPressure β n = QuantitativePaper.pressure n β := by
  unfold countingPressure QuantitativePaper.pressure
  simp_rw [countingLogPartition_eq_logPartition]
  rw [disorderLaw_eq_couplingLaw]

theorem limitingPressure_eq_parisiPDEValue (β : ℝ) (hβ : 0 < β) :
    limitingPressure β = Paper.parisiPDEValue β 0 := by
  have hP : countingPressure β = Paper.finiteSKFreeEnergy β 0 := by
    funext n
    rw [countingPressure_eq_pressure]
    exact QuantitativePaper.pressure_eq_finiteSKFreeEnergy n β
  unfold limitingPressure
  rw [hP]
  exact (Paper.physicalParisiFormula β 0 hβ).limUnder_eq

theorem variance_energyFreeEnergy (n : ℕ) (β : ℝ) :
    variance (QuantitativePaper.energyFreeEnergy n β) (QuantitativePaper.couplingLaw n) =
      (β ^ 2)⁻¹ * QuantitativePaper.freeEnergyVariance n β := by
  change variance (fun g => QuantitativePaper.logPartition n β g / β)
      (QuantitativePaper.couplingLaw n) =
    (β ^ 2)⁻¹ * variance (QuantitativePaper.logPartition n β)
      (QuantitativePaper.couplingLaw n)
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, inv_pow]
  ring

theorem energyMeanDeficit_eq_pressure_gap (n : ℕ) (β : ℝ) :
    QuantitativePaper.energyMeanDeficit n β =
      (Paper.parisiPDEValue β 0 - QuantitativePaper.pressure n β) / β := by
  unfold QuantitativePaper.energyMeanDeficit QuantitativePaper.scalarEnergyValue
  rw [zero_div, QuantitativePaper.constrainedParisiValue_zero]
  unfold QuantitativePaper.energyFreeEnergy QuantitativePaper.pressure
  rw [integral_div]
  ring

theorem lowerBound_of_main_statement (hFluct : MainFluctuationStatement) :
    LowerBoundStatement := by
  intro β hβ ε hε
  have hβp : 0 < β := zero_lt_one.trans hβ
  obtain ⟨c, hc, hshort⟩ := QuantitativePaper.short_variance_mean β hβ
  let k : ℝ := (β ^ 2)⁻¹
  have hk : 0 < k := inv_pos.mpr (sq_pos_of_pos hβp)
  obtain ⟨N, hN⟩ := (hFluct β hβ).2.1 (4 * ε / 5) (by positivity)
  refine ⟨β * c * k ^ (5 / 4 : ℝ), by positivity, max N 2, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left N 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hn0 : 0 < n := by omega
  have hv : (n : ℝ) ^ ((1 : ℝ) / 3 - 4 * ε / 5) ≤
      QuantitativePaper.freeEnergyVariance n β := by
    rw [← freeEnergyVariance_eq_quantitative]
    exact (hN n hnN).1
  have hve : k * (n : ℝ) ^ ((1 : ℝ) / 3 - 4 * ε / 5) ≤
      variance (QuantitativePaper.energyFreeEnergy n β) (QuantitativePaper.couplingLaw n) := by
    rw [variance_energyFreeEnergy]
    exact mul_le_mul_of_nonneg_left hv hk.le
  have hm := QuantitativeFollowup.mean_lower_of_variance_exponent (n : ℝ)
    (variance (QuantitativePaper.energyFreeEnergy n β) (QuantitativePaper.couplingLaw n))
    (QuantitativePaper.energyMeanDeficit n β) c k ((1 : ℝ) / 3 - 4 * ε / 5)
    (Nat.cast_pos.mpr hn0) hc.le hk hve (hshort n hn0 β le_rfl)
  have hexp : (((1 : ℝ) / 3 - 4 * ε / 5) - 1) * (5 / 4 : ℝ) =
      -(5 / 6 : ℝ) - ε := by ring
  rw [hexp, energyMeanDeficit_eq_pressure_gap] at hm
  have hm' := (le_div_iff₀ hβp).mp hm
  rw [limitingPressure_eq_parisiPDEValue β hβp, countingPressure_eq_pressure]
  calc
    β * c * k ^ (5 / 4 : ℝ) * (n : ℝ) ^ (-(5 / 6 : ℝ) - ε) =
        (c * k ^ (5 / 4 : ℝ) * (n : ℝ) ^ (-(5 / 6 : ℝ) - ε)) * β := by ring
    _ ≤ Paper.parisiPDEValue β 0 - QuantitativePaper.pressure n β := hm'

end OAI.SKFluctuations.MeanBias
