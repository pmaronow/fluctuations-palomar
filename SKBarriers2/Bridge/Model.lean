module

public import OAI.Probability.SKBarriers.Coverage.ThermodynamicLimit
public import QuantitativePaper.Model

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open OAI.SK OAI.SK.Analytic

namespace SKBarriers2.Bridge

theorem disorderLaw_eq_couplingLaw (n : ℕ) :
    disorderLaw n = QuantitativePaper.couplingLaw n := rfl

theorem spin_eq_spinSign (b : Bool) : spin b = Paper.spinSign b := rfl

theorem beta_hamiltonian_eq_skHamiltonian (β : ℝ) {n : ℕ}
    (J : Disorder n) (x : Config n) :
    β * hamiltonian J x = Paper.skHamiltonian β 0 J x := by
  unfold hamiltonian Paper.skHamiltonian
  simp only [spin_eq_spinSign, zero_mul, add_zero]
  ring

theorem hamiltonian_eq_energy {n : ℕ} (J : Disorder n) (x : Config n) :
    hamiltonian J x = QuantitativePaper.energy n J x := by
  simpa only [one_mul, QuantitativePaper.energy] using
    beta_hamiltonian_eq_skHamiltonian 1 J x

theorem partition_eq_skPartitionFunction (β : ℝ) {n : ℕ} (J : Disorder n) :
    partition β J = Paper.skPartitionFunction β 0 J := by
  unfold partition Paper.skPartitionFunction
  apply Finset.sum_congr rfl
  intro x _
  rw [beta_hamiltonian_eq_skHamiltonian]

theorem logPartition_eq (β : ℝ) {n : ℕ} (J : Disorder n) :
    logPartition β J = QuantitativePaper.logPartition n β J := by
  exact congrArg Real.log (partition_eq_skPartitionFunction β J)

theorem quenchedPressure_eq_pressure (β : ℝ) (n : ℕ) :
    quenchedPressure β n = QuantitativePaper.pressure n β := by
  unfold quenchedPressure QuantitativePaper.pressure
  simp_rw [logPartition_eq]
  rw [disorderLaw_eq_couplingLaw]

theorem variance_logPartition_eq_freeEnergyVariance (β : ℝ) (n : ℕ) :
    variance (fun J : Disorder n => logPartition β J) (disorderLaw n) =
      QuantitativePaper.freeEnergyVariance n β := by
  unfold QuantitativePaper.freeEnergyVariance
  simp_rw [logPartition_eq]
  rw [disorderLaw_eq_couplingLaw]

end SKBarriers2.Bridge
