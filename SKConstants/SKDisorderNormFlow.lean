module

public import SKConstants.SKDisorderNorm
public import SKConstants.SKFlowWitness

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator

namespace SKConstants

theorem sk_flow_failure_decay_of_witness_twelve (beta q d : ℝ)
    (hwitness : Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-d))
        (Real.exp (-((n : ℝ) ^ (1 - q)))) 12)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (flowGood beta ((n : ℝ) ^ (-d))
        (Real.exp (-((n : ℝ) ^ (1 - q)))))ᶜ) atTop (𝓝 0) :=
  sk_flow_failure_decay_of_witness_and_norm beta q d (fun _ => 12)
    hwitness skDisorderLaw_operator_norm_twelve_tendsto_zero

theorem sk_joint_bad_start_decay_of_witness_twelve (beta c q d delta : ℝ)
    (hcq : c < q) (hq : q < 1) (hd : 0 < d) (hdelta : 0 < delta)
    (hwitness : Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-d))
        (Real.exp (-((n : ℝ) ^ (1 - q)))) 12)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | delta < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) atTop (𝓝 0) :=
  sk_joint_bad_start_decay_of_witness_and_norm beta c q d delta (fun _ => 12)
    hcq hq hd hdelta hwitness skDisorderLaw_operator_norm_twelve_tendsto_zero

theorem optimizedSKTypicalStartStatement_of_witness_twelve
    (hwitness : ∀ (beta c : ℝ), 1 < beta → 0 < c → c < 1 / 4 →
      Tendsto (fun n : ℕ => (skDisorderLaw n).real
        (lowFlowWitnessEvent beta ((n : ℝ) ^ (-(optimizedParameters c).d))
          (Real.exp (-((n : ℝ) ^ (1 - (optimizedParameters c).q)))) 12))
        atTop (𝓝 0)) : OptimizedSKTypicalStartStatement := by
  apply optimizedSKTypicalStartStatement_of_flow_probability
  intro beta c hbeta hc hquarter
  exact sk_flow_failure_decay_of_witness_twelve beta (optimizedParameters c).q
    (optimizedParameters c).d (hwitness beta c hbeta hc hquarter)

end SKConstants
