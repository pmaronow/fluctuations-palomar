module

public import SKConstants.GaussianProposal
public import SKConstants.HeatBathMeasurability
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SKConstants

theorem continuous_goeMatrix {V : Type*} [Fintype V] [DecidableEq V] (sigma : ℝ) :
    Continuous (GaussianProposal.goeMatrix (ι := V) sigma) := by
  unfold GaussianProposal.goeMatrix
  fun_prop

/-- The paper's completed SK disorder, with off-diagonal variance `1/n`
and diagonal variance `2/n` for positive `n`. -/
@[expose] def skDisorderLaw (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
    (GaussianProposal.goeMatrix (1 / Real.sqrt (((2 : ℕ) : ℝ) * (n : ℝ))))

instance skDisorderLaw_isProbability (n : ℕ) : IsProbabilityMeasure (skDisorderLaw n) := by
  unfold skDisorderLaw
  infer_instance

theorem sk_goe_covariance (n : ℕ) (hn : 0 < n) (i j k l : Fin n) :
    cov[fun z : EuclideanSpace ℝ (Fin n × Fin n) ↦
      GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i j,
      fun z ↦ GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z k l;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] =
      (1 / (n : ℝ)) * ((if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [GaussianProposal.goeEntry_covariance]
  congr 1
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- The actual SK disorder–Gibbs joint law. -/
@[expose] def skJointLaw (n : ℕ) (beta : ℝ) :
    Measure (Matrix (Fin n) (Fin n) ℝ × Spin n) := jointGibbsMeasure beta (skDisorderLaw n)

instance skJointLaw_isProbability (n : ℕ) (beta : ℝ) :
    IsProbabilityMeasure (skJointLaw n beta) := by unfold skJointLaw; infer_instance

@[expose] def OptimizedSKTypicalStartStatement : Prop :=
  ∀ (beta c : ℝ), 1 < beta → 0 < c → c < 1 / 4 →
    Tendsto (fun n : ℕ ↦ (skJointLaw n beta).real
      {z | (1 / 4 : ℝ) < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) atTop (𝓝 0)

end SKConstants
