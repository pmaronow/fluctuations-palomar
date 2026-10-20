module

public import SKConstants.Completion.LGram.MixedRows
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {N : ℕ}

def wholeGramEvent {Ξ : Type*} [MeasurableSpace Ξ] {n d : ℕ}
    (μ : Measure Ξ) (X : Fin n → Ξ → EuclideanSpace ℝ (Fin d)) (η : ℝ) : Set Ξ :=
  {w | ‖Concentration.centeredEmpiricalCovariance μ X w‖ ≤ η}

def gramTailBudget (N d : ℕ) (K η : ℝ) : ℝ :=
  2 * (9 : ℝ)^d * Real.exp (-(N:ℝ) * min
    ((η/2)^2 / (192 * Concentration.squareVarianceScale K 3))
    ((η/2) / (8 * Concentration.squareVarianceScale K 3)))

theorem measurableSet_wholeGramEvent {Ξ : Type*} [MeasurableSpace Ξ] {n d : ℕ}
    (μ : Measure Ξ) (X : Fin n → Ξ → EuclideanSpace ℝ (Fin d))
    (hX : ∀ i, Measurable (X i)) (η : ℝ) : MeasurableSet (wholeGramEvent μ X η) :=
  measurableSet_le (Concentration.measurable_centeredEmpiricalCovariance X hX).norm measurable_const

theorem mixedRows_covariance_operator_variance_tail
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1<β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (d : ℕ)
    (g : ℕ → ℝ≥0) (hg : StrictMono g) (H : ℝ≥0) (hN : 0<N) (η : ℝ) (hη : 0<η) :
    (actualParisiFullMixedRowsLaw W Z β H N).real
      {w | 2*η < ‖Concentration.centeredEmpiricalCovariance (actualParisiFullMixedRowsLaw W Z β H N)
        (actualParisiFullMixedRows W Z β hβ t g d) w‖} ≤
      2*(9:ℝ)^(d+(d+1))*Real.exp (-(N:ℝ)*min
        (η^2/(192*Concentration.squareVarianceScale
          (actualParisiFullMixedRowMGFProxy W β (t d):ℝ) 3))
        (η/(8*Concentration.squareVarianceScale
          (actualParisiFullMixedRowMGFProxy W β (t d):ℝ) 3))) := by
  let μ := actualParisiFullQuerySpinLaw W Z β H
  let u := t
  let K := actualParisiFullMixedRowMGFProxy W β (t d)
  have hMGF (i : Fin N) (a : EuclideanSpace ℝ (Fin (d+(d+1)))) (ha : ‖a‖≤1) :
      HasSubgaussianMGF (fun w=>⟪actualParisiFullMixedRows W Z β hβ u g d i w,a⟫_ℝ) K
        (actualParisiFullMixedRowsLaw W Z β H N) := by
    apply HasSubgaussianMGF.of_map
      (X:=fun w=>⟪actualParisiFullMixedRow W Z β hβ u g d w,a⟫_ℝ) (measurable_pi_apply i).aemeasurable
    change HasSubgaussianMGF (fun w=>⟪actualParisiFullMixedRow W Z β hβ u g d w,a⟫_ℝ) K
      ((Measure.pi (fun _ : Fin N=>μ)).map (Function.eval i))
    rw [(measurePreserving_eval (fun _ : Fin N=>μ) i).map_eq]
    exact mixedRow_unit_hasSubgaussianMGF W Z β hβ t ht d g hg H a ha
  have hSecond (i : Fin N) (a : EuclideanSpace ℝ (Fin (d+(d+1)))) (ha : ‖a‖≤1) :
      (∫w,⟪actualParisiFullMixedRows W Z β hβ u g d i w,a⟫_ℝ^2
        ∂actualParisiFullMixedRowsLaw W Z β H N)≤3 := by
    have hm : Measurable (fun w=>⟪actualParisiFullMixedRow W Z β hβ u g d w,a⟫_ℝ^2) := by
      have hm := measurable_actualParisiFullMixedRow W Z β hβ u g d
      fun_prop
    have he := (measurePreserving_eval (fun _ : Fin N=>μ) i).hasLaw.integral_comp hm.aestronglyMeasurable
    change (∫w,⟪actualParisiFullMixedRows W Z β hβ u g d i w,a⟫_ℝ^2
        ∂actualParisiFullMixedRowsLaw W Z β H N)=
      ∫w,⟪actualParisiFullMixedRow W Z β hβ u g d w,a⟫_ℝ^2 ∂μ at he
    rw [he]
    have hB := mixedRow_secondMoment_le W Z β hβ t ht d g hg H a
    exact hB.trans (by nlinarith [norm_nonneg a])
  simpa only [show (64:ℝ)*3=192 by norm_num] using
    Concentration.independent_empirical_covariance_operator_variance_tail hN
      (actualParisiFullMixedRows W Z β hβ u g d)
      (actualParisiFullMixedRows_independent W Z β hβ u g d H)
      (measurable_actualParisiFullMixedRows W Z β hβ u g d) K
      (by dsimp [K,actualParisiFullMixedRowMGFProxy];positivity) hMGF 3 (by norm_num) hSecond η hη

theorem mixedRows_wholeGramEvent_compl_le
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (d : ℕ)
    (g : ℕ → ℝ≥0) (hg : StrictMono g) (H : ℝ≥0)
    (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (actualParisiFullMixedRowsLaw W Z β H N).real
      (wholeGramEvent (actualParisiFullMixedRowsLaw W Z β H N)
        (actualParisiFullMixedRows W Z β hβ t g d) η)ᶜ ≤
      gramTailBudget N (d+(d+1)) (actualParisiFullMixedRowMGFProxy W β (t d)) η := by
  simpa only [wholeGramEvent, Set.compl_ofPred, not_le, gramTailBudget,
    mul_div_cancel₀ _ (show (2:ℝ) ≠ 0 by norm_num)] using
    mixedRows_covariance_operator_variance_tail W Z β hβ t ht d g hg H hN (η/2)
      (half_pos hη)

theorem gramTailBudget_eq_quadratic (N d : ℕ) (K η : ℝ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    gramTailBudget N d K η =
      2 * (9:ℝ)^d * Real.exp (-(N:ℝ)*η^2 /
        (768 * Concentration.squareVarianceScale K 3)) := by
  have hS : 0 < Concentration.squareVarianceScale K 3 :=
    Concentration.squareVarianceScale_pos (by norm_num)
  have hm : (η/2)^2 / (192 * Concentration.squareVarianceScale K 3) ≤
      (η/2) / (8 * Concentration.squareVarianceScale K 3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh : η^2 ≤ η := by nlinarith
    nlinarith
  unfold gramTailBudget
  rw [min_eq_left hm]
  congr 2
  ring

end SKConstants.Completion.LGram
