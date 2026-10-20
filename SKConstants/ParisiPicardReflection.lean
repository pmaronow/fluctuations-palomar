module
public import SKConstants.ParisiCDFDiffusion

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK

theorem correctionIter_neg_of_odd {Ω : Type*} [MeasurableSpace Ω]
    (b : BoundedLipschitzDrift) (ho : ∀ v, Function.Odd (b.f v))
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    b.correctionIter (fun v w => -B v w) n t ω = -b.correctionIter B n t ω := by
  induction n generalizing t with
  | zero => simp only [BoundedLipschitzDrift.correctionIter, neg_zero]
  | succ n ih =>
    simp only [BoundedLipschitzDrift.correctionIter, timePrimitive,
      BoundedLipschitzDrift.action]
    have he : (fun s : ℝ => b.f (Real.toNNReal s)
        (-B (Real.toNNReal s) ω + b.correctionIter (fun v w => -B v w) n
          (Real.toNNReal s) ω)) =
        fun s => -b.f (Real.toNNReal s)
          (B (Real.toNNReal s) ω + b.correctionIter B n (Real.toNNReal s) ω) := by
      funext s
      rw [ih, ← neg_add, ho]
    rw [he, intervalIntegral.integral_neg]

theorem solution_neg_of_odd {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (b : BoundedLipschitzDrift) (ho : ∀ v, Function.Odd (b.f v))
    (ℱ : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ) (hB : IsProgressive ℱ B)
    (t : ℝ≥0) (ω : Ω) :
    b.solution (fun v w => -B v w) t ω = -b.solution B t ω := by
  have hpos := (b.correctionIter_tendsto ℱ hB t ω).neg
  have hneg := b.correctionIter_tendsto ℱ hB.neg t ω
  simp only [correctionIter_neg_of_odd b ho B] at hneg
  have he := tendsto_nhds_unique hneg hpos
  simp only [BoundedLipschitzDrift.solution, he, neg_add]

theorem correctionIter_congr_path {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (b : BoundedLipschitzDrift) (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → Ω' → ℝ)
    (ω : Ω) (ω' : Ω') (h : ∀ t, B t ω = C t ω') (n : ℕ) (t : ℝ≥0) :
    b.correctionIter B n t ω = b.correctionIter C n t ω' := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [BoundedLipschitzDrift.correctionIter, timePrimitive,
      BoundedLipschitzDrift.action]
    congr 1
    funext s
    rw [h, ih]

theorem solution_congr_path {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (b : BoundedLipschitzDrift) (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → Ω' → ℝ)
    (ω : Ω) (ω' : Ω') (h : ∀ t, B t ω = C t ω') (t : ℝ≥0) :
    b.solution B t ω = b.solution C t ω' := by
  have he : (fun n => b.correctionIter B n t ω) = fun n => b.correctionIter C n t ω' :=
    funext (fun n => correctionIter_congr_path b B C ω ω' h n t)
  simp only [BoundedLipschitzDrift.solution, BoundedLipschitzDrift.correction, h, he]

end SKConstants
