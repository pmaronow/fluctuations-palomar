module

public import SKConstants.Completion.NScalar.IntervalGrid
public import SKConstants.Completion.LBase.CurvatureIntegral

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.NScalar
open SKConstantsOAI.ZeroTemperatureSK LBase
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedLipschitzDrift.solution
variable {Ω : Type*} [MeasurableSpace Ω]

def actualCurvatureDyadicIntervalSum (W : BrownianSystem Ω) (β : ℝ)
    (s t : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^l),
    actualCurvatureProcess W β ((s + (t-s) * ((i : ℝ≥0) / 2^l) : ℝ≥0) : ℝ) w *
      (W.B (s + (t-s) * (((i+1 : ℕ) : ℝ≥0) / 2^l)) w -
        W.B (s + (t-s) * ((i : ℝ≥0) / 2^l)) w)

theorem actualCurvatureDyadicIntervalSum_eq_sub (W : BrownianSystem Ω) (β : ℝ)
    (s t : ℝ≥0) (l : ℕ) (w : Ω) :
    actualCurvatureDyadicIntervalSum W β s t l w =
      actualCurvatureLeftSum W β (intervalDyadicGrid s t) 2 l w -
        actualCurvatureLeftSum W β (intervalDyadicGrid s t) 1 l w := by
  unfold actualCurvatureLeftSum
  rw [one_mul, two_mul, Finset.sum_range_add, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 2^l + i + 1 = 2^l + (i+1) by omega,
    intervalDyadicGrid_second, intervalDyadicGrid_second]

theorem actual_curvature_dyadic_interval_meanSquare_tendsto
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Tendsto (fun l => ∫ w, (actualCurvatureDyadicIntervalSum W β s t l w -
      (actualParisiMagnetizationObservable W β t w -
        actualParisiMagnetizationObservable W β s w))^2 ∂W.law) atTop (𝓝 0) := by
  let G := intervalDyadicGrid s t
  let X := fun l w => actualCurvatureLeftSum W β G 2 l w -
    actualParisiMagnetizationObservable W β t w
  let Y := fun l w => actualCurvatureLeftSum W β G 1 l w -
    actualParisiMagnetizationObservable W β s w
  have hX (l : ℕ) : MemLp (X l) 2 W.law :=
    (memLp_actualCurvatureLeftSum W β G 2 l).sub (memLp_actualMagnetization W β t)
  have hY (l : ℕ) : MemLp (Y l) 2 W.law :=
    (memLp_actualCurvatureLeftSum W β G 1 l).sub (memLp_actualMagnetization W β s)
  have hx : Tendsto (fun l => ∫ w, (X l w)^2 ∂W.law) atTop (𝓝 0) := by
    simpa only [G, X, intervalDyadicGrid_end s t hst] using
      actual_curvature_leftSum_meanSquare_tendsto W β hβ G 2
        (brownianDyadicWidth t) (brownianDyadicWidth_tendsto t)
        (fun l i _ => intervalDyadicGrid_width_le s t hst l i)
  have hy : Tendsto (fun l => ∫ w, (Y l w)^2 ∂W.law) atTop (𝓝 0) := by
    simpa only [G, Y, intervalDyadicGrid_start] using
      actual_curvature_leftSum_meanSquare_tendsto W β hβ G 1
        (brownianDyadicWidth t) (brownianDyadicWidth_tendsto t)
        (fun l i _ => intervalDyadicGrid_width_le s t hst l i)
  have H := tendsto_integral_sq_sub
    (fun l => (hX l).aestronglyMeasurable.aemeasurable)
    (fun l => (hY l).aestronglyMeasurable.aemeasurable)
    (fun l => (hX l).integrable_sq) (fun l => (hY l).integrable_sq) hx hy
  apply H.congr'
  apply Filter.Eventually.of_forall
  intro l
  apply integral_congr_ae
  apply ae_of_all
  intro w
  dsimp only [X, Y, G]
  rw [actualCurvatureDyadicIntervalSum_eq_sub]
  congr 1
  ring

end SKConstants.Completion.NScalar
