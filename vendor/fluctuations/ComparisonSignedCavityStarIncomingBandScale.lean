module

public import ComparisonSignedCavityActualStarTwoLevelProjection

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity

theorem savedWeightedExteriorScale_star_band {xs W v s C : ℝ}
    (hxs : 0 ≤ xs) (hW : 0 < W) (hv : 0 < v) (hC : 0 ≤ C)
    (hxsW : xs ≤ W) (hs : s ≤ C*W) :
    savedWeightedExteriorScale xs W v (xs+s) ≤
      Real.sqrt (1+C)*savedWeightedExteriorScale xs W v W := by
  have hsize : xs+s ≤ (1+C)*W := by nlinarith
  have H:=Real.sqrt_le_sqrt hsize
  rw [Real.sqrt_mul (by positivity : 0 ≤ 1+C)] at H
  unfold savedWeightedExteriorScale
  calc
    xs^3*Real.sqrt (xs+s)/(Real.sqrt (W^3)*v) ≤
        xs^3*(Real.sqrt (1+C)*Real.sqrt W)/(Real.sqrt (W^3)*v) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left H (by positivity)) (by positivity)
    _=Real.sqrt (1+C)*(xs^3*Real.sqrt W/(Real.sqrt (W^3)*v)) := by ring

end OAI.SKFluctuations.Cavity
