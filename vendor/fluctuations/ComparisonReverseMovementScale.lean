module

public import ComparisonPhysicalReverseMovement
public import ReverseMovementPowerExtraction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem physical_reverse_movement_le_power_scale (n l : ℕ) (hl : 2 < l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {xs N A y ell a eps0 : ℝ}
    (hxs : 0 < xs) (hN : 0 < N) (hA : 0 < A) (hy : 0 < y) (hell : 0 < ell)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps.length+1)
    (hmean : physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 i ≤ A*ell)
    (hraw : physicalRawRatio n l steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id ≤ N^eps0)
    (hmass : xs+physicalCutMass 0 steps j ≤ y) (hyN : y ≤ N^a) (hellN : N^(-10:ℝ) ≤ ell) :
    physicalSideMovementMoment n steps q0 i j ≤
      ((2:ℝ)^(2*(l:ℝ)/((l:ℝ)-1))*A^(((l:ℝ)-2)/((l:ℝ)-1)))*
        N^(2*(l:ℝ)*eps0/((l:ℝ)-1)+(a+10)/((l:ℝ)-1))*y*ell := by
  let Q := physicalRawRatio n l steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
  let Δ := physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 i
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (physicalRawRatio_one_le n l steps 0 xs _ id measurable_id)
  have hΔ : 0 ≤ Δ := by
    dsimp only [Δ]
    rw [← physical_movement_second_eq_profile_increment n steps ha q0 hij]
    exact integral_nonneg (fun _=>sq_nonneg _)
  have hm0 : 0 ≤ xs+physicalCutMass 0 steps j :=
    add_nonneg hxs.le (physicalCutMass_mem steps ha j).1
  have hmovement := physical_movement_fourth_le_raw_interpolation n l hl steps ha q0 hxs hij hj
  have hp : (2:ℝ) < l := by exact_mod_cast hl
  have hp0 : 0 ≤ 1/((l:ℝ)-1) := div_nonneg zero_le_one (by linarith)
  have hmasspow : (xs+physicalCutMass 0 steps j)^l ≤ y^l := pow_le_pow_left₀ hm0 hmass _
  have hbig : ((2*Q)^(2*l)*(xs+physicalCutMass 0 steps j)^l)^(1/((l:ℝ)-1)) ≤
      ((2*Q)^(2*l)*y^l)^(1/((l:ℝ)-1)) :=
    Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hmasspow (by positivity)) hp0
  have hm : physicalSideMovementMoment n steps q0 i j ≤
      Δ^(((l:ℝ)-2)/((l:ℝ)-1))*((2*Q)^(2*l)*y^l)^(1/((l:ℝ)-1)) :=
    hmovement.trans (mul_le_mul_of_nonneg_left hbig (Real.rpow_nonneg hΔ _))
  have h := reverse_movement_power_extraction hN hΔ hA hQ hy hell hp hmean hraw hyN hellN
  have he : (2*(l:ℝ))=(2*l:ℕ) := by norm_cast
  rw [he,Real.rpow_natCast,Real.rpow_natCast] at h
  apply hm.trans
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

end OAI.SKFluctuations
