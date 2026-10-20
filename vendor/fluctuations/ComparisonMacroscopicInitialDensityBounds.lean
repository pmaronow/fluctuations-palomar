module

public import SKFluctuationsOAI.Probability.SKFluctuations.ScalarFlattenedContinuity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal BigOperators

set_option maxHeartbeats 400000

theorem macroScalarInitialDensityConstant_uniform_bounds {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) :
    2*T*Real.exp (-12*T) ≤ scalarInitialDensityConstant hT α ∧
      scalarInitialDensityConstant hT α ≤
        T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) := by
  let P := rescaledMassProfile α hT
  have hP (s : ℝ) : P.mass s ≤ 1 := (α.property.1 (s/T)).2
  have h4 := scalarProfileJet_four_zero_upper P hP 0 (Real.toNNReal T)
  have h4b := scalarProfileJet_bound P hP 0 (Real.toNNReal T) 3 0
  have h2 := scalarProfileJet_curvature_lower P hP 0 (Real.toNNReal T) 0
  have h2p := scalarProfileJet_curvature_pos P hP 0 (Real.toNNReal T) 0
  have h2b := (scalarProfileJet_admissible P hP 0 (Real.toNNReal T) 0).2
  simp only [Real.coe_toNNReal _ hT.le, Scalar.curvature, Real.tanh_zero,
    zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one] at h4 h2
  let a := scalarProfileJet P 0 (Real.toNNReal T) 4 0
  let b := scalarProfileJet P 0 (Real.toNNReal T) 2 0
  have hb : 0 < b ∧ b ≤ 1 := ⟨h2p, by
    linarith [sq_nonneg (scalarProfileJet P 0 (Real.toNNReal T) 1 0)]⟩
  have he4 : (Real.exp (-6*T))^2 = Real.exp (-12*T) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he2 : (Real.exp (-4*T))^3 = Real.exp (-12*T) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ha : 4*Real.exp (-12*T) ≤ a^2 := by
    have hs : 0 ≤ -2*Real.exp (-6*T)-a := by linarith
    have hh := mul_self_le_mul_self (by positivity : 0 ≤ 2*Real.exp (-6*T))
      (by linarith : 2*Real.exp (-6*T) ≤ -a)
    nlinarith [he4]
  have hab : a^2 ≤ (ReplicaTree.attachmentCount 1 3 : ℝ)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg a) h4b 2
    simpa only [sq_abs] using hh
  have hb3 : b^3 ≤ 1 := by nlinarith [sq_nonneg (b-1)]
  have he3 : Real.exp (-12*T) ≤ b^3 := by
    have hh := pow_le_pow_left₀ (Real.exp_nonneg (-4*T)) h2 3
    simpa only [he2] using hh
  have hconst : scalarInitialDensityConstant hT α = T*a^2/(2*b^3) := by
    simp only [scalarInitialDensityConstant, scalarTailSpatialJet, scalarTailJet,
      scalarProfileHeatJet, mul_zero, sub_zero, mul_one, Pi.zero_apply]
    rfl
  rw [hconst]
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*b^3)).mpr
    have hh := mul_le_mul_of_nonneg_left hb3 (by positivity : 0 ≤ 4*T*Real.exp (-12*T))
    have haT := mul_le_mul_of_nonneg_left ha hT.le
    nlinarith
  · calc
      T*a^2/(2*b^3) ≤ T*a^2/(2*Real.exp (-12*T)) :=
        div_le_div_of_nonneg_left (by positivity)
          (by positivity) (mul_le_mul_of_nonneg_left he3 (by norm_num))
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab hT.le) (by positivity)

end OAI.SKFluctuations.Hierarchy
