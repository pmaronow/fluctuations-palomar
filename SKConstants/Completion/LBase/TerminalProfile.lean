module

public import SKConstants.Completion.LBase.InverseProfile

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Ω : Type*} [MeasurableSpace Ω]

def terminalTailConstant (β : ℝ) : ℝ :=
  4 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2) *
    Real.sqrt ((parisiEquilibriumPhysicalEndpoint β : ℝ) + 2)

lemma terminalTailConstant_pos (β : ℝ) : 0 < terminalTailConstant β := by
  unfold terminalTailConstant
  positivity

lemma actual_susceptibility_le_one (W : BrownianSystem Ω) (β t : ℝ) :
    actualParisiFullSusceptibilityExpected W β t ≤ 1 := by
  have H := actualParisiFullSusceptibilityExpected_sq_le_squareExpected W β t
  have Hr := (actualParisiFullSusceptibilitySquareExpected_bounds W β t).2
  nlinarith [sq_nonneg (actualParisiFullSusceptibilityExpected W β t - 1)]

theorem actual_susceptibility_global_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    actualParisiFullSusceptibilityExpected W β t ≤
      terminalTailConstant β * (Real.exp (-t / 2) / Real.sqrt (1 + t)) := by
  let E : ℝ := parisiEquilibriumPhysicalEndpoint β
  have hE : 0 ≤ E := (parisiEquilibriumPhysicalEndpoint β).coe_nonneg
  have hs : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr (by linarith)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hs).mpr
  by_cases hsmall : t ≤ E + 1
  · have hroot : Real.sqrt (1 + t) ≤ Real.sqrt (E + 2) := Real.sqrt_le_sqrt (by linarith)
    have hexp : 1 ≤ Real.exp ((E + 1) / 2) * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    calc
      _ ≤ Real.sqrt (1 + t) := mul_le_of_le_one_left (Real.sqrt_nonneg _) (actual_susceptibility_le_one W β t)
      _ ≤ Real.sqrt (E + 2) := hroot
      _ ≤ (4 * Real.sqrt (E + 2)) * (Real.exp ((E + 1) / 2) * Real.exp (-t / 2)) := by
        nlinarith [Real.sqrt_nonneg (E + 2), mul_le_mul_of_nonneg_left hexp (show 0 ≤ 4 * Real.sqrt (E + 2) by positivity)]
      _ = _ := by unfold terminalTailConstant; dsimp [E]; ring
  · let v := t - E
    have hv : 1 ≤ v := by dsimp [v]; linarith
    have hv0 : 0 < v := by linarith
    have hpost := actualParisiFullSusceptibilityExpected_post W β hβ v hv0.le
    have hEv : E + v = t := by dsimp [v]; ring
    change actualParisiFullSusceptibilityExpected W β (E + v) = _ at hpost
    rw [hEv] at hpost
    have HP := actualParisiContinuationP_le_tail W β v hv0
    rw [scalarTailScale, Real.coe_toNNReal v hv0.le] at HP
    have hden : 0 < Real.sqrt (2 * Real.pi * v) := by positivity
    have hratio : Real.sqrt (1 + t) / Real.sqrt (2 * Real.pi * v) ≤ Real.sqrt (E + 2) := by
      apply (div_le_iff₀ hden).mpr
      rw [← Real.sqrt_mul (by positivity : 0 ≤ E + 2)]
      apply Real.sqrt_le_sqrt
      have hfirst : 1 + t ≤ (E + 2) * v := by nlinarith
      have hsecond : v ≤ 2 * Real.pi * v := by nlinarith [Real.pi_gt_three]
      exact hfirst.trans (mul_le_mul_of_nonneg_left hsecond (by positivity))
    have hexp : Real.exp (-v / 2) ≤ Real.exp ((E + 1) / 2) * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [v]
      linarith
    calc
      _ ≤ (4 * (Real.exp (-v / 2) * (Real.sqrt (2 * Real.pi * v))⁻¹)) * Real.sqrt (1 + t) :=
        mul_le_mul_of_nonneg_right (hpost.trans_le HP) (Real.sqrt_nonneg _)
      _ = (4 * Real.exp (-v / 2)) * (Real.sqrt (1 + t) / Real.sqrt (2 * Real.pi * v)) := by ring
      _ ≤ (4 * Real.exp (-v / 2)) * Real.sqrt (E + 2) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ (4 * (Real.exp ((E + 1) / 2) * Real.exp (-t / 2))) * Real.sqrt (E + 2) := by gcongr
      _ = _ := by unfold terminalTailConstant; dsimp [E]; ring

theorem actual_susceptibility_square_global_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    (actualParisiFullSusceptibilityExpected W β t)^2 ≤
      (terminalTailConstant β)^2 * Real.exp (-t) / (1 + t) := by
  have H := pow_le_pow_left₀ (actualParisiFullSusceptibilityExpected_nonneg W β t)
    (actual_susceptibility_global_tail W β hβ t ht) 2
  have hs : (Real.sqrt (1 + t))^2 = 1 + t := Real.sq_sqrt (by linarith)
  have he : (Real.exp (-t / 2))^2 = Real.exp (-t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [mul_pow, div_pow, hs, he, mul_div_assoc] using H

theorem actual_susceptibility_square_shift_log_bound
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (A L t : ℝ) (n : ℕ) (hn : 0 < n) (ht : 0 ≤ t)
    (horizon : A + L * Real.log (n : ℝ) ≤ t) :
    (actualParisiFullSusceptibilityExpected W β t)^2 ≤
      (terminalTailConstant β)^2 * Real.exp (-A) * (n : ℝ)^(-L) := by
  have H := actual_susceptibility_square_global_tail W β hβ t ht
  have he : Real.exp (-(A + L * Real.log (n : ℝ))) =
      Real.exp (-A) * (n : ℝ)^(-L) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hn), ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (terminalTailConstant β)^2 * Real.exp (-t) :=
      H.trans (div_le_self (by positivity) (by linarith))
    _ ≤ (terminalTailConstant β)^2 * Real.exp (-(A + L * Real.log (n : ℝ))) := by gcongr
    _ = _ := by rw [he]; ring

end SKConstants.Completion.LBase
