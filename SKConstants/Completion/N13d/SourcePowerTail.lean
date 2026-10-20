module

public import SKConstants.Completion.N13d.SourceCompletion
public import SKConstants.Completion.N13d.PowerTail
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators RealInnerProductSpace

namespace SKConstants.Completion.N13d
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC5 LM5 LBase
variable {Ω : Type*} [MeasurableSpace Ω]

def sourceGaussianTailConstant (β T : ℝ) : ℝ :=
  Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)+5*T+
    (terminalTailConstant β)^2*Real.exp 1

theorem sourceGaussianTailConstant_pos (β T : ℝ) (hT : 0 ≤ T) :
    0 < sourceGaussianTailConstant β T := by
  unfold sourceGaussianTailConstant
  positivity

theorem growing_previous_susceptibility_square_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r K : ℕ) (hN : 0 < r+K) (b : ℝ)
    (hprev : -1+b*Real.log ((r+K:ℕ):ℝ) ≤ (growingQueryTime δ K : ℝ)) :
    (actualParisiFullSusceptibilityExpected W β (growingQueryTime δ K))^2 ≤
      (terminalTailConstant β)^2*Real.exp 1*((r+K:ℕ):ℝ)^(-b) := by
  simpa only [neg_neg] using actual_susceptibility_square_shift_log_bound W β hβ
    (-1) b (growingQueryTime δ K) (r+K) hN (growingQueryTime δ K).coe_nonneg hprev

theorem growingVarianceBudget_le_three_powers
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r K : ℕ) (hN : 0 < r+K) (τ T ell a γ b : ℝ)
    (hT : 0 ≤ T) (hell : 1 ≤ ell)
    (hmesh : (δ : ℝ) = ((r+K:ℕ):ℝ)^(-a))
    (hτ : τ^2 ≤ T*ell*((r+K:ℕ):ℝ)^(-2*γ))
    (hprev : -1+b*Real.log ((r+K:ℕ):ℝ) ≤ (growingQueryTime δ K : ℝ)) :
    growingVarianceBudget W β δ r K τ ≤
      sourceGaussianTailConstant β T*ell*((r+K:ℕ):ℝ)⁻¹ *
        (((r+K:ℕ):ℝ)^(-a)+((r+K:ℕ):ℝ)^(-2*γ)+((r+K:ℕ):ℝ)^(-b)) := by
  let N : ℝ := (r+K:ℕ)
  let A := Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)
  let D := (terminalTailConstant β)^2*Real.exp 1
  let C := sourceGaussianTailConstant β T
  have hC : 0 ≤ C := (sourceGaussianTailConstant_pos β T hT).le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCeq : C = A+5*T+D := rfl
  have hAC : A ≤ C := by linarith
  have hTC : 5*T ≤ C := by linarith
  have hDC : D ≤ C := by linarith
  have hCell : C ≤ C*ell := by nlinarith
  have hNpos : 0 < N := Nat.cast_pos.mpr hN
  have hM : A*(δ : ℝ) ≤ C*ell*N^(-a) := by
    rw [hmesh]
    exact mul_le_mul_of_nonneg_right (hAC.trans hCell) (Real.rpow_pos_of_pos hNpos _).le
  have hTau : 5*τ^2 ≤ C*ell*N^(-2*γ) := by
    calc
      _ ≤ 5*(T*ell*N^(-2*γ)) := mul_le_mul_of_nonneg_left hτ (by norm_num)
      _ = (5*T)*ell*N^(-2*γ) := by ring
      _ ≤ _ := by gcongr
  have hP : (actualParisiFullSusceptibilityExpected W β (growingQueryTime δ K))^2 ≤
      C*ell*N^(-b) :=
    (growing_previous_susceptibility_square_le W β hβ δ r K hN b hprev).trans
      (mul_le_mul_of_nonneg_right (hDC.trans hCell) (Real.rpow_pos_of_pos hNpos _).le)
  unfold growingVarianceBudget
  change N⁻¹*(A*(δ : ℝ)+5*τ^2+_) ≤ _
  calc
    _ ≤ N⁻¹*(C*ell*N^(-a)+C*ell*N^(-2*γ)+C*ell*N^(-b)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hM hTau) hP) (by positivity)
    _ = _ := by ring

theorem growingSourceDiscardedEnergy_tail_C2
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K : ℕ) (hN : 0 < r+K) (τ T ell a γ b z : ℝ)
    (hτ : 0 ≤ τ) (hT : 0 ≤ T) (hell : 1 ≤ ell)
    (hpost : parisiEquilibriumPhysicalEndpoint β ≤ growingQueryTime δ K)
    (hmesh : (δ : ℝ) = ((r+K:ℕ):ℝ)^(-a))
    (hcoeff : τ^2 ≤ T*ell*((r+K:ℕ):ℝ)^(-2*γ))
    (hprev : -1+b*Real.log ((r+K:ℕ):ℝ) ≤ (growingQueryTime δ K : ℝ)) :
    (M1.SourceLinkedLaw W β hβ δ r K).real {u |
      (growingSourceCompact δ r K u).1 ∈ growingCoefficientEvent W β hβ δ r K τ ∧
      ((r+K:ℕ):ℝ)^(-z) ≤ |growingSourceDiscardedEnergy W β hβ δ r K u|} ≤
      2*Real.exp (-((r+K:ℕ):ℝ)^(1-sharpGaussianPower a γ b z)/
        (6*sourceGaussianTailConstant β T*ell)) := by
  let N : ℝ := (r+K:ℕ)
  let C := sourceGaussianTailConstant β T
  have hNpos : 0 < N := Nat.cast_pos.mpr hN
  have hN1 : 1 ≤ N := by
    change (1:ℝ) ≤ ((r+K:ℕ):ℝ)
    exact_mod_cast (show 1 ≤ r+K from hN)
  have hC : 0 < C := sourceGaussianTailConstant_pos β T hT
  have hEll : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hVB : growingVarianceBudget W β δ r K τ ≤
      3*C*ell*N^(sharpGaussianPower a γ b z-2*z-1) := by
    calc
      _ ≤ C*ell*N⁻¹*(N^(-a)+N^(-2*γ)+N^(-b)) :=
        growingVarianceBudget_le_three_powers W β hβ δ r K hN τ T ell a γ b
          hT hell hmesh hcoeff hprev
      _ ≤ C*ell*N⁻¹*(3*N^(sharpGaussianPower a γ b z-2*z)) :=
        mul_le_mul_of_nonneg_left (three_powers_le N a γ b z hN1) (by positivity)
      _ = _ := by
        rw [Real.rpow_sub hNpos (sharpGaussianPower a γ b z-2*z) 1, Real.rpow_one]
        ring
  have hVpos : 0 < growingVarianceBudget W β δ r K τ := by
    unfold growingVarianceBudget
    positivity
  refine (growingSourceDiscardedEnergy_tail_on W β hβ δ hδ r K hN τ hτ hpost
    (N^(-z)) (Real.rpow_pos_of_pos hNpos _)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  rw [← gaussian_power_ratio N C ell a γ b z hNpos hC hEll]
  have hh := div_le_div_of_nonneg_left (sq_nonneg (N^(-z)))
    (show 0 < 2*growingVarianceBudget W β δ r K τ by positivity)
    (mul_le_mul_of_nonneg_left hVB (by norm_num : (0:ℝ) ≤ 2))
  convert neg_le_neg hh using 1 <;> ring

end SKConstants.Completion.N13d
