module

public import ComparisonNativeActualChildParameterGrowth
public import ComparisonNativeActualMinimumChild

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000

theorem actual_child_full_strength_at_parent_test_lower
    {c0 x : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hx : 0 < x) :
    c0^3*x^2 ≤ laplaceComparisonStrength (c0*x) ((c0*x)^2) x := by
  have H := laplaceComparisonStrength_lower (mul_pos hc0 hx)
    (sq_pos_of_pos (mul_pos hc0 hx)) hx
  have H1 : c0^3*x^2 ≤ (c0*x)^2 := by
    have Hc : c0^3 ≤ c0^2 := by nlinarith [mul_le_mul_of_nonneg_left hc01 (sq_nonneg c0)]
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right Hc (sq_nonneg x)
  have H2 : (c0*x)^3/x=c0^3*x^2 := by field_simp
  apply le_trans (le_min H1 ?_) H
  rw [H2]

theorem actual_child_direct_calibration_at_parent_test
    {n : ℕ} {delta c0 d lam x : ℝ}
    (hn : 0 < n) (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hlam : 0 < lam) (hx : 0 < x) :
    let E := actualChildErrorBudget n delta c0 d lam x
    let dc := actualChildRadius c0 x
    comparisonLowerScale n E dc ≤ x ∧
      (n:ℝ)*E^2 ≤ laplaceComparisonStrength dc (dc^2) x*x^2 ∧
      x^2 ≤ (max 1 (1/c0^3))^2*laplaceComparisonStrength dc (dc^2) x := by
  dsimp only
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hN
  have Hceil := actual_child_budget_ceiling n delta c0 d lam x
  have HE : 0 ≤ actualChildErrorBudget n delta c0 d lam x :=
    (actual_child_budget_pos hN hc0 hlam hx).le
  have Hroot : Real.sqrt (n:ℝ)*actualChildErrorBudget n delta c0 d lam x ≤ (c0*x)^2 := by
    have H := (le_div_iff₀ hs).mp Hceil
    simpa only [actualChildRadius,mul_comm] using H
  have Hstrength := actual_child_full_strength_at_parent_test_lower hc0 hc01 hx
  refine ⟨?_,?_,?_⟩
  · unfold comparisonLowerScale actualChildRadius
    apply (div_le_iff₀ (mul_pos hc0 hx)).mpr
    have Hc := mul_le_mul_of_nonneg_left hc01 (sq_nonneg x)
    nlinarith only [Hroot,Hc,hc0]
  · have Hsq := pow_le_pow_left₀ (mul_nonneg hs.le HE) Hroot 2
    rw [mul_pow,Real.sq_sqrt hN.le] at Hsq
    have Hc : c0^4 ≤ c0^3 := by
      have H := mul_le_mul_of_nonneg_left hc01 (pow_nonneg hc0.le 3)
      nlinarith only [H]
    have Hs := mul_le_mul_of_nonneg_right Hstrength (sq_nonneg x)
    have Hc' := mul_le_mul_of_nonneg_right Hc (pow_nonneg hx.le 4)
    simp only [actualChildRadius]
    nlinarith only [Hsq,Hs,Hc']
  · let C := max 1 (1/c0^3)
    have HC : 1 ≤ C := le_max_left _ _
    have HCpow : 1 ≤ C*c0^3 := by
      have H := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (1/c0^3))
        (pow_nonneg hc0.le 3)
      simpa only [div_mul_cancel₀ 1 (pow_pos hc0 3).ne'] using H
    have HCsq : 1 ≤ C^2*c0^3 := HCpow.trans
      (mul_le_mul_of_nonneg_right (by nlinarith only [HC] : C ≤ C^2) (pow_nonneg hc0.le 3))
    have H := mul_le_mul_of_nonneg_left Hstrength (sq_nonneg C)
    have H' := mul_le_mul_of_nonneg_right HCsq (sq_nonneg x)
    simp only [actualChildRadius]
    nlinarith only [H,H']

end OAI.SKFluctuations.LaplaceWindowFormalization
