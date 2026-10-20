module

public import QuantitativePaper.UniformQuantitativeParisi
public import QuantitativePaper.GroundQuantitativePassage

@[expose] public section

/-! The genuine earlier finite-model comparison supplies the absorption prior. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 900000

theorem absolute_comparison_prior (n : ℕ) (hn : 0<n) (β lam : ℝ)
    (hβ : 0<β) (hlam : 0<lam) (hlamβ : lam ≤ β/2) :
    0 ≤ energyComparisonError n β lam ∧
      energyComparisonError n β lam ≤ quantitativeParisiConstant*
        ((n:ℝ)^(-2/3:ℝ)*lam^(-1/3:ℝ)) := by
  have hs : lam/β∈Ioc (0:ℝ) (1/2):=⟨div_pos hlam hβ,(div_le_iff₀ hβ).mpr (by linarith)⟩
  have h:=uniform_quantitative_parisi_fractional n hn β (lam/β) hβ hs
  refine ⟨?_,?_⟩
  · rw [energyComparisonError_eq_fractional_gap n β lam hβ.ne']
    exact div_nonneg h.1 hβ.le
  have hm : min (β^2) (min (β*(n:ℝ)^(-(1/2:ℝ)))
      (β^(2/3:ℝ)*(n:ℝ)^(-(2/3:ℝ))*(lam/β)^(-(1/3:ℝ)))) ≤
      β^(2/3:ℝ)*(n:ℝ)^(-(2/3:ℝ))*(lam/β)^(-(1/3:ℝ)):=
    (min_le_right _ _).trans (min_le_right _ _)
  have hu:=h.2.trans (mul_le_mul_of_nonneg_left hm quantitativeParisiConstant_pos.le)
  rw [energyComparisonError_eq_fractional_gap n β lam hβ.ne']
  calc
    _ ≤ (quantitativeParisiConstant*(β^(2/3:ℝ)*(n:ℝ)^(-(2/3:ℝ))*(lam/β)^(-(1/3:ℝ))))/β:=
      div_le_div_of_nonneg_right hu hβ.le
    _ = quantitativeParisiConstant*((β^(2/3:ℝ)*(n:ℝ)^(-(2/3:ℝ))*(lam/β)^(-(1/3:ℝ)))/β):=by ring
    _ = _ := by rw [energyComparisonError_third_rate_normalization n β lam hβ hlam.le];norm_num

end QuantitativePaper
