module

public import QuantitativePaper.AbsoluteComparisonScoreBound
public import QuantitativePaper.AbsoluteComparisonTraceBound

@[expose] public section

/-! A true refined defect bound for every attained actual vector minimum. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper QuantitativeFollowup FourPapersCommon
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 2000000
variable {n : ℕ}

def absoluteComparisonQuarterConstant : ℝ := 32768/(1-(2:ℝ)^(-1/2:ℝ))
def absoluteComparisonThirdConstant (T k Cs : ℝ) : ℝ :=
  32768*(1+Real.sqrt (p2QuantileConstant T k Cs))/(1-(2:ℝ)^(-1/3:ℝ))
def absoluteComparisonBudgetConstant : ℝ :=
  (1-(2:ℝ)^(-1/3:ℝ))*absoluteComparisonDyadicConstant

private theorem absoluteComparison_score_algebra (a b c d x y h t : ℝ)
    (hh : h≠0) (ht : t≠0) :
    4*(8192*a*b/h+8192*c*d*(x+y/t))=
      (32768/h)*a*b+(32768*c/t)*d*(t*x+y) := by
  field_simp [hh,ht]
  <;> ring

theorem absoluteComparison_rate_constants_pos (T k Cs : ℝ) :
    0<absoluteComparisonQuarterConstant ∧ 0<absoluteComparisonThirdConstant T k Cs ∧
      0<absoluteComparisonBudgetConstant := by
  have hh : 0<1-(2:ℝ)^(-1/2:ℝ):=sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have ht : 0<1-(2:ℝ)^(-1/3:ℝ):=sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  unfold absoluteComparisonQuarterConstant absoluteComparisonThirdConstant absoluteComparisonBudgetConstant
  exact ⟨div_pos (by norm_num) hh,div_pos (by positivity) ht,
    mul_pos ht absoluteComparisonDyadicConstant_pos⟩

theorem absolute_refined_defect_bound (T k Cs : ℝ)
    (hT : T∈Ioc (0:ℝ) (1/4)) (hk : 0<k) (hCs : 0 ≤ Cs)
    (hn : 0<n) (μ ν : ParisiMeasure) (β lam r η : ℝ)
    (hβ : 1 ≤ β) (hlam : lam∈Ioc (0:ℝ) 1) (hlamβ : lam<β)
    (hr : r∈Ioc (0:ℝ) 1) (hη : 0 ≤ η)
    (hμ : μ∈scalarFloor (lam/β)) (hν : ν∈scalarFloor (lam/β))
    (hmin : ∀ρ∈scalarFloor (lam/β), responseEnergyFunctional n μ β (1-r) lam ≤
      responseEnergyFunctional n ρ β (1-r) lam)
    (hbudget : responseEnergyFunctional n ν β (1-r) lam-responseEnergyFunctional n μ β (1-r) lam ≤ η)
    (htrial : ∀y∈Icc (0:ℝ) T,k*y ≤ β*parisiCDF ν y ∧ β*parisiCDF ν y ≤ 2)
    (hdensity : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (0:ℝ) T) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (0:ℝ) T)) :
    β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-r) (by linarith [hr.1]) ≤
      min (1/((n:ℝ)*r*lam)) (2*((n:ℝ)*r)^(-1/2:ℝ))+
      absoluteComparisonQuarterConstant*((n:ℝ)*r)^(-3/4:ℝ)*lam^(-1/2:ℝ)+
      absoluteComparisonThirdConstant T k Cs*(n:ℝ)^(-2/3:ℝ)*r^(-65/66:ℝ)*
        (absoluteComparisonBudgetConstant+lam^(-1/3:ℝ)*η^(1/11:ℝ)) := by
  have hβp : 0<β:=by linarith
  have hs : lam/β∈Ioo (0:ℝ) 1:=⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr hlamβ⟩
  have ht : 1-r<1:=by linarith [hr.1]
  have hminV : ∀ρ∈scalarFloor (lam/β), vectorMeasureFunctional n μ β (1-r) (lam/β) ≤
      vectorMeasureFunctional n ρ β (1-r) (lam/β):=fun ρ hρ=>
    (div_le_div_iff_of_pos_right hβp).mp (hmin ρ hρ)
  have hD:=vectorInterpolationDefect_le_trace_add_score_variance hn μ (lam/β) β (1-r)
    hs hμ hβp.ne' ht hminV
  have hA:=absolute_trace_min_bound hn μ β lam r hβp hs hr hμ hminV
  have hW:=absolute_score_variance_refined_bound T k Cs hT hk hCs hn μ ν β lam r η
    hβ hlam hlamβ hr hη hμ hν hmin hbudget htrial hdensity
  have hDβ:=mul_le_mul_of_nonneg_left hD hβp.le
  have hWT:=mul_le_mul_of_nonneg_left hW (by norm_num : (0:ℝ) ≤ 4)
  have hdthird : 1-(2:ℝ)^(-1/3:ℝ)≠0:=ne_of_gt (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))
  have hdhalf : 1-(2:ℝ)^(-1/2:ℝ)≠0:=ne_of_gt (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))
  have heq : 4*(8192*(((n:ℝ)*r)^(-3/4:ℝ))*lam^(-1/2:ℝ)/(1-(2:ℝ)^(-1/2:ℝ))+
      8192*(1+Real.sqrt (p2QuantileConstant T k Cs))*(n:ℝ)^(-2/3:ℝ)*r^(-65/66:ℝ)*
        (absoluteComparisonDyadicConstant+lam^(-1/3:ℝ)*η^(1/11:ℝ)/(1-(2:ℝ)^(-1/3:ℝ))))=
      absoluteComparisonQuarterConstant*((n:ℝ)*r)^(-3/4:ℝ)*lam^(-1/2:ℝ)+
      absoluteComparisonThirdConstant T k Cs*(n:ℝ)^(-2/3:ℝ)*r^(-65/66:ℝ)*
        (absoluteComparisonBudgetConstant+lam^(-1/3:ℝ)*η^(1/11:ℝ)):=by
    unfold absoluteComparisonQuarterConstant absoluteComparisonThirdConstant absoluteComparisonBudgetConstant
    convert absoluteComparison_score_algebra (((n:ℝ)*r)^(-3/4:ℝ)) (lam^(-1/2:ℝ))
      (1+Real.sqrt (p2QuantileConstant T k Cs)) ((n:ℝ)^(-2/3:ℝ)*r^(-65/66:ℝ))
      absoluteComparisonDyadicConstant (lam^(-1/3:ℝ)*η^(1/11:ℝ))
      (1-(2:ℝ)^(-1/2:ℝ)) (1-(2:ℝ)^(-1/3:ℝ)) hdhalf hdthird using 1 <;> ring
  rw [heq] at hWT
  nlinarith only [hDβ,hA,hWT]

end QuantitativePaper
