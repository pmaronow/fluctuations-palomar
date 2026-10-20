module

public import QuantitativePaper.AbsoluteComparisonScoreSum
public import QuantitativePaper.AbsoluteComparisonWeightedPowers
public import FourPapersCommon.AbsoluteComparisonDyadicPowers

@[expose] public section

/-! The sharper defect's genuine score-variance contribution. Every
quantile-diameter input is discharged by the actual p2 variational bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper QuantitativeFollowup FourPapersCommon
open scoped ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 2200000
variable {n : ℕ}

theorem absolute_score_variance_refined_bound (T k Cs : ℝ)
    (hT : T ∈ Ioc (0 : ℝ) (1/4)) (hk : 0 < k) (hCs : 0 ≤ Cs)
    (hn : 0 < n) (μ ν : ParisiMeasure) (β lam r η : ℝ)
    (hβ : 1 ≤ β) (hlam : lam ∈ Ioc (0 : ℝ) 1) (hlamβ : lam < β)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hη : 0 ≤ η)
    (hμ : μ ∈ scalarFloor (lam/β)) (hν : ν ∈ scalarFloor (lam/β))
    (hmin : ∀ρ ∈ scalarFloor (lam/β), responseEnergyFunctional n μ β (1-r) lam ≤
      responseEnergyFunctional n ρ β (1-r) lam)
    (hbudget : responseEnergyFunctional n ν β (1-r) lam-responseEnergyFunctional n μ β (1-r) lam ≤ η)
    (htrial : ∀y ∈ Icc (0 : ℝ) T, k*y ≤ β*parisiCDF ν y ∧ β*parisiCDF ν y ≤ 2)
    (hdensity : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (0 : ℝ) T) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (0 : ℝ) T)) :
    β*vectorInterpolationScoreVariance (n := n) μ (lam/β) β (1-r) (by linarith [hr.1]) ≤
      8192*(((n : ℝ)*r)^(-3/4 : ℝ))*lam^(-1/2 : ℝ)/(1-(2 : ℝ)^(-1/2 : ℝ))+
      8192*(1+Real.sqrt (p2QuantileConstant T k Cs))*(n : ℝ)^(-2/3 : ℝ)*r^(-65/66 : ℝ)*
        (absoluteComparisonDyadicConstant+lam^(-1/3 : ℝ)*η^(1/11 : ℝ)/(1-(2 : ℝ)^(-1/3 : ℝ))) := by
  let P := p2QuantileConstant T k Cs
  let a := ((n : ℝ)*r)^(-3/4 : ℝ)
  let B := (1+Real.sqrt P)*(n : ℝ)^(-2/3 : ℝ)*r^(-65/66 : ℝ)
  let U := fun j : ℕ => (2 : ℝ)^j*lam
  have hβp : 0 < β := by linarith
  have hs : lam/β ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hlam.1 hβp,(div_lt_one hβp).mpr hlamβ⟩
  have hP : 0 < P := p2QuantileConstant_pos T k Cs hT.1 hk
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hminV : ∀ρ ∈ scalarFloor (lam/β), vectorMeasureFunctional n μ β (1-r) (lam/β) ≤
      vectorMeasureFunctional n ρ β (1-r) (lam/β) := by
    intro ρ hρ
    exact (div_le_div_iff_of_pos_right hβp).mp (hmin ρ hρ)
  have hraw := absolute_score_variance_shell_sum hn μ β lam r hβp hr hs hμ hminV
  have hhalf₀ := absoluteComparisonDyadic_half_sum lam hlam.1
  have hthird₀ := absoluteComparisonDyadic_third_sum lam hlam.1
  have hmixed := absoluteComparisonDyadic_mixed_sum lam hlam
  have hhalf : Summable (fun j => (U j)^(-1/2 : ℝ)) ∧
      (∑'j : ℕ,(U j)^(-1/2 : ℝ)) = lam^(-1/2 : ℝ)/(1-(2 : ℝ)^(-1/2 : ℝ)) := by
    convert hhalf₀ using 1 <;> norm_num [U,absoluteComparisonDyadicScale]
  have hthird : Summable (fun j => (U j)^(-1/3 : ℝ)) ∧
      (∑'j : ℕ,(U j)^(-1/3 : ℝ)) = lam^(-1/3 : ℝ)/(1-(2 : ℝ)^(-1/3 : ℝ)) := by
    convert hthird₀ using 1 <;> norm_num [U,absoluteComparisonDyadicScale]
  have heq : (fun j => absoluteDyadicPieceRate (U j))=absoluteComparisonDyadicBudget lam := by
    funext j
    norm_num [absoluteComparisonDyadicBudget,absoluteComparisonDyadicScale,absoluteDyadicPieceRate,U]
  have hpiece : Summable (fun j => absoluteDyadicPieceRate (U j)) ∧
      (∑'j : ℕ,absoluteDyadicPieceRate (U j)) ≤ absoluteComparisonDyadicConstant := by
    rw [heq]
    exact hmixed
  have hpoint (j : ℕ) : absoluteEnergyScoreShellBound n μ β lam r j ≤
      8192*(a*(U j)^(-1/2 : ℝ)+B*(absoluteDyadicPieceRate (U j)+(U j)^(-1/3 : ℝ)*η^(1/11 : ℝ))) := by
    have hd := absoluteQuantileShellDiameter_mem_unit μ (lam/β) hs j
    have hUp : 0 < U j := by dsimp [U];positivity [hlam.1]
    have hdiam : U j ≤ 1 → absoluteQuantileShellDiameter μ (lam/β) j ≤
        P*(r^(-3/5 : ℝ)*(U j)+r^(-7/11 : ℝ)*η^(2/11 : ℝ)) := by
      intro hU
      unfold absoluteQuantileShellDiameter
      split_ifs with hpos
      · exact p2_dyadic_quantile_diameter_le T k Cs hT hk hCs n hn μ ν β lam r η hβ
          ⟨hlam.1.le,hlamβ.le⟩ hr hη hμ hν hmin hbudget htrial hdensity j hlam.1 hU hpos
      · positivity [hr.1]
    have hh := absolute_diameter_weighted_power_bound (n : ℝ) r (U j) η P
      (absoluteQuantileShellDiameter μ (lam/β) j) hnR hr hUp hη hP.le hd hdiam
    unfold absoluteEnergyScoreShellBound
    dsimp only [a,B,U] at *
    nlinarith only [hh]
  have hdom : Summable (fun j => 8192*(a*(U j)^(-1/2 : ℝ)+
      B*(absoluteDyadicPieceRate (U j)+(U j)^(-1/3 : ℝ)*η^(1/11 : ℝ)))) :=
    ((hhalf.1.mul_left a).add ((hpiece.1.add (hthird.1.mul_right _)).mul_left B)).mul_left 8192
  have hsum := (summable_absoluteEnergyScoreShellBound hn μ β lam r hr.1 hs hlam.1).tsum_le_tsum hpoint hdom
  have hvalue : (∑'j : ℕ,8192*(a*(U j)^(-1/2 : ℝ)+
      B*(absoluteDyadicPieceRate (U j)+(U j)^(-1/3 : ℝ)*η^(1/11 : ℝ)))) =
      8192*(a*(lam^(-1/2 : ℝ)/(1-(2 : ℝ)^(-1/2 : ℝ)))+
        B*((∑'j : ℕ,absoluteDyadicPieceRate (U j))+
          (lam^(-1/3 : ℝ)/(1-(2 : ℝ)^(-1/3 : ℝ)))*η^(1/11 : ℝ))) := by
    rw [tsum_mul_left,(hhalf.1.mul_left a).tsum_add ((hpiece.1.add (hthird.1.mul_right _)).mul_left B),
      tsum_mul_left,tsum_mul_left,hpiece.1.tsum_add (hthird.1.mul_right _),tsum_mul_right,hhalf.2,hthird.2]
  rw [hvalue] at hsum
  calc
    _ ≤ 8192*(a*(lam^(-1/2 : ℝ)/(1-(2 : ℝ)^(-1/2 : ℝ)))+
        B*((∑'j : ℕ,absoluteDyadicPieceRate (U j))+
          (lam^(-1/3 : ℝ)/(1-(2 : ℝ)^(-1/3 : ℝ)))*η^(1/11 : ℝ))) := hraw.trans hsum
    _ ≤ 8192*(a*(lam^(-1/2 : ℝ)/(1-(2 : ℝ)^(-1/2 : ℝ)))+
        B*(absoluteComparisonDyadicConstant+
          (lam^(-1/3 : ℝ)/(1-(2 : ℝ)^(-1/3 : ℝ)))*η^(1/11 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hpiece.2 le_rfl)
          (show 0 ≤ B by dsimp [B];positivity [hr.1]))) (by norm_num)
    _ = _ := by dsimp [a,B,P];ring

end QuantitativePaper
