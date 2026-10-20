module

public import QuantitativePaper.AbsoluteComparisonScoreShell
public import QuantitativePaper.VectorInterpolationDefect
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! Honest disjoint-shell integration of the physical terminal-spin score.
The infinite comparison series is summable before using its sharper
quantile-diameter bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper QuantitativeFollowup FourPapersCommon
open scoped ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem absolute_dyadic_negative_power_summable (lam p : ℝ) (hlam : 0 < lam) (hp : p < 0) :
    Summable (fun j : ℕ => ((2 : ℝ)^j*lam)^p) := by
  have hρ : |(2 : ℝ)^p| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hp
  have hh := (summable_geometric_of_abs_lt_one hρ).mul_left (lam^p)
  convert hh using 1
  funext j
  rw [Real.mul_rpow (by positivity) hlam.le,←Real.rpow_pow_comm (by norm_num)]
  ring

def absoluteEnergyScoreShellBound (n : ℕ) (μ : ParisiMeasure) (β lam r : ℝ) (j : ℕ) : ℝ :=
  8192*((((n : ℝ)*r)^(-3/4 : ℝ))*((2 : ℝ)^j*lam)^(-1/2 : ℝ)+
    (((n : ℝ)*r)^(-2/3 : ℝ))*((2 : ℝ)^j*lam)^(-1/3 : ℝ)*
      (absoluteQuantileShellDiameter μ (lam/β) j)^(2/3 : ℝ))

theorem summable_absoluteEnergyScoreShellBound (hn : 0 < n) (μ : ParisiMeasure)
    (β lam r : ℝ) (hr : 0 < r) (hs : lam/β ∈ Ioo (0 : ℝ) 1) (hlam : 0 < lam) :
    Summable (absoluteEnergyScoreShellBound n μ β lam r) := by
  have h₀ := (absolute_dyadic_negative_power_summable lam (-1/2) hlam (by norm_num)).mul_left
    (((n : ℝ)*r)^(-3/4 : ℝ))
  have h₁ := (absolute_dyadic_negative_power_summable lam (-1/3) hlam (by norm_num)).mul_left
    (((n : ℝ)*r)^(-2/3 : ℝ))
  have hsum := (h₀.add h₁).mul_left 8192
  apply Summable.of_nonneg_of_le (fun j => by
    have hd := absoluteQuantileShellDiameter_mem_unit μ (lam/β) hs j
    unfold absoluteEnergyScoreShellBound
    positivity [hd.1]) (fun j => ?_) hsum
  have hd := absoluteQuantileShellDiameter_mem_unit μ (lam/β) hs j
  have hp := Real.rpow_le_one hd.1 hd.2 (by norm_num : (0 : ℝ) ≤ 2/3)
  unfold absoluteEnergyScoreShellBound
  have hh := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ ((n : ℝ)*r)^(-2/3 : ℝ)*((2 : ℝ)^j*lam)^(-1/3 : ℝ) by positivity)
  nlinarith only [hh]

theorem absolute_score_variance_shell_sum (hn : 0 < n) (μ : ParisiMeasure)
    (β lam r : ℝ) (hβ : 0 < β) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hs : lam/β ∈ Ioo (0 : ℝ) 1) (hμ : μ ∈ scalarFloor (lam/β))
    (hmin : ∀ν ∈ scalarFloor (lam/β), vectorMeasureFunctional n μ β (1-r) (lam/β) ≤
      vectorMeasureFunctional n ν β (1-r) (lam/β)) :
    β*vectorInterpolationScoreVariance (n := n) μ (lam/β) β (1-r) (by linarith [hr.1]) ≤
      ∑'j : ℕ, absoluteEnergyScoreShellBound n μ β lam r j := by
  let s := lam/β
  let ψ : ℝ → ℝ := fun v => variance
    (vectorMeasureOverlapScore (n := n) μ β (1-r) (by linarith [hr.1]) (parisiFreeQuantile μ s v))
    (vectorMeasureSpinPathLaw μ β (1-r) s (by linarith [hr.1]))
  have hψ : Measurable ψ := (measurable_variance_vectorMeasureOverlapScore μ β (1-r) s (by linarith [hr.1])).comp
    (parisiFreeQuantile_measurable μ s)
  have hb : ∀v, 0 ≤ ψ v ∧ ψ v ≤ 1 := fun v =>
    ⟨variance_nonneg _ _,variance_vectorMeasureOverlapScore_le_one μ β (1-r) s (by linarith [hr.1]) _⟩
  letI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (1-s))) := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo];exact ENNReal.ofReal_ne_top)
  have hi : IntegrableOn ψ (Ioo (0 : ℝ) (1-s)) := Integrable.of_bound hψ.aestronglyMeasurable 1
    (.of_forall fun v => by rw [Real.norm_of_nonneg (hb v).1];exact (hb v).2)
  have hcover : (⋃j : ℕ,dyadicQuantileShell s s j) = Ioo (0 : ℝ) (1-s) := by
    rw [dyadicQuantileShells_cover s s hs.1]
    ext v
    simp only [sub_self,mem_inter_iff,mem_Ioo,mem_Ici,and_iff_left_iff_imp]
    exact fun hv => hv.1.le
  have hsum := hasSum_integral_iUnion
    (fun j => (dyadicQuantileShell_ordConnected s s j).measurableSet)
    (dyadicQuantileShells_pairwiseDisjoint s s hs.1) (hcover.symm ▸ hi)
  have hlam : 0 < lam := (div_pos_iff_of_pos_right hβ).mp hs.1
  have hbound := summable_absoluteEnergyScoreShellBound hn μ β lam r hr.1 hs hlam
  have hh := (hsum.mul_left β).summable.tsum_le_tsum
    (fun j => absolute_score_quantile_shell hn μ β lam r hβ hr hs hμ hmin j) hbound
  rw [(hsum.mul_left β).tsum_eq,hcover] at hh
  unfold vectorInterpolationScoreVariance
  rw [integral_parisiFreeMeasure μ s _ (measurable_variance_vectorMeasureOverlapScore μ β (1-r) s (by linarith [hr.1])),
    integral_Ioc_eq_integral_Ioo]
  exact hh

end QuantitativePaper
