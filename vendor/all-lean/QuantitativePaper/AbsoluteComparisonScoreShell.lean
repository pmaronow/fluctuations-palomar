module

public import QuantitativePaper.MovingScoreQuantileShell
public import QuantitativePaper.AbsoluteComparisonPowerNormalization

@[expose] public section

/-! The genuine terminal-spin score shell in physical energy units.
Temperature cancellation is exact, with the actual quantile diameter. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper QuantitativeFollowup FourPapersCommon
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
variable {n : ℕ}

def absoluteQuantileShellDiameter (μ : ParisiMeasure) (s : ℝ) (j : ℕ) : ℝ :=
  if 0 < volume.real (dyadicQuantileShell s s j) then
    parisiQuantileImageDiameter μ s (dyadicQuantileShell s s j) else 0

theorem absoluteQuantileShellDiameter_mem_unit (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioo (0 : ℝ) 1) (j : ℕ) :
    absoluteQuantileShellDiameter μ s j ∈ Icc (0 : ℝ) 1 := by
  unfold absoluteQuantileShellDiameter
  split_ifs with hpos
  · exact ⟨parisiQuantileImageDiameter_nonneg_of_positive_interval μ s _
      (dyadicQuantileShell_ordConnected s s j) (dyadicQuantileShell_subset s s j) hpos,
      parisiQuantileImageDiameter_le_one μ s _ hpos⟩
  · constructor <;> norm_num

theorem absolute_score_quantile_shell (hn : 0 < n) (μ : ParisiMeasure)
    (β lam r : ℝ) (hβ : 0 < β) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hs : lam/β ∈ Ioo (0 : ℝ) 1) (hμ : μ ∈ scalarFloor (lam/β))
    (hmin : ∀ν ∈ scalarFloor (lam/β), vectorMeasureFunctional n μ β (1-r) (lam/β) ≤
      vectorMeasureFunctional n ν β (1-r) (lam/β)) (j : ℕ) :
    β*(∫v in dyadicQuantileShell (lam/β) (lam/β) j,
      variance (vectorMeasureOverlapScore (n := n) μ β (1-r) (by linarith [hr.1])
        (parisiFreeQuantile μ (lam/β) v)) (vectorMeasureSpinPathLaw μ β (1-r) (lam/β) (by linarith [hr.1]))) ≤
      8192*((((n : ℝ)*r)^(-3/4 : ℝ))*((2 : ℝ)^j*lam)^(-1/2 : ℝ)+
        (((n : ℝ)*r)^(-2/3 : ℝ))*((2 : ℝ)^j*lam)^(-1/3 : ℝ)*
          (absoluteQuantileShellDiameter μ (lam/β) j)^(2/3 : ℝ)) := by
  let J := dyadicQuantileShell (lam/β) (lam/β) j
  have hDom : J ⊆ Ioo (0 : ℝ) (1-lam/β) := dyadicQuantileShell_subset _ _ j
  have hlam : 0 < lam := (div_pos_iff_of_pos_right hβ).mp hs.1
  have hU : 0 < (2 : ℝ)^j*lam := by positivity
  by_cases hpos : 0 < volume.real J
  · have hthreshold : ∀ᵐv ∂volume.restrict J,
        (2 : ℝ)^j*(lam/β) ≤ parisiCDF μ (parisiFreeQuantile μ (lam/β) v) := by
      filter_upwards [ae_restrict_mem (dyadicQuantileShell_ordConnected _ _ j).measurableSet] with v hv
      have hL : (2 : ℝ)^j*(lam/β)-lam/β ≤ v := hv.2.1
      exact (by linarith : (2 : ℝ)^j*(lam/β) ≤ lam/β+v).trans
        (parisiCDF_freeQuantile_lower μ (lam/β) ⟨hs.1.le,hs.2.le⟩ (Ioo_subset_Ioc_self (hDom hv)))
    have hb := vector_refined_score_quantile_shell hn μ (lam/β) β (1-r) hβ.ne'
      (by linarith [hr.1]) hs hμ hmin J (dyadicQuantileShell_ordConnected _ _ j)
      hDom (volume.real J) ((2 : ℝ)^j*(lam/β)) hpos rfl
      (dyadicQuantileShell_length_le _ _ hs.1.le j) hthreshold
    have hh := mul_le_mul_of_nonneg_left hb hβ.le
    have hM : (n : ℝ)*((1-(1-r))*β^2) = (n : ℝ)*(r*β^2) := by ring
    have hUn : (2 : ℝ)^j*(lam/β) = ((2 : ℝ)^j*lam)/β := by ring
    rw [hM,hUn] at hh
    calc
      _ ≤ β*(8192*((((n : ℝ)*(r*β^2))^(-3/4 : ℝ))*(((2 : ℝ)^j*lam)/β)^(-1/2 : ℝ)+
        (((n : ℝ)*(r*β^2))^(-2/3 : ℝ))*(((2 : ℝ)^j*lam)/β)^(-1/3 : ℝ)*
          (parisiQuantileImageDiameter μ (lam/β) J)^(2/3 : ℝ))) := by
        convert hh using 1 <;> norm_num
      _ = 8192*((β*((n : ℝ)*(r*β^2))^(-3/4 : ℝ)*(((2 : ℝ)^j*lam)/β)^(-1/2 : ℝ))+
        (β*((n : ℝ)*(r*β^2))^(-2/3 : ℝ)*(((2 : ℝ)^j*lam)/β)^(-1/3 : ℝ))*
          (parisiQuantileImageDiameter μ (lam/β) J)^(2/3 : ℝ)) := by ring
      _ = _ := by
        rw [absolute_shell_quarter_normalization _ β r _ (Nat.cast_pos.mpr hn) hβ hr.1 hU,
          absolute_shell_third_normalization _ β r _ (Nat.cast_pos.mpr hn) hβ hr.1 hU]
        simp only [absoluteQuantileShellDiameter,if_pos hpos,J]
  · have hfinite : volume J ≠ ∞ := by
      apply ne_of_lt
      exact (measure_mono hDom).trans_lt (by rw [Real.volume_Ioo];exact ENNReal.ofReal_lt_top)
    have hzero : volume J = 0 := by
      have hz : volume.real J = 0 := le_antisymm (not_lt.mp hpos) measureReal_nonneg
      have he := ofReal_measureReal (μ := volume) (s := J) hfinite
      rw [hz,ENNReal.ofReal_zero] at he
      exact he.symm
    rw [setIntegral_measure_zero _ hzero,mul_zero]
    simp only [absoluteQuantileShellDiameter,if_neg hpos,J]
    positivity [hr.1]

end QuantitativePaper
