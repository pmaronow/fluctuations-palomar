module

public import SKConstants.ParisiSpinPinningRate
public import SKConstants.ParisiSpinPinningHamming
public import SKConstants.SKSparseBoundaryRate

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology BigOperators Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.M6

theorem actualRows_pinning_radius_tail {Omega : Type*} [MeasurableSpace Omega]
    (W : BrownianSystem Omega) (beta : ℝ) (hbeta : 1 < beta)
    (B rho : ℝ) (hB : 0 < B) (hrho : rho < B / 2) (T : ℕ → ℝ≥0)
    (hT : ∀ᶠ n : ℕ in atTop,
      parisiEquilibriumPhysicalEndpoint beta + (B * Real.log (n : ℝ)).toNNReal ≤ T n) :
    ∀ᶠ n : ℕ in atTop,
      (actualParisiTerminalSpinRowsLaw W beta (T n) n).real
        {omega | ‖spinEuclidean (actualParisiRowsTerminalSpin omega) -
          actualParisiRowsPosteriorMean W beta
            (parisiEquilibriumPhysicalEndpoint beta +
              (B * Real.log (n : ℝ)).toNNReal) omega‖^2 >
            (sparseFieldRadius rho n : ℝ) / 4} ≤
        2 * Real.exp (-(sparseFieldRadius rho n : ℝ) / 64) := by
  let rho' := (rho + B / 2) / 2
  have hrr : rho < rho' := by dsimp [rho']; linarith
  have hrB : rho' < B / 2 := by dsimp [rho']; linarith
  have hsmall := pinning_log_time_eventually_small B rho' hB hrB
  have hscale := constant_rpow_le_small_rpow (-rho') (-rho) 1 (1 / 8)
    (by linarith) (by norm_num) (by norm_num)
  filter_upwards [hsmall, hscale, hT, eventually_ge_atTop (1 : ℕ)]
    with n hs hc ht hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hR : (0 : ℝ) < (sparseFieldRadius rho n : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnR (1 - rho)))
  let eta := (sparseFieldRadius rho n : ℝ) / (8 * (n : ℝ))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hpow : (n : ℝ) * (n : ℝ)^(-rho) = (n : ℝ)^(1 - rho) := by
    calc
      _ = (n : ℝ)^(1 : ℝ) * (n : ℝ)^(-rho) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hnR]; congr 1
  have hceil : (n : ℝ)^(1 - rho) ≤ (sparseFieldRadius rho n : ℝ) := Nat.le_ceil _
  have hradius : (1 / 8) * (n : ℝ)^(-rho) ≤ eta := by
    dsimp [eta]
    rw [le_div_iff₀ (by positivity : 0 < 8 * (n : ℝ))]
    nlinarith
  have hS : 8 * Real.exp (-((B * Real.log (n : ℝ)).toNNReal : ℝ) / 2) ≤ eta := by
    simp only [one_mul] at hc
    exact hs.2.trans (hc.trans hradius)
  have htail := actualParisiPinning_iid_tail_exp W beta hbeta _ _ hs.1 ht n hn0
    eta heta hS
  have hsub : {omega | ‖spinEuclidean (actualParisiRowsTerminalSpin omega) -
        actualParisiRowsPosteriorMean W beta
          (parisiEquilibriumPhysicalEndpoint beta +
            (B * Real.log (n : ℝ)).toNNReal) omega‖^2 >
          (sparseFieldRadius rho n : ℝ) / 4} ⊆
      {omega | 2 * eta ≤ (∑ i : Fin n, actualParisiPinningError W beta
        (parisiEquilibriumPhysicalEndpoint beta + (B * Real.log (n : ℝ)).toNNReal)
          (omega i)) / (n : ℝ)} := by
    intro omega homega
    rw [mem_ofPred_eq, actualParisiRows_pinning_norm_sq] at homega
    change 2 * eta ≤ (∑ i : Fin n, actualParisiPinningError W beta
      (parisiEquilibriumPhysicalEndpoint beta + (B * Real.log (n : ℝ)).toNNReal)
        (omega i)) / (n : ℝ)
    rw [le_div_iff₀ hnR]
    dsimp [eta]
    have he : 2 * ((sparseFieldRadius rho n : ℝ) / (8 * (n : ℝ))) * (n : ℝ) =
        (sparseFieldRadius rho n : ℝ) / 4 := by field_simp; ring
    rw [he]
    exact homega.le
  apply (measureReal_mono hsub).trans
  convert htail using 1
  congr 2
  dsimp [eta]
  field_simp
  ring

theorem hamming_le_radius_of_pinning {n : ℕ} (x y : Spin n)
    (m m' : EuclideanSpace ℝ (Fin n)) (R : ℕ)
    (hx : ‖spinEuclidean x - m‖^2 ≤ (R : ℝ) / 4)
    (hm : ‖m - m'‖^2 ≤ (R : ℝ) / 4)
    (hy : ‖spinEuclidean y - m'‖^2 ≤ (R : ℝ) / 4) :
    hammingDist x y ≤ R := by
  have h := spinHamming_pinning_triangle x y m m'
  rw [norm_sub_rev m' (spinEuclidean y)] at h
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hc : (hammingDist x y : ℝ) ≤ R := by linarith
  exact_mod_cast hc

end SKConstants.M6
