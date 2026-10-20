module

public import ComparisonActualHighWallWeakComparableContext
public import ComparisonActualHighWallStarProjectionScalars

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ}

theorem rmin_over_test_le_high_floor (a : ActualHighWallData n delta)
    {x : ℝ} (hdx : a.d ≤ x) : a.rmin/x ≤ a.N^(-delta)/2 := by
  have hx : 0 < x := a.hd.trans_le hdx
  have hp : 0 < a.N^delta := Real.rpow_pos_of_pos a.hN _
  have Hcap := concreteWallCap_ge (δ := delta) a.hN a.hE a.hd a.hs.1.le
  have Hradius : a.rmin ≤ x/(2*a.N^delta) := by
    change comparisonSmallMass a.N a.E/(2*concreteWallCap a.N delta a.E a.d a.s) ≤ _
    exact (div_le_div_of_nonneg_left a.hU.le (mul_pos (by norm_num) hp)
      (mul_le_mul_of_nonneg_left Hcap (by norm_num))).trans
        (div_le_div_of_nonneg_right (a.hsmall.trans hdx) (by positivity))
  calc
    a.rmin/x ≤ (x/(2*a.N^delta))/x := div_le_div_of_nonneg_right Hradius hx.le
    _ = a.N^(-delta)/2 := by
      rw [Real.rpow_neg a.hN.le]
      field_simp

end ActualHighWallData

namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem rmin_over_larger_scale_tendsto_zero
    (hdelta : 0 < delta) (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hdx : ∀ n,(M n).data.d ≤ x n) :
    Tendsto (fun n => (M n).data.rmin/x n) atTop (𝓝 0) := by
  have HX := (((tendsto_rpow_neg_atTop hdelta).comp tendsto_natCast_atTop_atTop).comp
    ((tendsto_add_atTop_nat 1).comp hdim)).div_const 2
  apply squeeze_zero (fun n => div_nonneg (M n).data.hrbounds.1.le
    ((M n).data.hd.trans_le (hdx n)).le) _ (by simpa only [zero_div] using HX)
  intro n
  exact (M n).data.rmin_over_test_le_high_floor (hdx n)

theorem concrete_omission_over_larger_scale_tendsto_zero
    {m : ℝ} (hm : 0 < m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m (m/10000) cl cu Az C0 Ct D Bclock)
    (hE : ∀ᶠ n in atTop,(M n).data.E = wallHighError m (dim n+1))
    (hd : ∀ᶠ n in atTop,(M n).data.d = wallHighD m (dim n+1))
    (hs : ∀ᶠ n in atTop,(M n).data.s = wallHighMass m (dim n+1))
    (x : ℕ → ℝ) (hxs : ∀ n,(M n).xs ≤ x n) :
    Tendsto (fun n => (M n).data.s/x n) atTop (𝓝 0) := by
  have Hratio : Tendsto (fun n => (M n).data.s/comparisonLowerScale
      (M n).data.N (M n).data.E (M n).data.d) atTop (𝓝 0) := by
    apply ((concrete_wall_omission_ratio_tendsto_zero hm).comp
      ((tendsto_add_atTop_nat 1).comp hdim)).congr'
    filter_upwards [hE,hd,hs] with n hnE hnd hns
    simp only [Function.comp_apply,hnE,hnd,hns,ActualHighWallData.N]
  apply squeeze_zero (fun n => div_nonneg (M n).data.hs.1.le
    ((M n).hxs.trans_le (hxs n)).le) _ Hratio
  intro n
  exact div_le_div_of_nonneg_left (M n).data.hs.1.le
    (div_pos (mul_pos (Real.sqrt_pos.mpr (M n).data.hN) (M n).data.hE) (M n).data.hd)
    ((M n).hscale.trans (hxs n))

end ActualHighWallOverlapMinimum

theorem concrete_wall_conditional_scale_le_d
    {m : ℝ} (hm : 0 ≤ m) {n : ℕ} (hn : 0 < n) :
    comparisonConditionalScale (n : ℝ) (m/10000) (wallHighError m n) ((wallHighD m n)^2) ≤
      wallHighD m n := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have Heq : comparisonConditionalScale (n : ℝ) (m/10000) (wallHighError m n) ((wallHighD m n)^2) =
      (n : ℝ)^(m/10000)*comparisonLowerScale (n : ℝ) (wallHighError m n) (wallHighD m n) := by
    unfold comparisonConditionalScale comparisonLowerScale
    rw [Real.sqrt_sq (wallHighD_pos m hn).le]
    ring
  rw [Heq,wallHighLowerScale_eq m hn]
  unfold wallHighD
  rw [←Real.rpow_add hN]
  exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

end OAI.SKFluctuations.LaplaceWindowFormalization
