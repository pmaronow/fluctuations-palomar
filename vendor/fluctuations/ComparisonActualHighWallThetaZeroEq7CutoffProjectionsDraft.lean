module

public import ComparisonActualHighWallThetaZeroEq7OrdinaryCutoffDraft
public import ComparisonActualHighWallThetaZeroEq7ExactReverseGatesCorrectedDraft
public import ComparisonActualHighWallThetaZeroSelectedScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_conditional_scale_upper_of_floor_draft
    {N delta E d lam : ℝ}
    (hN : 1 ≤ N) (hE : 0 < E) (hd : 0 < d) (hd1 : d ≤ 1)
    (hlam : 0 < lam) (hupper : Real.sqrt N*E ≤ d^2)
    (hlamFloor : N^(-(10:ℝ)) ≤ lam) :
    comparisonConditionalScale N delta E lam ≤ N^(5+delta) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hN5 : 0 ≤ N^(-(5:ℝ)) := Real.rpow_nonneg hNp.le _
  have hpow : (N^(-(5:ℝ)))^2 = N^(-(10:ℝ)) := by
    rw [←Real.rpow_mul_natCast hNp.le]
    congr 1
    norm_num
  have hroot := Real.sqrt_le_sqrt hlamFloor
  rw [←hpow,Real.sqrt_sq hN5] at hroot
  have hrootPos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hd2 : d^2 ≤ 1 := pow_le_one₀ hd.le hd1
  have hnum := mul_le_mul_of_nonneg_left (hupper.trans hd2)
    (Real.rpow_nonneg hNp.le delta)
  have hpowId : N^(5+delta)*N^(-(5:ℝ)) = N^delta := by
    rw [←Real.rpow_add hNp]
    congr 1
    ring
  have Hright := mul_le_mul_of_nonneg_left hroot
    (Real.rpow_nonneg hNp.le (5+delta))
  rw [hpowId] at Hright
  unfold comparisonConditionalScale
  apply (div_le_iff₀ hrootPos).mpr
  nlinarith only [hnum,Hright]

theorem comparison_eq7_energy_floor_of_depth_draft
    {N d E : ℝ} (hN : 1 ≤ N) (hd : 0 < d)
    (hdepth : 1/N ≤ d)
    (hcoarse : N^(-(2:ℝ))*d^3 ≤ E) :
    N^(-(5:ℝ)) ≤ E := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hNinv : 0 ≤ 1/N := by positivity
  have H3 := pow_le_pow_left₀ hNinv hdepth 3
  have H := mul_le_mul_of_nonneg_left H3
    (Real.rpow_nonneg hNp.le (-(2:ℝ)))
  have hPow : N^(-(2:ℝ))*(1/N)^3 = N^(-(5:ℝ)) := by
    rw [show 1/N = N^(-(1:ℝ)) by
      rw [Real.rpow_neg hNp.le]; simp,
      ←Real.rpow_mul_natCast hNp.le, ←Real.rpow_add hNp]
    congr 1
    norm_num
  rw [hPow] at H
  exact H.trans hcoarse

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eq7_ordinary_cutoff_energy_floor_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 ≤ m) (hC0 : 0 < C0)
    (hN : 1 ≤ Q.data.N) (hC0N : C0 ≤ Q.data.N)
    (hdepth : 1/Q.data.N ≤ Q.data.d) :
    Q.data.N^(-(5:ℝ)) ≤ Q.data.E := by
  exact comparison_eq7_energy_floor_of_depth_draft hN Q.data.hd hdepth
    (comparison_eq7_post_energy_coarse_lower_draft hN hm hC0 hC0N
      Q.data.hd Q.data.hd1 Q.data.hE Q.hlower)

theorem eq7_ordinary_cutoff_power_le_N_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (z : ℝ) :
    Q.data.N*laplaceComparisonStrength Q.data.d Q.lam z ≤ Q.data.N := by
  have he := laplaceComparisonStrength_le Q.data.d Q.hlam.le z
  have hd2 : Q.data.d^2 ≤ 1 :=
    pow_le_one₀ Q.data.hd.le Q.data.hd1
  have H := mul_le_mul_of_nonneg_left
    (he.trans (Q.hld.trans hd2)) Q.data.hN.le
  simpa only [mul_one] using H

theorem eq7_ordinary_cutoff_at_mass_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (q C Y v : ℝ)
    (hN : 1 ≤ Q.data.N) (hdelta : 0 ≤ delta)
    (hcarrier : Q.xs = comparisonConditionalScale
      Q.data.N delta Q.data.E Q.lam)
    (hlamFloor : Q.data.N^(-(10:ℝ)) ≤ Q.lam)
    (hEfloor : Q.data.N^(-(5:ℝ)) ≤ Q.data.E)
    (hN3 : 72 ≤ Q.data.N^3)
    (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hv : 0 ≤ v) (hvA : v ≤ C*Q.xs)
    (hy : 0 ≤ Q.xs+min (16*v) 1)
    (hyA : Q.xs+min (16*v) 1 ≤ Y*Q.xs)
    (hK : q^4*Y^2*(16*C)^2 ≤ Q.data.N) :
    let y := Q.xs+min (16*v) 1
    let zg := Q.shiftedNativeModel.R (min (16*v) 1)
    let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
    let M := 16*v
    Q.lam*(18*(((q^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*
      Q.data.N^(-(30+10*delta))) ≤ Q.data.E := by
  let y := Q.xs+min (16*v) 1
  let zg := Q.shiftedNativeModel.R (min (16*v) 1)
  let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
  let M := 16*v
  let payload := (q^2*y)^2*power*M^2
  have hAupper : Q.xs ≤ Q.data.N^(5+delta) := by
    rw [hcarrier]
    exact comparison_eq7_conditional_scale_upper_of_floor_draft
      hN Q.data.hE Q.data.hd Q.data.hd1 Q.hlam Q.hupper hlamFloor
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMA : M ≤ 16*C*Q.xs := by
    dsimp only [M]
    nlinarith only [hvA]
  have hpower : 0 ≤ power := by
    dsimp only [power]
    exact (mul_pos Q.data.hN
      (laplaceComparisonStrength_pos Q.data.d Q.hlam zg)).le
  have hPupper : power ≤ Q.data.N :=
    Q.eq7_ordinary_cutoff_power_le_N_draft zg
  have hp : payload ≤ Q.data.N^(22+4*delta) :=
    comparison_eq7_ordinary_cutoff_payload_geometry_draft
      hN hdelta Q.hxs.le hAupper hy hyA hM hMA hpower hPupper
      hY hC hK
  have hp0 : 0 ≤ payload := by dsimp [payload]; positivity
  exact comparison_eq7_ordinary_cutoff_from_payload_draft
    hN hdelta hEfloor Q.hlam.le
    (Q.hld.trans (pow_le_one₀ Q.data.hd.le Q.data.hd1))
    rfl hN3 hp0 hp

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
