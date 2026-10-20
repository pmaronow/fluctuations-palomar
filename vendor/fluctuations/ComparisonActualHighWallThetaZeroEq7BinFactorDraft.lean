module

public import ComparisonNativeBinScale
public import ComparisonActualHighWallThetaZeroEq7FiniteMaskDefs

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

def comparisonEq7BinTemperatureConstant (beta : ℝ) : ℝ :=
  66+64*beta+65536*(1+beta)^2

def comparisonEq7BinFactorConstant (beta : ℝ) : ℝ :=
  185+128*beta+48*216*256*beta*32+
    comparisonEq7BinTemperatureConstant beta*108*256*32^2

theorem comparison_eq7_native_bin_factor_bound_draft
    {beta L a c mass rho : ℝ}
    (hbeta : 0 ≤ beta) (hL : 1 ≤ L)
    (ha0 : 0 ≤ a) (ha : a ≤ 216)
    (hc0 : 0 ≤ c) (hc : c ≤ 108)
    (hmass : 0 ≤ mass) (hrho : 0 < rho)
    (hratio : mass/rho ≤ 32) :
    0 ≤ nativeBinScaleLoss (beta*L) (a*16^2*L^2)
      (c*16^2*L^2) mass rho ∧
    nativeBinScaleLoss (beta*L) (a*16^2*L^2)
      (c*16^2*L^2) mass rho ≤
        comparisonEq7BinFactorConstant beta*L^4 := by
  let r := mass/rho
  let T := 66+64*(beta*L)+65536*(1+beta*L)^2
  let Tb := comparisonEq7BinTemperatureConstant beta
  let Cb := comparisonEq7BinFactorConstant beta
  have hr0 : 0 ≤ r := div_nonneg hmass hrho.le
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL2 : 1 ≤ L^2 := by nlinarith only [hL, sq_nonneg (L-1)]
  have hL4 : 1 ≤ L^4 := by nlinarith only [hL2, sq_nonneg (L^2-1)]
  have hLL2 : L ≤ L^2 := by nlinarith only [hL, sq_nonneg (L-1)]
  have hL3L4 : L^3 ≤ L^4 := by
    nlinarith only [hL, mul_nonneg (pow_nonneg hL0 3) (sub_nonneg.mpr hL)]
  have hbetaL : 0 ≤ beta*L := mul_nonneg hbeta hL0
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hTb0 : 0 ≤ Tb := by dsimp [Tb,comparisonEq7BinTemperatureConstant]; positivity
  have hT : T ≤ Tb*L^2 := by
    have hsum : 1+beta*L ≤ (1+beta)*L := by
      nlinarith only [hL]
    have hsum0 : 0 ≤ 1+beta*L := by linarith only [hbetaL]
    have hsq := pow_le_pow_left₀ hsum0 hsum 2
    have h1 : 66 ≤ 66*L^2 := by nlinarith only [hL2]
    have h2 : 64*beta*L ≤ 64*beta*L^2 := by
      have H := mul_le_mul_of_nonneg_left hLL2 (by positivity : 0 ≤ 64*beta)
      nlinarith only [H]
    dsimp only [T,Tb,comparisonEq7BinTemperatureConstant]
    nlinarith only [hsq,h1,h2]
  have hr2 : r^2 ≤ 32^2 :=
    pow_le_pow_left₀ hr0 hratio 2
  have hAS : 0 ≤ a*16^2*L^2 := by positivity
  have hAC : 0 ≤ c*16^2*L^2 := by positivity
  have hside :
      48*(a*16^2*L^2)*(beta*L)*r ≤
        (48*216*256*beta*32)*L^4 := by
    have Hcoef : a*r ≤ 216*32 := by
      have H := mul_le_mul ha hratio hr0 (by norm_num : (0:ℝ) ≤ 216)
      nlinarith only [H]
    have Hpow := mul_le_mul_of_nonneg_left hL3L4
      (show 0 ≤ 48*256*beta*216*32 by positivity)
    have Hside := mul_le_mul_of_nonneg_left Hcoef
      (show 0 ≤ 48*256*beta*L^3 by positivity)
    nlinarith only [Hpow,Hside]
  have hcov :
      T*(c*16^2*L^2)*r^2 ≤
        (Tb*108*256*32^2)*L^4 := by
    have Hcoef : c*r^2 ≤ 108*32^2 := by
      have H := mul_le_mul hc hr2 (sq_nonneg r)
        (by norm_num : (0:ℝ) ≤ 108)
      nlinarith only [H]
    have Hprod := mul_le_mul hT Hcoef
      (by positivity : 0 ≤ c*r^2)
      (by positivity : 0 ≤ Tb*L^2)
    have HL2 : 0 ≤ L^2 := sq_nonneg L
    have H := mul_le_mul_of_nonneg_left Hprod
      (show 0 ≤ 256*L^2 by positivity)
    nlinarith only [H]
  have hbase :
      1+2*(76+64*(beta*L))+32 ≤ (185+128*beta)*L^4 := by
    have h1 : 185 ≤ 185*L^4 := by nlinarith only [hL4]
    have h2 : 128*beta*L ≤ 128*beta*L^4 := by
      have hLL4 : L ≤ L^4 := le_trans hLL2
        (by nlinarith only [hL2,hL4, sq_nonneg (L^2-1)])
      exact mul_le_mul_of_nonneg_left hLL4 (by positivity)
    nlinarith only [h1,h2]
  have hnonneg : 0 ≤ nativeBinScaleLoss (beta*L)
      (a*16^2*L^2) (c*16^2*L^2) mass rho := by
    unfold nativeBinScaleLoss
    dsimp only [r] at hr0
    positivity
  refine ⟨hnonneg,?_⟩
  unfold nativeBinScaleLoss comparisonEq7BinFactorConstant
  dsimp only [T,Tb,r] at hT hside hcov hbase
  nlinarith only [hside,hcov,hbase]

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem eq7_inner_low_native_bin_factor_bound_draft
    {h beta : ℝ} (j : Eq7InnerLowDyad Q h)
    (hbeta : 0 ≤ beta) (hL : 1 ≤ Real.log Q.data.N) :
    0 ≤ nativeBinScaleLoss (beta*Real.log Q.data.N)
      (216*16^2*(Real.log Q.data.N)^2)
      (108*16^2*(Real.log Q.data.N)^2)
      (16*Q.eq7InnerDyadMass j.val.val) Q.data.s ∧
    nativeBinScaleLoss (beta*Real.log Q.data.N)
      (216*16^2*(Real.log Q.data.N)^2)
      (108*16^2*(Real.log Q.data.N)^2)
      (16*Q.eq7InnerDyadMass j.val.val) Q.data.s ≤
        comparisonEq7BinFactorConstant beta*(Real.log Q.data.N)^4 := by
  have hv : 0 < Q.eq7InnerDyadMass j.val.val :=
    (comparison_mass_dyadic_scale Q.data.hU j.val.val).1
  have hr : (16*Q.eq7InnerDyadMass j.val.val)/Q.data.s ≤ 32 := by
    apply (div_le_iff₀ Q.data.hs.1).mpr
    nlinarith only [j.property.2.1]
  exact comparison_eq7_native_bin_factor_bound_draft
    hbeta hL (by norm_num) le_rfl (by norm_num) le_rfl
    (by positivity : 0 ≤ 16*Q.eq7InnerDyadMass j.val.val)
    Q.data.hs.1 hr

theorem eq7_inner_post_native_bin_factor_bound_draft
    {h beta : ℝ} (j : Eq7InnerPostDyad Q h)
    (hbeta : 0 ≤ beta) (hL : 1 ≤ Real.log Q.data.N) :
    0 ≤ nativeBinScaleLoss (beta*Real.log Q.data.N)
      (108*16^2*(Real.log Q.data.N)^2)
      (54*16^2*(Real.log Q.data.N)^2)
      (16*Q.eq7InnerDyadMass j.val.val)
      (Q.eq7InnerWallStart j.val.val) ∧
    nativeBinScaleLoss (beta*Real.log Q.data.N)
      (108*16^2*(Real.log Q.data.N)^2)
      (54*16^2*(Real.log Q.data.N)^2)
      (16*Q.eq7InnerDyadMass j.val.val)
      (Q.eq7InnerWallStart j.val.val) ≤
        comparisonEq7BinFactorConstant beta*(Real.log Q.data.N)^4 := by
  have hv : 0 < Q.eq7InnerDyadMass j.val.val :=
    (comparison_mass_dyadic_scale Q.data.hU j.val.val).1
  have hq : Q.eq7InnerDyadMass j.val.val ≤
      Q.eq7InnerWallStart j.val.val := le_max_right _ _
  have hqpos : 0 < Q.eq7InnerWallStart j.val.val := hv.trans_le hq
  have hr : (16*Q.eq7InnerDyadMass j.val.val)/
      (Q.eq7InnerWallStart j.val.val) ≤ 32 := by
    apply (div_le_iff₀ hqpos).mpr
    nlinarith only [hq,hv]
  exact comparison_eq7_native_bin_factor_bound_draft
    hbeta hL (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by positivity : 0 ≤ 16*Q.eq7InnerDyadMass j.val.val)
    hqpos hr

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
