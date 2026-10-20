module

public import ComparisonActualHighWallGlobalThermalTail
public import ComparisonActualHighWallHighTailSite
public import ComparisonSignedCavityHighProfileNearTwoAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_high_wall_global_original_high_envelope_powers
    {m delta cl cu Az C0 Ct D Bclock c : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hc : 0< c) (hcout : cu*Az< c)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxsd : ∀n,(M n).xs≤(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀ᶠjGrid in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      let as:=finiteCutMasses us jGrid
      ∀U : ℕ,U≤as.length → 2*c*(M n).data.d≤ partitionPoint 0 as U →
      ∀theta : ℝ,1≤ theta → theta≤2 → 2-theta≤ actualMassSavingExponent m delta/128 →
        ClockTree.edgeBudget 0 as (fun j=>((M n).data.highErrorEnvelope (M n).alpha as U j)^theta)+
          (M n).data.d*ClockTree.edgeBudget 0 as ((M n).data.highErrorEnvelope (M n).alpha as U)≤
            (M n).data.N^(-(actualMassSavingExponent m delta/256))*(M n).data.d^2 := by
  let eta:=actualMassSavingExponent m delta
  let C:=actualLowErrorComparisonConstant (2*Bclock) Bclock
  have heta : 0< eta:=actualMassSavingExponent_pos hm hdelta
  have hBc : 0≤ Bclock:=(M 0).data.hTpos.le.trans (M 0).hT
  have hC : 0≤ C:=actualLowErrorComparisonConstant_nonneg _ hBc
  have HT:=eventually_actual_high_wall_global_thermal_tail hm hdelta hroom hcl hcu hAz hC0 hCt
    hc hcout M hxsd hdlim hsRatio
  have HS:=eventually_actual_high_wall_high_tail_site_le (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hC0
  have HC:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=4*C) (d:=1) (q:=-eta/16) (r:=-eta/32)
      zero_lt_one (by linarith))
  have HE:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-eta/128) (r:=-eta/256)
      zero_lt_one (by linarith))
  have HQ:=(hdlim.const_mul (2*c)).eventually
    (eventually_le_nhds (show (2*c)*(0:ℝ)<1 by simp))
  filter_upwards [HT,HS,HC,HE,HQ] with n hnT hnS hnC hnE hnQ
  let a:=M n
  let q:=2*c*a.data.d
  let price:=a.data.highContinuumPrice a.alpha q
  let bound:=a.data.N^(-eta/32)*a.data.d
  have hd:=a.data.hd
  have hN:=a.data.hN
  have hN1 : 1≤ a.data.N:=by dsimp only [a,ActualHighWallData.N];exact_mod_cast (by omega : 1≤ n+1)
  have hq0 : 0≤ q:=by dsimp only [q];positivity
  have hq1 : q≤1:=hnQ
  have hq : q∈Icc (0:ℝ) 1:=⟨hq0,hq1⟩
  have Htail:=hnT q le_rfl hq1
  let I:=∫u in q..1,a.data.thermal a.alpha u
  have hI : 0≤ I:=by
    apply intervalIntegral.integral_nonneg hq1
    intro u hu
    exact a.data.thermal_nonneg a.alpha ⟨hq0.trans hu.1,hu.2⟩
  have HPow : (a.data.N^(-(eta/8))*a.data.d)^2=a.data.N^(-(eta/4))*a.data.d^2:=by
    rw [mul_pow,←Real.rpow_mul_natCast hN.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-(eta/8))*(2:ℝ)=-(eta/4) by ring]
  have hSq : Real.sqrt I≤ a.data.N^(-(eta/8))*a.data.d:=by
    have HR : 0≤ a.data.N^(-(eta/8))*a.data.d:=by positivity
    have HI : I≤ a.data.N^(-(eta/4))*a.data.d^2:=Htail
    nlinarith only [Real.sq_sqrt hI,HR,HI,HPow]
  have hweak : a.data.N^(-(eta/8))≤ a.data.N^(-eta/16):=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsite : 1/a.data.N≤ a.data.N^(-eta/16)*a.data.d:=by
    simpa only [a,eta,neg_div] using hnS (M n) (hxsd n)
  have hsum : Real.sqrt I+1/a.data.N≤2*a.data.N^(-eta/16)*a.data.d:=by
    have HH:=hSq.trans (mul_le_mul_of_nonneg_right hweak hd.le)
    linarith only [HH,hsite]
  have hcompare : a.data.highComparisonConstant≤ C:=a.highComparisonConstant_le
  have hcoef : 4*C*a.data.N^(-eta/16)≤ a.data.N^(-eta/32):=by
    simpa only [a,ActualHighWallData.N,one_mul] using hnC
  have hPriceNonneg : 0≤ price:=by
    dsimp only [price,ActualHighWallData.highContinuumPrice]
    exact mul_nonneg (mul_nonneg (by norm_num) a.data.highComparisonConstant_nonneg)
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hPrice : price≤ bound:=by
    calc
      price=2*a.data.highComparisonConstant*(Real.sqrt I+1/a.data.N):=rfl
      _≤2*C*(Real.sqrt I+1/a.data.N):=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcompare (by norm_num)) (by positivity)
      _≤2*C*(2*a.data.N^(-eta/16)*a.data.d):=mul_le_mul_of_nonneg_left hsum (by positivity)
      _=(4*C*a.data.N^(-eta/16))*a.data.d:=by ring
      _≤bound:=mul_le_mul_of_nonneg_right hcoef hd.le
  have hsiteBase : 1/a.data.N≤ a.data.d:=by
    have HH:=Real.rpow_le_rpow_of_exponent_le hN1 (show -eta/16≤0 by linarith)
    rw [Real.rpow_zero] at HH
    exact hsite.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right HH hd.le)
  filter_upwards [a.data.eventually_high_edge_real_moment_le_actual_continuum a.alpha] with jGrid hgrid
  intro us hus
  dsimp only
  intro U hU hmass theta htheta1 htheta2 hdeficit
  let as:=finiteCutMasses us jGrid
  let R:=a.data.highErrorEnvelope a.alpha as U
  have Hmoment:=hgrid us hus q hq U hU hmass theta
    (zero_lt_one.trans_le htheta1) htheta2
  have Hfirst:=hgrid us hus q hq U hU hmass 1 (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at Hfirst
  have HP:=Real.rpow_le_rpow hPriceNonneg
    hPrice (zero_le_one.trans htheta1)
  have HEbound : a.data.N^(-eta/32)*a.data.d^2/a.data.d=bound:=by
    dsimp only [bound];field_simp
  have HA:=native_high_profile_near_two_absorption hN1 hd le_rfl hsiteBase heta
    htheta1 htheta2 hdeficit
  rw [HEbound] at HA
  have Htheta:=Hmoment.trans (HP.trans HA)
  have HdFirst:=mul_le_mul_of_nonneg_left (Hfirst.trans hPrice) hd.le
  have HEfirst : a.data.d*bound=a.data.N^(-eta/32)*a.data.d^2:=by dsimp only [bound];ring
  rw [HEfirst] at HdFirst
  have Hweak:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1 (show -eta/32≤ -eta/128 by linarith)) (sq_nonneg a.data.d)
  have Htotal:=add_le_add Htheta (HdFirst.trans Hweak)
  have Hcoeff : 2*a.data.N^(-eta/128)≤ a.data.N^(-eta/256):=by
    simpa only [a,ActualHighWallData.N,one_mul] using hnE
  have Hrate:=mul_le_mul_of_nonneg_right Hcoeff (sq_nonneg a.data.d)
  change ClockTree.edgeBudget 0 as (fun j=>(R j)^theta)+
    a.data.d*ClockTree.edgeBudget 0 as R≤_
  dsimp only [eta,a] at Htotal Hrate ⊢
  simp only [neg_div] at Htotal Hrate ⊢
  nlinarith only [Htotal,Hrate]

end OAI.SKFluctuations.LaplaceWindowFormalization
