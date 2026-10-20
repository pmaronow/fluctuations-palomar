module

public import ComparisonActualHighOnlySharpPhysicalBand
public import ComparisonActualHighOnlySharpGoodPoint
public import ComparisonActualHighOnlyInitialCharges

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 10000000
namespace ActualHighOnlyOverlapMinimum
open NativeOverlapMinimum

theorem eventually_actual_high_only_floor_mass_polynomial
    {m delta cl cu Az C0 Ct D Bclock c1 : ℝ}
    (hC0 : 0 < C0) (hc1 : c1 < 3*m+delta) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,M.xs ≤ W →
        M.context.N^(-delta)*M.context.U ≤ (1/2)*M.context.N^(-c1)*W := by
  have H := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=1/2)
      (q:=-(3*m+delta)) (r:=-c1) (by norm_num) (by linarith))
  filter_upwards [H] with n hn
  intro M W hxs
  have hW : 0 < W := M.hxs.trans_le hxs
  have hratio : M.context.U/W ≤ C0^3*M.context.N^(-3*m) :=
    (div_le_div_of_nonneg_left M.context.hU.le M.hxs hxs).trans
      (M.canonical_mass_small_ratio hC0)
  have Hmul := mul_le_mul_of_nonneg_left hratio
    (Real.rpow_nonneg M.context.hN.le (-delta))
  have He : M.context.N^(-delta)*(C0^3*M.context.N^(-3*m)) =
      C0^3*M.context.N^(-(3*m+delta)) := by
    rw [←mul_assoc,mul_comm (M.context.N^(-delta)) (C0^3),mul_assoc,
      ←Real.rpow_add M.context.hN]
    congr 2
    ring
  rw [He] at Hmul
  have Hcoeff : C0^3*M.context.N^(-(3*m+delta)) ≤ (1/2)*M.context.N^(-c1) := by
    simpa only [NativeOverlapContext.N] using hn
  have Hratio' : (M.context.N^(-delta)*M.context.U)/W ≤ (1/2)*M.context.N^(-c1) := by
    simpa only [mul_div_assoc] using Hmul.trans Hcoeff
  exact (div_le_iff₀ hW).mp Hratio'

theorem eventually_actual_high_only_sharp_central_mass_selection
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Ctest : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (a b c1 : ℝ) (ha : starMassBandConstant cu Az ≤ a) (hab : a ≤ b)
    (houter : 2*cu*(Az+1) ≤ a) (ha1 : 1 ≤ a) (_hc1 : 0 < c1) (hc1thermal : c1 < actualMassSavingExponent m delta/8)
    (hc1floor : c1 < 3*m+delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
      M.data.s ≤ 1/4 → M.data.s ≤ M.xs → 64*M.data.s ≤ a*M.xs →
      ∀W : ℝ,W=M.canonicalDirectTestBandScale →
      M.xs^2 ≤ Ctest*laplaceComparisonStrength M.context.d M.lam M.xs →
      W ≤ 1 → 2*b*W ≤ 1 →
      ∀p : M.Potential,∀s t : ℝ,a*W ≤ s → t ≤ b*W → s < t →
        M.context.N^(-c1)*W ≤ t-s →
      ∃u∈Ioo s t,p.H (M.R u) ≤ 0 ∧
        orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2 ≤
          M.context.N^(-(actualMassSavingExponent m delta/4))*(M.xs^4/W^2) ∧
        (orderedPathS (n+1) M.bf M.hf u-M.R u)^2 ≤
          16*M.cavityCapTravel^2+2*(M.context.N^(-(actualMassSavingExponent m delta/4))*(M.xs^4/W^2)) := by
  let η := actualMassSavingExponent m delta
  have hη : 0 < η := actualMassSavingExponent_pos hm hdelta
  have ha0 : 0 < a := (star_mass_band_constant_pos hcu hAz).trans_le ha
  have hc : 0 < a/cu := div_pos ha0 hcu
  have Hslab := eventually_actual_high_only_strong_high_mass_band (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCtest ha0 ha1 hab houter
  have Hfloor := eventually_actual_high_only_floor_mass_polynomial
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct)
    (D:=D) (Bclock:=Bclock) hC0 hc1floor
  have Hthermal := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/4)
      (q:=-(3*η/8)) (r:=-(η/4)-c1) (by norm_num) (by dsimp [η]; linarith))
  filter_upwards [Hslab,Hfloor,Hthermal] with n hnslab hnfloor hnthermal
  intro M hclock hsQuarter hsXs hsHigh W hcanonical hcompare hW1 h2bW p s t hs ht hst hwidth
  have hxs : M.xs ≤ W := by rw [hcanonical];exact M.canonical_direct_test_band_ge_scale
  have hbW : b*W ≤ 1 := by
    have hnonneg : 0 ≤ b*W := mul_nonneg (ha0.le.trans hab) (M.hxs.le.trans hxs)
    linarith only [h2bW,hnonneg]
  have hW : 0 < W := M.hxs.trans_le hxs
  have hxspos := M.hxs
  have hN := M.context.hN
  let F := fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  have hsubunit : Ioo (a*W) (b*W) ⊆ Icc (0:ℝ) 1 :=
    fun u hu=>⟨(mul_pos ha0 hW).le.trans hu.1.le,hu.2.le.trans hbW⟩
  have hiF : IntegrableOn F (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (M.original_thermal_intervalIntegrable)
  have hf0 u (hu : u∈Ioo (a*W) (b*W)) : 0 ≤ F u:=by
    have hui : u∈Icc M.data.s 1:=⟨by
      have HH:=mul_le_mul_of_nonneg_left hxs ha0.le
      linarith only [hsHigh,HH,hu.1,M.data.hs.1],hu.2.le.trans hbW⟩
    have hr:=M.shiftedNativeModel.R_bounds u
    have HD:=M.cavityRadiusPointDefect_nonneg hr
    have HS:=M.shiftedNativeModel.R_spec hui
    change M.alpha.val.val (M.R u)=u at HS
    change 0 ≤ orderedPathB (n+1) M.bf M.hf (M.alpha.val.val (M.R u))-
      (orderedPathS (n+1) M.bf M.hf (M.alpha.val.val (M.R u)))^2 at HD
    rw [HS] at HD
    exact HD
  have hsub : Ioo s t ⊆ Ioo (a*W) (b*W) :=
    fun u hu=>⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩
  have Hmono : (∫u in Ioo s t,F u) ≤ ∫u in Ioo (a*W) (b*W),F u := by
    apply setIntegral_mono_set (hiF.mono_set hsubunit) _ (Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hf0 u hu
  have Hslab' := hnslab M hclock hsQuarter hsXs hsHigh hcompare
    (by simpa only [←hcanonical] using hW1)
    (by simpa only [←hcanonical] using h2bW)
  rw [←hcanonical] at Hslab'
  have hends : a*W ≤ b*W := mul_le_mul_of_nonneg_right hab hW.le
  rw [intervalIntegral.integral_of_le hends,integral_Ioc_eq_integral_Ioo] at Hslab'
  have HI : (∫u in Ioo s t,F u) ≤ M.context.N^(-(3*η/8))*(M.xs^4/W) :=
    Hmono.trans Hslab'
  have hfloor := hnfloor M W hxs
  have hcoef : M.context.N^(-(3*η/8)) ≤ (1/4)*M.context.N^(-(η/4)-c1) := by
    simpa only [NativeOverlapContext.N,one_mul] using hnthermal
  let threshold := M.context.N^(-(η/4))*(M.xs^4/W^2)
  have hthreshold : 0 < threshold := by dsimp [threshold];positivity
  have hstep : 0 < M.context.N^(-c1)*W := by positivity
  have hpow : M.context.N^(-(η/4)-c1) = M.context.N^(-(η/4))*M.context.N^(-c1) := by
    rw [←Real.rpow_add hN]
    congr 1
  have hthermalbound : (∫u in Ioo s t,F u) <
      threshold*((t-s)-M.context.N^(-delta)*M.context.U) := by
    calc
      _ ≤ M.context.N^(-(3*η/8))*(M.xs^4/W) := HI
      _ ≤ ((1/4)*M.context.N^(-(η/4)-c1))*(M.xs^4/W) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = threshold*((1/4)*M.context.N^(-c1)*W) := by
        rw [hpow];dsimp [threshold];field_simp [ne_of_gt hW]
      _ < threshold*((1/2)*M.context.N^(-c1)*W) :=
        mul_lt_mul_of_pos_left (by nlinarith only [hstep]) hthreshold
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hfloor,hwidth]) hthreshold.le
  apply p.exists_thermal_good_star_off_floor_high_only _ hst (ht.trans hbW) hthreshold.le hthermalbound
  have HH:=mul_le_mul_of_nonneg_left hxs ha0.le
  linarith only [hsHigh,HH,hs,M.data.hs.1]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
