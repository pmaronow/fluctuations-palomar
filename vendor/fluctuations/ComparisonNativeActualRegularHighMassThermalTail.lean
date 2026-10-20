module

public import ComparisonNativeActualRegularHighMassPhysicalDyad
public import ComparisonNativeHighTailDyadicAccumulation

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_regular_strong_high_mass_thermal_tail
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0<c) (hcouter : 2*cu*(Az+1)≤c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.xs^2≤Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤1 →
        ∀u : ℝ,2*c*M.canonicalDirectTestBandScale≤u → u≤1 →
          (∫s in u..1,orderedPathB (n+1) M.bf M.hf s-(orderedPathS (n+1) M.bf M.hf s)^2)≤
            M.context.N^(-(actualMassSavingExponent m delta/4))*
              (M.xs^4/M.canonicalDirectTestBandScale^2) := by
  have Hdyad:=eventually_actual_regular_strong_high_mass_dyad
    (D:=D) (Cs:=Cs) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let eta:=actualMassSavingExponent m delta
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-eta/2) (r:=-eta/4)
      zero_lt_one (by linarith))
  filter_upwards [Hdyad,Hcoef] with n hnDyad hnCoef
  intro M hclock hsmall hW1 u hu hu1
  let W:=M.canonicalDirectTestBandScale
  let lo:=c*W
  let f:=fun s=>orderedPathB (n+1) M.bf M.hf s-(orderedPathS (n+1) M.bf M.hf s)^2
  let A:=M.context.N^(-eta/2)*(M.xs^4/W^2)
  have hW : 0<W:=M.canonical_direct_test_band_pos
  have hlo : 0<lo:=mul_pos hc hW
  have hlohalf : lo≤1/2:=by dsimp only [lo,W] at *;linarith only [hu,hu1]
  have hfi : IntervalIntegrable f volume 0 1:=native_comparison_thermal_intervalIntegrable M
  have hf0 s (hs : s∈Icc (0:ℝ) 1) : 0≤f s := by
    have hr:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha s
    have HD:=M.cavityRadiusPointDefect_nonneg hr
    simpa only [f,NativeOverlapMinimum.cavityRadiusPointDefect,comparisonSweepQuantile_mass_spec
      M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha hs] using HD
  have hA : 0≤A:=by dsimp [A];positivity
  have Htail:=native_high_tail_integral_le_dyadic_budget hfi hf0 hlo hlohalf hA (by
    intro v hv hv2 hvlo
    have HH:=hnDyad M hclock hsmall hW1 v hv hv2 hvlo
    have htarget : 0<M.xs^4*v/W^2:=by have :=M.hxs;positivity
    have HI:=(div_le_iff₀ htarget).mp HH
    convert HI using 1
    dsimp only [A,f,W,eta]
    simp only [neg_div]
    ring)
  have hbig : IntervalIntegrable f volume lo 1:=by
    apply hfi.mono_set
    rw [uIcc_of_le (by linarith only [hlohalf]),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hlo.le le_rfl
  have hlu : lo≤u:=by dsimp only [lo,W] at *;linarith only [hu,hlo]
  have hnonneg : 0≤ᵐ[volume.restrict (Ioc lo 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hf0 s ⟨hlo.le.trans hs.1.le,hs.2⟩
  have Hmono:=intervalIntegral.integral_mono_interval hlu hu1 le_rfl hnonneg hbig
  have Hc : 2*M.context.N^(-eta/2)≤M.context.N^(-eta/4) := by
    simpa only [NativeOverlapContext.N,mul_one,one_mul,neg_div] using hnCoef
  have Hrate:=mul_le_mul_of_nonneg_right Hc (show 0≤M.xs^4/W^2 by positivity)
  apply Hmono.trans (Htail.trans _)
  convert Hrate using 1
  all_goals (dsimp only [A,W,eta]; simp only [neg_div]; try ring)

end OAI.SKFluctuations.LaplaceWindowFormalization
