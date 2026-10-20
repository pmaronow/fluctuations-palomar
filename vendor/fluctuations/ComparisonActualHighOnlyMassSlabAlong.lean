module

public import ComparisonActualHighOnlyMassSlabNormalized
public import ComparisonActualHighOnlyWallMassChargesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
open ActualHighOnlyOverlapMinimum

theorem actual_high_only_complete_mass_slab_thermal_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hW : ∀ᶠn in atTop,W n ≤ 1)
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) (hCW : ∀ᶠn in atTop,C*W n ≤ 1) :
    Tendsto (fun n=>(∫u in c*W n..C*W n,
      orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(W n)^3) atTop (𝓝 0) := by
  let η:=actualMassSavingExponent m delta
  have hη : 0 < η:=actualMassSavingExponent_pos hm hdelta
  obtain ⟨Cwall,Cfloor,hCwall,hCfloor,Hbound⟩:=
    eventually_actual_high_only_complete_mass_slab_normalized_le Bclock (D:=D) hm hdelta hroom
      hcl hcu hAz hC0 hCt c C hc hcC
  have Hsmall:=actual_small_mass_ratio_tendsto_zero_along hC0 hm dim hdim M W hxs
  have Hwall:=actual_omitted_wall_mass_ratio_tendsto_zero_along hC0 hm dim hdim M W hxs hsRatio
  have HN : Tendsto (fun n=>(M n).data.N) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have Hpow : Tendsto (fun n=>(M n).data.N^(-(η/2))) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop (show 0 < η/2 by positivity)).comp HN
  have Hlim:=((Hpow.add (Hwall.const_mul Cwall)).add
    ((hsRatio.add Hsmall).const_mul Cfloor))
  simp only [mul_zero,zero_add] at Hlim
  have Hstart : ∀ᶠn in atTop,32*(M n).data.s < c*W n:=by
    filter_upwards [hsRatio.eventually (eventually_lt_nhds (by positivity : (0:ℝ) < c/32))]
      with n hn
    have hn' : (M n).data.s/W n < c/32:=hn
    have hw : 0 < W n:=(M n).hxs.trans_le (hxs n)
    have H:=(div_lt_iff₀ hw).mp hn'
    nlinarith
  have HwallOne : ∀ᶠn in atTop,max (M n).data.U (M n).data.s/W n ≤ 1:=
    Hwall.eventually (eventually_le_nhds zero_lt_one)
  apply squeeze_zero' _ _ Hlim
  · filter_upwards [hCW] with n hnCW
    have hw : 0 < W n:=(M n).hxs.trans_le (hxs n)
    have hcCW : c*W n ≤ C*W n:=mul_le_mul_of_nonneg_right hcC hw.le
    have hlo : 0 ≤ c*W n:=mul_nonneg hc.le hw.le
    have hhi : C*W n ≤ 1:=hnCW
    have H:=intervalIntegral.integral_nonneg_of_ae_restrict (μ:=volume) hcCW
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact (M n).actual_thermal_nonneg_on_unit
          ⟨hlo.trans hu.1,hu.2.trans hhi⟩)
    exact div_nonneg H (pow_pos hw 3).le
  · filter_upwards [hdim.eventually Hbound,hclock,Hcutoff,hCW,Hstart,HwallOne,hW]
      with n hn hnc hnCut hnCW hnStart hnWall hnW
    exact hn (M n) hnCut.1 hnCut.2 hnc (W n) (hxs n) hnW hnCW hnStart hnWall

end OAI.SKFluctuations.LaplaceWindowFormalization
