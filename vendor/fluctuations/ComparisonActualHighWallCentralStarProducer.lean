module

public import ComparisonActualHighWallRegularSlab
public import ComparisonActualHighWallCentralStarCore
public import ComparisonSignedCavityActualSlowWindowSequence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
namespace ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_central_mass_selection
    {m delta cl cu Az C0 Ct D Bclock a b c1 : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (ha : starMassBandConstant cu Az≤ a) (hab : a< b)
    (_hc1 : 0< c1) (hc1thermal : c1< actualMassSavingExponent m delta/8) (hc1floor : c1<3*m+delta)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsd : ∀n,(M n).xs≤ (M n).data.d) (hdW : ∀n,(M n).data.d≤ W n)
    (hWlim : Tendsto W atTop (𝓝 0)) (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀P : (M n).Potential,∀s t : ℝ,
      a*W n≤ s → t≤ b*W n → s< t → (M n).data.N^(-c1)*W n≤ t-s →
      ∃u∈Ioo s t,P.H ((M n).data.wallRadius (M n).alpha u)≤0 ∧
        orderedPathB (n+1) (M n).bf (M n).hf u-(orderedPathS (n+1) (M n).bf (M n).hf u)^2≤
          (M n).data.N^(-(actualMassSavingExponent m delta/4))*(W n)^2 ∧
        (orderedPathS (n+1) (M n).bf (M n).hf u-(M n).data.wallRadius (M n).alpha u)^2≤
          16*(M n).cavityCapTravel^2+2*((M n).data.N^(-(actualMassSavingExponent m delta/4))*(W n)^2) := by
  have hgap : cu*Az< a:=by
    have HH : cu*Az< starMassBandConstant cu Az:=by unfold starMassBandConstant;linarith
    exact HH.trans_le ha
  have hxs n : (M n).xs≤ W n:=(hxsd n).trans (hdW n)
  have HS:=eventually_actual_high_wall_regular_mass_slab_polynomial hm hdelta hroom hcl hcu hAz
    hC0 hCt hgap hab M W hxsd hdW hWlim hsRatio
  have HP:=eventually_actual_high_wall_star_band_parameters hm hdelta hcl hcu hAz hC0 hgap M W hxs hsRatio
  have HF:=eventually_actual_high_wall_floor_mass_polynomial (m:=m) (delta:=delta) (cl:=cl)
    (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hc1floor
  have HC:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/4)
      (q:=-(actualMassSavingExponent m delta/2)) (r:=-(actualMassSavingExponent m delta/4)-c1)
      (by norm_num) (by linarith [actualMassSavingExponent_pos hm hdelta]))
  have HB:=(hWlim.const_mul b).eventually (eventually_le_nhds (show b*(0:ℝ)<1 by simp))
  filter_upwards [HS,HP,HF,HC,HB] with n hs hp hf hc hb
  intro P s t hstart hend hst hwidth
  have hcoef : (M n).data.N^(-(actualMassSavingExponent m delta/2))≤
      (1/4)*(M n).data.N^(-(actualMassSavingExponent m delta/4)-c1):=by
    simpa only [ActualHighWallData.N,one_mul] using hc
  have hwall : (M n).data.rmin+(M n).cavityCapTravel≤ ((a/cu)/2)*W n:=by
    convert hp.2.2.2.2.2.2 using 1;ring
  exact P.central_star_from_integrated_band hcl hcu hAz
    ((M n).data.hd.trans_le (hdW n)) (hxs n) ha hab.le hb hp.1.le hwall hs hcoef
    (hf (M n) (W n) (hxs n)) hstart hend hst hwidth

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
