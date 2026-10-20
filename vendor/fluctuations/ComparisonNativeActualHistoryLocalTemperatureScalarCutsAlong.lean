module

public import ComparisonNativeActualHistoryLocalTemperatureCouplingAlong
public import ComparisonNativeGeneralScalarCuts
public import ComparisonSignedCavityActualCalibratedBandGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell)
    (hlocal : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∀R > 0,∃C : ℝ,0 < C ∧
      (∀ᶠn in atTop,W n*R < actualMixedClock (dim n+1) (M n).bf (M n).hf (min (C*W n) 1)/(T-epsilon) ∧
        W n*R < (M n).R (min (C*W n) 1)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ min (C*W n) 1},
        |actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T-epsilon)-(M n).R w|
          ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^2) atTop (𝓝 0) := by
  intro R hR
  let C:=max (2*starMassBandConstant cu Az) (2*cu*(R+1))
  have hA : starMassBandConstant cu Az ≤ C/2 := by dsimp [C];linarith [le_max_left (2*starMassBandConstant cu Az) (2*cu*(R+1))]
  have hRC : R+1 ≤ (C/2)/cu := (le_div_iff₀ hcu).mpr (by
    dsimp [C];nlinarith only [le_max_right (2*starMassBandConstant cu Az) (2*cu*(R+1))])
  have hC : 0 < C := by have H:=star_mass_band_constant_pos hcu hAz;linarith
  have Hcouple:=actual_selected_bad_history_local_temperature_initial_scalar_radius_coupling_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin dim hdim
    root M W hxs hWlim epsilon shell hepsilon hshell hlocal hb hh Hhistory C hC
  have Hroot:=actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have Hsmall:=Hcouple.eventually (eventually_lt_nhds (show (0:ℝ) < C/2 by positivity))
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  refine ⟨C,hC,?_,?_⟩
  · filter_upwards [HW,Hsmall,Hroot] with n hnW hnsmall hnRoot
    have hw:=hW n
    rw [min_eq_left hnW]
    have hv : C*W n∈Icc (0:ℝ) 1 := ⟨by positivity,hnW⟩
    have hs : (C/2)*W n∈Icc (0:ℝ) (C*W n) := ⟨by positivity,by nlinarith [hW n]⟩
    have Hrad:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (hW n) (hxs n) hA (hs.2.trans hnW) (show (C/2)*W n∈Icc ((C/2)*W n) ((C/2)*W n) from ⟨le_rfl,le_rfl⟩)).1
    have Hrise : W n*R+W n ≤ (M n).R ((C/2)*W n) := by
      nlinarith only [Hrad,mul_le_mul_of_nonneg_right hRC (hW n).le]
    have Hint : (∫u in 0..C*W n,|actualScalarClockQuantile (T-epsilon) (dim n+1) (M n).bf (M n).hf u-(M n).R u|) <
        W n*(C*W n-(C/2)*W n) := by
      have H:=(div_lt_iff₀ (pow_pos (hW n) 2)).mp hnsmall
      have Heq : (∫u in 0..C*W n,
          |actualScalarClockQuantile (T-epsilon) (dim n+1) (M n).bf (M n).hf u-(M n).R u|)=
          ∫u in 0..C*W n,|actualMixedClock (dim n+1) (M n).bf (M n).hf u/(T-epsilon)-(M n).R u| := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hv.1] at hu
        dsimp only
        rw [(M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root (T-epsilon) hnRoot.2 hu.1]
      rw [Heq]
      convert H using 1;ring
    have Hq:=monotone_scalar_cut_of_original_integral _ _
      (actualScalarClockQuantile_monotone hlocal (dim n+1) (by omega) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone)
      ((comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk (M n).context.hkc
        (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
      hv hs Hrise ((M n).inherited_scalar_radius_intervalIntegrable hlocal hv) Hint
    have HRmono:=(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha) hs.2
    rw [actualScalarClockQuantile_on (dim n+1) (M n).bf (M n).hf (by positivity : 0<C*W n)] at Hq
    exact ⟨Hq,by linarith [hW n]⟩
  · apply Hcouple.congr'
    filter_upwards [HW] with n hnW
    have hw:=hW n
    rw [min_eq_left hnW,comparison_original_retained_integral_eq_interval
      (show C*W n∈Icc (0:ℝ) 1 from ⟨by positivity,hnW⟩)
      (fun u=>|actualMixedClock (dim n+1) (M n).bf (M n).hf u/(T-epsilon)-(M n).R u|)]

theorem actual_selected_bad_history_local_temperature_original_scalar_cdf_caps_along
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell)
    (hlocal : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    (∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧
    ∀R > 0,∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
      ((M n).inheritedScalarMassProfile (hlocal.trans_le (sub_le_self T hepsilon)) htotal).val
        (((T-epsilon)/T)*(W n*R)) ≤ C*W n := by
  have hT:0 < T:=hlocal.trans_le (sub_le_self T hepsilon)
  refine ⟨(actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory).mono (fun _ hn=>hn.1),?_⟩
  intro R hR
  obtain ⟨C,hC,Hcut,_⟩:=actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin dim hdim
    root M W hxs hWlim epsilon shell hepsilon hshell hlocal hb hh Hhistory R hR
  refine ⟨C,hC,?_⟩
  filter_upwards [Hcut] with n hn
  intro htotal
  have hW:0 < W n:=(M n).hxs.trans_le (hxs n)
  have hv:min (C*W n) 1∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le hW.le) zero_le_one,min_le_right _ _⟩
  have hv0:0 < min (C*W n) 1:=lt_min (mul_pos hC hW) zero_lt_one
  have Hamb:((T-epsilon)/T)*(W n*R) <
      actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf (min (C*W n) 1) := by
    rw [actualScalarClockQuantile_on (dim n+1) (M n).bf (M n).hf hv0]
    have H:=mul_lt_mul_of_pos_left hn.1 (div_pos hlocal hT)
    convert H using 1; field_simp [hlocal.ne',hT.ne']
  have H:=quantileMassProfile_le_of_larger_clock
    (actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf)
    (actualScalarClockQuantile_monotone hT (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone)
    (actualScalarClockQuantile_bounds hT (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone ((M n).inherited_total_clock_le htotal))
    hv Hamb
  exact H.trans (min_le_left _ _)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
