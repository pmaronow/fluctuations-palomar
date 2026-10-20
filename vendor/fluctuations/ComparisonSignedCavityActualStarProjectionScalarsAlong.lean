module

public import ComparisonSignedCavityActualSlowWindowBufferCutsAlong
public import ComparisonSignedCavityActualStarProjectionScalars

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeStarBuffer
set_option maxHeartbeats 10000000

namespace NativeOverlapMinimum

theorem eventually_actual_slow_window_projection_scalars_along
    {m delta cl cu Az C0 Ct D Bclock L epsilon : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hL : 0 < L) (hepsilon : 0 < epsilon)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hscale : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2) :
    ∃Kv Ks Cprof Ddepth : ℝ,1 ≤ Kv ∧ Kv ≤ Ks ∧ 0 < Cprof ∧ 0 < Ddepth ∧
      ∀ᶠn : ℕ in atTop,∀T Cs : ℝ,∀w : ActualSlowWindowChoice,
      IsActualCalibratedSlowWindow (M n) (W n) T L Cs w →
      let u := w.star.val
      let t := massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+3)
      let v := Kv*W n
      let s := Ks*W n
      let theta := (M n).context.N^(-(3*actualSlowWindowExponent m delta))
      let g := laplaceComparisonStrength (M n).context.d (M n).lam
      let shortfloor := g v*theta*v/(3*(M n).context.M (Cprof*v)*Real.log (M n).context.N)
      calibratedBandStart cu Az*W n ≤ u ∧ t ≤ 1 ∧ u < t ∧ theta*v ≤ t-u ∧
      (M n).R t ≤ v ∧ 2*(M n).R t ≤ s ∧ W n ≤ v ∧ W n ≤ s ∧ (M n).z ≤ s/2 ∧ 4*s ≤ 1 ∧
      g v ≤ (W n)^2 ∧ t ≤ Cprof*v ∧ Cprof*v ≤ 1 ∧ cl ≤ (M n).context.M (Cprof*v) ∧
      (M n).context.M t ≤ (M n).context.M (Cprof*v) ∧
      0 < shortfloor ∧ shortfloor ≤ epsilon*(W n)^3/Real.log (M n).context.N ∧
      ∃J : ℕ,1 ≤ J ∧ (1:ℝ)/8 ≤ (2:ℝ)^J*s ∧ (2:ℝ)^J*s ≤ 1 ∧
        ((J+4:ℕ):ℝ) ≤ Ddepth*Real.log (M n).context.N := by
  let a := calibratedBandStart cu Az
  let b := a+4*L
  let Kv := 1+b/cl+Az
  let Ks := 2*Kv
  let Cprof := 1+b
  let Ddepth := 2/Real.log 2+5
  let c1 := actualSlowWindowExponent m delta
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hab : a ≤ b := by dsimp only [b];linarith
  have hb : 0 < b := ha.trans_le hab
  have hKv : 1 ≤ Kv := by
    have H := div_pos hb hcl
    dsimp only [Kv]
    linarith only [H,hAz]
  have hKv0 : 0 < Kv := zero_lt_one.trans_le hKv
  have hKs : Kv ≤ Ks := by dsimp only [Ks];linarith only [hKv0]
  have hCp : 0 < Cprof := by dsimp only [Cprof];linarith only [hb]
  have hDd : 0 < Ddepth := by dsimp only [Ddepth];positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have hc1 : 0 < c1 := actualSlowWindowExponent_pos hm hdelta hroom
  have hAa : starMassBandConstant cu Az ≤ a := by
    dsimp only [a,calibratedBandStart]
    linarith [star_mass_band_constant_pos hcu hAz]
  have Hr := eventually_actual_minimum_scale_polynomial_lower
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hband := (hWlim.const_mul b).eventually
    (eventually_le_nhds (show b*(0:ℝ) < 1 by simp))
  have Hcap := (hWlim.const_mul (Cprof*Kv)).eventually
    (eventually_le_nhds (show Cprof*Kv*(0:ℝ) < 1 by simp))
  have Hsmall := (hWlim.const_mul (4*Ks)).eventually
    (eventually_le_nhds (show 4*Ks*(0:ℝ) < 1 by simp))
  have Hmacro := (hWlim.const_mul (2*Ks)).eventually
    (eventually_le_nhds (by norm_num : 2*Ks*(0:ℝ) < 1/8))
  have Hgap := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=Kv) (d:=1/2) (q:=-(3*c1)) (r:= -c1)
      (by norm_num) (by linarith))
  have Hfloor := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=Kv) (d:=3*cl*epsilon) (q:=-(3*c1)) (r:=0)
      (by positivity) (by linarith))
  have Hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((dim n+1:ℕ):ℝ) :=
    ((tendsto_add_atTop_nat 1).comp hdim).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  refine ⟨Kv,Ks,Cprof,Ddepth,hKv,hKs,hCp,hDd,?_⟩
  filter_upwards [hdim.eventually Hr,Hband,Hcap,Hsmall,Hmacro,Hgap,Hfloor,Hlog,hdim.eventually (eventually_gt_atTop (0:ℕ))]
    with n hnLower hnBand hnCap hnSmall hnMacro hnGap hnFloor hnLog hn0
  intro T Cs w hw
  dsimp only
  obtain ⟨p,hi,hN,hq,hqlower,htotal,hnodes,hstar,_⟩ := hw
  let u := w.star.val
  let t := massNode (a*W n) w.quarter (4*w.index+3)
  let v := Kv*W n
  let s := Ks*W n
  let theta := (M n).context.N^(-(3*c1))
  let g := laplaceComparisonStrength (M n).context.d (M n).lam
  let Cap := (M n).context.M (Cprof*v)
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hv : 0 < v := mul_pos hKv0 hW
  have hs : 0 < s := mul_pos (hKv0.trans_le hKs) hW
  have htheta : 0 < theta := Real.rpow_pos_of_pos (M n).context.hN _
  have hlog : 0 < Real.log (M n).context.N := lt_of_lt_of_le zero_lt_one hnLog
  have hut : u < t := by dsimp only [u,t,a] at *;linarith only [hstar.2,hq]
  have htband := hnodes (4*w.index+3) (by omega)
  have htunit : t ∈ Icc (0:ℝ) 1 := ⟨(mul_pos ha hW).le.trans htband.1,htband.2.trans hnBand⟩
  have hustar := calibrated_mass_central_subset hq.le (calibrated_mass_middle_subset hq.le hstar)
  have huband := calibrated_mass_block_subset hq.le hi htotal hustar
  have hR := (M n).actual_closed_regular_mass_band_radius_bounds
    hcl hcu hAz hW (hxs n) hAa hnBand htband
  have hRv : (M n).R t ≤ v := by
    have H := mul_le_mul_of_nonneg_right (show b/cl ≤ Kv by dsimp only [Kv];linarith only [hAz]) hW.le
    exact hR.2.trans H
  have hRs : 2*(M n).R t ≤ s := by
    have H := mul_le_mul_of_nonneg_left hRv (by norm_num : (0:ℝ) ≤ 2)
    simpa only [s,v,Ks,mul_assoc] using H
  have hWv : W n ≤ v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hKv hW.le
  have hWs : W n ≤ s := hWv.trans (mul_le_mul_of_nonneg_right hKs hW.le)
  have hzs : (M n).z ≤ s/2 := by
    have HZ := (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)
    have Hcoef : Az ≤ Kv := by
      have Hpos := div_pos hb hcl
      dsimp only [Kv]
      linarith only [Hpos]
    have H := mul_le_mul_of_nonneg_right Hcoef hW.le
    dsimp only [s,Ks]
    linarith only [HZ,H]
  have hsone : 4*s ≤ 1 := by simpa only [s,mul_assoc] using hnSmall
  have hvone : v ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right hKs hW.le
    linarith only [H,hsone,hs]
  have hgupper : g v ≤ (W n)^2 := by
    have H := (laplaceComparisonStrength_monotonicities (M n).context.hd.ne' (M n).hlam
      (r₀:=0) le_rfl).1
      ⟨(M n).hxs.le,(hxs n).trans (hWv.trans hvone)⟩ ⟨hv.le,hvone⟩ ((hxs n).trans hWv)
    exact H.trans (hscale n)
  have hmasscap : t ≤ Cprof*v := by
    have H := mul_le_mul_of_nonneg_left hWv hb.le
    have H' : b*v ≤ Cprof*v := by dsimp only [Cprof];nlinarith only [hv]
    exact htband.2.trans (H.trans H')
  have hcapunit : Cprof*v ∈ Icc (0:ℝ) 1 := ⟨(mul_pos hCp hv).le,by simpa only [v,mul_assoc] using hnCap⟩
  have hcapmono : (M n).context.M t ≤ Cap := (M n).context.hm htunit hcapunit hmasscap
  have hrpos : 0 < (M n).R t := (mul_pos (div_pos ha hcu) hW).trans_le hR.1
  have hzRt : (M n).z ≤ (M n).R t := by
    have hcoeff : Az ≤ a/cu := by
      apply (le_div_iff₀ hcu).mpr
      dsimp only [a,calibratedBandStart,starMassBandConstant]
      nlinarith only [hcu,hAz]
    have H := mul_le_mul_of_nonneg_right hcoeff hW.le
    exact ((M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)).trans (H.trans hR.1)
  have hcaplo : cl ≤ Cap := ((M n).regular_mass_cap_lower htunit hrpos hzRt).trans hcapmono
  have hCappos : 0 < Cap := hcl.trans_le hcaplo
  have hgap : theta*v ≤ t-u := by
    have H : Kv*theta ≤ (1/2)*(M n).context.N^(-c1) := hnGap
    have Hmul := mul_le_mul_of_nonneg_right H hW.le
    have Hhalf := mul_le_mul_of_nonneg_left hqlower (by norm_num : (0:ℝ) ≤ 1/2)
    dsimp only [v]
    nlinarith only [Hmul,Hhalf,hstar.2]
  have hfloorcoef : Kv*theta ≤ 3*cl*epsilon := by
    simpa only [Function.comp_apply,NativeOverlapContext.N,Real.rpow_zero,mul_one] using hnFloor
  have hshortpos : 0 < g v*theta*v/(3*Cap*Real.log (M n).context.N) := by
    have hg := laplaceComparisonStrength_pos (M n).context.d (M n).hlam v
    change 0 < laplaceComparisonStrength (M n).context.d (M n).lam v*theta*v/
      (3*Cap*Real.log (M n).context.N)
    positivity
  have hshortupper : g v*theta*v/(3*Cap*Real.log (M n).context.N) ≤
      epsilon*(W n)^3/Real.log (M n).context.N := by
    calc
      _ ≤ (W n)^2*theta*v/(3*Cap*Real.log (M n).context.N) := by gcongr
      _ ≤ (W n)^2*theta*v/(3*cl*Real.log (M n).context.N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      _ = (Kv*theta/(3*cl))*((W n)^3/Real.log (M n).context.N) := by dsimp only [v];ring
      _ ≤ epsilon*((W n)^3/Real.log (M n).context.N) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ (by positivity : 0 < 3*cl)).mpr
          (by nlinarith only [hfloorcoef])) (by positivity)
      _ = _ := by ring
  have hNgt : 1 < (M n).context.N := by
    dsimp only [NativeOverlapContext.N]
    exact_mod_cast (by omega : 1 < dim n+1)
  obtain ⟨J,hJ,hreach,hend,hdepth⟩ := exists_actual_buffer_dyadic_count hNgt hnLog hs
    (by norm_num : (0:ℝ) < 1/8) (by simpa only [s,mul_assoc] using hnMacro)
    (by norm_num : (1:ℝ)/8 ≤ 1) (((hnLower (M n)).trans (hxs n)).trans hWs)
  refine ⟨huband.1,htunit.2,hut,hgap,hRv,hRs,hWv,hWs,hzs,hsone,hgupper,hmasscap,hcapunit.2,hcaplo,hcapmono,
    hshortpos,hshortupper,J,hJ,hreach,?_,?_⟩
  · linarith only [hend]
  · dsimp only [Ddepth]
    push_cast at hdepth hnLog ⊢
    nlinarith only [hdepth,hnLog]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
