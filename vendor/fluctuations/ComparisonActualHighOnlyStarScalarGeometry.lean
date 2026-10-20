module

public import ComparisonSignedCavityActualBufferEndpointGeometryAlong
public import ComparisonSignedCavityActualStarProjectionScalarsAlong
public import ComparisonActualHighOnlyCommonBuffers
public import ComparisonActualHighOnlyLowSharpWindowSourceAlong
public import ComparisonActualHighOnlyScalarUtilities
public import ComparisonActualHighOnlySourceProjectionAlong

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
 theorem eventually_star_scale_polynomial_lower_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.context.N^(-(2:ℝ)) ≤ M.xs := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/C0) (q:=-(2:ℝ)) (r:=-(1:ℝ)/6+m)
      (by positivity) (by linarith))
  filter_upwards [H] with n hn M
  simpa only [one_mul,ActualHighOnlyComparisonData.N] using hn.trans (M.original_scale_polynomial_lower_high_only hC0)
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 9000000

namespace ActualHighOnlyOverlapMinimum

theorem eventually_actual_buffer_endpoint_geometry_along_high_only
    {m delta cl cu Az C0 Ct D Bclock L c1 : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0)
    (hL : 0 < L) (hc1 : 0 < c1)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs  ≤  W n) (hWlim : Tendsto W atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs) :
    ∃K Cprof Rmacro Ddepth : ℝ,1  ≤  K ∧ 0 < Cprof ∧ 0 < Rmacro ∧ 0 < Ddepth ∧
      Rmacro  ≤  1/(4*K) ∧ ∀ᶠn : ℕ in atTop,
      let a := calibratedBandStart cu Az
      let b := a+4*L
      ∀lo hi : ℝ,lo ∈ Icc (a*W n) (b*W n) → hi ∈ Icc (a*W n) (b*W n) →
        lo  ≤  hi → (M n).context.N^(-c1)*W n  ≤  hi-lo →
      let rlo := (M n).R lo
      let rhi := (M n).R hi
      0 < lo ∧ hi  ≤  1 ∧ (M n).xs  ≤  rlo ∧ (M n).z  ≤  rlo/2 ∧ rlo  ≤  rhi ∧ rhi  ≤  K*rlo ∧
      hi  ≤  Cprof*rlo ∧ Cprof*rlo  ≤  1 ∧ 2*rhi  ≤  1 ∧
      (M n).context.N^(-(2*c1))*rlo  ≤  hi-lo ∧ hi-lo  ≤  K*cu*rlo ∧
      ∃J : ℕ,1  ≤  J ∧ Rmacro  ≤  (2:ℝ)^J*rlo ∧ (2:ℝ)^J*rhi  ≤  1 ∧
        ((J+3:ℕ):ℝ)  ≤  Ddepth*Real.log (M n).context.N := by
  let a := calibratedBandStart cu Az
  let b := a+4*L
  let rmin := a/cu
  let rmax := b/cl
  let K := 1+rmax/rmin
  let Cprof := 1+b/rmin
  let Rmacro := 1/(8*K)
  let Ddepth := 2/Real.log 2+4
  have hA := star_mass_band_constant_pos hcu hAz
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hab : a  ≤  b := by dsimp only [b];linarith
  have hb : 0 < b := ha.trans_le hab
  have hrmin : 0 < rmin := div_pos ha hcu
  have hrmax : 0 < rmax := div_pos hb hcl
  have hK : 1  ≤  K := by
    have H := div_pos hrmax hrmin
    dsimp only [K]
    linarith only [H]
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCprof : 0 < Cprof := by dsimp only [Cprof];positivity
  have hmacro : 0 < Rmacro := by dsimp only [Rmacro];positivity
  have hDdepth : 0 < Ddepth := by dsimp only [Ddepth];positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have hmacrobound : Rmacro  ≤  1/(4*K) := by
    dsimp only [Rmacro]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hKpos]
  have hRone : Rmacro  ≤  1 := by
    dsimp only [Rmacro]
    apply (div_le_iff₀ (by positivity : 0 < 8*K)).mpr
    nlinarith only [hK]
  have hAa : starMassBandConstant cu Az  ≤  a := by
    dsimp only [a,calibratedBandStart]
    linarith only [hA,hcu]
  have hmin2 : 2  ≤  rmin := by
    apply (le_div_iff₀ hcu).mpr
    dsimp only [a,calibratedBandStart]
    linarith only [hA]
  have hminAz : 2*Az  ≤  rmin := by
    apply (le_div_iff₀ hcu).mpr
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith only [hcu]
  have hKr : rmax  ≤  K*rmin := by
    dsimp only [K]
    rw [add_mul,one_mul,div_mul_cancel₀ _ hrmin.ne']
    linarith only [hrmin]
  have hCr : b  ≤  Cprof*rmin := by
    dsimp only [Cprof]
    rw [add_mul,one_mul,div_mul_cancel₀ _ hrmin.ne']
    linarith only [hrmin]
  have HWband := (hWlim.const_mul b).eventually
    (eventually_le_nhds (show b*(0:ℝ) < 1 by simp))
  have HWprof := (hWlim.const_mul (Cprof*rmax)).eventually
    (eventually_le_nhds (show Cprof*rmax*(0:ℝ) < 1 by simp))
  have HWmacro := (hWlim.const_mul (2*rmax)).eventually
    (eventually_le_nhds (show 2*rmax*(0:ℝ) < Rmacro by simpa using hmacro))
  have Hwidth := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=rmax) (d:=1) (q:=-(2*c1)) (r:= -c1)
      zero_lt_one (by linarith))
  have Hlower := eventually_star_scale_polynomial_lower_high_only
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hlog : ∀ᶠn : ℕ in atTop,1  ≤  Real.log ((dim n+1:ℕ):ℝ) :=
    ((tendsto_add_atTop_nat 1).comp hdim).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  refine ⟨K,Cprof,Rmacro,Ddepth,hK,hCprof,hmacro,hDdepth,hmacrobound,?_⟩
  filter_upwards [Hcutoff,HWband,HWprof,HWmacro,Hwidth,hdim.eventually Hlower,Hlog,hdim.eventually (eventually_gt_atTop (0:ℕ))]
    with n hnCutoff hnBand hnProf hnMacro hnWidth hnLower hnLog hn0
  dsimp only
  intro lo hi hlo hhi hlohi hwidth
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have ha1 : 1 ≤ a := by
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith only [hcu,hAz,mul_nonneg hcu.le (by linarith : 0 ≤ Az+1)]
  have hhigh : (M n).data.s ≤ a*W n := hnCutoff.2.trans ((hxs n).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 hW.le))
  have hRlo := (M n).actual_closed_regular_mass_band_radius_bounds
    hcl hcu hAz hW (hxs n) hAa hnBand hhigh hlo
  have hRhi := (M n).actual_closed_regular_mass_band_radius_bounds
    hcl hcu hAz hW (hxs n) hAa hnBand hhigh hhi
  have hxlo : (M n).xs  ≤  (M n).R lo := by
    have H := mul_le_mul_of_nonneg_right hmin2 hW.le
    linarith only [hxs n,H,hRlo.1,hW]
  have hzlo : (M n).z  ≤  (M n).R lo/2 := by
    have H := mul_le_mul_of_nonneg_right hminAz hW.le
    have HZ := (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)
    linarith only [H,HZ,hRlo.1]
  have hRlopos : 0 < (M n).R lo := (M n).hxs.trans_le hxlo
  have hmono := (M n).R_monotone hlohi
  have hratio : (M n).R hi  ≤  K*(M n).R lo := by
    calc
      _  ≤  rmax*W n := hRhi.2
      _  ≤  (K*rmin)*W n := mul_le_mul_of_nonneg_right hKr hW.le
      _  ≤  K*(M n).R lo := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hRlo.1 hKpos.le
  have hmass : hi  ≤  Cprof*(M n).R lo := by
    calc
      _  ≤  b*W n := hhi.2
      _  ≤  (Cprof*rmin)*W n := mul_le_mul_of_nonneg_right hCr hW.le
      _  ≤  Cprof*(M n).R lo := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hRlo.1 hCprof.le
  have hprofone : Cprof*(M n).R lo  ≤  1 := by
    exact (mul_le_mul_of_nonneg_left hRlo.2 hCprof.le).trans (by
      simpa only [mul_assoc] using hnProf)
  have htwolo : 2*(M n).R lo  ≤  Rmacro := by nlinarith only [hRlo.2,hnMacro]
  have htwohi : 2*(M n).R hi  ≤  1 := by nlinarith only [hRhi.2,hnMacro,hRone]
  have hbufferwidth : (M n).context.N^(-(2*c1))*(M n).R lo  ≤  hi-lo := by
    calc
      _  ≤  (M n).context.N^(-(2*c1))*(rmax*W n) :=
        mul_le_mul_of_nonneg_left hRlo.2 (Real.rpow_nonneg (M n).context.hN.le _)
      _ = (rmax*(M n).context.N^(-(2*c1)))*W n := by ring
      _  ≤  (M n).context.N^(-c1)*W n := mul_le_mul_of_nonneg_right (by
        simpa only [Function.comp_apply,ActualHighOnlyComparisonData.N,one_mul] using hnWidth) hW.le
      _  ≤  hi-lo := hwidth
  have hlopos : 0 < lo := (mul_pos ha hW).trans_le hlo.1
  have hhiunit : hi ∈ Icc (0:ℝ) 1 := ⟨hlopos.le.trans hlohi,hhi.2.trans hnBand⟩
  have hregular := ((M n).regular ((M n).R hi)
    ⟨by linarith only [hzlo,hmono,hRlopos],by linarith only [htwohi]⟩).2
  rw [(M n).R_spec_high hhiunit (hRlopos.trans_le hmono)] at hregular
  have hupperwidth : hi-lo  ≤  K*cu*(M n).R lo := by
    have H := mul_le_mul_of_nonneg_left hratio hcu.le
    nlinarith only [hregular,H,hlopos]
  have hN : 1 < (M n).context.N := by
    dsimp only [ActualHighOnlyComparisonData.N]
    exact_mod_cast (by omega : 1 < dim n+1)
  obtain ⟨J,hJ,hreach,hsharp,hdepth⟩ := exists_actual_buffer_dyadic_count hN hnLog hRlopos
    hmacro htwolo hRone ((hnLower (M n)).trans hxlo)
  have hlast : (2:ℝ)^J*(M n).R hi  ≤  1 := by
    have Hratio := mul_le_mul_of_nonneg_left hratio (by positivity : 0  ≤  (2:ℝ)^J)
    have Hsharp := mul_lt_mul_of_pos_left hsharp hKpos
    have Hmacro : K*(2*Rmacro)=(1:ℝ)/4 := by dsimp only [Rmacro];field_simp;ring
    rw [Hmacro] at Hsharp
    nlinarith only [Hratio,Hsharp]
  exact ⟨hlopos,hhiunit.2,hxlo,hzlo,hmono,hratio,hmass,hprofone,htwohi,hbufferwidth,hupperwidth,
    J,hJ,hreach,hlast,hdepth⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer NativeOverlapMinimum
set_option maxHeartbeats 8000000

namespace ActualHighOnlyOverlapMinimum

theorem eventually_actual_slow_window_buffer_cuts_along_high_only
    {m delta cl cu Az C0 Ct D Bclock L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hL : 0 < L)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs  ≤  W n) (hWlim : Tendsto W atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs) :
    ∃K Cprof Rmacro Ddepth : ℝ,1  ≤  K ∧ 0 < Cprof ∧ 0 < Rmacro ∧ 0 < Ddepth ∧
      Rmacro  ≤  1/(4*K) ∧ ∀ᶠn : ℕ in atTop,
      ∀T Cs : ℝ,∀w : ActualSlowWindowChoice,IsActualCalibratedSlowWindow_high_only (M n) (W n) T L Cs w →
      ∃past future : ActualMinimumRetainedBufferCuts_high_only (M n)
        (2*actualSlowWindowExponent m delta) K Cprof Ddepth Rmacro,
        past.lo.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index) ∧
        past.hi.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+1) ∧
        future.lo.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+3) ∧
        future.hi.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*(w.index+1)) ∧
        past.hi.val-past.lo.val=w.quarter ∧ future.hi.val-future.lo.val=w.quarter := by
  have hc1 := actualSlowWindowExponent_pos hm hdelta hroom
  obtain ⟨K,Cprof,Rmacro,Ddepth,hK,hCp,hRm,hDd,hmacro,HG⟩ :=
    eventually_actual_buffer_endpoint_geometry_along_high_only hm hcl hcu hAz hC0 hL hc1 dim hdim M W hxs hWlim Hcutoff
  refine ⟨K,Cprof,Rmacro,Ddepth,hK,hCp,hRm,hDd,hmacro,?_⟩
  filter_upwards [HG] with n hn
  intro T Cs w hw
  obtain ⟨p,hi,hN,hq,hqlower,htotal,hnodes,_⟩ := hw
  let start := calibratedBandStart cu Az*W n
  have hcut : ∀j : ℕ,j+1  ≤  4*w.blocks →
      ∃cut : ActualMinimumRetainedBufferCuts_high_only (M n)
        (2*actualSlowWindowExponent m delta) K Cprof Ddepth Rmacro,
        cut.lo.val=massNode start w.quarter j ∧
        cut.hi.val=massNode start w.quarter (j+1) ∧ cut.hi.val-cut.lo.val=w.quarter := by
    intro j hj
    have hlo := hnodes j (by omega)
    have hhi := hnodes (j+1) hj
    have hgap : massNode start w.quarter (j+1)-massNode start w.quarter j=w.quarter := by
      unfold massNode
      push_cast
      ring
    have hlt : massNode start w.quarter j < massNode start w.quarter (j+1) := by
      linarith only [hgap,hq]
    have hwidth : (M n).context.N^(-actualSlowWindowExponent m delta)*W n  ≤ 
        massNode start w.quarter (j+1)-massNode start w.quarter j := by rw [hgap];exact hqlower
    obtain ⟨hlopos,hhi1,hxslo,hzlo,_,hratio,hmass,hcaproom,hroom,hwidth',hmassupper,
      J,hJ,hreach,hdyadic,hdepth⟩ := hn (massNode start w.quarter j)
        (massNode start w.quarter (j+1)) hlo hhi hlt.le hwidth
    let lo : PositiveMass := ⟨massNode start w.quarter j,hlopos⟩
    let hi : PositiveMass := ⟨massNode start w.quarter (j+1),hlopos.trans hlt⟩
    have hdepth' : (J:ℝ)  ≤  Ddepth*Real.log ((dim n+1:ℕ):ℝ) := by
      have H : (J:ℝ)  ≤  ((J+3:ℕ):ℝ) := by exact_mod_cast Nat.le_add_right J 3
      exact H.trans hdepth
    let cut : ActualMinimumRetainedBufferCuts_high_only (M n)
        (2*actualSlowWindowExponent m delta) K Cprof Ddepth Rmacro := {
      lo:=lo,hi:=hi,ordered:=hlt,high_le_one:=hhi1,
      scale_lower:=hxslo,regular_lower:=hzlo,room:=hroom,radius_ratio:=hratio,
      cap_mass:=hmass,cap_room:=hcaproom,mass_upper:=hmassupper,mass_lower:=hwidth',
      height:=J,height_pos:=hJ,reach:=hreach,dyadic_room:=hdyadic,height_bound:=hdepth' }
    exact ⟨cut,rfl,rfl,hgap⟩
  obtain ⟨past,hplo,hphi,hpgap⟩ := hcut (4*w.index) (by omega)
  obtain ⟨future,hflo,hfhi,hfgap⟩ := hcut (4*w.index+3) (by omega)
  refine ⟨past,future,hplo,hphi,hflo,?_,hpgap,hfgap⟩
  convert hfhi using 1

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
set_option maxHeartbeats 10000000

namespace ActualHighOnlyOverlapMinimum

theorem eventually_actual_slow_window_projection_scalars_along_high_only
    {m delta cl cu Az C0 Ct D Bclock L epsilon : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0)
    (hL : 0 < L) (hepsilon : 0 < epsilon)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs  ≤  W n) (hWlim : Tendsto W atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (hscale : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs  ≤  (W n)^2) :
    ∃Kv Ks Cprof Ddepth : ℝ,1  ≤  Kv ∧ Kv  ≤  Ks ∧ 0 < Cprof ∧ 0 < Ddepth ∧
      ∀ᶠn : ℕ in atTop,∀T Cs : ℝ,∀w : ActualSlowWindowChoice,
      IsActualCalibratedSlowWindow_high_only (M n) (W n) T L Cs w →
      let u := w.star.val
      let t := massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+3)
      let v := Kv*W n
      let s := Ks*W n
      let theta := (M n).context.N^(-(3*actualSlowWindowExponent m delta))
      let g := laplaceComparisonStrength (M n).context.d (M n).lam
      let shortfloor := g v*theta*v/(3*(M n).context.M (Cprof*v)*Real.log (M n).context.N)
      calibratedBandStart cu Az*W n  ≤  u ∧ t  ≤  1 ∧ u < t ∧ theta*v  ≤  t-u ∧
      (M n).R t  ≤  v ∧ 2*(M n).R t  ≤  s ∧ W n  ≤  v ∧ W n  ≤  s ∧ (M n).z  ≤  s/2 ∧ 4*s  ≤  1 ∧
      g v  ≤  (W n)^2 ∧ t  ≤  Cprof*v ∧ Cprof*v  ≤  1 ∧ cl  ≤  (M n).context.M (Cprof*v) ∧
      (M n).context.M t  ≤  (M n).context.M (Cprof*v) ∧
      0 < shortfloor ∧ shortfloor  ≤  epsilon*(W n)^3/Real.log (M n).context.N ∧
      ∃J : ℕ,1  ≤  J ∧ (1:ℝ)/8  ≤  (2:ℝ)^J*s ∧ (2:ℝ)^J*s  ≤  1 ∧
        ((J+4:ℕ):ℝ)  ≤  Ddepth*Real.log (M n).context.N := by
  let a := calibratedBandStart cu Az
  let b := a+4*L
  let Kv := 1+b/cl+Az
  let Ks := 2*Kv
  let Cprof := 1+b
  let Ddepth := 2/Real.log 2+5
  let c1 := actualSlowWindowExponent m delta
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hab : a  ≤  b := by dsimp only [b];linarith
  have hb : 0 < b := ha.trans_le hab
  have hKv : 1  ≤  Kv := by
    have H := div_pos hb hcl
    dsimp only [Kv]
    linarith only [H,hAz]
  have hKv0 : 0 < Kv := zero_lt_one.trans_le hKv
  have hKs : Kv  ≤  Ks := by dsimp only [Ks];linarith only [hKv0]
  have hCp : 0 < Cprof := by dsimp only [Cprof];linarith only [hb]
  have hDd : 0 < Ddepth := by dsimp only [Ddepth];positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have hc1 : 0 < c1 := actualSlowWindowExponent_pos hm hdelta hroom
  have hAa : starMassBandConstant cu Az  ≤  a := by
    dsimp only [a,calibratedBandStart]
    linarith [star_mass_band_constant_pos hcu hAz]
  have Hr := eventually_star_scale_polynomial_lower_high_only
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
  have Hlog : ∀ᶠn : ℕ in atTop,1  ≤  Real.log ((dim n+1:ℕ):ℝ) :=
    ((tendsto_add_atTop_nat 1).comp hdim).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  refine ⟨Kv,Ks,Cprof,Ddepth,hKv,hKs,hCp,hDd,?_⟩
  filter_upwards [Hcutoff,hdim.eventually Hr,Hband,Hcap,Hsmall,Hmacro,Hgap,Hfloor,Hlog,hdim.eventually (eventually_gt_atTop (0:ℕ))]
    with n hnCutoff hnLower hnBand hnCap hnSmall hnMacro hnGap hnFloor hnLog hn0
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
  have ha1 : 1 ≤ a := by
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith only [hcu,hAz,mul_nonneg hcu.le (by linarith : 0 ≤ Az+1)]
  have hhigh : (M n).data.s ≤ a*W n := hnCutoff.2.trans ((hxs n).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 hW.le))
  have hR := (M n).actual_closed_regular_mass_band_radius_bounds
    hcl hcu hAz hW (hxs n) hAa hnBand hhigh htband
  have hRv : (M n).R t  ≤  v := by
    have H := mul_le_mul_of_nonneg_right (show b/cl  ≤  Kv by dsimp only [Kv];linarith only [hAz]) hW.le
    exact hR.2.trans H
  have hRs : 2*(M n).R t  ≤  s := by
    have H := mul_le_mul_of_nonneg_left hRv (by norm_num : (0:ℝ)  ≤  2)
    simpa only [s,v,Ks,mul_assoc] using H
  have hWv : W n  ≤  v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hKv hW.le
  have hWs : W n  ≤  s := hWv.trans (mul_le_mul_of_nonneg_right hKs hW.le)
  have hzs : (M n).z  ≤  s/2 := by
    have HZ := (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)
    have Hcoef : Az  ≤  Kv := by
      have Hpos := div_pos hb hcl
      dsimp only [Kv]
      linarith only [Hpos]
    have H := mul_le_mul_of_nonneg_right Hcoef hW.le
    dsimp only [s,Ks]
    linarith only [HZ,H]
  have hsone : 4*s  ≤  1 := by simpa only [s,mul_assoc] using hnSmall
  have hvone : v  ≤  1 := by
    have H := mul_le_mul_of_nonneg_right hKs hW.le
    linarith only [H,hsone,hs]
  have hgupper : g v  ≤  (W n)^2 := by
    have H := (laplaceComparisonStrength_monotonicities (M n).context.hd.ne' (M n).hlam
      (r₀:=0) le_rfl).1
      ⟨(M n).hxs.le,(hxs n).trans (hWv.trans hvone)⟩ ⟨hv.le,hvone⟩ ((hxs n).trans hWv)
    exact H.trans (hscale n)
  have hmasscap : t  ≤  Cprof*v := by
    have H := mul_le_mul_of_nonneg_left hWv hb.le
    have H' : b*v  ≤  Cprof*v := by dsimp only [Cprof];nlinarith only [hv]
    exact htband.2.trans (H.trans H')
  have hcapunit : Cprof*v ∈ Icc (0:ℝ) 1 := ⟨(mul_pos hCp hv).le,by simpa only [v,mul_assoc] using hnCap⟩
  have hcapmono : (M n).context.M t  ≤  Cap := (M n).context.hm htunit hcapunit hmasscap
  have hrpos : 0 < (M n).R t := (mul_pos (div_pos ha hcu) hW).trans_le hR.1
  have hzRt : (M n).z  ≤  (M n).R t := by
    have hcoeff : Az  ≤  a/cu := by
      apply (le_div_iff₀ hcu).mpr
      dsimp only [a,calibratedBandStart,starMassBandConstant]
      nlinarith only [hcu,hAz]
    have H := mul_le_mul_of_nonneg_right hcoeff hW.le
    exact ((M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)).trans (H.trans hR.1)
  have hcaplo : cl  ≤  Cap := by
    have Hcl:=(M n).regular 1 ⟨(M n).hz.2,le_rfl⟩
    have hcl1 : cl ≤ 1 := by simpa only [mul_one,(M n).alpha.property.2.1] using Hcl.1
    have hN : (1:ℝ) ≤ (M n).data.N := by exact_mod_cast Nat.succ_pos (dim n)
    exact hcl1.trans ((Real.one_le_rpow hN hdelta.le).trans
      (comparisonCap_ge_rpow (M n).data.hN (M n).data.hE (M n).data.hd hcapunit.1))
  have hCappos : 0 < Cap := hcl.trans_le hcaplo
  have hgap : theta*v  ≤  t-u := by
    have H : Kv*theta  ≤  (1/2)*(M n).context.N^(-c1) := hnGap
    have Hmul := mul_le_mul_of_nonneg_right H hW.le
    have Hhalf := mul_le_mul_of_nonneg_left hqlower (by norm_num : (0:ℝ)  ≤  1/2)
    dsimp only [v]
    nlinarith only [Hmul,Hhalf,hstar.2]
  have hfloorcoef : Kv*theta  ≤  3*cl*epsilon := by
    simpa only [Function.comp_apply,ActualHighOnlyComparisonData.N,Real.rpow_zero,mul_one] using hnFloor
  have hshortpos : 0 < g v*theta*v/(3*Cap*Real.log (M n).context.N) := by
    have hg := laplaceComparisonStrength_pos (M n).context.d (M n).hlam v
    change 0 < laplaceComparisonStrength (M n).context.d (M n).lam v*theta*v/
      (3*Cap*Real.log (M n).context.N)
    positivity
  have hshortupper : g v*theta*v/(3*Cap*Real.log (M n).context.N)  ≤ 
      epsilon*(W n)^3/Real.log (M n).context.N := by
    calc
      _  ≤  (W n)^2*theta*v/(3*Cap*Real.log (M n).context.N) := by gcongr
      _  ≤  (W n)^2*theta*v/(3*cl*Real.log (M n).context.N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      _ = (Kv*theta/(3*cl))*((W n)^3/Real.log (M n).context.N) := by dsimp only [v];ring
      _  ≤  epsilon*((W n)^3/Real.log (M n).context.N) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ (by positivity : 0 < 3*cl)).mpr
          (by nlinarith only [hfloorcoef])) (by positivity)
      _ = _ := by ring
  have hNgt : 1 < (M n).context.N := by
    dsimp only [ActualHighOnlyComparisonData.N]
    exact_mod_cast (by omega : 1 < dim n+1)
  obtain ⟨J,hJ,hreach,hend,hdepth⟩ := exists_actual_buffer_dyadic_count hNgt hnLog hs
    (by norm_num : (0:ℝ) < 1/8) (by simpa only [s,mul_assoc] using hnMacro)
    (by norm_num : (1:ℝ)/8  ≤  1) (((hnLower (M n)).trans (hxs n)).trans hWs)
  refine ⟨huband.1,htunit.2,hut,hgap,hRv,hRs,hWv,hWs,hzs,hsone,hgupper,hmasscap,hcapunit.2,hcaplo,hcapmono,
    hshortpos,hshortupper,J,hJ,hreach,?_,?_⟩
  · linarith only [hend]
  · dsimp only [Ddepth]
    push_cast at hdepth hnLog ⊢
    nlinarith only [hdepth,hnLog]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
