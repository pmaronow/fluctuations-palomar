module

public import ComparisonActualHighWallSlowWindowData
public import ComparisonSignedCavityActualStarProjectionScalars

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
set_option maxHeartbeats 16000000

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ}
theorem strength_at_scale (a : ActualHighWallData n delta) : a.g a.d=a.d^2 := by
  have HL:=laplaceComparisonStrength_lower a.hd (sq_pos_of_pos a.hd) a.hd
  have HE : a.d^3/a.d=a.d^2:=by field_simp
  rw [HE,min_self] at HL
  exact le_antisymm (laplaceComparisonStrength_le a.d (sq_nonneg _) a.d) HL
end ActualHighWallData

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem regular_cl_le_one
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : cl ≤ 1 := by
  have H:=(M.regular 1 ⟨M.hz.2,le_rfl⟩).1
  simpa only [mul_one,M.alpha.property.2.1] using H

theorem regular_mass_cap_lower
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : 0 ≤ u) : cl ≤ M.data.M u :=
  M.regular_cl_le_one.trans ((show (1:ℝ) ≤ M.data.N^delta from
    le_trans (by norm_num) M.data.hq).trans
      (concreteWallCap_ge M.data.hN M.data.hE M.data.hd hu))

theorem fixed_canonical_scale
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hfixed : M.xs=M.data.d) :
    max M.xs (Real.sqrt (M.data.g M.xs))=M.data.d := by
  rw [hfixed,M.data.strength_at_scale,Real.sqrt_sq_eq_abs,abs_of_pos M.data.hd,max_self]

theorem eventually_actual_high_wall_fixed_slow_window_projection_scalars
    {m delta cl cu Az C0 Ct D Bclock L epsilon : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hL : 0 < L) (hepsilon : 0 < epsilon)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0)) :
    let W:=fun n=>(M n).data.d
    ∃Kv Ks Cprof Ddepth : ℝ,1 ≤ Kv ∧ Kv ≤ Ks ∧ 0 < Cprof ∧ 0 < Ddepth ∧
      ∀ᶠn : ℕ in atTop,∀Cs : ℝ,∀w : ActualSlowWindowChoice,
      IsActualHighWallCalibratedSlowWindow (M n) (W n) L Cs w →
      let u := w.star.val
      let t := massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+3)
      let v := Kv*W n
      let s := Ks*W n
      let theta := (M n).data.N^(-(3*actualSlowWindowExponent m delta))
      let g := laplaceComparisonStrength (M n).data.d ((M n).data.d^2)
      let shortfloor := g v*theta*v/(3*(M n).data.M (Cprof*v)*Real.log (M n).data.N)
      calibratedBandStart cu Az*W n ≤ u ∧ t ≤ 1 ∧ u < t ∧ theta*v ≤ t-u ∧
      (M n).data.wallRadius (M n).alpha t ≤ v ∧ 2*(M n).data.wallRadius (M n).alpha t ≤ s ∧ W n ≤ v ∧ W n ≤ s ∧ (M n).z ≤ s/2 ∧ 4*s ≤ 1 ∧
      g v ≤ (W n)^2 ∧ t ≤ Cprof*v ∧ Cprof*v ≤ 1 ∧ cl ≤ (M n).data.M (Cprof*v) ∧
      (M n).data.M t ≤ (M n).data.M (Cprof*v) ∧
      0 < shortfloor ∧ shortfloor ≤ epsilon*(W n)^3/Real.log (M n).data.N ∧
      ∃J : ℕ,1 ≤ J ∧ (1:ℝ)/8 ≤ (2:ℝ)^J*s ∧ (2:ℝ)^J*s ≤ 1 ∧
        ((J+4:ℕ):ℝ) ≤ Ddepth*Real.log (M n).data.N := by
  dsimp only
  let W:=fun n=>(M n).data.d
  have hxs n : (M n).xs ≤ W n:=by rw [hfixed n]
  have hscale n : laplaceComparisonStrength (M n).data.d ((M n).data.d^2) (M n).xs ≤ (W n)^2:=
    laplaceComparisonStrength_le _ (sq_nonneg _) _
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
  have Hr := eventually_actual_high_wall_scale_polynomial_lower
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hband := (hWlim.const_mul b).eventually
    (eventually_le_nhds (show b*(0:ℝ) < 1 by simp))
  have Hcap := (hWlim.const_mul (Cprof*Kv)).eventually
    (eventually_le_nhds (show Cprof*Kv*(0:ℝ) < 1 by simp))
  have Hsmall := (hWlim.const_mul (4*Ks)).eventually
    (eventually_le_nhds (show 4*Ks*(0:ℝ) < 1 by simp))
  have Hmacro := (hWlim.const_mul (2*Ks)).eventually
    (eventually_le_nhds (by norm_num : 2*Ks*(0:ℝ) < 1/8))
  have Hgap := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=Kv) (d:=1/2) (q:=-(3*c1)) (r:= -c1)
      (by norm_num) (by linarith))
  have Hfloor := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=Kv) (d:=3*cl*epsilon) (q:=-(3*c1)) (r:=0)
      (by positivity) (by linarith))
  have Hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  refine ⟨Kv,Ks,Cprof,Ddepth,hKv,hKs,hCp,hDd,?_⟩
  filter_upwards [Hr,Hband,Hcap,Hsmall,Hmacro,Hgap,Hfloor,Hlog,eventually_gt_atTop (0:ℕ)]
    with n hnLower hnBand hnCap hnSmall hnMacro hnGap hnFloor hnLog hn0
  intro Cs w hw
  obtain ⟨p,hi,hN,hq,hqlower,htotal,hnodes,hstar,_⟩ := hw
  let u := w.star.val
  let t := massNode (a*W n) w.quarter (4*w.index+3)
  let v := Kv*W n
  let s := Ks*W n
  let theta := (M n).data.N^(-(3*c1))
  let g := laplaceComparisonStrength (M n).data.d ((M n).data.d^2)
  let Cap := (M n).data.M (Cprof*v)
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hv : 0 < v := mul_pos hKv0 hW
  have hs : 0 < s := mul_pos (hKv0.trans_le hKs) hW
  have htheta : 0 < theta := Real.rpow_pos_of_pos (M n).data.hN _
  have hlog : 0 < Real.log (M n).data.N := lt_of_lt_of_le zero_lt_one hnLog
  have hut : u < t := by dsimp only [u,t,a] at *;linarith only [hstar.2,hq]
  have htband := hnodes (4*w.index+3) (by omega)
  have htunit : t ∈ Icc (0:ℝ) 1 := ⟨(mul_pos ha hW).le.trans htband.1,htband.2.trans hnBand⟩
  have hustar := calibrated_mass_central_subset hq.le (calibrated_mass_middle_subset hq.le hstar)
  have huband := calibrated_mass_block_subset hq.le hi htotal hustar
  have ha1 : 1 ≤ a := by
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith only [hcu,hAz]
  have hhigh : (M n).data.s ≤ a*W n:=by
    have H:=(M n).hsxs.trans (hxs n)
    have HA:=mul_le_mul_of_nonneg_right ha1 hW.le
    exact H.trans (by simpa only [one_mul] using HA)
  have hR := (M n).actual_closed_regular_mass_band_radius_bounds
    hcl hcu hAz hW (hxs n) hAa hnBand hhigh htband
  have hRv : (M n).data.wallRadius (M n).alpha t ≤ v := by
    have H := mul_le_mul_of_nonneg_right (show b/cl ≤ Kv by dsimp only [Kv];linarith only [hAz]) hW.le
    exact hR.2.trans H
  have hRs : 2*(M n).data.wallRadius (M n).alpha t ≤ s := by
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
    have H := (laplaceComparisonStrength_monotonicities (M n).data.hd.ne' (sq_pos_of_pos (M n).data.hd)
      (r₀:=0) le_rfl).1
      ⟨(M n).hxs.le,(hxs n).trans (hWv.trans hvone)⟩ ⟨hv.le,hvone⟩ ((hxs n).trans hWv)
    exact H.trans (hscale n)
  have hmasscap : t ≤ Cprof*v := by
    have H := mul_le_mul_of_nonneg_left hWv hb.le
    have H' : b*v ≤ Cprof*v := by dsimp only [Cprof];nlinarith only [hv]
    exact htband.2.trans (H.trans H')
  have hcapunit : Cprof*v ∈ Icc (0:ℝ) 1 := ⟨(mul_pos hCp hv).le,by simpa only [v,mul_assoc] using hnCap⟩
  have hcapmono : (M n).data.M t ≤ Cap := (M n).data.hm htunit hcapunit hmasscap
  have hcaplo : cl ≤ Cap:=(M n).regular_mass_cap_lower hcapunit.1
  have hCappos : 0 < Cap := hcl.trans_le hcaplo
  have hgap : theta*v ≤ t-u := by
    have H : Kv*theta ≤ (1/2)*(M n).data.N^(-c1) := hnGap
    have Hmul := mul_le_mul_of_nonneg_right H hW.le
    have Hhalf := mul_le_mul_of_nonneg_left hqlower (by norm_num : (0:ℝ) ≤ 1/2)
    dsimp only [v]
    nlinarith only [Hmul,Hhalf,hstar.2]
  have hfloorcoef : Kv*theta ≤ 3*cl*epsilon := by
    simpa only [ActualHighWallData.N,Real.rpow_zero,mul_one] using hnFloor
  have hshortpos : 0 < g v*theta*v/(3*Cap*Real.log (M n).data.N) := by
    have hg := laplaceComparisonStrength_pos (M n).data.d (sq_pos_of_pos (M n).data.hd) v
    change 0 < laplaceComparisonStrength (M n).data.d ((M n).data.d^2) v*theta*v/
      (3*Cap*Real.log (M n).data.N)
    positivity
  have hshortupper : g v*theta*v/(3*Cap*Real.log (M n).data.N) ≤
      epsilon*(W n)^3/Real.log (M n).data.N := by
    calc
      _ ≤ (W n)^2*theta*v/(3*Cap*Real.log (M n).data.N) := by gcongr
      _ ≤ (W n)^2*theta*v/(3*cl*Real.log (M n).data.N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      _ = (Kv*theta/(3*cl))*((W n)^3/Real.log (M n).data.N) := by dsimp only [v];ring
      _ ≤ epsilon*((W n)^3/Real.log (M n).data.N) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ (by positivity : 0 < 3*cl)).mpr
          (by nlinarith only [hfloorcoef])) (by positivity)
      _ = _ := by ring
  have hNgt : 1 < (M n).data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast (by omega : 1 < n+1)
  obtain ⟨J,hJ,hreach,hend,hdepth⟩ := exists_actual_buffer_dyadic_count hNgt hnLog hs
    (by norm_num : (0:ℝ) < 1/8) (by simpa only [s,mul_assoc] using hnMacro)
    (by norm_num : (1:ℝ)/8 ≤ 1) (((hnLower (M n)).trans (hxs n)).trans hWs)
  refine ⟨huband.1,htunit.2,hut,hgap,hRv,hRs,hWv,hWs,hzs,hsone,hgupper,hmasscap,hcapunit.2,hcaplo,hcapmono,
    hshortpos,hshortupper,J,hJ,hreach,?_,?_⟩
  · linarith only [hend]
  · dsimp only [Ddepth]
    push_cast at hdepth hnLog ⊢
    nlinarith only [hdepth,hnLog]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
