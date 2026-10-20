module

public import ComparisonActualHighWallStarClockDistinct
public import ComparisonSignedCavityActualBufferEndpointGeometry

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 12000000
namespace ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_scale_polynomial_lower
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.N^(-(2:ℝ)) ≤ M.xs := by
  have Hcoef := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/C0) (q:=-(2:ℝ)) (r:=-(1:ℝ))
      (by positivity) (by norm_num))
  filter_upwards [Hcoef] with n hn
  intro M
  have hupper : M.data.E ≤ M.data.d^2/Real.sqrt M.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hlower : (1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d ≤ M.data.E := by
    have H : (M.data.N^(-(2:ℝ)/3+m)*M.data.d)/C0 ≤ M.data.E :=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have Hparent := comparison_parent_scale_lower_bounds M.data.hN (one_div_pos.mpr hC0)
    M.data.hd hlower hupper
  have Hpow : M.data.N^(-(1:ℝ)) ≤ M.data.N^(-(1:ℝ)/6+m) :=
    Real.rpow_le_rpow_of_exponent_le (by
      dsimp only [ActualHighWallData.N]
      exact_mod_cast Nat.succ_pos n) (by linarith)
  have Hx := (mul_le_mul_of_nonneg_left Hpow (one_div_pos.mpr hC0).le).trans
    (Hparent.2.2.trans M.hscale)
  exact (show M.data.N^(-(2:ℝ)) ≤ (1/C0)*M.data.N^(-(1:ℝ)) by
    simpa only [ActualHighWallData.N,one_mul] using hn).trans Hx

theorem eventually_actual_high_wall_buffer_endpoint_geometry
    {m delta cl cu Az C0 Ct D Bclock L c1 : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hL : 0 < L) (hc1 : 0 < c1)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hdW : ∀n,(M n).data.d ≤ W n) (hWlim : Tendsto W atTop (𝓝 0)) :
    ∃K Cprof Rmacro Ddepth : ℝ,1 ≤ K ∧ 0 < Cprof ∧ 0 < Rmacro ∧ 0 < Ddepth ∧
      Rmacro ≤ 1/(4*K) ∧ ∀ᶠn : ℕ in atTop,
      let a := calibratedBandStart cu Az
      let b := a+4*L
      ∀lo hi : ℝ,lo ∈ Icc (a*W n) (b*W n) → hi ∈ Icc (a*W n) (b*W n) →
        lo ≤ hi → (M n).data.N^(-c1)*W n ≤ hi-lo →
      let rlo := (M n).data.wallRadius (M n).alpha lo
      let rhi := (M n).data.wallRadius (M n).alpha hi
      0 < lo ∧ hi ≤ 1 ∧ (M n).data.s ≤ lo ∧ (M n).data.rmin ≤ rlo/4 ∧ (M n).xs ≤ rlo ∧ (M n).z ≤ rlo/2 ∧ rlo ≤ rhi ∧ rhi ≤ K*rlo ∧
      hi ≤ Cprof*rlo ∧ Cprof*rlo ≤ 1 ∧ 2*rhi ≤ 1 ∧
      (M n).data.N^(-(2*c1))*rlo ≤ hi-lo ∧ hi-lo ≤ K*cu*rlo ∧
      ∃J : ℕ,1 ≤ J ∧ Rmacro ≤ (2:ℝ)^J*rlo ∧ (2:ℝ)^J*rhi ≤ 1 ∧
        ((J+3:ℕ):ℝ) ≤ Ddepth*Real.log (M n).data.N := by
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
  have hab : a ≤ b := by dsimp only [b];linarith
  have hb : 0 < b := ha.trans_le hab
  have hrmin : 0 < rmin := div_pos ha hcu
  have hrmax : 0 < rmax := div_pos hb hcl
  have hK : 1 ≤ K := by
    have H := div_pos hrmax hrmin
    dsimp only [K]
    linarith only [H]
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCprof : 0 < Cprof := by dsimp only [Cprof];positivity
  have hmacro : 0 < Rmacro := by dsimp only [Rmacro];positivity
  have hDdepth : 0 < Ddepth := by dsimp only [Ddepth];positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have hmacrobound : Rmacro ≤ 1/(4*K) := by
    dsimp only [Rmacro]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hKpos]
  have hRone : Rmacro ≤ 1 := by
    dsimp only [Rmacro]
    apply (div_le_iff₀ (by positivity : 0 < 8*K)).mpr
    nlinarith only [hK]
  have hAa : starMassBandConstant cu Az ≤ a := by
    dsimp only [a,calibratedBandStart]
    linarith only [hA,hcu]
  have hmin2 : 2 ≤ rmin := by
    apply (le_div_iff₀ hcu).mpr
    dsimp only [a,calibratedBandStart]
    linarith only [hA]
  have hminAz : 2*Az ≤ rmin := by
    apply (le_div_iff₀ hcu).mpr
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith only [hcu]
  have hKr : rmax ≤ K*rmin := by
    dsimp only [K]
    rw [add_mul,one_mul,div_mul_cancel₀ _ hrmin.ne']
    linarith only [hrmin]
  have hCr : b ≤ Cprof*rmin := by
    dsimp only [Cprof]
    rw [add_mul,one_mul,div_mul_cancel₀ _ hrmin.ne']
    linarith only [hrmin]
  have HWband := (hWlim.const_mul b).eventually
    (eventually_le_nhds (show b*(0:ℝ) < 1 by simp))
  have HWprof := (hWlim.const_mul (Cprof*rmax)).eventually
    (eventually_le_nhds (show Cprof*rmax*(0:ℝ) < 1 by simp))
  have HWmacro := (hWlim.const_mul (2*rmax)).eventually
    (eventually_le_nhds (show 2*rmax*(0:ℝ) < Rmacro by simpa using hmacro))
  have Hwidth := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=rmax) (d:=1) (q:=-(2*c1)) (r:= -c1)
      zero_lt_one (by linarith))
  have Hlower := eventually_actual_high_wall_scale_polynomial_lower
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  refine ⟨K,Cprof,Rmacro,Ddepth,hK,hCprof,hmacro,hDdepth,hmacrobound,?_⟩
  filter_upwards [HWband,HWprof,HWmacro,Hwidth,Hlower,Hlog,eventually_gt_atTop (0:ℕ)]
    with n hnBand hnProf hnMacro hnWidth hnLower hnLog hn0
  dsimp only
  intro lo hi hlo hhi hlohi hwidth
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have ha1 : 1 ≤ a := by
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith only [hcu,hAz]
  have hhigh : (M n).data.s ≤ a*W n := by
    have H := (M n).hsxs.trans (hxs n)
    have Hmul := mul_le_mul_of_nonneg_right ha1 hW.le
    exact H.trans (by simpa only [one_mul] using Hmul)
  have hRlo := (M n).actual_closed_regular_mass_band_radius_bounds
    hcl hcu hAz hW (hxs n) hAa hnBand hhigh hlo
  have hRhi := (M n).actual_closed_regular_mass_band_radius_bounds
    hcl hcu hAz hW (hxs n) hAa hnBand hhigh hhi
  have hxlo : (M n).xs ≤ (M n).data.wallRadius (M n).alpha lo := by
    have H := mul_le_mul_of_nonneg_right hmin2 hW.le
    linarith only [hxs n,H,hRlo.1,hW]
  have hzlo : (M n).z ≤ (M n).data.wallRadius (M n).alpha lo/2 := by
    have H := mul_le_mul_of_nonneg_right hminAz hW.le
    have HZ := (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)
    linarith only [H,HZ,hRlo.1]
  have hRlopos : 0 < (M n).data.wallRadius (M n).alpha lo := (M n).hxs.trans_le hxlo
  have hmono := (M n).data.wallRadius_monotone (M n).alpha hlohi
  have hratio : (M n).data.wallRadius (M n).alpha hi ≤ K*(M n).data.wallRadius (M n).alpha lo := by
    calc
      _ ≤ rmax*W n := hRhi.2
      _ ≤ (K*rmin)*W n := mul_le_mul_of_nonneg_right hKr hW.le
      _ ≤ K*(M n).data.wallRadius (M n).alpha lo := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hRlo.1 hKpos.le
  have hmass : hi ≤ Cprof*(M n).data.wallRadius (M n).alpha lo := by
    calc
      _ ≤ b*W n := hhi.2
      _ ≤ (Cprof*rmin)*W n := mul_le_mul_of_nonneg_right hCr hW.le
      _ ≤ Cprof*(M n).data.wallRadius (M n).alpha lo := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hRlo.1 hCprof.le
  have hprofone : Cprof*(M n).data.wallRadius (M n).alpha lo ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hRlo.2 hCprof.le).trans (by
      simpa only [mul_assoc] using hnProf)
  have htwolo : 2*(M n).data.wallRadius (M n).alpha lo ≤ Rmacro := by nlinarith only [hRlo.2,hnMacro]
  have htwohi : 2*(M n).data.wallRadius (M n).alpha hi ≤ 1 := by nlinarith only [hRhi.2,hnMacro,hRone]
  have hbufferwidth : (M n).data.N^(-(2*c1))*(M n).data.wallRadius (M n).alpha lo ≤ hi-lo := by
    calc
      _ ≤ (M n).data.N^(-(2*c1))*(rmax*W n) :=
        mul_le_mul_of_nonneg_left hRlo.2 (Real.rpow_nonneg (M n).data.hN.le _)
      _ = (rmax*(M n).data.N^(-(2*c1)))*W n := by ring
      _ ≤ (M n).data.N^(-c1)*W n := mul_le_mul_of_nonneg_right (by
        simpa only [ActualHighWallData.N,one_mul] using hnWidth) hW.le
      _ ≤ hi-lo := hwidth
  have hlopos : 0 < lo := (mul_pos ha hW).trans_le hlo.1
  have hhiunit : hi ∈ Icc (0:ℝ) 1 := ⟨hlopos.le.trans hlohi,hhi.2.trans hnBand⟩
  have hregular := ((M n).regular ((M n).data.wallRadius (M n).alpha hi)
    ⟨by linarith only [hzlo,hmono,hRlopos],by linarith only [htwohi]⟩).2
  rw [(M n).data.wallRadius_spec (M n).alpha
    ⟨(hhigh.trans hlo.1).trans hlohi,hhiunit.2⟩] at hregular
  have hupperwidth : hi-lo ≤ K*cu*(M n).data.wallRadius (M n).alpha lo := by
    have H := mul_le_mul_of_nonneg_left hratio hcu.le
    nlinarith only [hregular,H,hlopos]
  have hN : 1 < (M n).data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast (by omega : 1 < n+1)
  obtain ⟨J,hJ,hreach,hsharp,hdepth⟩ := exists_actual_buffer_dyadic_count hN hnLog hRlopos
    hmacro htwolo hRone ((hnLower (M n)).trans hxlo)
  have hlast : (2:ℝ)^J*(M n).data.wallRadius (M n).alpha hi ≤ 1 := by
    have Hratio := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (2:ℝ)^J)
    have Hsharp := mul_lt_mul_of_pos_left hsharp hKpos
    have Hmacro : K*(2*Rmacro)=(1:ℝ)/4 := by dsimp only [Rmacro];field_simp;ring
    rw [Hmacro] at Hsharp
    nlinarith only [Hratio,Hsharp]
  have hwallroom : (M n).data.rmin ≤ (M n).data.wallRadius (M n).alpha lo/4 := by
    have Hrad := hRlo.1
    have Hmin := mul_le_mul_of_nonneg_right hmin2 hW.le
    have HW := (M n).data.hrbounds.2.1.trans (div_le_div_of_nonneg_right (hdW n) (by norm_num : (0:ℝ) ≤ 4))
    linarith only [Hrad,Hmin,HW,hW]
  exact ⟨hlopos,hhiunit.2,hhigh.trans hlo.1,hwallroom,hxlo,hzlo,hmono,hratio,hmass,hprofone,htwohi,hbufferwidth,hupperwidth,
    J,hJ,hreach,hlast,hdepth⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
