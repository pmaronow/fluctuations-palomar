module

public import ComparisonActualHighWallCriticalClockRadiusPointwise
public import ComparisonActualHighWallCriticalMeanRadiusL1Along
public import ComparisonActualHighWallInitialMismatchAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

namespace ActualHighWallOverlapMinimum

theorem actual_high_wall_clock_radius_prefix_integral_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock C : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC : 1 ≤ C)
    (hfixed : M.xs = M.data.d)
    (hsmall : M.xs^2 ≤ M.data.T)
    (hunit : C*M.xs ≤ 1) :
    (∫u in 0..C*M.xs,
      |actualScalarClockQuantile M.data.T (n+1) M.bf M.hf u-
        M.data.wallRadius M.alpha u|) ≤
    (∫u in 0..C*M.xs,
      |orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u|)+
      (4*(Az+1/cl)+1)*M.xs*M.data.s := by
  let v := C*M.xs
  let q := actualScalarClockQuantile M.data.T (n+1) M.bf M.hf
  let S := orderedPathS (n+1) M.bf M.hf
  let R := M.data.wallRadius M.alpha
  let A := 4*(Az+1/cl)+1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hv : v∈Icc (0:ℝ) 1 := ⟨mul_nonneg (zero_le_one.trans hC) M.hxs.le,hunit⟩
  have hs : M.data.s ≤ v := M.hsxs.trans (by
    simpa only [v,one_mul] using mul_le_mul_of_nonneg_right hC M.hxs.le)
  have hsub : uIcc (0:ℝ) v ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hv.2
  have hqi : IntervalIntegrable q volume 0 v :=
    (show MonotoneOn q (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using
        actualScalarClockQuantile_monotone M.data.hTpos (n+1) (by omega) M.bf M.hf
          (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)).intervalIntegrable.mono_set hsub
  have hsi : IntervalIntegrable S volume 0 v :=
    (show MonotoneOn S (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.full_mass_mean_monotone).intervalIntegrable.mono_set hsub
  have hri : IntervalIntegrable R volume 0 v :=
    (M.data.wallRadius_lipschitz M.alpha).continuous.intervalIntegrable 0 v
  have hqri : IntervalIntegrable (fun u=>|q u-R u|) volume 0 v := (hqi.sub hri).abs
  have hsri : IntervalIntegrable (fun u=>|S u-R u|) volume 0 v := (hsi.sub hri).abs
  have hlow : ∀u∈Ioo (0:ℝ) M.data.s, |q u-R u|≤|S u-R u|+A*M.xs := by
    intro u hu
    have hu01 : u∈Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2.le.trans M.data.hs1⟩
    have hrad := M.full_radius_le_source_envelope hcl hAz hu01
    have hcr : 0≤Az+1/cl := by positivity
    have hr : R u≤2*(Az+1/cl)*M.xs := by
      have H:=mul_le_mul_of_nonneg_left (by linarith only [hu.2,M.hsxs] : M.xs+u≤2*M.xs) hcr
      dsimp only [R] at H hrad ⊢
      nlinarith only [H,hrad]
    have hf := M.data.low_field_cubic M.alpha hu01 hu.2
    have hd : M.data.d^2≤M.data.T := by simpa only [hfixed] using hsmall
    have hfsmall : (M.hf u:ℝ)/M.data.T≤M.xs/16 := by
      apply (div_le_iff₀ M.data.hTpos).mpr
      have H:=mul_le_mul_of_nonneg_right hsmall M.hxs.le
      rw [←hfixed] at hf
      nlinarith only [hf,H]
    have hp := M.low_mass_mixed_clock_radius_abs_le hu01
    dsimp only [q,R,S]
    rw [actualScalarClockQuantile_on (n+1) M.bf M.hf hu.1]
    dsimp only [A]
    nlinarith only [hp,hr,hfsmall,M.hxs]
  have hhigh : ∀u∈Ioo M.data.s v, |q u-R u|≤|S u-R u| := by
    intro u hu
    have hui : u∈Icc M.data.s 1 := ⟨hu.1.le,hu.2.le.trans hv.2⟩
    have H:=M.high_mass_mixed_clock_radius_abs_le_mean_radius_abs
      (by simpa only [hfixed] using hsmall) hui
    dsimp only [q,R,S]
    rw [actualScalarClockQuantile_on (n+1) M.bf M.hf (M.data.hs.1.trans hu.1)]
    exact H
  have hiloQ := hqri.mono_set (by
    rw [uIcc_of_le M.data.hs.1.le,uIcc_of_le hv.1]
    exact Icc_subset_Icc le_rfl hs)
  have hiloS := hsri.mono_set (by
    rw [uIcc_of_le M.data.hs.1.le,uIcc_of_le hv.1]
    exact Icc_subset_Icc le_rfl hs)
  have hihiQ := hqri.mono_set (by
    rw [uIcc_of_le hs,uIcc_of_le hv.1]
    exact Icc_subset_Icc M.data.hs.1.le le_rfl)
  have hihiS := hsri.mono_set (by
    rw [uIcc_of_le hs,uIcc_of_le hv.1]
    exact Icc_subset_Icc M.data.hs.1.le le_rfl)
  have Hlow := intervalIntegral.integral_mono_on_of_le_Ioo M.data.hs.1.le
    hiloQ (hiloS.add intervalIntegrable_const) hlow
  rw [intervalIntegral.integral_add hiloS intervalIntegrable_const,
    intervalIntegral.integral_const,sub_zero,smul_eq_mul] at Hlow
  have Hhigh := intervalIntegral.integral_mono_on_of_le_Ioo hs
    hihiQ hihiS hhigh
  rw [←intervalIntegral.integral_add_adjacent_intervals hiloQ hihiQ,
    ←intervalIntegral.integral_add_adjacent_intervals hiloS hihiS]
  dsimp only [v,q,S,R] at *
  linarith only [Hlow,Hhigh]

theorem actual_high_wall_critical_clock_radius_l1_along
    {m delta cl cu Az C0 Ct D Bclock T0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT0 : 0 < T0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hT : ∀n,T0≤(M n).data.T)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (C : ℝ) (hC : 1 ≤ C) :
    Tendsto (fun n=>(∫u in 0..C*(M n).xs,
      |actualScalarClockQuantile (M n).data.T (dim n+1) (M n).bf (M n).hf u-
        (M n).data.wallRadius (M n).alpha u|)/(M n).xs^2) atTop (𝓝 0) := by
  let A := 4*(Az+1/cl)+1
  have Hmean := actual_high_wall_critical_mean_radius_l1_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hxlim hsRatio
    C (zero_lt_one.trans_le hC)
  have Hbound := Hmean.add (hsRatio.const_mul A)
  simp only [mul_zero,zero_add] at Hbound
  have Hunit := (hxlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
  have Hsmall := (hxlim.pow 2).eventually
    (eventually_le_nhds (show (0:ℝ)^2<T0 by simpa using hT0))
  apply squeeze_zero' _ _ Hbound
  · filter_upwards [] with n
    exact div_nonneg (intervalIntegral.integral_nonneg
      (mul_nonneg (zero_le_one.trans hC) (M n).hxs.le)
      (fun _ _=>abs_nonneg _)) (sq_nonneg _)
  · filter_upwards [Hunit,Hsmall] with n hnUnit hnSmall
    have hf := (M n).actual_high_wall_clock_radius_prefix_integral_le
      hcl hAz hC (hfixed n) (hnSmall.trans (hT n)) hnUnit
    have H := div_le_div_of_nonneg_right hf (sq_nonneg (M n).xs)
    apply H.trans_eq
    dsimp only [A]
    field_simp [(M n).hxs.ne']

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
