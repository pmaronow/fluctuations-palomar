module

public import ComparisonNativeGeneralScalarCoupling
public import ComparisonSignedCavityActualCalibratedBandGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem monotone_scalar_cut_of_original_integral
    (q r : ℝ→ℝ) (hq : MonotoneOn q (Icc (0:ℝ) 1)) (hr : MonotoneOn r (Icc (0:ℝ) 1))
    {v s t e : ℝ} (hv : v∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) v)
    (hrise : t+e ≤ r s)
    (hi : IntervalIntegrable (fun u=>|q u-r u|) volume 0 v)
    (hsmall : (∫u in 0..v,|q u-r u|) < e*(v-s)) : t < q v := by
  by_contra hn
  have hqv : q v ≤ t := le_of_not_gt hn
  have his : IntervalIntegrable (fun u=>|q u-r u|) volume s v := hi.mono_set (by
    rw [uIcc_of_le hs.2,uIcc_of_le hv.1]
    exact Icc_subset_Icc hs.1 le_rfl)
  have hpoint : ∀u∈Icc s v,e ≤ |q u-r u| := by
    intro u hu
    have hui : u∈Icc (0:ℝ) 1 := ⟨hs.1.trans hu.1,hu.2.trans hv.2⟩
    have Hq : q u ≤ t := (hq hui hv hu.2).trans hqv
    have Hr : t+e ≤ r u := hrise.trans (hr ⟨hs.1,hs.2.trans hv.2⟩ hui hu.1)
    linarith [neg_le_abs (q u-r u)]
  have Hlower:=intervalIntegral.integral_mono_on hs.2 intervalIntegrable_const his hpoint
  rw [intervalIntegral.integral_const,smul_eq_mul] at Hlower
  have Hupper:=intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
    (ae_of_all _ (fun _=>abs_nonneg _)) hi
  nlinarith only [Hlower,Hupper,hsmall]

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_scalar_radius_intervalIntegrable {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) {v : ℝ} (hv : v∈Icc (0:ℝ) 1) :
    IntervalIntegrable (fun u=>|actualScalarClockQuantile T (n+1) M.bf M.hf u-M.R u|) volume 0 v := by
  have hqi : IntervalIntegrable (actualScalarClockQuantile T (n+1) M.bf M.hf) volume 0 v :=
    (show MonotoneOn (actualScalarClockQuantile T (n+1) M.bf M.hf) (uIcc (0:ℝ) v) by
      rw [uIcc_of_le hv.1]
      exact (actualScalarClockQuantile_monotone hT (n+1) (by omega) M.bf M.hf
        M.inherited_bf_monotone M.inherited_hf_monotone).mono (Icc_subset_Icc le_rfl hv.2)).intervalIntegrable
  exact (hqi.sub ((comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha).intervalIntegrable 0 v)).abs

theorem general_compact_original_scalar_cuts
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (Kb Kh : ℕ→ℝ≥0)
    (hparent : ∀n,LipschitzOnWith (Kb n) (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc 0 1))
    (hfield : ∀n,LipschitzOnWith (Kh n) (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc 0 1))
    (hT : 0 < T) (htotal : ∀n u,u∈Icc (0:ℝ) 1 → (M n).h u+(M n).b u ≤ T)
    (hEq4 : ∀C > 0,∃Cb Ch : ℝ,0 ≤ Cb ∧ 0 ≤ Ch ∧ ∀ᶠn in atTop,
      ∀u∈Icc (0:ℝ) (C*W n),|(M n).b u-T| ≤ Cb*(W n)^2 ∧ |(M n).h u| ≤ Ch*(W n)^3) :
    ∀R > 0,∃C : ℝ,0 < C ∧
      (∀ᶠn in atTop,W n*R < actualScalarClockQuantile T (n+1) (M n).bf (M n).hf (min (C*W n) 1) ∧
        W n*R < (M n).R (min (C*W n) 1)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ min (C*W n) 1},
        |actualScalarClockQuantile T (n+1) (M n).bf (M n).hf w-(M n).R w|
          ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^2) atTop (𝓝 0) := by
  intro R hR
  let C:=max (2*starMassBandConstant cu Az) (2*cu*(R+1))
  have hA : starMassBandConstant cu Az ≤ C/2 := by dsimp [C];linarith [le_max_left (2*starMassBandConstant cu Az) (2*cu*(R+1))]
  have hRC : R+1 ≤ (C/2)/cu := (le_div_iff₀ hcu).mpr (by
    dsimp [C];nlinarith only [le_max_right (2*starMassBandConstant cu Az) (2*cu*(R+1))])
  have hC : 0 < C := by have H:=star_mass_band_constant_pos hcu hAz;linarith
  obtain ⟨Cb,Ch,hCb,hCh,HEq⟩:=hEq4 C hC
  have Hcouple:=general_initial_scalar_radius_coupling hm hdelta hroom hcl hcu hAz hC0 hCt
    M W hxs hWlim Kb Kh hparent hfield hT htotal C Cb Ch hC hCb hCh HEq
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have Hsmall:=Hcouple.eventually (eventually_lt_nhds (show (0:ℝ) < C/2 by positivity))
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  refine ⟨C,hC,?_,?_⟩
  · filter_upwards [HW,Hsmall] with n hnW hnsmall
    have hw:=hW n
    rw [min_eq_left hnW]
    have hv : C*W n∈Icc (0:ℝ) 1 := ⟨by positivity,hnW⟩
    have hs : (C/2)*W n∈Icc (0:ℝ) (C*W n) := ⟨by positivity,by nlinarith [hW n]⟩
    have Hrad:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (hW n) (hxs n) hA (hs.2.trans hnW) (show (C/2)*W n∈Icc ((C/2)*W n) ((C/2)*W n) from ⟨le_rfl,le_rfl⟩)).1
    have Hrise : W n*R+W n ≤ (M n).R ((C/2)*W n) := by
      nlinarith only [Hrad,mul_le_mul_of_nonneg_right hRC (hW n).le]
    have Hint : (∫u in 0..C*W n,|actualScalarClockQuantile T (n+1) (M n).bf (M n).hf u-(M n).R u|) <
        W n*(C*W n-(C/2)*W n) := by
      have H:=(div_lt_iff₀ (pow_pos (hW n) 2)).mp hnsmall
      convert H using 1;ring
    have Hq:=monotone_scalar_cut_of_original_integral _ _
      (actualScalarClockQuantile_monotone hT (n+1) (by omega) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone)
      ((comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk (M n).context.hkc
        (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
      hv hs Hrise ((M n).inherited_scalar_radius_intervalIntegrable hT hv) Hint
    have HRmono:=(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha) hs.2
    exact ⟨Hq,by linarith [hW n]⟩
  · apply Hcouple.congr'
    filter_upwards [HW] with n hnW
    have hw:=hW n
    rw [min_eq_left hnW,comparison_original_retained_integral_eq_interval
      (show C*W n∈Icc (0:ℝ) 1 from ⟨by positivity,hnW⟩)
      (fun u=>|actualScalarClockQuantile T (n+1) (M n).bf (M n).hf u-(M n).R u|)]

theorem general_scalar_cdf_local_caps
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (Kb Kh : ℕ→ℝ≥0)
    (hparent : ∀n,LipschitzOnWith (Kb n) (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc 0 1))
    (hfield : ∀n,LipschitzOnWith (Kh n) (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc 0 1))
    (hT : 0 < T) (htotal : ∀n u,u∈Icc (0:ℝ) 1 → (M n).h u+(M n).b u ≤ T)
    (hEq4 : ∀C > 0,∃Cb Ch : ℝ,0 ≤ Cb ∧ 0 ≤ Ch ∧ ∀ᶠn in atTop,
      ∀u∈Icc (0:ℝ) (C*W n),|(M n).b u-T| ≤ Cb*(W n)^2 ∧ |(M n).h u| ≤ Ch*(W n)^3) :
    ∀R > 0,∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ((M n).inheritedScalarMassProfile hT (htotal n)).val (W n*R) ≤ C*W n := by
  intro R hR
  obtain ⟨C,hC,Hcut,_⟩:=general_compact_original_scalar_cuts hm hdelta hroom hcl hcu hAz hC0 hCt
    M W hxs hWlim Kb Kh hparent hfield hT htotal hEq4 R hR
  refine ⟨C,hC,?_⟩
  filter_upwards [Hcut] with n hn
  have hw:=(M n).hxs.trans_le (hxs n)
  have hv : min (C*W n) 1∈Icc (0:ℝ) 1 :=
    ⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have H:=quantileMassProfile_le_of_larger_clock
    (actualScalarClockQuantile T (n+1) (M n).bf (M n).hf)
    (actualScalarClockQuantile_monotone hT (n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone)
    (actualScalarClockQuantile_bounds hT (n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone ((M n).inherited_total_clock_le (htotal n)))
    hv hn.1
  exact H.trans (min_le_left _ _)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
