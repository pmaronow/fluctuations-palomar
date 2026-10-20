module

public import SKProof.Port.ComparisonActualOriginalQRegularInitialMassMismatchAlong
public import SKProof.Port.ComparisonActualOriginalQLargerWorkingScale
public import ComparisonNativeActualPositiveBandTruncation
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum

 theorem actual_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u|)/(W n)^2) atTop (𝓝 0) := by
  let v:=fun n=>min (C*W n) 1
  have hw n : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hv n : v n∈Icc (0:ℝ) 1:=⟨le_min (mul_nonneg hC.le (hw n).le) zero_le_one,min_le_right _ _⟩
  have hvc n : v n ≤ C*W n:=min_le_left _ _
  have Hsquare:=ActualThetaZeroOverlapMinimum.regular_original_retained_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W v hxs hWlim hclock C hC hv hvc
    (G.omission_over_larger_scale_zero W hxs) (G.eventually_geometric_gates_original_q.mono fun n hn=>⟨hn.2,hn.1⟩)
  let mu:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}
  have Hspin:=comparison_original_mass_normalized_L1_tendsto mu (fun _=>inferInstance)
    (fun n w=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf w-(M n).sweepRadius w)
    W hw hC.le (fun n=>((M n).original_retained_mismatch_integrable (v n)).1)
    (fun n=>((M n).original_retained_mismatch_integrable (v n)).2)
    (fun n=>by rw [comparison_original_retained_mass_exact (hv n)];exact hvc n) Hsquare
  apply Hspin.congr'
  filter_upwards [(hWlim.const_mul C).eventually (eventually_le_nhds (by simp : C*(0:ℝ)<1))] with n hn
  dsimp only [mu,v]
  rw [min_eq_left hn,integral_smul_measure,ENNReal.toReal_ofReal (one_div_nonneg.mpr (hw n).le)]
  simp_rw [abs_div,abs_of_pos (hw n)]
  rw [integral_div,comparison_original_retained_integral_eq_interval
    (show C*W n∈Icc (0:ℝ) 1 from ⟨(mul_pos hC (hw n)).le,hn⟩)
    (fun u=>|orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u|)]
  simp only [smul_eq_mul]
  ring

theorem eventually_actual_regular_calibrated_mass_band
    {m delta cl cu Az C0 Ct D Bclock L T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hL : 0 < L) (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (M : (n : ℕ) → ActualThetaZeroOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs  ≤  W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1) :
    ∃Cs : ℝ,0 < Cs ∧ ∀ᶠn : ℕ in atTop,
      let a := calibratedBandStart cu Az
      let b := a+4*L
      let S := orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf
      MonotoneOn S (Icc (0:ℝ) 1) ∧ b*W n  ≤  1 ∧
      (∀u∈Icc (a*W n) (b*W n),
        (3*(starMassBandConstant cu Az/cu)/4)*W n  ≤  S u ∧
        S u  ≤  Cs*W n ∧
        (a/cu)*W n  ≤  (M n).sweepRadius u ∧ (M n).sweepRadius u  ≤  (b/cl)*W n ∧
        (M n).xs  ≤  (M n).sweepRadius u ∧ (M n).z  ≤  (M n).sweepRadius u/2) ∧
      S (b*W n)-S (a*W n)  ≤  Cs*W n := by
  let A := starMassBandConstant cu Az
  let a := calibratedBandStart cu Az
  let b := a+4*L
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hab : a  ≤  b := by dsimp only [b];linarith
  have hbpos : 0 < b := ha.trans_le hab
  obtain ⟨B,hB,Hraw⟩ := eventually_actual_mass_mean_upper_original_q (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs := B*(1+b)
  have hCs : 0 < Cs := by dsimp only [Cs];positivity
  let c:=A/cu
  have hc : 0 < c:=div_pos hA hcu
  have Habs:=actual_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt N hN M G W hxs hWlim hclock (2*A) (by positivity)
  have Htiny:=Habs.eventually (eventually_lt_nhds (show (0:ℝ)<c*A/4 by positivity))
  have Hhigh:=G.positive_larger_bands_high W hxs hA
  have Hsmall := (hWlim.const_mul b).eventually
    (eventually_le_nhds (show b*(0:ℝ) < 1 by simp))
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [Htiny,Hhigh,hN.eventually Hraw,G.eventually_geometric_gates_original_q,Hsmall] with n hntiny hnhigh hnraw hngate hnsmall
  dsimp only
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hmono := (M n).mass_mean_monotone
  let v:=2*A*W n
  have hv : v∈Icc (A*W n) (2*A*W n):=⟨by dsimp only [v];nlinarith [hA,hW],le_rfl⟩
  have hAv : 2*A  ≤  a := by dsimp only [a,calibratedBandStart,A];linarith
  have hav : A  ≤  a := by linarith
  have hv1 : v  ≤  1 := by
    have H := mul_le_mul_of_nonneg_right (hAv.trans hab) hW.le
    exact hv.2.trans (H.trans hnsmall)
  have hvi : v ∈ Icc (0:ℝ) 1 := ⟨(mul_pos hA hW).le.trans hv.1,hv1⟩
  have hAWunit : A*W n ≤ 1:=hv.1.trans hvi.2
  have hrstart:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hW (hxs n)
    (show A ≤ A from le_rfl) hAWunit hnhigh (show A*W n∈Icc (A*W n) (A*W n) from ⟨le_rfl,le_rfl⟩)).1
  have hfi : IntervalIntegrable (fun u=>|orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u|) volume 0 v := by
    have HS : IntervalIntegrable (orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf) volume 0 v := (show MonotoneOn (orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf) (uIcc (0:ℝ) v) by
      rw [uIcc_of_le hvi.1];exact hmono.mono (Icc_subset_Icc le_rfl hvi.2)).intervalIntegrable
    exact (HS.sub (((M n).sweepRadius_continuous).intervalIntegrable 0 v)).abs

  have Hint : (∫u in 0..v,|orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u|)<
      (c*W n/4)*(v-A*W n):=by
    have H:=(div_lt_iff₀ (pow_pos hW 2)).mp hntiny
    convert H using 1; dsimp only [v]; ring
  have Hmean:=monotone_scalar_cut_of_original_integral _ _ hmono
    (((M n).sweepRadius_monotone).monotoneOn _)

    hvi ⟨(mul_pos hA hW).le,hv.1⟩
    (show (3*c/4)*W n+c*W n/4 ≤ (M n).sweepRadius (A*W n) by dsimp only [c];nlinarith only [hrstart]) hfi Hint
  have hmean : (3*(A/cu)/4)*W n ≤ orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf v:=Hmean.le
  have hall : ∀u∈Icc (a*W n) (b*W n),
      (3*(A/cu)/4)*W n  ≤  orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf u ∧
      orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf u  ≤  Cs*W n ∧
      (a/cu)*W n  ≤  (M n).sweepRadius u ∧ (M n).sweepRadius u  ≤  (b/cl)*W n ∧
      (M n).xs  ≤  (M n).sweepRadius u ∧ (M n).z  ≤  (M n).sweepRadius u/2 := by
    intro u hu
    have hu0 : 0 < u := (mul_pos ha hW).trans_le hu.1
    have hui : u ∈ Icc (0:ℝ) 1 := ⟨hu0.le,hu.2.trans hnsmall⟩
    have hvu : v  ≤  u := hv.2.trans
      ((mul_le_mul_of_nonneg_right hAv hW.le).trans hu.1)
    have hupper := hnraw (M n) hngate.2 hngate.1 u ⟨hu0,hui.2⟩
    have hsize : (M n).xs+u  ≤  (1+b)*W n := by nlinarith only [hxs n,hu.2]
    have hup : orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf u  ≤  Cs*W n :=
      hupper.trans (by simpa only [Cs,mul_assoc] using mul_le_mul_of_nonneg_left hsize hB.le)
    have hr := (M n).actual_closed_regular_mass_band_radius_bounds
      hcl hcu hAz hW (hxs n) hav hnsmall
      (hnhigh.trans (mul_le_mul_of_nonneg_right hav hW.le)) hu
    have hlo : 2*W n  ≤  (a/cu)*W n := by
      apply mul_le_mul_of_nonneg_right _ hW.le
      apply (le_div_iff₀ hcu).mpr
      dsimp only [a,calibratedBandStart,A]
      linarith [star_mass_band_constant_pos hcu hAz]
    have hzlo : 2*Az*W n  ≤  (a/cu)*W n := by
      have HC : 2*Az  ≤  a/cu := by
        apply (le_div_iff₀ hcu).mpr
        dsimp only [a,calibratedBandStart,A,starMassBandConstant]
        nlinarith only [hcu]
      exact mul_le_mul_of_nonneg_right HC hW.le
    have hzW : (M n).z  ≤  Az*W n :=
      (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)
    exact ⟨hmean.trans (hmono hvi hui hvu),hup,hr.1,hr.2,
      (hxs n).trans (by linarith only [hW,hlo,hr.1]),by linarith only [hzW,hzlo,hr.1]⟩
  have haend : a*W n  ≤  b*W n := mul_le_mul_of_nonneg_right hab hW.le
  have hstart0 : 0  ≤  orderedPathS (N n+1) (M n).sweepBf (M n).sweepHf (a*W n) :=
    (M n).mass_mean_nonneg ⟨(mul_pos ha hW).le,haend.trans hnsmall⟩
  refine ⟨hmono,hnsmall,hall,?_⟩
  have Hend := (hall (b*W n) ⟨haend,le_rfl⟩).2.1
  linarith only [Hend,hstart0]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
