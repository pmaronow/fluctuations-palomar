module

public import ComparisonActualHighOnlyScalarGoodPointOffFloor
public import ComparisonActualHighOnlyLargerWorkingScale
public import ComparisonActualHighOnlyFlatWeightedAlong
public import ComparisonSignedCavityActualRegularCalibratedBand

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum

theorem eventually_actual_HIGH_mean_point
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2) atTop atTop) :
    ∀ᶠn in atTop,∃p : (M n).Potential,∃u∈Ioo
      (starMassBandConstant cu Az*(M n).xs) (2*starMassBandConstant cu Az*(M n).xs),
      p.H ((M n).R u)≤0 ∧
      (3*(starMassBandConstant cu Az/cu)/4)*(M n).xs≤orderedPathS (dim n+1) (M n).bf (M n).hf u := by
  let A:=starMassBandConstant cu Az
  let c:=A/cu
  let K:=(Az+1/cl)*(1+2*A)
  have hA : 0 < A:=star_mass_band_constant_pos hcu hAz
  have hc : 0 < c:=div_pos hA hcu
  have hK : 0 < K:=by dsimp only [K];positivity
  have hroom : 0 < 3*m+delta:=by linarith only [hm,hdelta]
  have Htravel:=(actual_cap_travel_ratio_tendsto_zero_along hC0 hroom dim hdim M
    (fun n=>(M n).xs) (fun _=>le_rfl)).eventually (eventually_le_nhds (show (0:ℝ)<c/4 by positivity))
  have Hfloor:=G.eventually_floor_and_omission_small hC0 hroom hdim
    (fun n=>(M n).xs) (fun _=>le_rfl) (epsilon:=A/2) (by positivity)
  have Hflat:=comparison_strength_eventually_flat_of_divergence
    (fun n=>(M n).context.d) (fun n=>(M n).lam) (fun n=>(M n).xs)
    (Eventually.of_forall fun n=>⟨(M n).context.hd,(M n).hlam,(M n).hxs,(M n).hld⟩) hlarge hK
  have Hunit:=(G.xs_zero.const_mul (2*A)).eventually (eventually_le_nhds (by simp : 2*A*(0:ℝ)<1))
  filter_upwards [Htravel,Hfloor,Hflat,Hunit,G.positive_bands_high A hA,G.eventually_geometric_gates]
    with n hntravel hnfloor hnflat hnunit hnhigh hngate
  obtain ⟨p⟩:=(M n).exists_potential_high_only hngate.2
  have hx:0 < (M n).xs:=(M n).hxs
  have HF:∀r∈Icc (0:ℝ) (K*(M n).xs),comparisonLogSlope
      (laplaceComparisonStrength (M n).context.d (M n).lam) r=0:=by
    intro r hr
    have H:=(hnflat (r/(M n).xs) ⟨div_nonneg hr.1 hx.le,(div_le_iff₀ hx).mpr hr.2⟩).2.1
    simpa only [mul_div_cancel₀ r hx.ne'] using H
  have HP:∀ᵐu,u∈Ioo (A*(M n).xs) ((2*A)*(M n).xs)→
      p.H ((M n).R u)≤0→|orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|≤(M n).cavityCapTravel:=by
    filter_upwards [p.flat_nonpositive_abs_mismatch_ae_high_mass HF] with u hu huband hnonpos
    have hui:u∈Icc (M n).data.s 1:=⟨hnhigh.trans huband.1.le,huband.2.le.trans hnunit⟩
    have HR:=(M n).inverse_radius_le_source_mass hcl hAz ⟨(M n).data.hs.1.trans hui.1,hui.2⟩
    have HH:=mul_le_mul_of_nonneg_left
      (show (M n).xs+u≤(1+2*A)*(M n).xs by linarith only [huband.2])
      (show 0≤Az+1/cl by positivity)
    have hR:(M n).R u≤K*(M n).xs:=HR.trans (by convert HH using 1;dsimp only [K];ring)
    exact hu hui hR hnonpos
  have Hsmall:(∫u in 0..(2*A)*(M n).xs,|(0:ℝ)|)<(M n).xs^3*
      ((2*A-A)*(M n).xs-((M n).data.s+(M n).context.N^(-delta)*(M n).context.U)):=by
    simp only [abs_zero,intervalIntegral.integral_zero]
    apply mul_pos (pow_pos hx 3)
    nlinarith only [hnfloor,hA,hx]
  obtain ⟨u,hu,hnonpos,_,hpoint⟩:=p.exists_scalar_good_point_off_floor (fun _=>(0:ℝ))
    hA.le (show A < 2*A by linarith only [hA]) hnunit intervalIntegrable_const Hsmall
    (fun u=>p.H ((M n).R u)≤0→|orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|≤(M n).cavityCapTravel) HP
  have hr:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hx le_rfl
    (show starMassBandConstant cu Az≤A from le_rfl) hnunit hnhigh ⟨hu.1.le,hu.2.le⟩).1
  have Htravel:(M n).cavityCapTravel≤(c/4)*(M n).xs:=(div_le_iff₀ hx).mp hntravel
  have Hmis:=hpoint hnonpos
  refine ⟨p,u,hu,hnonpos,?_⟩
  dsimp only [c] at Htravel
  nlinarith only [hr,Htravel,(abs_le.mp Hmis).1]

theorem eventually_actual_HIGH_calibrated_mass_band
    {m delta cl cu Az C0 Ct D Bclock L T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hL : 0 < L) (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2) atTop atTop)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hcanonical : ∀n,W n=(M n).xs)
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1) :
    ∃Cs : ℝ,0 < Cs ∧ ∀ᶠn : ℕ in atTop,
      let a := calibratedBandStart cu Az
      let b := a+4*L
      let S := orderedPathS (N n+1) (M n).bf (M n).hf
      MonotoneOn S (Icc (0:ℝ) 1) ∧ b*W n ≤ 1 ∧
      (∀u∈Icc (a*W n) (b*W n),
        (3*(starMassBandConstant cu Az/cu)/4)*W n ≤ S u ∧
        S u ≤ Cs*W n ∧
        (a/cu)*W n ≤ (M n).R u ∧ (M n).R u ≤ (b/cl)*W n ∧
        (M n).xs ≤ (M n).R u ∧ (M n).z ≤ (M n).R u/2) ∧
      S (b*W n)-S (a*W n) ≤ Cs*W n := by
  let A := starMassBandConstant cu Az
  let a := calibratedBandStart cu Az
  let b := a+4*L
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hab : a ≤ b := by dsimp only [b];linarith
  have hbpos : 0 < b := ha.trans_le hab
  obtain ⟨B,hB,Hraw⟩ := eventually_actual_high_only_mass_mean_upper
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs := B*(1+b)
  have hCs : 0 < Cs := by dsimp only [Cs];positivity
  have Hstar := eventually_actual_HIGH_mean_point hm hdelta hcl hcu hAz hC0 N hN M G hlarge
  have Hsmall := (hWlim.const_mul b).eventually
    (eventually_le_nhds (show b*(0:ℝ) < 1 by simp))
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [Hstar,hN.eventually Hraw,G.eventually_geometric_gates,G.positive_bands_high A hA,Hsmall] with n hnstar hnraw hngate hnhigh hnsmall
  dsimp only
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hmono := (M n).mass_mean_monotone
  obtain ⟨p,v,hv,_,hmean⟩ := hnstar
  simp only [←hcanonical n] at hv hmean hnhigh
  have hAv : 2*A ≤ a := by dsimp only [a,calibratedBandStart,A];linarith
  have hav : A ≤ a := by linarith
  have hv1 : v ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right (hAv.trans hab) hW.le
    exact hv.2.le.trans (H.trans hnsmall)
  have hvi : v ∈ Icc (0:ℝ) 1 := ⟨((mul_pos hA hW).trans hv.1).le,hv1⟩
  have hall : ∀u∈Icc (a*W n) (b*W n),
      (3*(A/cu)/4)*W n ≤ orderedPathS (N n+1) (M n).bf (M n).hf u ∧
      orderedPathS (N n+1) (M n).bf (M n).hf u ≤ Cs*W n ∧
      (a/cu)*W n ≤ (M n).R u ∧ (M n).R u ≤ (b/cl)*W n ∧
      (M n).xs ≤ (M n).R u ∧ (M n).z ≤ (M n).R u/2 := by
    intro u hu
    have hu0 : 0 < u := (mul_pos ha hW).trans_le hu.1
    have hui : u ∈ Icc (0:ℝ) 1 := ⟨hu0.le,hu.2.trans hnsmall⟩
    have hvu : v ≤ u := hv.2.le.trans
      ((mul_le_mul_of_nonneg_right hAv hW.le).trans hu.1)
    have hupper := hnraw (M n) hngate.2 hngate.1 u ⟨hu0,hui.2⟩
    have hsize : (M n).xs+u ≤ (1+b)*W n := by nlinarith only [hxs n,hu.2]
    have hup : orderedPathS (N n+1) (M n).bf (M n).hf u ≤ Cs*W n :=
      hupper.trans (by simpa only [Cs,mul_assoc] using mul_le_mul_of_nonneg_left hsize hB.le)
    have hr := (M n).actual_closed_regular_mass_band_radius_bounds
      hcl hcu hAz hW (hxs n) hav hnsmall
      (hnhigh.trans (mul_le_mul_of_nonneg_right hav hW.le)) hu
    have hlo : 2*W n ≤ (a/cu)*W n := by
      apply mul_le_mul_of_nonneg_right _ hW.le
      apply (le_div_iff₀ hcu).mpr
      dsimp only [a,calibratedBandStart,A]
      linarith [star_mass_band_constant_pos hcu hAz]
    have hzlo : 2*Az*W n ≤ (a/cu)*W n := by
      have HC : 2*Az ≤ a/cu := by
        apply (le_div_iff₀ hcu).mpr
        dsimp only [a,calibratedBandStart,A,starMassBandConstant]
        nlinarith only [hcu]
      exact mul_le_mul_of_nonneg_right HC hW.le
    have hzW : (M n).z ≤ Az*W n :=
      (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)
    exact ⟨hmean.trans (hmono hvi hui hvu),hup,hr.1,hr.2,
      (hxs n).trans (by linarith only [hW,hlo,hr.1]),by linarith only [hzW,hzlo,hr.1]⟩
  have haend : a*W n ≤ b*W n := mul_le_mul_of_nonneg_right hab hW.le
  have hstart0 : 0 ≤ orderedPathS (N n+1) (M n).bf (M n).hf (a*W n) :=
    (M n).mass_mean_nonneg ⟨(mul_pos ha hW).le,haend.trans hnsmall⟩
  refine ⟨hmono,hnsmall,hall,?_⟩
  have Hend := (hall (b*W n) ⟨haend,le_rfl⟩).2.1
  linarith only [Hend,hstart0]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
