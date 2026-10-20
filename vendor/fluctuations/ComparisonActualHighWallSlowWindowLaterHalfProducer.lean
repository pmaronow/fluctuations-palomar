module

public import ComparisonActualHighWallCalibratedBandProducer
public import ComparisonActualHighWallCentralStarProducer
public import ComparisonActualHighWallSlowWindowData
public import ComparisonNativeStarLateHalfSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum NativeStarBuffer
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
namespace ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_calibrated_slow_window_later_half
    {m delta cl cu Az C0 Ct D Bclock T0 L : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hT0 : 0< T0) (hL : 0< L)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsd : ∀n,(M n).xs≤ (M n).data.d) (hdW : ∀n,(M n).data.d≤ W n)
    (hWlim : Tendsto W atTop (𝓝 0)) (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (hT : ∀n,T0≤ (M n).data.T) :
    ∃Cs : ℝ,0< Cs ∧ ∀ᶠn in atTop,∃w : ActualSlowWindowChoice,
      IsActualHighWallCalibratedSlowWindow (M n) (W n) L Cs w ∧
      (calibratedBandStart cu Az+2*L)*W n ≤
        massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index) := by
  let A:=starMassBandConstant cu Az
  let a:=calibratedBandStart cu Az
  let b:=a+4*L
  let c:=A/cu
  let eta:=actualMassSavingExponent m delta
  let c1:=actualSlowWindowExponent m delta
  have hA : 0< A:=star_mass_band_constant_pos hcu hAz
  have ha : 0< a:=calibrated_band_start_pos hcu hAz
  have hc : 0< c:=div_pos hA hcu
  have hab : a< b:=by dsimp only [b];linarith
  have hAa : A≤ a:=by dsimp only [a,calibratedBandStart,A];linarith
  have hgap : cu*Az< a:=by
    have HA : cu*Az< A:=by dsimp only [A,starMassBandConstant];linarith
    exact HA.trans_le hAa
  have hc1 : 0< c1:=actualSlowWindowExponent_pos hm hdelta hroom
  have Hc1:=actualSlowWindowExponent_bounds hm hdelta
  have hxs n : (M n).xs≤ W n:=(hxsd n).trans (hdW n)
  obtain ⟨Cs,hCs,Hband⟩:=eventually_actual_high_wall_calibrated_mass_band
    hm hdelta hroom hcl hcu hAz hC0 hCt hT0 hL M W hxsd hdW hWlim hsRatio hT
  have Hblock:=(tendsto_add_atTop_nat 1).eventually
    (eventually_exists_native_continuum_star_later_half (A:=L) (B:=Cs) hL hc1)
  have Hcentral:=eventually_actual_high_wall_central_mass_selection hm hdelta hroom hcl hcu hAz
    hC0 hCt hAa hab hc1 Hc1.1 Hc1.2.1 M W hxsd hdW hWlim hsRatio
  have Hparameters:=eventually_actual_high_wall_star_band_parameters hm hdelta hcl hcu hAz
    hC0 hgap M W hxs hsRatio
  have Htravel:=(tendsto_add_atTop_nat 1).eventually
    (eventually_actual_high_wall_cap_travel_small (m:=m) (delta:=delta) (cl:=cl) (cu:=cu)
      (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=c/32) hC0 (by linarith) (by positivity))
  have Hsize:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=c^2/64) (q:=-(eta/4)) (r:=0)
      (by positivity) (by linarith [actualMassSavingExponent_pos hm hdelta]))
  have HWclock:=(hWlim.pow 2).eventually (eventually_le_nhds (show (0:ℝ)^2<T0/2 by simpa using half_pos hT0))
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [Hband,Hblock,Hcentral,Hparameters,Htravel,Hsize,HWclock]
    with n hnBand hnBlock hnCentral hnParameters hnTravel hnSize hnClock
  dsimp only at hnBand
  have hW : 0< W n:=(M n).data.hd.trans_le (hdW n)
  have hsmall : b*W n≤1:=hnBand.2.1
  have hend : a*W n+4*L*W n≤1:=by nlinarith only [hsmall]
  have hvariation : orderedPathS (n+1) (M n).bf (M n).hf (a*W n+4*L*W n)-
      orderedPathS (n+1) (M n).bf (M n).hf (a*W n)≤ Cs*W n:=by
    have HE : a*W n+4*L*W n=b*W n:=by dsimp only [b];ring
    rw [HE];exact hnBand.2.2.2
  obtain ⟨N,quarter,i,hi,hN,hq,hqlower,htotal,hlate,hosc⟩:=hnBlock
    (orderedPathS (n+1) (M n).bf (M n).hf) (a*W n) (W n) hnBand.1
    (mul_pos ha hW).le hW hend hvariation
  have hnodes : ∀j≤4*N,massNode (a*W n) quarter j∈Icc (a*W n) (b*W n):=by
    intro j hj
    exact calibrated_mass_node_mem hq.le hj htotal
  let s:=massNode (a*W n) quarter (4*i+1)+quarter/2
  let t:=massNode (a*W n) quarter (4*i+3)-quarter/2
  have hlength : t-s=quarter:=calibrated_mass_middle_length _ _ _
  have hst : s< t:=by linarith only [hlength,hq]
  have hs : a*W n≤ s:=by
    have HH:=(hnodes (4*i+1) (by omega)).1
    dsimp only [s];linarith only [HH,hq]
  have ht : t≤ b*W n:=by
    have HH:=(hnodes (4*i+3) (by omega)).2
    dsimp only [t];linarith only [HH,hq]
  have hwidth : (M n).data.N^(-c1)*W n≤ t-s:=by rw [hlength];exact hqlower
  obtain ⟨P⟩:=(M n).exists_potential
  obtain ⟨v,hv,hH,hthermal,hmismatch⟩:=hnCentral P s t hs ht hst hwidth
  have hvblock:=calibrated_mass_central_subset hq.le (calibrated_mass_middle_subset hq.le hv)
  have hvband:=calibrated_mass_block_subset hq.le hi htotal hvblock
  have hvpos : 0< v:=(mul_pos ha hW).trans_le hvband.1
  let u : PositiveMass:=⟨v,hvpos⟩
  have Hbandv:=hnBand.2.2.1 v hvband
  have htravel : (M n).cavityCapTravel≤ c*W n/32:=by
    exact (hnTravel (M n)).1.trans (by
      simpa only [div_mul_eq_mul_div] using
        (mul_le_mul_of_nonneg_left (hxs n) (show 0≤ c/32 by positivity)))
  have hsize : (M n).data.N^(-(eta/4))≤ c^2/64:=by
    simpa only [ActualHighWallData.N,Real.rpow_zero,mul_one,one_mul] using hnSize
  have htbound : (M n).data.N^(-(eta/4))*(W n)^2≤ (c*W n)^2/64:=by
    have HH:=mul_le_mul_of_nonneg_right hsize (sq_nonneg (W n));nlinarith only [HH]
  have htravel2:=pow_le_pow_left₀ (M n).cavityCapTravel_nonneg htravel 2
  have hsq : (orderedPathS (n+1) (M n).bf (M n).hf v-(M n).data.wallRadius (M n).alpha v)^2≤
      (c*W n/4)^2:=by nlinarith only [hmismatch,htravel2,htbound,sq_nonneg (c*W n)]
  have habs : |orderedPathS (n+1) (M n).bf (M n).hf v-(M n).data.wallRadius (M n).alpha v|≤ c*W n/4:=by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤ c*W n/4)).mp
    simpa only [sq_abs] using hsq
  have hvhigh : v∈Icc (M n).data.s 1:=⟨hnParameters.1.le.trans hvband.1,hvband.2.trans hsmall⟩
  have hclocksize : (W n)^2≤ (M n).data.T/2:=hnClock.trans
    (div_le_div_of_nonneg_right (hT n) (by norm_num))
  obtain ⟨hclock,hcomp⟩:=(M n).selected_high_mass_clock_calibration hvhigh hc hW (hdW n)
    hclocksize Hbandv.1 habs
  have hcomp' : |actualMixedClock (n+1) (M n).bf (M n).hf v-
      (M n).data.T*orderedPathS (n+1) (M n).bf (M n).hf v|≤ ((c+1)/4)*(W n)^3:=
    hcomp.trans (by nlinarith only [pow_pos hW 3])
  refine ⟨⟨N,quarter,i,u⟩,?_,?_⟩
  · refine ⟨P,hi,hN,hq,hqlower,htotal,hnodes,hv,hH,hthermal,
      Hbandv.1,Hbandv.2.1,Hbandv.2.2.1,Hbandv.2.2.2.1,Hbandv.2.2.2.2.1,Hbandv.2.2.2.2.2,
      hclock,hcomp',?_⟩
    intro w hw
    exact hosc w hw v hvblock
  · convert hlate using 1; dsimp only [a]; ring

theorem exists_actual_high_wall_calibrated_slow_window_later_half_sequence
    {m delta cl cu Az C0 Ct D Bclock T0 L : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hT0 : 0< T0) (hL : 0< L)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsd : ∀n,(M n).xs≤ (M n).data.d) (hdW : ∀n,(M n).data.d≤ W n)
    (hWlim : Tendsto W atTop (𝓝 0)) (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (hT : ∀n,T0≤ (M n).data.T) :
    ∃Cs : ℝ,0< Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      ∀ᶠn in atTop,IsActualHighWallCalibratedSlowWindow (M n) (W n) L Cs (w n) ∧
        (calibratedBandStart cu Az+2*L)*W n ≤
          massNode (calibratedBandStart cu Az*W n) (w n).quarter (4*(w n).index) := by
  obtain ⟨Cs,hCs,H⟩:=eventually_actual_high_wall_calibrated_slow_window_later_half hm hdelta hroom
    hcl hcu hAz hC0 hCt hT0 hL M W hxsd hdW hWlim hsRatio hT
  obtain ⟨w,hw⟩:=exists_point_sequence_of_eventually_exists
    (fun n w=>IsActualHighWallCalibratedSlowWindow (M n) (W n) L Cs w ∧
      (calibratedBandStart cu Az+2*L)*W n ≤
        massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index)) H
  exact ⟨Cs,hCs,w,hw⟩

theorem calibrated_slow_window_later_half_star_after_target
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {W L Cs Cmass : ℝ} (hW : 0 < W)
    (hCmass : Cmass ≤ calibratedBandStart cu Az+2*L)
    (w : ActualSlowWindowChoice)
    (hw : IsActualHighWallCalibratedSlowWindow M W L Cs w ∧
      (calibratedBandStart cu Az+2*L)*W ≤
        massNode (calibratedBandStart cu Az*W) w.quarter (4*w.index)) :
    Cmass*W < w.star.val := by
  rcases hw.1 with ⟨_,_,_,hq,_,_,_,hstar,_⟩
  have hfirst : Cmass*W ≤
      massNode (calibratedBandStart cu Az*W) w.quarter (4*w.index) :=
    (mul_le_mul_of_nonneg_right hCmass hW.le).trans hw.2
  have hmiddle : massNode (calibratedBandStart cu Az*W) w.quarter (4*w.index) <
      massNode (calibratedBandStart cu Az*W) w.quarter (4*w.index+1)+w.quarter/2 := by
    unfold massNode
    push_cast
    nlinarith [hq]
  exact hfirst.trans_lt (hmiddle.trans hstar.1)

theorem actual_high_wall_radius_band_mass_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hcu : 0 ≤ cu) (hAz : 0 ≤ Az)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {W Cband r : ℝ} (hW : 0 < W) (hBand : 0 ≤ Cband)
    (hxsW : M.xs ≤ W) (hr : r ≤ Cband*W) (hr1 : r ≤ 1) :
    M.alpha.val.val r ≤ cu*(Cband+Az)*W := by
  let t := max r M.z
  have ht : t ∈ Icc M.z 1 :=
    ⟨le_max_right _ _, max_le hr1 M.hz.2⟩
  have hzsmall : M.z ≤ Az*W :=
    M.hzxs.trans (mul_le_mul_of_nonneg_left hxsW hAz)
  have htbound : t ≤ (Cband+Az)*W := by
    apply max_le
    · nlinarith only [hr, mul_nonneg hAz hW.le]
    · nlinarith only [hzsmall, mul_nonneg hBand hW.le]
  have hup := (M.alpha.val.property.2 (le_max_left r M.z)).trans
    (M.regular t ht).2
  simpa only [mul_assoc] using
    hup.trans (mul_le_mul_of_nonneg_left htbound hcu)

theorem calibrated_slow_window_later_half_covers_radius_band
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hcu : 0 ≤ cu) (hAz : 0 ≤ Az)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {W L Cs Cband r : ℝ} (hW : 0 < W) (hBand : 0 ≤ Cband)
    (hxsW : M.xs ≤ W) (hr : r ≤ Cband*W) (hr1 : r ≤ 1)
    (hTarget : cu*(Cband+Az) ≤ calibratedBandStart cu Az+2*L)
    (w : ActualSlowWindowChoice)
    (hw : IsActualHighWallCalibratedSlowWindow M W L Cs w ∧
      (calibratedBandStart cu Az+2*L)*W ≤
        massNode (calibratedBandStart cu Az*W) w.quarter (4*w.index)) :
    M.alpha.val.val r < w.star.val := by
  have hmass := actual_high_wall_radius_band_mass_le hcu hAz M hW hBand hxsW hr hr1
  have hstar : (cu*(Cband+Az))*W < w.star.val :=
    calibrated_slow_window_later_half_star_after_target M hW hTarget w hw
  exact hmass.trans_lt hstar

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
