module

public import ComparisonNativeInheritedStarActualBufferedSequence
public import ComparisonActualHighOnlyCommonBuffers
public import ComparisonActualHighOnlyStarScalarGeometry

@[expose] public section
set_option linter.unusedVariables false

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeStarBuffer ActualHighOnlyOverlapMinimum NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 9000000
attribute [local instance] Classical.propDecidable

def ActualSlowWindowNativeBufferBudget_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (p : ℕ) (Craw saving : ℝ)
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℝ) (w : ActualSlowWindowChoice) (us : List PositiveMass) : Prop :=
  let start := calibratedBandStart cu Az*W
  ∃p0 p1 p3 p4 : PositiveMass,
    p0.val=massNode start w.quarter (4*w.index) ∧
    p1.val=massNode start w.quarter (4*w.index+1) ∧
    p3.val=massNode start w.quarter (4*w.index+3) ∧
    p4.val=massNode start w.quarter (4*(w.index+1)) ∧
    p0∈us ∧ p1∈us ∧ p3∈us ∧ p4∈us ∧ w.star∈us ∧
    ∀ᶠj : ℕ in atTop,
      let as := finiteCutMasses us j
      let q := completedPathClock (n+1) M.bf M.hf
      let steps := sampleClockSteps q 0 as
      let fork := (physicalRetainedIndex steps w.star.val).val
      let t := (physicalRetainedIndex steps p3.val).val
      let S := orderedPathS (n+1) M.bf M.hf w.star.val
      ∃B : PhysicalStarBufferData (n+1) steps (q 0) fork t S,
        B.km=physicalWindowWeight steps 0 (actualMinimumRetainedBufferRows_high_only M as p0 p1) ∧
        B.kp=physicalWindowWeight steps 0 (actualMinimumRetainedBufferRows_high_only M as p3 p4) ∧
        physicalBufferCenteredNorm (n+1) steps (q 0) B.km (2*(p+1):ℕ)  ≤ 
          ((n+1:ℕ):ℝ)^(-saving)*W ∧
        physicalBufferCenteredNorm (n+1) steps (q 0) B.kp (2*(p+1):ℕ)  ≤ 
          ((n+1:ℕ):ℝ)^(-saving)*W ∧
        B.eta  ≤  ((n+1:ℕ):ℝ)^(-saving)*W ∧
        (physicalRawRatio (n+1) (p+1) steps 0 M.xs
          (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2  ≤  2*Craw

theorem eventually_actual_inherited_slow_window_native_buffers_along_high_only
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock T L Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct) (hL : 0 < L)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs  ≤  W n) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs) :
    ∃Craw : ℝ,0 < Craw ∧ ∀ᶠn : ℕ in atTop,
      ∀extra : List PositiveMass,(∀u∈extra,u.val  ≤  1) →
      ∃us : List PositiveMass,(∀u∈us,u.val  ≤  1) ∧ (∀u∈extra,u∈us) ∧
        ActualSlowWindowNativeBufferBudget_high_only p Craw (actualSlowWindowExponent m delta/16)
          (M n) (W n) (w n) us := by
  let c := actualSlowWindowExponent m delta
  let aBand := calibratedBandStart cu Az
  let bBand := aBand+4*L
  let Cv := bBand/cl
  have hc : 0 < c := actualSlowWindowExponent_pos hm hdelta hroom
  have hExp := actual_slow_window_buffer_exponent hm hdelta hroom
  have ha : 0 < aBand := calibrated_band_start_pos hcu hAz
  have hb : 0 < bBand := by dsimp only [bBand];linarith
  have hCv : 0 < Cv := div_pos hb hcl
  have hAa : starMassBandConstant cu Az  ≤  aBand := by
    unfold aBand calibratedBandStart
    have H := star_mass_band_constant_pos hcu hAz
    linarith
  obtain ⟨K,Cprof,Rmacro,Ddepth,hK,hCprof,hRmacro,hDdepth,_,hgeometry⟩ :=
    eventually_actual_slow_window_buffer_cuts_along_high_only hm hdelta hroom hcl hcu hAz hC0 hL dim hdim M W hxs hWlim Hcutoff
  let Fcap := max (1+2*cu) (1+1/Rmacro)
  obtain ⟨Craw,hCraw,hcommon⟩ := eventually_actual_minimum_inherited_common_retained_buffers_high_only p Bclock
    (Fcap:=Fcap) hm hdelta hC0 hCt hroom hExp.2.1 hK hCprof.le hcl hcu hAz hDdepth.le hRmacro
    (le_max_left _ _) (le_max_right _ _)
  have Hsize := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=Cv) (d:=1) (q:=-(c/8)) (r:=-(c/16))
      zero_lt_one (by linarith))
  have Heta := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:= -c/2) (r:=-(c/16))
      zero_lt_one (by linarith))
  have Hband := (hWlim.const_mul bBand).eventually
    (eventually_le_nhds (by simp : bBand*(0:ℝ) < 1))
  refine ⟨Craw,hCraw,?_⟩
  filter_upwards [Hcutoff,hw,hgeometry,((tendsto_add_atTop_nat 1).comp hdim).eventually hcommon,Hsize,Heta,Hband]
    with n hnCutoff hnwindow hngeometry hncommon hnsize hneta hnband
  intro extra hextra
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  obtain ⟨past,future,hp0,hp1,hp3,hp4,_,_⟩ := hngeometry T Cs (w n) hnwindow
  obtain ⟨pot,hi,hblocks,hquarter,hqlower,htotal,hnodes,hstar,hH,hthermal,hSlo,hShi,
    hRlo,hRhi,hxstar,hzstar,hKstar,hcomp,hosc⟩ := hnwindow
  have hpastband : past.lo.val∈Icc (aBand*W n) (bBand*W n) := by
    rw [hp0]
    exact hnodes _ (by omega)
  have hfutureband : future.lo.val∈Icc (aBand*W n) (bBand*W n) := by
    rw [hp3]
    exact hnodes _ (by omega)
  have haBand1 : 1 ≤ aBand := by
    dsimp only [aBand,calibratedBandStart,starMassBandConstant]
    nlinarith only [hcu,hAz,mul_nonneg hcu.le (by linarith : 0 ≤ Az+1)]
  have hhighStart : (M n).data.s ≤ aBand*W n := hnCutoff.2.trans ((hxs n).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right haBand1 hW.le))
  have hVp : (M n).R past.lo.val  ≤  Cv*W n :=
    ((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hW (hxs n) hAa hnband hhighStart hpastband).2
  have hVf : (M n).R future.lo.val  ≤  Cv*W n :=
    ((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hW (hxs n) hAa hnband hhighStart hfutureband).2
  let Bs : Fin 2 → ActualMinimumRetainedBufferCuts_high_only (M n) (2*c) K Cprof Ddepth Rmacro :=
    fun i=>if i.val=0 then past else future
  have hVs : ∀i,(M n).R (Bs i).lo.val  ≤  Cv*W n := by
    intro i
    dsimp only [Bs]
    split_ifs
    · exact hVp
    · exact hVf
  have hstar1 : (w n).star.val  ≤  1 := by
    have H := hnodes (4*(w n).index+3) (by omega)
    exact hstar.2.le.trans (by linarith [H.2])
  obtain ⟨us,hus,hextraus,hret,hbuffers⟩ := hncommon (M n) hnCutoff.1 hnCutoff.2 2 Bs (Cv*W n) hVs
    ((w n).star::extra) (by intro u hu;rcases List.mem_cons.mp hu with rfl|hu;exact hstar1;exact hextra u hu)
  have hrp := hret (0 : Fin 2)
  have hrf := hret (1 : Fin 2)
  change past.lo∈us ∧ past.hi∈us at hrp
  change future.lo∈us ∧ future.hi∈us at hrf
  have hrstar : (w n).star∈us := hextraus _ (by simp)
  have hretainextra : ∀u∈extra,u∈us := fun u hu=>hextraus u (List.mem_cons_of_mem _ hu)
  have h1star : past.hi.val  ≤  (w n).star.val := by rw [hp1];linarith [hstar.1]
  have hstar3 : (w n).star.val  ≤  future.lo.val := by rw [hp3];linarith [hstar.2]
  have h04 : past.lo.val  ≤  future.hi.val :=
    past.ordered.le.trans (h1star.trans (hstar3.trans future.ordered.le))
  let S := orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let eta := ((dim n+1:ℕ):ℝ)^(-c/2)*W n
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hS0 : |orderedPathS (dim n+1) (M n).bf (M n).hf past.lo.val-S|  ≤  eta :=
    hosc past.lo.val (by simpa only [hp0,hp4] using (show past.lo.val∈Icc past.lo.val future.hi.val from ⟨le_rfl,h04⟩))
  have hS4 : |orderedPathS (dim n+1) (M n).bf (M n).hf future.hi.val-S|  ≤  eta :=
    hosc future.hi.val (by simpa only [hp0,hp4] using (show future.hi.val∈Icc past.lo.val future.hi.val from ⟨h04,le_rfl⟩))
  have Hdata := eventually_retained_original_star_buffer_data (dim n) (M n).bf (M n).hf
    ((M n).bf_monotone) ((M n).hf_monotone) us hus
    past.lo past.hi (w n).star future.lo future.hi hrp.1 hrp.2 hrstar hrf.1 hrf.2
    past.ordered h1star hstar3 future.ordered heta.le heta hS0 hS4
  refine ⟨us,hus,hretainextra,past.lo,past.hi,future.lo,future.hi,hp0,hp1,hp3,hp4,
    hrp.1,hrp.2,hrf.1,hrf.2,hrstar,?_⟩
  filter_upwards [hbuffers,Hdata] with j hj hdata
  obtain ⟨B,hkm,hkp,hBerta⟩ := hdata
  have hpm := hj.2 (0 : Fin 2)
  have hpf := hj.2 (1 : Fin 2)
  change actualMinimumRetainedBufferNorm_high_only p (M n) (finiteCutMasses us j) past.lo past.hi  ≤ 
    ((dim n+1:ℕ):ℝ)^(-(c/8))*(Cv*W n) at hpm
  change actualMinimumRetainedBufferNorm_high_only p (M n) (finiteCutMasses us j) future.lo future.hi  ≤ 
    ((dim n+1:ℕ):ℝ)^(-(c/8))*(Cv*W n) at hpf
  have hscale : ((dim n+1:ℕ):ℝ)^(-(c/8))*(Cv*W n)  ≤  ((dim n+1:ℕ):ℝ)^(-(c/16))*W n := by
    have H := mul_le_mul_of_nonneg_right hnsize hW.le
    simpa only [Function.comp_apply,one_mul,mul_assoc,mul_left_comm,mul_comm] using H
  refine ⟨B,hkm,hkp,?_,?_,?_,hj.1⟩
  · rw [hkm]
    exact hpm.trans hscale
  · rw [hkp]
    exact hpf.trans hscale
  · rw [hBerta]
    have H := mul_le_mul_of_nonneg_right hneta hW.le
    simpa only [Function.comp_apply,eta,c,one_mul,mul_assoc,two_mul,add_mul] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
