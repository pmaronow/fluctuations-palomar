module

public import ComparisonNativeStarOriginalBufferTransfer
public import ComparisonSignedCavityActualSlowWindowBufferCutsAlong
public import ComparisonNativeStarActualBufferedSequence
public import ComparisonNativeInheritedStarMinimumCommonBuffers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeStarBuffer NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 9000000
attribute [local instance] Classical.propDecidable

theorem eventually_actual_inherited_slow_window_native_buffers_along
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock T L Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hL : 0 < L)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    ∃Craw : ℝ,0 < Craw ∧ ∀ᶠn : ℕ in atTop,
      ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
      ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧
        ActualSlowWindowNativeBufferBudget p Craw (actualSlowWindowExponent m delta/16)
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
  have hAa : starMassBandConstant cu Az ≤ aBand := by
    unfold aBand calibratedBandStart
    have H := star_mass_band_constant_pos hcu hAz
    linarith
  obtain ⟨K,Cprof,Rmacro,Ddepth,hK,hCprof,hRmacro,hDdepth,_,hgeometry⟩ :=
    eventually_actual_slow_window_buffer_cuts_along hm hdelta hroom hcl hcu hAz hC0 hL dim hdim M W hxs hWlim
  let Fcap := max (1+2*cu) (1+1/Rmacro)
  obtain ⟨Craw,hCraw,hcommon⟩ := eventually_actual_minimum_inherited_common_retained_buffers p Bclock
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
  filter_upwards [hw,hgeometry,((tendsto_add_atTop_nat 1).comp hdim).eventually hcommon,Hsize,Heta,Hband]
    with n hnwindow hngeometry hncommon hnsize hneta hnband
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
  have hVp : (M n).R past.lo.val ≤ Cv*W n :=
    ((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hW (hxs n) hAa hnband hpastband).2
  have hVf : (M n).R future.lo.val ≤ Cv*W n :=
    ((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hW (hxs n) hAa hnband hfutureband).2
  let Bs : Fin 2 → ActualMinimumRetainedBufferCuts (M n) (2*c) K Cprof Ddepth Rmacro :=
    fun i=>if i.val=0 then past else future
  have hVs : ∀i,(M n).R (Bs i).lo.val ≤ Cv*W n := by
    intro i
    dsimp only [Bs]
    split_ifs
    · exact hVp
    · exact hVf
  have hstar1 : (w n).star.val ≤ 1 := by
    have H := hnodes (4*(w n).index+3) (by omega)
    exact hstar.2.le.trans (by linarith [H.2])
  obtain ⟨us,hus,hextraus,hret,hbuffers⟩ := hncommon (M n) 2 Bs (Cv*W n) hVs
    ((w n).star::extra) (by intro u hu;rcases List.mem_cons.mp hu with rfl|hu;exact hstar1;exact hextra u hu)
  have hrp := hret (0 : Fin 2)
  have hrf := hret (1 : Fin 2)
  change past.lo∈us ∧ past.hi∈us at hrp
  change future.lo∈us ∧ future.hi∈us at hrf
  have hrstar : (w n).star∈us := hextraus _ (by simp)
  have hretainextra : ∀u∈extra,u∈us := fun u hu=>hextraus u (List.mem_cons_of_mem _ hu)
  have h1star : past.hi.val ≤ (w n).star.val := by rw [hp1];linarith [hstar.1]
  have hstar3 : (w n).star.val ≤ future.lo.val := by rw [hp3];linarith [hstar.2]
  have h04 : past.lo.val ≤ future.hi.val :=
    past.ordered.le.trans (h1star.trans (hstar3.trans future.ordered.le))
  let S := orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let eta := ((dim n+1:ℕ):ℝ)^(-c/2)*W n
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hS0 : |orderedPathS (dim n+1) (M n).bf (M n).hf past.lo.val-S| ≤ eta :=
    hosc past.lo.val (by simpa only [hp0,hp4] using (show past.lo.val∈Icc past.lo.val future.hi.val from ⟨le_rfl,h04⟩))
  have hS4 : |orderedPathS (dim n+1) (M n).bf (M n).hf future.hi.val-S| ≤ eta :=
    hosc future.hi.val (by simpa only [hp0,hp4] using (show future.hi.val∈Icc past.lo.val future.hi.val from ⟨h04,le_rfl⟩))
  have had := comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have Hdata := eventually_retained_original_star_buffer_data (dim n) (M n).bf (M n).hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus
    past.lo past.hi (w n).star future.lo future.hi hrp.1 hrp.2 hrstar hrf.1 hrf.2
    past.ordered h1star hstar3 future.ordered heta.le heta hS0 hS4
  refine ⟨us,hus,hretainextra,past.lo,past.hi,future.lo,future.hi,hp0,hp1,hp3,hp4,
    hrp.1,hrp.2,hrf.1,hrf.2,hrstar,?_⟩
  filter_upwards [hbuffers,Hdata] with j hj hdata
  obtain ⟨B,hkm,hkp,hBerta⟩ := hdata
  have hpm := hj.2 (0 : Fin 2)
  have hpf := hj.2 (1 : Fin 2)
  change actualMinimumRetainedBufferNorm p (M n) (finiteCutMasses us j) past.lo past.hi ≤
    ((dim n+1:ℕ):ℝ)^(-(c/8))*(Cv*W n) at hpm
  change actualMinimumRetainedBufferNorm p (M n) (finiteCutMasses us j) future.lo future.hi ≤
    ((dim n+1:ℕ):ℝ)^(-(c/8))*(Cv*W n) at hpf
  have hscale : ((dim n+1:ℕ):ℝ)^(-(c/8))*(Cv*W n) ≤ ((dim n+1:ℕ):ℝ)^(-(c/16))*W n := by
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
