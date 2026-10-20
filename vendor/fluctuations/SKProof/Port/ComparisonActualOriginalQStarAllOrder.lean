module

public import ComparisonNativeInheritedStarActualAllOrder
public import SKProof.Port.ComparisonActualOriginalQStarBuffersAlong
public import SKProof.Port.ComparisonActualOriginalQStarCanonicalGeometry
public import SKProof.Port.ComparisonActualOriginalQStarProjectionNumerics
public import SKProof.Port.ComparisonActualOriginalQStarFinalNet

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
theorem eventually_actual_inherited_native_star_order_at_slow_window_along_original_q
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock T L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hL : 0 < L) {Ccal : ℝ} (hCcal : 1  ≤  Ccal)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ)
    (hcanonical : ∀n,W n=max (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)))
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2  ≤  Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow_original_q (M n) (W n) T L Cs (w n))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs) :
    ∃Craw : ℝ,0 < Craw ∧ ActualNativeStarOrderSavingAlong_original_q p Craw
      (actualSlowWindowExponent m delta/64) M W w := by
  let c := actualSlowWindowExponent m delta
  have hc : 0 < c := actualSlowWindowExponent_pos hm hdelta hroom
  have Hc := (actualSlowWindowExponent_bounds hm hdelta).2.2
  have hprojection : 2*(c/8) < 3*m-delta-3*c := by linarith
  have hxs n : (M n).xs  ≤  W n := by rw [hcanonical];exact le_max_left _ _
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  obtain ⟨Craw,hCraw,Hbuffer⟩ := eventually_actual_inherited_slow_window_native_buffers_along_original_q p
    hm hdelta hroom hcl hcu hAz hC0 hCt hL dim hdim M W hxs hWlim w hw Hcutoff
  obtain ⟨Kv,Cprof,Lcount,H0,hKv,hCprof,hLcount,hH0,Hgeometry⟩ :=
    eventually_actual_inherited_canonical_slow_window_projection_geometry_along_original_q hm hdelta hroom hcl hcu hAz hC0 hL
      hCcal dim hdim M W hcanonical hWlim Hcutoff hcompare
  have Hkv := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=Kv) (d:=1) (q:=-(c/8)) (r:=-(c/16))
      zero_lt_one (by linarith))
  have Hproject := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_actual_minimum_original_projection_moment_original_q p Bclock
      (cl:=cl) (cu:=cu) (Az:=Az) (Ddepth:=D)
      (c1:=3*c) (saving:=c/8) hm hC0 hCt hCprof.le hLcount.le
      (by positivity : 0  ≤  2*Craw) hH0.le hprojection)
  have Hconstant := hdim.eventually (eventually_star_pair_constant_absorbed p (actualBufferedStarPairConstant p Cs) hc)
  refine ⟨Craw,hCraw,?_⟩
  filter_upwards [Hbuffer,Hgeometry,Hproject,Hkv,Hconstant,hw] with n hnBuffer hnGeom hnProj hnKv hnConst hnWindow
  intro extra hextra
  have hWn : 0 < W n := hW n
  have hN1 : (1:ℝ)  ≤  ((dim n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos (dim n)
  obtain ⟨us,hus,hretain,hbudget⟩ := hnBuffer extra hextra
  obtain ⟨p0,p1,p3,p4,hp0,hp1,hp3,hp4,hr0,hr1,hr3,hr4,hrstar,Hdata⟩ := hbudget
  obtain ⟨_,_,hxv,hv1,HG⟩ := hnGeom
  have Hgeom := HG T Cs (w n) hnWindow p3 hp3 us hus hrstar hr3
  obtain ⟨potential,_,_,_,_,_,_,_,_,_,hSlo,hShi,_⟩ := hnWindow
  have hbf := (M n).sweep_bf_monotone
  have hhf := (M n).sweep_hf_monotone
  have hSnonneg : 0  ≤  orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (w n).star.val := by
    have hcstar : 0 < starMassBandConstant cu Az/cu := div_pos (star_mass_band_constant_pos hcu hAz) hcu
    exact (mul_pos (by positivity : 0 < 3*(starMassBandConstant cu Az/cu)/4) (hW n)).le.trans hSlo
  have hSabs : |orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (w n).star.val|  ≤  Cs*W n := by
    rw [abs_of_nonneg hSnonneg]
    exact hShi
  have hScaled : ((dim n+1:ℕ):ℝ)^(-(c/8))*(Kv*W n)  ≤  ((dim n+1:ℕ):ℝ)^(-(c/16))*W n := by
    have H := mul_le_mul_of_nonneg_right hnKv (hW n).le
    simpa only [Function.comp_apply,one_mul,mul_assoc,mul_left_comm,mul_comm] using H
  refine ⟨us,hus,hretain,hrstar,?_⟩
  filter_upwards [Hdata,Hgeom] with j hj hjGeom
  let as := finiteCutMasses us j
  let ho := finiteCutMasses_ordered us hus j
  let q := completedPathClock (dim n+1) (M n).sweepBf (M n).sweepHf
  let steps := sampleClockSteps q 0 as
  let fork := (physicalRetainedIndex steps (w n).star.val).val
  let t := (physicalRetainedIndex steps p3.val).val
  let S := orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (w n).star.val
  let epsilon := ((dim n+1:ℕ):ℝ)^(-(c/16))
  obtain ⟨B,_,_,hCm,hCp,hEta,hRaw⟩ := hj
  have hProj := hnProj (M n) as ho fork t (H0/(Kv*W n)) (Kv*W n)
    ((M n).data.N^(-(3*c))) (by positivity) hxv hv1 le_rfl hjGeom hRaw
  have hProjW : physicalOverlapProjectionErrorMoment (dim n+1) (p+1) steps
      (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id fork t  ≤
        (epsilon*W n)^(2*(p+1)) := by
    exact hProj.trans (pow_le_pow_left₀ (by positivity) hScaled _)
  have heps : 0 < epsilon := by dsimp only [epsilon];positivity
  have heps1 : epsilon  ≤  1 := Real.rpow_le_one_of_one_le_of_nonpos
    hN1 (by linarith)
  have Hstar := physical_star_from_buffer_data_polynomial (dim n+1) (p+1) (by omega)
    steps (sampleClockSteps_ordered q as ho) (q 0) fork t S B heps heps1 (hW n).le hCs.le
    hSabs hCm hCp hEta hProjW
  have Hnative := nativeRetainedCenteredMoment_eq_physicalStar (dim n) (p+1) (M n).sweepBf (M n).sweepHf
    hbf hhf as ho (w n).star.val S
  refine ⟨hRaw,?_⟩
  rw [Hnative]
  exact Hstar.trans (hnConst (W n) (hW n).le)

end OAI.SKFluctuations.LaplaceWindowFormalization
