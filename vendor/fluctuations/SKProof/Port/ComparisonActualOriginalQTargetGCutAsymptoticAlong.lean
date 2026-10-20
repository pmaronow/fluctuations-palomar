module

public import ComparisonSignedCavityActualTargetGCutAsymptoticAlong
public import SKProof.Port.ComparisonActualOriginalQPullbackFourProducers
public import SKProof.Port.ComparisonActualOriginalQTargetGCutEnvelope
public import SKProof.Port.ComparisonActualOriginalQTargetGCutDensity
public import SKProof.Port.ComparisonActualOriginalQInheritedTargetScalarCutClock
public import SKProof.Port.ComparisonActualOriginalQTargetGCutResponse
public import SKProof.Port.ComparisonActualOriginalQTargetGCutResponseAlong
public import ComparisonNativeActualTargetGCutEnvelope
public import ComparisonSignedCavityActualTargetGCutResponseAlong
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_target_G_cut_comparison_vanishing_envelope_along_original_q
    (Bclock Temp Cf Ccut Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut) (houter : 0 < Couter)
    {m delta cl cu Az C0 Ct D Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).directTestWorkingScale) atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U V : ℕ,i<U → U ≤ V → V ≤ as.length →
          partitionPoint 0 as i ≤ Ccut*x n →
          partitionPoint 0 as V ≤ Couter*(M n).directTestWorkingScale →
          abs (nativeActualTargetLongitudinalResponse_original_q (M n) as i U-
            nativeActualTargetLongitudinalResponse_original_q (M n) as i V) ≤ eta n*(x n)^3 ∧
          abs (nativeActualTargetConditionalResponse_original_q (M n) as i U-
            nativeActualTargetConditionalResponse_original_q (M n) as i V) ≤ eta n*(x n)^3 := by
  obtain ⟨C,R,hC,hR,Hfinite⟩ := eventually_actual_minimum_inherited_target_G_cut_thermal_comparison_along_original_q
    dim hdim Bclock Temp Cf Ccut Couter hTemp hCf hCcut houter.le
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let eta := fun n=>(M n).targetGCutEnvelope (x n) Couter C R
  refine ⟨eta,fun n=>(M n).targetGCutEnvelope_nonneg (x n) houter.le hC.le hR.le,?_,?_⟩
  · exact ActualThetaZeroOverlapMinimum.targetGCutEnvelope_tendsto_zero_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M x hxs hxlim hclock Homit Hcutoff hsmall hWlim
      Couter C R houter
  · have HW1 := hWlim.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
    filter_upwards [Hfinite,hsource,HW1,Hcutoff] with n hn hs hnW hcut
    intro L us hus hret hmesh
    have hx := (M n).hxs.trans_le (hxs n)
    have hW := (M n).canonical_direct_test_band_pos
    have Hgrid := hn (M n) hcut.1 hcut.2 hs ((M n).canonical_direct_test_band_ge_scale.trans hnW) L us hus hret hmesh
    filter_upwards [Hgrid] with jGrid hj
    dsimp only at hj ⊢
    intro i U V hi hUV hV hmass hVmass
    have HH := hj i U V hi hUV hV (x n) (M n).directTestWorkingScale (hxs n) hmass
      (M n).canonical_direct_test_band_ge_scale hVmass
    let as:=finiteCutMasses us jGrid
    let f:=fun u=>Real.sqrt (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
      (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2)
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hqU:=partitionPoint_mem as ho U
    have hqV:=partitionPoint_mem as ho V
    have hqUV:=partitionPoint_mono as ho hUV
    have hf : IntervalIntegrable f volume 0 1:=native_intervalIntegrable_sqrt_of_intervalIntegrable
      ((M n).original_thermal_intervalIntegrable)
    have htop : 0 ≤ min (Couter*(M n).directTestWorkingScale) 1 :=
      le_min (mul_pos houter hW).le zero_le_one
    have Hprefix := hf.mono_set (by
      rw [uIcc_of_le htop,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl (min_le_right _ _))
    have HB : (∫u in partitionPoint 0 as U..partitionPoint 0 as V,f u) ≤
        (∫u in 0..min (Couter*(M n).directTestWorkingScale) 1,f u) :=
      intervalIntegral.integral_mono_interval hqU.1 hqUV (le_min hVmass hqV.2)
        (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) Hprefix
    have HT : (∫u in partitionPoint 0 as V..1,f u) ≤ (∫u in 0..1,f u) :=
      intervalIntegral.integral_mono_interval hqV.1 hqV.2 le_rfl
        (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) hf
    have HB' := add_le_add HB (le_refl (3/(dim n+1:ℕ):ℝ))
    have HT' := add_le_add HT (le_refl (3/(dim n+1:ℕ):ℝ))
    have Hbound := mul_le_mul_of_nonneg_left
      (add_le_add HB' (mul_le_mul_of_nonneg_left HT' (mul_pos hR hW).le)) (mul_pos hC hx).le
    have Heq : C*x n*((∫u in 0..min (Couter*(M n).directTestWorkingScale) 1,f u)+
        3/(dim n+1:ℕ)+R*(M n).directTestWorkingScale*((∫u in 0..1,f u)+3/(dim n+1:ℕ)))=
        eta n*(x n)^3 := by
      dsimp only [eta,ActualThetaZeroOverlapMinimum.targetGCutEnvelope,ActualHighWallData.N,f]
      field_simp
    rw [Heq] at Hbound
    exact ⟨HH.1.trans Hbound,HH.2.trans Hbound⟩

end OAI.SKFluctuations.Cavity
