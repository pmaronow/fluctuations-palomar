module

public import SKProof.Port.ComparisonActualOriginalQSharpSecondAlong
public import SKProof.Port.ComparisonActualOriginalQTargetHighTailPowers
public import ComparisonSignedCavitySharpOriginalLowRadiusAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
theorem eventually_actual_sharp_star_original_low_radius_saving_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Lwin Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0)
    (C : ℝ) (hC : 0 ≤ C)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow_original_q (M n) (W n) Temp Lwin Cs (w n)) :
    ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1)→(w n).star∈us→
      ∀ᶠk : ℕ in atTop,
        C*(nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf (finiteCutMasses us k)
          (retainedMassPrefixIndex (w n).star.val (finiteCutMasses us k))+1/(dim n+1:ℕ)) ≤
          ((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*((M n).xs^2/W n) := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  have hW n : 0 < W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos
  have Hsecond:=eventually_actual_sharp_star_second_moment_final_net_along_original_q hm hdelta dim hdim M W hW w hw
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have Hcoef:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=2*C) (d:=1) (q:=-eta/16) (r:=-eta/32)
      zero_lt_one (by linarith))
  filter_upwards [Hsecond,HW1,Hcoef,hdim.eventually (eventually_actual_minimum_high_tail_site_le_original_q Bclock hm hdelta hC0)]
    with n hn hW1 hncoef hnsite
  dsimp only [Function.comp_apply] at hncoef
  intro us hus hstar
  filter_upwards [hn us hus hstar] with k hk
  let as:=finiteCutMasses us k
  let N:=((dim n+1:ℕ):ℝ)
  let A:=(M n).xs^2/W n
  have hN : 0 < N:=by dsimp [N];positivity
  have hA : 0 < A:=div_pos (sq_pos_of_pos (M n).hxs) (hW n)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HS:=native_original_retained_star_low_second (dim n) (M n).sweepBf (M n).sweepHf
    (M n).sweep_bf_monotone (M n).sweep_hf_monotone as ho (w n).star
    (finiteCutMasses_nodes us k hstar)
  have Hmoment : nativeOriginalCutLowErrorSecond (dim n) (M n).sweepBf (M n).sweepHf as
      (retainedMassPrefixIndex (w n).star.val as) ≤ N^(-eta/8)*((M n).xs^4/(W n)^2) := by
    rw [HS]
    simpa only [ActualHighWallData.N,N,as,eta,neg_div] using hk
  have he : (N^(-eta/16)*A)^2=N^(-eta/8)*((M n).xs^4/(W n)^2) := by
    have hp : (N^(-eta/16))^2=N^(-eta/8) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
      congr 1
      norm_num
      ring
    rw [mul_pow,hp]
    dsimp only [A]
    ring
  have HR : nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as
      (retainedMassPrefixIndex (w n).star.val as) ≤ N^(-eta/16)*A := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [he]
    exact Hmoment
  have Hsite : 1/(dim n+1:ℕ) ≤ N^(-eta/16)*A := by
    simpa only [ActualHighWallData.N,N,A,eta,←hcanonical n,neg_div] using
      hnsite (M n) (by simpa only [←hcanonical n] using hW1)
  have Hsum:=mul_le_mul_of_nonneg_left (add_le_add HR Hsite) hC
  have Hfinal:=mul_le_mul_of_nonneg_right hncoef hA.le
  dsimp only [as] at Hsum
  convert Hsum.trans (by convert Hfinal using 1;ring) using 1
  simp only [A,eta,one_mul,neg_div]

end OAI.SKFluctuations.Cavity
