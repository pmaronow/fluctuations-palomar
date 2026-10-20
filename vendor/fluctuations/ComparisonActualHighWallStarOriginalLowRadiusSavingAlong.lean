module

public import ComparisonActualHighWallStarOriginalSecondAlong
public import ComparisonActualHighWallHighTailSite

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_star_original_low_radius_saving_along
    {m delta cl cu Az C0 Ct D Bclock Lwin Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0)
    (C : ℝ) (hC : 0 ≤ C)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow (M n) (M n).data.d Lwin Cs (w n)) :
    ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1)→(w n).star∈us→
      ∀ᶠk : ℕ in atTop,
        C*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us k)
          (retainedMassPrefixIndex (w n).star.val (finiteCutMasses us k))+1/(dim n+1:ℕ)) ≤
          ((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).data.d := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  have Hsecond:=eventually_actual_high_wall_star_original_second_moment_along hm hdelta dim hdim M w hw
  have Hcoef:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=2*C) (d:=1) (q:=-eta/16) (r:=-eta/32)
      zero_lt_one (by linarith))
  filter_upwards [Hsecond,Hcoef,hdim.eventually (eventually_actual_high_wall_high_tail_site_le
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hC0)]
    with n hn hncoef hnsite
  dsimp only [Function.comp_apply] at hncoef
  intro us hus hstar
  filter_upwards [hn us hus hstar] with k hk
  let as:=finiteCutMasses us k
  let N:=((dim n+1:ℕ):ℝ)
  let A:=(M n).data.d
  have hN : 0 < N:=by dsimp [N];positivity
  have hA : 0 < A:=(M n).data.hd
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HS:=native_original_retained_star_low_second (dim n) (M n).bf (M n).hf
    ((M n).data.bf_monotone (M n).alpha) ((M n).data.hf_monotone (M n).alpha) as ho (w n).star
    (finiteCutMasses_nodes us k hstar)
  have Hmoment : nativeOriginalCutLowErrorSecond (dim n) (M n).bf (M n).hf as
      (retainedMassPrefixIndex (w n).star.val as) ≤ N^(-eta/8)*(M n).data.d^2 := by
    rw [HS]
    simpa only [ActualHighWallData.N,N,as,eta,neg_div] using hk
  have he : (N^(-eta/16)*A)^2=N^(-eta/8)*(M n).data.d^2 := by
    have hp : (N^(-eta/16))^2=N^(-eta/8) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
      congr 1
      norm_num
      ring
    rw [mul_pow,hp]
  have HR : nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as
      (retainedMassPrefixIndex (w n).star.val as) ≤ N^(-eta/16)*A := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [he]
    exact Hmoment
  have Hsite : 1/(dim n+1:ℕ) ≤ N^(-eta/16)*A := by
    simpa only [ActualHighWallData.N,N,A,eta,neg_div] using hnsite (M n) (hfixed n).le
  have Hsum:=mul_le_mul_of_nonneg_left (add_le_add HR Hsite) hC
  have Hfinal:=mul_le_mul_of_nonneg_right hncoef hA.le
  dsimp only [as] at Hsum
  have Hmajor : C*(N^(-eta/16)*A+N^(-eta/16)*A) ≤ N^(-eta/32)*A:=by
    convert Hfinal using 1
    all_goals dsimp only [N]
    all_goals ring
  simpa only [N,A,eta,one_mul,neg_div] using Hsum.trans Hmajor

end OAI.SKFluctuations.Cavity
