module

public import ComparisonSignedCavityActualInheritedSquareStarAlong
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong

@[expose] public section
set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum ActualThetaZeroOverlapMinimum

def ActualOriginalSquareStarMomentOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1) → (w n).star∈us →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>((M n).sweepBf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>((M n).sweepHf (partitionPoint 0 as k):ℝ)
        ∀(U : ℕ) (a t : ℝ),a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        nativeOriginalSquareCenteredMoment (dim n) (p+1) U as b h
          (retainedMassPrefixIndex (w n).star.val as)
          (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (w n).star.val) a t≤
            (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_inherited_native_star_every_final_net_to_square_along_original_q
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock Temp Cf saving : ℝ}
    (hCf : 0 ≤ Cf) (hC0 : 0 < C0) (hs : 0 < saving)
    (hroom : saving < (5:ℝ)/6+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hsource : ∀ᶠn in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarMomentOnEveryFinalNetAlong_original_q p saving M W w) :
    ActualOriginalSquareStarMomentOnEveryFinalNetAlong_original_q p (saving/2) M W w := by
  let B:=4*Cf+2*Temp
  let C:=Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1)*(Real.exp (110*Temp)+1)
  have Hsite:=eventually_omitted_site_below_saved_scale_original_q (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hroom
  have HC:=eventually_rest_star_cost_absorbed (p+1) (by omega) C hs
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,hdim.eventually Hsite,hdim.eventually HC,HW,hdim.eventually (eventually_gt_atTop (0:ℕ)),hsource] with n hn hnsite hnC hnW hn0 hnsource
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U a t ha ht
  let as:=finiteCutMasses us j
  let b:=fun k=>((M n).sweepBf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).sweepHf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let S:=orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (w n).star.val
  let z:=((dim n+1:ℕ):ℝ)^(-saving)*W n
  have hz : 0≤ z := mul_nonneg (Real.rpow_nonneg (by positivity) _) ((M n).hxs.le.trans (hxs n))
  have hMxs : (M n).xs≤1 := (hxs n).trans hnW
  have Hbudget:=native_small_source_clock_full_square_budget_original_q (M n) Temp Cf hCf hnsource hMxs as ho
  have Hbond:=(hnsource _ (partitionPoint_mem as ho as.length)).1
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>((M n).sweepBf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>(M n).sweep_bf_monotone hx hy hxy) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>((M n).sweepHf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>(M n).sweep_hf_monotone hx hy hxy) as ho
  have Hrest:=native_original_square_centered_le_native_retained (dim n) (p+1) U
    (M n).sweepBf (M n).sweepHf as ho (w n).star.val S a t ha ht hbm hhm
  dsimp only at Hrest
  have Hcoeff : Real.exp (220*(finitePhysicalMixedClock (dim n+1) as b h as.length+b as.length+h as.length))*
      (2:ℝ)^(2*(p+1)-1)≤ Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left Hbudget (by norm_num)
  have Hexp : Real.exp (110*b as.length)≤ Real.exp (110*Temp) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left Hbond (by norm_num))
  have Hstar : nativeRetainedCenteredMoment (dim n) (p+1) (M n).sweepBf (M n).sweepHf as (w n).star.val S≤ z^(2*(p+1)) := hj
  have Hsitepow : (1/(dim n+1:ℕ):ℝ)^(2*(p+1))≤ z^(2*(p+1)) :=
    pow_le_pow_left₀ (by positivity) (hnsite (M n) (W n) (hxs n)) _
  have Hinside : Real.exp (110*b as.length)*nativeRetainedCenteredMoment (dim n) (p+1)
      (M n).sweepBf (M n).sweepHf as (w n).star.val S+(1/(dim n+1:ℕ):ℝ)^(2*(p+1))≤
        (Real.exp (110*Temp)+1)*z^(2*(p+1)) := by
    have HE:=mul_le_mul Hexp Hstar
      (nativeRetainedCenteredMoment_nonneg (dim n) (p+1) (M n).sweepBf (M n).sweepHf as ho (w n).star.val S)
      (Real.exp_pos _).le
    nlinarith only [HE,Hsitepow]
  have Hsum0 : 0≤ Real.exp (110*b as.length)*nativeRetainedCenteredMoment (dim n) (p+1)
      (M n).sweepBf (M n).sweepHf as (w n).star.val S+(1/(dim n+1:ℕ):ℝ)^(2*(p+1)) := by
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le
      (nativeRetainedCenteredMoment_nonneg (dim n) (p+1) (M n).sweepBf (M n).sweepHf as ho (w n).star.val S)) (by positivity)
  have Hbound:=Hrest.trans (mul_le_mul Hcoeff Hinside Hsum0 (by positivity))
  have Hbound' : nativeOriginalSquareCenteredMoment (dim n) (p+1) U as b h
      (retainedMassPrefixIndex (w n).star.val as) S a t≤ C*z^(2*(p+1)) := by
    simpa only [C,mul_assoc] using Hbound
  exact Hbound'.trans (hnC (W n) ((M n).hxs.le.trans (hxs n)))

end OAI.SKFluctuations.LaplaceWindowFormalization
