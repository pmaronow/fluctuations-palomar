module

public import ComparisonSignedCavityActualSquareStarRates
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

theorem actual_inherited_native_star_every_final_net_to_square
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock Temp Cf saving : ℝ}
    (hCf : 0 ≤ Cf) (hC0 : 0 < C0) (hs : 0 < saving)
    (hroom : saving < (5:ℝ)/6+m)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarMomentOnEveryFinalNet p saving M W w) :
    ActualOriginalSquareStarMomentOnEveryFinalNet p (saving/2) M W w := by
  let B:=4*Cf+2*Temp
  let C:=Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1)*(Real.exp (110*Temp)+1)
  have Hsite:=eventually_omitted_site_below_saved_scale (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hroom
  have HC:=eventually_rest_star_cost_absorbed (p+1) (by omega) C hs
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsite,HC,HW,eventually_gt_atTop (0:ℕ),hsource] with n hn hnsite hnC hnW hn0 hnsource
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U a t ha ht
  let as:=finiteCutMasses us j
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let S:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  let z:=((n+1:ℕ):ℝ)^(-saving)*W n
  have hz : 0≤z := mul_nonneg (Real.rpow_nonneg (by positivity) _) ((M n).hxs.le.trans (hxs n))
  have hMxs : (M n).xs≤1 := (hxs n).trans hnW
  have Hbudget:=native_small_source_clock_full_square_budget (M n) Temp Cf hCf hnsource hMxs as ho
  have Hbond:=(hnsource _ (partitionPoint_mem as ho as.length)).1
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>((M n).bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>((M n).hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  have Hrest:=native_original_square_centered_le_native_retained n (p+1) U
    (M n).bf (M n).hf as ho (w n).star.val S a t ha ht hbm hhm
  dsimp only at Hrest
  have Hcoeff : Real.exp (220*(finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length))*
      (2:ℝ)^(2*(p+1)-1)≤Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left Hbudget (by norm_num)
  have Hexp : Real.exp (110*b as.length)≤Real.exp (110*Temp) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left Hbond (by norm_num))
  have Hstar : nativeRetainedCenteredMoment n (p+1) (M n).bf (M n).hf as (w n).star.val S≤z^(2*(p+1)) := hj
  have Hsitepow : (1/(n+1:ℕ):ℝ)^(2*(p+1))≤z^(2*(p+1)) :=
    pow_le_pow_left₀ (by positivity) (hnsite (M n) (W n) (hxs n)) _
  have Hinside : Real.exp (110*b as.length)*nativeRetainedCenteredMoment n (p+1)
      (M n).bf (M n).hf as (w n).star.val S+(1/(n+1:ℕ):ℝ)^(2*(p+1))≤
        (Real.exp (110*Temp)+1)*z^(2*(p+1)) := by
    have HE:=mul_le_mul Hexp Hstar
      (nativeRetainedCenteredMoment_nonneg n (p+1) (M n).bf (M n).hf as ho (w n).star.val S)
      (Real.exp_pos _).le
    nlinarith only [HE,Hsitepow]
  have Hsum0 : 0≤Real.exp (110*b as.length)*nativeRetainedCenteredMoment n (p+1)
      (M n).bf (M n).hf as (w n).star.val S+(1/(n+1:ℕ):ℝ)^(2*(p+1)) := by
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le
      (nativeRetainedCenteredMoment_nonneg n (p+1) (M n).bf (M n).hf as ho (w n).star.val S)) (by positivity)
  have Hbound:=Hrest.trans (mul_le_mul Hcoeff Hinside Hsum0 (by positivity))
  have Hbound' : nativeOriginalSquareCenteredMoment n (p+1) U as b h
      (retainedMassPrefixIndex (w n).star.val as) S a t≤C*z^(2*(p+1)) := by
    simpa only [C,mul_assoc] using Hbound
  exact Hbound'.trans (hnC (W n) ((M n).hxs.le.trans (hxs n)))

end OAI.SKFluctuations.LaplaceWindowFormalization
