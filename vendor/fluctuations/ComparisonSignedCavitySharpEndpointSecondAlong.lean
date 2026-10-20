module

public import ComparisonSignedCavitySharpEndpointSecond
public import ComparisonSignedCavitySharpOriginalLowRadiusAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 18000000

def ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1)→(w n).star∈us→
    ∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
      let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
      ∀U : ℕ,nativeOriginalSquareCenteredMoment (dim n) 1 U as b h
        (retainedMassPrefixIndex (w n).star.val as)
        (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) 1 1≤
          (((dim n+1:ℕ):ℝ)^(-saving)*((M n).xs^2/W n))^2

theorem eventually_actual_sharp_star_inherited_endpoint_second_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0)
    (hCf : 0 ≤ Cf)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hw : ∀ᶠn : ℕ in atTop,
      IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
      (actualMassSavingExponent m delta/32) M W w := by
  let C:=sharpEndpointSecondComparisonConstant Temp Cf
  have hC : 0 ≤ C:=sharpEndpointSecondComparisonConstant_nonneg Temp Cf
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along hm hdelta hC0
    (C+1) (by linarith) dim hdim M W hcanonical hWlim w hw
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HR,Hsource,HW] with n hn hsource hW1
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let S:=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let star:=retainedMassPrefixIndex (w n).star.val as
  let rho:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as star
  let site : ℝ:=1/(dim n+1:ℕ)
  let z:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*((M n).xs^2/W n)
  have hrho : 0 ≤ rho:=Real.sqrt_nonneg _
  have hsite : 0 ≤ site:=by dsimp only [site];positivity
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hxs : (M n).xs≤1:=by
    have H : (M n).xs≤W n:=by rw [hcanonical];exact le_max_left _ _
    exact H.trans hW1
  have Hbudget:=native_small_source_clock_full_square_budget (M n) Temp Cf hCf hsource hxs as ho
  have Hbond:=(hsource _ (partitionPoint_mem as ho as.length)).1
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show ((M n).bf u:ℝ)≤(M n).bf v from hbf hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show ((M n).hf u:ℝ)≤(M n).hf v from hhf hu hv huv) as ho
  have HS:=native_original_retained_star_low_second (dim n) (M n).bf (M n).hf hbf hhf as ho
    (w n).star (finiteCutMasses_nodes us j hstar)
  have Hsecond : nativeOriginalCutLowErrorSecond (dim n) (M n).bf (M n).hf as star=rho^2:=
    (Real.sq_sqrt (nativeOriginalCutLowErrorSecond_nonneg (dim n) (M n).bf (M n).hf ho star)).symm
  have Hclock : Real.exp (220*(finitePhysicalMixedClock (dim n+1) as b h as.length+
      b as.length+h as.length))≤Real.exp (220*(4*Cf+2*Temp)):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left Hbudget (by norm_num))
  have Hexp : Real.exp (110*b as.length)≤Real.exp (110*Temp):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left Hbond (by norm_num))
  intro U
  have Hrest:=native_original_square_centered_le_native_retained (dim n) 1 U
    (M n).bf (M n).hf as ho (w n).star.val S 1 1 (by norm_num) (by norm_num) hbm hhm
  dsimp only at Hrest
  norm_num only [Nat.mul_one, Nat.reduceSub, pow_one] at Hrest
  change nativeOriginalSquareCenteredMoment (dim n) 1 U as b h star S 1 1≤
    Real.exp (220*(finitePhysicalMixedClock (dim n+1) as b h as.length+b as.length+h as.length))*2*
      (Real.exp (110*b as.length)*nativeRetainedCenteredMoment (dim n) 1
        (M n).bf (M n).hf as (w n).star.val S+site^2) at Hrest
  rw [←HS,Hsecond] at Hrest
  have Hinside : Real.exp (110*b as.length)*rho^2+site^2≤
      Real.exp (110*Temp)*rho^2+site^2:=
    add_le_add (mul_le_mul_of_nonneg_right Hexp (sq_nonneg rho)) (le_refl _)
  have Hfirst:=Hrest.trans (mul_le_mul (mul_le_mul_of_nonneg_right Hclock (by norm_num : (0:ℝ)≤2))
    Hinside (by positivity) (by positivity))
  have Hraw : Real.exp (110*Temp)*rho^2+site^2≤(Real.exp (110*Temp)+1)*(rho+site)^2:=by
    have H1:=mul_nonneg (Real.exp_pos (110*Temp)).le (sq_nonneg site)
    have H2:=mul_nonneg (Real.exp_pos (110*Temp)).le (mul_nonneg hrho hsite)
    nlinarith [sq_nonneg rho,mul_nonneg hrho hsite]
  have Hfull : nativeOriginalSquareCenteredMoment (dim n) 1 U as b h star S 1 1≤C*(rho+site)^2:=by
    apply Hfirst.trans
    convert mul_le_mul_of_nonneg_left Hraw
      (show 0≤Real.exp (220*(4*Cf+2*Temp))*2 by positivity) using 1
    dsimp only [C,sharpEndpointSecondComparisonConstant]
    ring
  have Hcoef : C≤(C+1)^2:=by nlinarith [sq_nonneg C]
  have Hscaled:=mul_le_mul_of_nonneg_right Hcoef (sq_nonneg (rho+site))
  change (C+1)*(rho+site)≤z at hj
  have Hsaved:=pow_le_pow_left₀ (mul_nonneg (by linarith : 0≤C+1) (add_nonneg hrho hsite)) hj 2
  apply Hfull.trans
  apply Hscaled.trans
  simpa only [z,mul_pow] using Hsaved

end OAI.SKFluctuations.LaplaceWindowFormalization
