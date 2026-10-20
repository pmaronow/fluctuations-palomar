module

public import ComparisonSignedCavityActualRestStarTransport
public import ComparisonNativeStarActualAllOrder
public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

namespace NativeOverlapMinimum

theorem original_scale_polynomial_lower
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
    (1/C0)*M.context.N^(-(1:ℝ)/6+m)≤M.xs := by
  have hupper : M.context.E≤M.context.d^2/Real.sqrt M.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hlower : (1/C0)*M.context.N^(-(2:ℝ)/3+m)*M.context.d≤M.context.E := by
    have H:= (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  exact (comparison_parent_scale_lower_bounds M.context.hN (one_div_pos.mpr hC0)
    M.context.hd hlower hupper).2.2.trans M.hscale

theorem eventually_omitted_site_below_saved_scale
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (hC0 : 0 < C0) (hroom : saving < (5:ℝ)/6+m) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,M.xs≤W → 1/(n+1:ℕ)≤((n+1:ℕ):ℝ)^(-saving)*W := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/C0)
      (q:=-(1:ℝ)) (r:=-saving-(1:ℝ)/6+m) (by positivity) (by linarith))
  filter_upwards [H] with n hn
  intro M W hxW
  have hN : 0<((n+1:ℕ):ℝ) := by positivity
  have Hl:=M.original_scale_polynomial_lower hC0
  have HP:=mul_le_mul_of_nonneg_left (Hl.trans hxW) (Real.rpow_nonneg hN.le (-saving))
  have he : ((n+1:ℕ):ℝ)^(-saving)*((1/C0)*M.context.N^(-(1:ℝ)/6+m))=
      (1/C0)*((n+1:ℕ):ℝ)^(-saving-(1:ℝ)/6+m) := by
    dsimp only [NativeOverlapContext.N]
    rw [mul_left_comm,←Real.rpow_add hN]
    have hexp : -saving+(-(1:ℝ)/6+m)=-saving-(1:ℝ)/6+m := by ring
    rw [hexp]
  rw [he] at HP
  have Hcoef : 1/(n+1:ℕ)≤(1/C0)*((n+1:ℕ):ℝ)^(-saving-(1:ℝ)/6+m) := by
    simpa only [one_mul,Real.rpow_neg_one,one_div] using hn
  exact Hcoef.trans HP

end NativeOverlapMinimum

theorem eventually_rest_star_cost_absorbed (l : ℕ) (hl : 0 < l)
    (C : ℝ) {saving : ℝ} (hs : 0 < saving) :
    ∀ᶠn : ℕ in atTop,∀W : ℝ,0≤W →
      C*(((n+1:ℕ):ℝ)^(-saving)*W)^(2*l)≤
        (((n+1:ℕ):ℝ)^(-(saving/2))*W)^(2*l) := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C) (d:=1)
      (q:=(-saving)*((2*l:ℕ):ℝ)) (r:=(-(saving/2))*((2*l:ℕ):ℝ))
      zero_lt_one (by
        have hcast : 0<((2*l:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
        nlinarith))
  filter_upwards [H] with n hn
  intro W hW
  have hN : 0<((n+1:ℕ):ℝ) := by positivity
  rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hN.le,←Real.rpow_mul_natCast hN.le]
  simpa only [mul_assoc,one_mul] using mul_le_mul_of_nonneg_right hn (pow_nonneg hW (2*l))

def ActualOriginalRestStarOrderSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀extra : List PositiveMass,(∀u∈extra,u.val≤1) →
    ∃us : List PositiveMass,(∀u∈us,u.val≤1) ∧ (∀u∈extra,u∈us) ∧ (w n).star∈us ∧
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
        nativeOriginalRestCenteredMoment n (p+1) as b h
          (retainedMassPrefixIndex (w n).star.val as)
          (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)≤
            (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_native_star_order_saving_to_rest
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock Temp Craw saving : ℝ}
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hs : 0 < saving)
    (hroom : saving < (5:ℝ)/6+m)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarOrderSaving p Craw saving M W w) :
    ActualOriginalRestStarOrderSaving p (saving/2) M W w := by
  let B:=4*bareSourceClockConstant cl Az D+2*Temp
  let C:=Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1)*(Real.exp (110*Temp)+1)
  have Hsite:=eventually_omitted_site_below_saved_scale (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hroom
  have HC:=eventually_rest_star_cost_absorbed (p+1) (by omega) C hs
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsite,HC,HW,eventually_gt_atTop (0:ℕ)] with n hn hnsite hnC hnW hn0
  intro extra hextra
  obtain ⟨us,hus,hretain,hstar,Hj⟩:=hn extra hextra
  refine ⟨us,hus,hretain,hstar,?_⟩
  filter_upwards [Hj] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let S:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  let z:=((n+1:ℕ):ℝ)^(-saving)*W n
  have hz : 0≤z := mul_nonneg (Real.rpow_nonneg (by positivity) _) ((M n).hxs.le.trans (hxs n))
  have hMxs : (M n).xs≤1 := (hxs n).trans hnW
  have Hbudget:=(M n).bare_sampled_full_square_clock_budget hcl hAz Temp (hb n) (hh n) hMxs as ho
  have Hbond:=((M n).bare_source_clock_bounds hcl hAz Temp (hb n) (hh n)
    (partitionPoint_mem as ho as.length)).2.1
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>((M n).bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>((M n).hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  have Hrest:=native_original_rest_centered_le_native_retained n (p+1) hn0
    (M n).bf (M n).hf as ho (w n).star.val S hbm hhm
  dsimp only at Hrest
  have Hcoeff : Real.exp (220*(finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length))*
      (2:ℝ)^(2*(p+1)-1)≤Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left Hbudget (by norm_num)
  have Hexp : Real.exp (110*b as.length)≤Real.exp (110*Temp) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left Hbond (by norm_num))
  have Hstar : nativeRetainedCenteredMoment n (p+1) (M n).bf (M n).hf as (w n).star.val S≤z^(2*(p+1)) := hj.2
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
  have Hbound' : nativeOriginalRestCenteredMoment n (p+1) as b h
      (retainedMassPrefixIndex (w n).star.val as) S≤C*z^(2*(p+1)) := by
    simpa only [C,mul_assoc] using Hbound
  exact Hbound'.trans (hnC (W n) ((M n).hxs.le.trans (hxs n)))

end OAI.SKFluctuations.LaplaceWindowFormalization
