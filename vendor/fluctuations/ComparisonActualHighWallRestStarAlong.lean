module

public import ComparisonActualHighWallStarFinalNetAlong
public import ComparisonActualHighWallHighMassNumerics
public import ComparisonActualHighWallSourceClockBudget
public import ComparisonSignedCavityActualInheritedRestStarAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_omitted_site_below_saved_scale
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (hC0 : 0 < C0) (hroom : saving < (5:ℝ)/6+m) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,M.xs≤W → 1/(n+1:ℕ)≤((n+1:ℕ):ℝ)^(-saving)*W := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/C0)
      (q:=-(1:ℝ)) (r:=-saving-(1:ℝ)/6+m) (by positivity) (by linarith))
  filter_upwards [H] with n hn
  intro M W hxW
  have hN : 0<((n+1:ℕ):ℝ) := by positivity
  have Hl:=M.high_mass_scale_critical_lower hC0
  have HP:=mul_le_mul_of_nonneg_left (Hl.trans hxW) (Real.rpow_nonneg hN.le (-saving))
  have he : ((n+1:ℕ):ℝ)^(-saving)*((1/C0)*M.data.N^(-(1:ℝ)/6+m))=
      (1/C0)*((n+1:ℕ):ℝ)^(-saving-(1:ℝ)/6+m) := by
    dsimp only [ActualHighWallData.N]
    rw [mul_left_comm,←Real.rpow_add hN]
    have hexp : -saving+(-(1:ℝ)/6+m)=-saving-(1:ℝ)/6+m := by ring
    rw [hexp]
  rw [he] at HP
  have Hcoef : 1/(n+1:ℕ)≤(1/C0)*((n+1:ℕ):ℝ)^(-saving-(1:ℝ)/6+m) := by
    simpa only [one_mul,Real.rpow_neg_one,one_div] using hn
  exact Hcoef.trans HP

def ActualHighWallRestStarMomentOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1) → (w n).star∈us →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
        nativeOriginalRestCenteredMoment (dim n) (p+1) as b h
          (retainedMassPrefixIndex (w n).star.val as)
          (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val)≤
            (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_high_wall_star_every_final_net_to_rest_along
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (hC0 : 0 < C0) (hs : 0 < saving)
    (hroom : saving < (5:ℝ)/6+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (H : ActualHighWallStarMomentOnEveryFinalNetAlong p saving M W w) :
    ActualHighWallRestStarMomentOnEveryFinalNetAlong p (saving/2) M W w := by
  let Temp:=max Bclock 0
  let B:=2*Temp
  let C:=Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1)*(Real.exp (110*Temp)+1)
  have Hsite:=eventually_actual_high_wall_omitted_site_below_saved_scale (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hroom
  have HC:=eventually_rest_star_cost_absorbed (p+1) (by omega) C hs
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,hdim.eventually Hsite,hdim.eventually HC,HW,hdim.eventually (eventually_gt_atTop (0:ℕ))] with n hn hnsite hnC hnW hn0
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let S:=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let z:=((dim n+1:ℕ):ℝ)^(-saving)*W n
  have hz : 0≤z := mul_nonneg (Real.rpow_nonneg (by positivity) _) ((M n).hxs.le.trans (hxs n))
  have hMxs : (M n).xs≤1 := (hxs n).trans hnW
  have hT : (M n).data.T≤Temp:=(M n).hT.trans (le_max_left _ _)
  have Hbudget : finitePhysicalMixedClock (dim n+1) as b h as.length+b as.length+h as.length≤B:=
    ((M n).data.full_square_clock_budget (M n).alpha as ho).trans (by dsimp only [B];linarith only [hT])
  have Hbond : b as.length≤Temp:=by
    have HH:=(M n).data.total_clock_le (M n).alpha _ (partitionPoint_mem as ho as.length)
    have HP:=((M n).hf (partitionPoint 0 as as.length)).coe_nonneg
    dsimp only [b];linarith only [HH,HP,hT]
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun x hx y hy hxy=>show ((M n).bf x:ℝ)≤((M n).bf y:ℝ) from (M n).data.bf_monotone (M n).alpha hx hy hxy) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun x hx y hy hxy=>show ((M n).hf x:ℝ)≤((M n).hf y:ℝ) from (M n).data.hf_monotone (M n).alpha hx hy hxy) as ho
  have Hrest:=native_original_rest_centered_le_native_retained (dim n) (p+1) hn0
    (M n).bf (M n).hf as ho (w n).star.val S hbm hhm
  dsimp only at Hrest
  have Hcoeff : Real.exp (220*(finitePhysicalMixedClock (dim n+1) as b h as.length+b as.length+h as.length))*
      (2:ℝ)^(2*(p+1)-1)≤Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left Hbudget (by norm_num)
  have Hexp : Real.exp (110*b as.length)≤Real.exp (110*Temp) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left Hbond (by norm_num))
  have Hstar : nativeRetainedCenteredMoment (dim n) (p+1) (M n).bf (M n).hf as (w n).star.val S≤z^(2*(p+1)) := hj
  have Hsitepow : (1/(dim n+1:ℕ):ℝ)^(2*(p+1))≤z^(2*(p+1)) :=
    pow_le_pow_left₀ (by positivity) (hnsite (M n) (W n) (hxs n)) _
  have Hinside : Real.exp (110*b as.length)*nativeRetainedCenteredMoment (dim n) (p+1)
      (M n).bf (M n).hf as (w n).star.val S+(1/(dim n+1:ℕ):ℝ)^(2*(p+1))≤
        (Real.exp (110*Temp)+1)*z^(2*(p+1)) := by
    have HE:=mul_le_mul Hexp Hstar
      (nativeRetainedCenteredMoment_nonneg (dim n) (p+1) (M n).bf (M n).hf as ho (w n).star.val S)
      (Real.exp_pos _).le
    nlinarith only [HE,Hsitepow]
  have Hsum0 : 0≤Real.exp (110*b as.length)*nativeRetainedCenteredMoment (dim n) (p+1)
      (M n).bf (M n).hf as (w n).star.val S+(1/(dim n+1:ℕ):ℝ)^(2*(p+1)) := by
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le
      (nativeRetainedCenteredMoment_nonneg (dim n) (p+1) (M n).bf (M n).hf as ho (w n).star.val S)) (by positivity)
  have Hbound:=Hrest.trans (mul_le_mul Hcoeff Hinside Hsum0 (by positivity))
  have Hbound' : nativeOriginalRestCenteredMoment (dim n) (p+1) as b h
      (retainedMassPrefixIndex (w n).star.val as) S≤C*z^(2*(p+1)) := by
    simpa only [C,mul_assoc] using Hbound
  exact Hbound'.trans (hnC (W n) ((M n).hxs.le.trans (hxs n)))

end OAI.SKFluctuations.LaplaceWindowFormalization
