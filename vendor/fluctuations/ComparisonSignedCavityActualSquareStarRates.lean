module

public import ComparisonSignedCavityActualResourcePairProducer

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

def nativeOriginalSquareCenteredMoment (n l U : ℕ) (as : List PositiveMass)
    (b h : ℕ → ℝ) (j : ℕ) (S a t : ℝ) : ℝ :=
  (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
    (finitePhysicalCavitySquareVariance n U as b h a t)
    (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
      (joinSpin (ClockTree.pairSpin as j σ).2)-S|^(2*l)) 0

theorem native_original_square_centered_le_native_retained (n l U : ℕ)
    (bf hf : ℝ → ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as) (u S a t : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hb : Monotone (fun j=>(bf (partitionPoint 0 as j):ℝ)))
    (hh : Monotone (fun j=>(hf (partitionPoint 0 as j):ℝ))) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let j:=retainedMassPrefixIndex u as
    let K:=finitePhysicalMixedClock (n+1) as b h
    nativeOriginalSquareCenteredMoment n l U as b h j S a t≤
      Real.exp (220*(K as.length+b as.length+h as.length))*(2:ℝ)^(2*l-1)*
        (Real.exp (110*b as.length)*nativeRetainedCenteredMoment n l bf hf as u S+
          (1/(n+1:ℕ):ℝ)^(2*l)) := by
  dsimp only
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  have H:=cavityPath_pairDeleted_moment_le_physicalStar n l U ho ha ht hb hh
    (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh (fun _=>NNReal.coe_nonneg _))
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _)
    (finitePhysicalMixedClock_nonneg (n+1) as b h (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _))
    (retainedMassPrefixIndex u as) (retainedMassPrefixIndex_le_length u as) S
  dsimp only at H
  rw [physicalStarPairMoment_eq_pairDisorder (n+1) l as ho _
    (retainedMassPrefixIndex u as) (retainedMassPrefixIndex_le_length u as) S] at H
  exact H

def ActualOriginalSquareStarMomentOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1) → (w n).star∈us →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
        ∀(U : ℕ) (a t : ℝ),a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        nativeOriginalSquareCenteredMoment n (p+1) U as b h
          (retainedMassPrefixIndex (w n).star.val as)
          (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val) a t≤
            (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_native_star_every_final_net_to_square
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock Temp saving : ℝ}
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hs : 0 < saving)
    (hroom : saving < (5:ℝ)/6+m)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarMomentOnEveryFinalNet p saving M W w) :
    ActualOriginalSquareStarMomentOnEveryFinalNet p (saving/2) M W w := by
  let B:=4*bareSourceClockConstant cl Az D+2*Temp
  let C:=Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1)*(Real.exp (110*Temp)+1)
  have Hsite:=eventually_omitted_site_below_saved_scale (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hroom
  have HC:=eventually_rest_star_cost_absorbed (p+1) (by omega) C hs
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsite,HC,HW,eventually_gt_atTop (0:ℕ)] with n hn hnsite hnC hnW hn0
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

theorem exists_actual_bare_original_square_star_on_every_final_net
    {m delta cl cu Az C0 Ct D Bclock T L Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ)
    (hcanonical : ∀n,W n=max (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)))
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNet p saving M W w) := by
  obtain ⟨hs,Cs,hCs,w,hw,H,Hfinite⟩:=exists_actual_bare_native_star_on_every_final_net
    hm hdelta hroom hcl hcu hAz hC0 hCt hT hL hCcal M W hcanonical hWlim hcompare hb hh
  have hxs n : (M n).xs≤W n := by rw [hcanonical];exact le_max_left _ _
  have hsite : actualSlowWindowExponent m delta/128 < (5:ℝ)/6+m := by
    have Hc:=(actualSlowWindowExponent_bounds hm hdelta).2.2
    linarith
  have Hrest (p : ℕ) : ActualOriginalSquareStarMomentOnEveryFinalNet p
      (actualSlowWindowExponent m delta/256) M W w := by
    have HG:=actual_native_star_every_final_net_to_square p hcl hAz hC0 hs hsite M W hxs hWlim hb hh w (H p)
    simpa only [show (actualSlowWindowExponent m delta/128)/2=actualSlowWindowExponent m delta/256 by ring] using HG
  exact ⟨by linarith,Cs,hCs,w,hw,Hrest⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
