module

public import ComparisonSignedCavityActualInheritedProjectionPowersAlong
public import ComparisonSignedCavityActualRestStarRates
public import ComparisonActualHighOnlyStarFinalNet
public import ComparisonActualHighOnlyCanonicalSourceMoments
public import ComparisonActualHighOnlyAnalyticBasics

@[expose] public section
noncomputable section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualHighOnlyOverlapMinimum

namespace ActualHighOnlyOverlapMinimum

theorem original_scale_polynomial_lower_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
    (1/C0)*M.context.N^(-(1:ℝ)/6+m)≤M.xs := by
  have hupper : M.context.E≤M.context.d^2/Real.sqrt M.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hlower : (1/C0)*M.context.N^(-(2:ℝ)/3+m)*M.context.d≤M.context.E := by
    have H:= (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  exact (comparison_parent_scale_lower_bounds M.context.hN (one_div_pos.mpr hC0)
    M.context.hd hlower hupper).2.2.trans M.hscale

theorem eventually_omitted_site_below_saved_scale_high_only
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (hC0 : 0 < C0) (hroom : saving < (5:ℝ)/6+m) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,M.xs≤W → 1/(n+1:ℕ)≤((n+1:ℕ):ℝ)^(-saving)*W := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/C0)
      (q:=-(1:ℝ)) (r:=-saving-(1:ℝ)/6+m) (by positivity) (by linarith))
  filter_upwards [H] with n hn
  intro M W hxW
  have hN : 0<((n+1:ℕ):ℝ) := by positivity
  have Hl:=M.original_scale_polynomial_lower_high_only hC0
  have HP:=mul_le_mul_of_nonneg_left (Hl.trans hxW) (Real.rpow_nonneg hN.le (-saving))
  have he : ((n+1:ℕ):ℝ)^(-saving)*((1/C0)*M.context.N^(-(1:ℝ)/6+m))=
      (1/C0)*((n+1:ℕ):ℝ)^(-saving-(1:ℝ)/6+m) := by
    dsimp only [ActualHighOnlyComparisonData.N]
    rw [mul_left_comm,←Real.rpow_add hN]
    have hexp : -saving+(-(1:ℝ)/6+m)=-saving-(1:ℝ)/6+m := by ring
    rw [hexp]
  rw [he] at HP
  have Hcoef : 1/(n+1:ℕ)≤(1/C0)*((n+1:ℕ):ℝ)^(-saving-(1:ℝ)/6+m) := by
    simpa only [one_mul,Real.rpow_neg_one,one_div] using hn
  exact Hcoef.trans HP

end ActualHighOnlyOverlapMinimum

end OAI.SKFluctuations.LaplaceWindowFormalization
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualHighOnlyOverlapMinimum

def ActualOriginalRestStarMomentOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
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

theorem actual_inherited_native_star_every_final_net_to_rest_along_high_only
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock Temp Cf saving : ℝ}
    (hCf : 0 ≤ Cf) (hC0 : 0 < C0) (hs : 0 < saving)
    (hroom : saving < (5:ℝ)/6+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hsource : ∀ᶠn : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (H : ActualNativeStarMomentOnEveryFinalNetAlong_high_only p saving M W w) :
    ActualOriginalRestStarMomentOnEveryFinalNetAlong_high_only p (saving/2) M W w := by
  let B:=4*Cf+2*Temp
  let C:=Real.exp (220*B)*(2:ℝ)^(2*(p+1)-1)*(Real.exp (110*Temp)+1)
  have Hsite:=eventually_omitted_site_below_saved_scale_high_only (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 hroom
  have HC:=eventually_rest_star_cost_absorbed (p+1) (by omega) C hs
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,hdim.eventually Hsite,hdim.eventually HC,HW,hdim.eventually (eventually_gt_atTop (0:ℕ)),hsource] with n hn hnsite hnC hnW hn0 hnsource
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
  have Hbudget:=native_small_source_clock_full_square_budget_high_only (M n) Temp Cf hCf hnsource hMxs as ho
  have Hbond:=(hnsource _ (partitionPoint_mem as ho as.length)).1
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>((M n).bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>(M n).bf_monotone hx hy hxy) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>((M n).hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>(M n).hf_monotone hx hy hxy) as ho
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
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 12000000

def ActualOriginalStarProjectionPowerOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as j):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
      let center:=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∀(T : ClockTree (Spin (dim n)) tail) (s : T.Slot),
        let qs:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j))
        (∫z,T.expect (restWeight (dim n)) (restFeature (dim n)) qs
          (fun σ=>|nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (T.atSlot σ s)|^(2*(p+1)))
          (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0) ≤
          (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_rest_star_to_projection_powers_along_high_only
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (p : ℕ) {dim : ℕ→ℕ} (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualOriginalRestStarMomentOnEveryFinalNetAlong_high_only p saving M W w) :
    ActualOriginalStarProjectionPowerOnEveryFinalNetAlong_high_only p saving M W w := by
  filter_upwards [H] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hindex T s
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  apply (native_common_star_projection_power_le_original_pair (dim n) (2*(p+1)) pre mid tail ho T s
    0 _ (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) 0).trans
  have HK (bs : List PositiveMass) (hbs : bs=finiteCutMasses us k) (j : ℕ)
      (hj : j=retainedMassPrefixIndex (w n).star.val (finiteCutMasses us k)) :
      (ClockTree.pairClock bs j).disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0
        (fun j=>Sum.elim (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
          (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)))
        (fun σ=>|deletedOverlap (dim n) (joinSpin ((ClockTree.pairSpin bs j σ).1,false))
          (joinSpin ((ClockTree.pairSpin bs j σ).2,false))-
            orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val|^(2*(p+1))) 0 ≤
        (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) := by
    subst bs j
    exact hk
  exact HK _ hcut _ hindex

def ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (j k : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∀(T : ClockTree (Spin (dim n)) tail) (s t : T.Slot),
        let qs:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+(mid.length+l))
        nativeRootTestExpect (dim n) T qs
          (nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0)
          exteriorForestStarRoot
          (fun z σ=>(nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (T.atSlot σ s)^j*
            nativeStarCenteredProjection (dim n) tail qs center (exteriorForestStarRoot z) (T.atSlot σ t)^k)^2) ≤
          (((dim n+1:ℕ):ℝ)^(-saving)*W n)^(2*(j+k))

theorem actual_star_projection_powers_to_mixed_along_high_only
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (j k : ℕ) {dim : ℕ→ℕ} (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNetAlong_high_only p saving M W w) :
    ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w := by
  filter_upwards [H (2*j-1),H (2*k-1)] with n hnJ hnK
  intro us hus hstar
  filter_upwards [hnJ us hus hstar,hnK us hus hstar] with r hrJ hrK
  dsimp only at hrJ hrK ⊢
  intro pre mid tail hcut hindex T s t
  let q : ℕ → RestCoordinate (dim n) → ℝ:=fun l=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) l):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) l):ℝ))
  let qs:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+(mid.length+l))
  let center:=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val
  let μ:=nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos (dim n)) (restFeature (dim n))
    pre mid tail ho 0 q 0
  apply native_star_projection_mixed_power_second_le (dim n) j k T ho.suffix_end.suffix_end qs μ
    exteriorForestStarRoot departedAnchorExteriorRoot_measurable center s t
    (((dim n+1:ℕ):ℝ)^(-saving)*W n) (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hW n))
  · by_cases hj : j=0
    · subst j
      simp only [mul_zero,pow_zero,nativeRootTestExpect]
      simp only [T.expect_const (restWeight_pos (dim n)) (restFeature (dim n)) ho.suffix_end.suffix_end]
      simp
    · have he : 2*(2*j-1+1)=4*j := by omega
      simpa only [he,nativeRootTestExpect,qs,μ,q,center] using hrJ pre mid tail hcut hindex T s
  · by_cases hk : k=0
    · subst k
      simp only [mul_zero,pow_zero,nativeRootTestExpect]
      simp only [T.expect_const (restWeight_pos (dim n)) (restFeature (dim n)) ho.suffix_end.suffix_end]
      simp
    · have he : 2*(2*k-1+1)=4*k := by omega
      simpa only [he,nativeRootTestExpect,qs,μ,q,center] using hrK pre mid tail hcut hindex T t

theorem actual_inherited_native_star_to_all_projection_powers_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Cf saving : ℝ}
    (hCf : 0 ≤ Cf) (hC0 : 0 < C0) (hsaving : 0 < saving)
    (hroom : saving < (5:ℝ)/6+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (Hnative : ∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong_high_only p saving M W w) :
    (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNetAlong_high_only p (saving/2) M W w) ∧
    (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNetAlong_high_only p (saving/2) M W w) ∧
    ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k (saving/2) M W w := by
  have Hrest (p : ℕ) : ActualOriginalRestStarMomentOnEveryFinalNetAlong_high_only p (saving/2) M W w :=
    actual_inherited_native_star_every_final_net_to_rest_along_high_only p hCf hC0 hsaving hroom
      dim hdim M W hxs hWlim hsource w (Hnative p)
  have Hpow (p : ℕ) : ActualOriginalStarProjectionPowerOnEveryFinalNetAlong_high_only p (saving/2) M W w :=
    actual_rest_star_to_projection_powers_along_high_only p M W w (Hrest p)
  exact ⟨Hrest,Hpow,fun j k=>actual_star_projection_powers_to_mixed_along_high_only j k M W
    (fun n=>(M n).hxs.le.trans (hxs n)) w Hpow⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
