module

public import SKProof.Port.ComparisonActualOriginalQActualFourGaCurrent
public import ComparisonSignedCavityInheritedFourGaCurrentForestAlong
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQInheritedResourceGaCurrentAlong

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum ActualThetaZeroOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualFourGaCurrentForestOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (seedBound k₀ r₀ depth : ℕ) (eta Cmass cK C : ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(U : ℕ) (seed : List NativeResourceMark)
      (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
      seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves≤r₀ →
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed st.generation st.tree st.term →
      0 < mid.length → ∀(hs : pre.length+mid.length < U) (hU : U≤(pre++(mid++tail)).length),
    ∀x V : ℝ,(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → W n ≤ V → V ≤ 1 →
      V≤(M n).sweepRadius (partitionPoint 0 as U) →
      (M n).sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as (pre.length+mid.length) →
      ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth [st]).map
        (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q|)).sum ≤
        |st.term.coefficient| *C*((dim n):ℝ)^(-eta)*(M n).xs^2*nativeResourceScale x (W n) 1 seed

theorem actual_four_Ga_current_forest_from_resource_rows_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp Cf eta Cmass cK C₀ : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hcK : 0<cK) (hC₀ : 0<C₀)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (hsource : ∀ᶠn : ℕ in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (hcutoff : ∀ᶠn : ℕ in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (hxs : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1)
    (Hrows : ActualResourceGaCurrentOnEveryFinalNetAlong_original_q (seedBound+k₀+depth) (r₀+6*depth+1)
      eta Cmass C₀ M W w) :
    ∃C : ℝ,0<C ∧ ActualFourGaCurrentForestOnEveryFinalNetAlong_original_q seedBound k₀ r₀ depth eta Cmass cK C M W w := by
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0≤Cw:=by dsimp only [Cw];positivity
  let Vcost:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 r₀ depth
  have hVcost : 0≤Vcost:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let C:=2*Vcost*(Temp/cK)*C₀+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hrows,hsource,hxs] with n hn hnsource hnxs
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  intro pre mid tail hcut hindex hmass U seed st hseedlength hgen hleaf hP hmid hs hU
    x V hx hxW hmi hWV hV1 hVU hlow hz hstarK
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
  let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=(dim n)) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as pre.length star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth [st]
  have ho : MassOrdered 0 as:=by simpa only [as,hcut] using finiteCutMasses_ordered us hus j
  have hx0:0<x:=(M n).hxs.trans_le hx
  have hW:0<W n:=hx0.trans_le hxW
  have hseed : 0≤nativeResourceScale x (W n) 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos hx0 hW zero_lt_one).le
  let B:=C₀*((dim n):ℝ)^(-eta)*(M n).xs^2*nativeResourceScale x (W n) 1 seed
  have hB : 0≤B:=by dsimp only [B];positivity
  have HK : cK*W n ≤ K star:=by simpa only [as,K,star,hcut] using hstarK
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q| ≤
      |Q.term.coefficient| *(Temp/cK)*B:=by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hP) Q hQ
    have Hdepth:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hgen) Q hQ
    have Hleaf:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
      r₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hleaf) Q hQ
    have Hdegree : Q.term.resources.length ≤ seedBound+k₀+depth:=by
      rw [Hvalid.total_factor_depth]
      omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ r₀+6*depth+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      dsimp only [g] at HH ⊢
      omega
    have H0:=hj pre mid tail hcut hindex hmass Q.tree U Q.generation seed Q.term Hvalid
      Hdegree hmid hs hU (by omega) x V hx hxW hmi hWV hV1 hVU hlow hz
    have H1:=hj pre mid tail hcut hindex hmass g.tree U Q.generation seed (Q.term.retarget 0)
      Hvalid.retarget (by simpa only [NativeResourceTerm.retarget_resources] using Hdegree)
      hmid hs hU hg x V hx hxW hmi hWV hV1 hVU hlow hz
    apply actual_minimum_four_Ga_current_error_abs_le_original_q (M n) Q hW hcK hB hTemp
      (hnsource _ (partitionPoint_mem as ho star)).1 HK
    · convert H0 using 1
      dsimp only [B]
      ring
    · convert H1 using 1
      dsimp only [B,NativeResourceTerm.retarget]
      ring
  have Hsum:=nativeActualFourCenteredForest_singleton_abs_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    weight hCw (fun Q tag=>actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q
      (M n) hCf hnsource hnxs hW hcK as ho hs hU HK Q tag) depth st hleaf
    (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q|)
    (B:=(Temp/cK)*B) (by positivity) (by
      intro Q hQ
      rw [abs_abs]
      exact (Hrow Q hQ).trans_eq (by ring))
  have Hnonneg : 0≤(rows.map (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q|)).sum:=
    List.sum_nonneg (by intro z hz;obtain ⟨Q,hQ,rfl⟩:=List.mem_map.mp hz;exact abs_nonneg _)
  change |(rows.map (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q|)).sum| ≤ _ at Hsum
  rw [abs_of_nonneg Hnonneg] at Hsum
  apply Hsum.trans
  have HC : 2*Vcost*(Temp/cK)*C₀ ≤ C:=by dsimp only [C];linarith
  have HH:=mul_le_mul_of_nonneg_left HC
    (show 0≤|st.term.coefficient| *((dim n):ℝ)^(-eta)*(M n).xs^2*nativeResourceScale x (W n) 1 seed by positivity)
  convert HH using 1 <;> (try dsimp only [Vcost,B]) <;> ring

theorem eventually_inherited_same_star_four_Ga_current_forest_along_original_q (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (Cmass cK : ℝ) (hCm : 1 ≤ Cmass) (hcK : 0<cK) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (hcutoff : ∀ᶠn : ℕ in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_original_q j k saving M W w) :
    ∃C : ℝ,0<C ∧ ActualFourGaCurrentForestOnEveryFinalNetAlong_original_q seedBound k₀ r₀ depth eta Cmass cK C M W w := by
  obtain ⟨C,hC,HC⟩:=eventually_inherited_same_star_resource_Ga_current_along_original_q hdim
    (seedBound+k₀+depth) (r₀+6*depth+1) Cmass hCm heta hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource hcutoff saving hsaving w Hmixed
  have HX : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1:=by
    filter_upwards [hWlim.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn
    exact ((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm).trans hn.le
  exact actual_four_Ga_current_forest_from_resource_rows_along_original_q seedBound k₀ r₀ depth hTemp hCf hcK hC
    M W w hsource hcutoff HX HC

end OAI.SKFluctuations.Cavity
