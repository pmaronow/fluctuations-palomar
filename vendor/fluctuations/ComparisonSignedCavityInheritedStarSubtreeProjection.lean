module

public import ComparisonSignedCavityActualStarSubtreeProjection
public import ComparisonSignedCavityInheritedAnchorPrimitives

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_star_subtree_projection_fourth
    (Bclock Temp Cf Cmass c₀ : ℝ) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hc₀ : 0<c₀)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
        ∀(T : ClockTree (Spin n) tail) (s t : T.Slot),s≠t →
        ∀r v : ℝ,0<r → M.xs ≤ v → (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
          M.R (partitionPoint 0 as (pre.length+mid.length+T.splitIndex s t))=v →
          M.R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          c₀*W^3/Real.log (n:ℝ) ≤ laplaceComparisonStrength M.context.d M.lam v*v/
            (12*Real.log M.context.N) →
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(2*(n:ℝ)^(-eta)*savedWeightedExteriorScale r W v (C*W))^4 ∧
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (exteriorForestStarRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(2*(n:ℝ)^(-eta)*savedWeightedExteriorScale r W v (C*W))^4 := by
  obtain ⟨C,hC,hraw⟩:=eventually_actual_minimum_inherited_fresh_star_exterior_fourth_bound
    Bclock Temp Cf Cmass hCf hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  have hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  have hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  refine ⟨C,hC,?_⟩
  filter_upwards [hraw,hlog,hdepth,eventually_gt_atTop (0:ℕ),
    eventually_native_subtree_exterior_fourth_from_primitives Bclock (cl/2) c₀
      (by positivity) hc₀ hgap] with n hnraw hnlog hndepth hn hnrate
  intro M hsource hxs L us hus hret hmesh
  have hnd : 1/M.context.N ≤ M.context.d := by
    have H:=hndepth M.context.E M.context.d M.context.hE M.context.hd M.hlower
    have H' : comparisonLowerScale ((n+1:ℕ):ℝ) M.context.E M.context.d ≤ M.context.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ M.context.hd).mpr (by simpa only [pow_two] using M.hupper)
    exact H.trans H'
  have hfinemesh : ∀ᶠk : ℕ in atTop,(((k+1:ℕ):ℝ)⁻¹)/M.context.floor ≤ M.xs/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const M.context.floor).eventually
      (gt_mem_nhds (show 0/M.context.floor<M.xs/16 by simpa only [zero_div] using
        (show 0<M.xs/16 from div_pos M.hxs (by norm_num))))).mono
    intro k hk
    simpa using hk.le
  filter_upwards [hnraw M hsource hxs L us hus hret hmesh,hfinemesh] with k hk hkm
  dsimp only at hk ⊢
  intro pre mid tail hcut W hW hmass T s t hst r v hr hxv hcritical hvr hlow hz hduration
  let as:=finiteCutMasses us k
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
  let qs:=nativeStarSuffixClock n pre mid q
  let steps:=nativeSampledPhysicalSteps n M.bf M.hf as
  let star:=pre.length+mid.length
  let high:=star+T.splitIndex s t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hop : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ ho
  have hot:=hop.suffix_end.suffix_end
  have hhigh : high ≤ as.length := by
    have H:=T.splitIndex_le_clockLength s t
    dsimp only [high,star,as]
    rw [←hcut]
    simp only [List.length_append]
    omega
  have hv : 0<v:=M.hxs.trans_le hxv
  have hWpos : 0<W:=M.hxs.trans_le hW
  obtain ⟨start,hstart,hbefore,ha,hpos,hdur,hB,hprefix,htail,hord,d,hd,hds,hdclock⟩:=
    NativeOverlapMinimum.exists_observed_rest_finite_innovation n hn M hcl hnlog hnd
      as ho (by positivity : 0 ≤ (((k+1:ℕ):ℝ)⁻¹)) (finiteCutMasses_mesh us hus k)
      hv (hkm.trans (div_le_div_of_nonneg_right hxv (by norm_num))) hhigh hvr hlow hz
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have heq : clockSteps tail (fun j=>restFiniteVariance n (qs j))=steps.drop star :=
    native_star_suffix_clock_eq_drop n M.bf M.hf (toNNReal_monotoneOn had.1)
      (toNNReal_monotoneOn had.2.1) as pre mid tail ho hcut
  have hsplit : high-star=T.splitIndex s t:=by dsimp [high];omega
  have hpr : (clockSteps tail (fun j=>restFiniteVariance n (qs j))).take (T.splitIndex s t)=
      cutSlice steps star start++cutSlice steps start high := by
    rw [heq,←hsplit]
    exact hprefix
  have hta : (clockSteps tail (fun j=>restFiniteVariance n (qs j))).drop (T.splitIndex s t)=steps.drop high := by
    rw [heq,←hsplit]
    exact htail
  have horder : OrderedSteps (cl*v/2) (cutSlice steps start high++
      (clockSteps tail (fun j=>restFiniteVariance n (qs j))).drop (T.splitIndex s t)) := by
    rw [hta]
    exact hord
  have Hraw:=hk pre mid tail hcut W hW hmass
  let :=  nativeTwinPrefixDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail hop 0 q 0
  let :=  nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail hop 0 q 0
  have hHtw : (∫z,(ClockTree.single (S:=Spin n) tail).expect (restWeight n) (restFeature n)
      qs (fun _=>|(1:ℝ)|^8) (twinPrefixBRoot z)
      ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤ (1:ℝ)^8 := by
    rw [native_twin_star_fresh_hweight_eighth_eq_one n pre mid tail hop]
    norm_num
  have hHco : (∫z,(ClockTree.single (S:=Spin n) tail).expect (restWeight n) (restFeature n)
      qs (fun _=>|(1:ℝ)|^8) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤ (1:ℝ)^8 := by
    rw [native_common_star_fresh_hweight_eighth_eq_one n pre mid tail hop]
    norm_num
  constructor
  · have H:=hnrate tail tail _ _ hot hot T s t (ClockTree.single tail) (fun _=>1)
      (ClockTree.singleSlot tail) qs qs hst (cutSlice steps start high) (cutSlice steps star start)
      (cl*v/2) _ 1 (C*W) r W v hpr (by positivity) hpos hB (by norm_num) (by positivity)
      hr hWpos hv (by ring_nf;exact le_rfl) (hduration.trans hdur) hcritical horder _
      (nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
      twinPrefixBRoot twinPrefixDRoot twinPrefixBRoot_measurable twinPrefixDRoot_measurable
      d hd hds hdclock hHtw Hraw.1
    simpa only [mul_one] using H
  · have H:=hnrate tail tail _ _ hot hot T s t (ClockTree.single tail) (fun _=>1)
      (ClockTree.singleSlot tail) qs qs hst (cutSlice steps start high) (cutSlice steps star start)
      (cl*v/2) _ 1 (C*W) r W v hpr (by positivity) hpos hB (by norm_num) (by positivity)
      hr hWpos hv (by ring_nf;exact le_rfl) (hduration.trans hdur) hcritical horder _
      (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
      exteriorForestStarRoot exteriorForestStarRoot departedAnchorExteriorRoot_measurable
      departedAnchorExteriorRoot_measurable d hd hds hdclock hHco Hraw.2
    simpa only [mul_one] using H

end OAI.SKFluctuations.Cavity
