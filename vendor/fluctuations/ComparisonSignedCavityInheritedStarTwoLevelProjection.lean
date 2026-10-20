module

public import ComparisonSignedCavityActualStarTwoLevelProjection
public import ComparisonSignedCavityInheritedStarRootAnchorRaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_star_two_level_projection_fourth
    (Bclock Temp Cf Ccal : ℝ) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(Ei : ClockTree (Spin n) (mid++tail)) (Es T : ClockTree (Spin n) tail)
          (H : Ei.Assignment → Es.Assignment → ℝ) (e : Es.Slot) (s t : T.Slot),s ≠ t →
        ∀v : ℝ,W ≤ v →
          M.R (partitionPoint 0 as (pre.length+mid.length+T.splitIndex s t))=v →
          M.R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeTwoLevelProjectionFourth n Es Ei T (fun ζ η=>H η ζ) e s t qs qi qs
            (exteriorForestStarRoot z) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
              (M.xs+partitionPoint 0 as (pre.length+mid.length)))^4*
              Real.sqrt (∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
                (fun η ζ=>|H η ζ|^8) (exteriorForestIRoot z) (exteriorForestStarRoot z)
                ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) := by
  have hCcal0 : 0 < Ccal:=zero_lt_one.trans_le hCcal
  obtain ⟨Cr,hCr,Hraw⟩:=eventually_actual_minimum_inherited_star_exterior_fourth_bound
    (D:=D) Bclock Temp Cf hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  have hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  refine ⟨2*(2*C0)^3*Real.sqrt Cr,by positivity,?_⟩
  filter_upwards [Hraw,hlog,hdepth,eventually_ge_atTop (2:ℕ),
    eventually_native_two_level_fourth_from_primitives Bclock (cl/2) (1/(24*Ccal^3))
      (by positivity) (by positivity) hgap] with n hnraw hnlog hndepth hn2 hnrate
  intro M hsource hxs hcompare L us hus hret hmesh
  have hn : 0 < n := by omega
  have hnd : 1/M.context.N ≤ M.context.d := by
    have H:=hndepth M.context.E M.context.d M.context.hE M.context.hd M.hlower
    have H' : comparisonLowerScale ((n+1:ℕ):ℝ) M.context.E M.context.d ≤ M.context.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ M.context.hd).mpr (by simpa only [pow_two] using M.hupper)
    exact H.trans H'
  have hfinemesh : ∀ᶠk : ℕ in atTop,(((k+1:ℕ):ℝ)⁻¹)/M.context.floor ≤ M.xs/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const M.context.floor).eventually
      (gt_mem_nhds (show 0/M.context.floor < M.xs/16 by simpa only [zero_div] using
        (show 0 < M.xs/16 from div_pos M.hxs (by norm_num))))).mono
    intro k hk
    simpa using hk.le
  filter_upwards [hnraw M hsource hxs L us hus hret hmesh,hfinemesh] with k hk hkm
  dsimp only at hk ⊢
  intro pre mid tail hcut Ei Es T H e s t hst v hWv hvr hlow hz
  let as:=finiteCutMasses us k
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
  let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
  let qs:=nativeStarSuffixClock n pre mid q
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let steps:=nativeSampledPhysicalSteps n M.bf M.hf as
  let star:=pre.length+mid.length
  let high:=star+T.splitIndex s t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hop : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ ho
  have hot:=hop.suffix_end.suffix_end
  have hhigh : high ≤ as.length := by
    have HH:=T.splitIndex_le_clockLength s t
    dsimp only [high,star,as]
    rw [←hcut]
    simp only [List.length_append]
    omega
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hxv : M.xs ≤ v:=(le_max_left _ _).trans hWv
  have hv : 0 < v:=M.hxs.trans_le hxv
  have hv1 : v ≤ 1 := by
    rw [←hvr]
    exact (comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha _).2
  obtain ⟨hcritical,hduration⟩:=native_minimum_observed_calibration_scales
    M hn2 hm.le hC0 hCcal hcompare hWv hv1
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
  have hsipos : 0 < Cr*(M.xs+partitionPoint 0 as (pre.length+mid.length)) :=
    mul_pos hCr (add_pos_of_pos_of_nonneg M.hxs (partitionPoint_mem as ho (pre.length+mid.length)).1)
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail hop 0 q 0
  have HF:=hnrate tail (mid++tail) tail _ _ _ hot hop.suffix_end hot Es Ei T (fun ζ η=>H η ζ) e s t hst qs qi qs
    (cutSlice steps start high) (cutSlice steps star start) (cl*v/2) _
    (Cr*(M.xs+partitionPoint 0 as (pre.length+mid.length))) ((2*C0)*M.xs) W v hpr
    (by positivity) hpos hB hsipos.le (by exact mul_pos (by positivity) M.hxs) hW hv
    (by ring_nf;exact le_rfl) (hduration.trans hdur) hcritical horder _
    (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
    exteriorForestStarRoot exteriorForestIRoot exteriorForestStarRoot
    departedAnchorExteriorRoot_measurable departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
    d hd hds hdclock (hk pre mid tail hcut Es e)
  have he : 2*(n:ℝ)^(-eta)*savedWeightedExteriorScale ((2*C0)*M.xs) W v
      (Cr*(M.xs+partitionPoint 0 as (pre.length+mid.length))) =
      (2*(2*C0)^3*Real.sqrt Cr)*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
        (M.xs+partitionPoint 0 as (pre.length+mid.length)) := by
    rw [savedWeightedExteriorScale_scaled_star_incoming hCr.le]
    ring
  have Hmean :
      (∫z,nativeExteriorForestMean Es Ei (restWeight n) (restFeature n) qs qi
        (fun ζ η=>|H η ζ|^8) (exteriorForestStarRoot z) (exteriorForestIRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)=
      (∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
        (fun η ζ=>|H η ζ|^8) (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0):=by
    apply integral_congr_ae
    exact Eventually.of_forall fun z=>native_exterior_forest_mean_star_flip n Ei Es
      (fun η ζ=>|H η ζ|^8) qi qs (exteriorForestIRoot z) (exteriorForestStarRoot z)
  rw [Hmean] at HF
  simpa only [he] using HF

end OAI.SKFluctuations.Cavity
