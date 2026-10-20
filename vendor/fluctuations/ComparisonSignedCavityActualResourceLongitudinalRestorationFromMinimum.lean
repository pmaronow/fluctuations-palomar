module

public import ComparisonSignedCavityInheritedBoundedDegreeLongitudinalProfile
public import ComparisonSignedCavityActualResourceLongitudinalRestorationReadout
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_resource_longitudinal_restoration_from_minimum
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a : T.Slot,
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualResourceLongitudinalRestoration M U P a| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_bounded_degree_longitudinal_restoration_profile
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨C*A^degree,by positivity,?_⟩
  filter_upwards [HC,HA] with n hnC hnA
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnC M hsource hxs L us hus hret hmesh,
    hnA M hsource hxs L us hus hret hmesh] with jGrid hjC hjA
  dsimp only at hjC hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW _hW1 hmi hms hcut a
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    x W hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
  let as:=finiteCutMasses us jGrid
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let profile:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    W*(T.forkCost R+edgeBudget 0 as R)
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have HF : 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)):=
    add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HR : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hprofile : 0 ≤ profile:=add_nonneg HF (mul_nonneg ((M.hxs.le.trans hx).trans hxW) HR)
  have HliveDegree : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,
      List.length_map] at Hlen
    omega
  have HL:=hjC P.live.factors.length HliveDegree U T hU hT G (fun _=>.centered) I x W hx hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass x W hmi hms) a
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.bf M.hf as=
      (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.bf M.hf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have H:=actual_resource_longitudinal_restoration_normalized_profile_le M hP hdepth ho hi
    (hs.trans_le hU) a hA hx hxW (mul_nonneg hC.le hprofile) HP (by
      dsimp only
      convert HL using 1 <;> first
      | rfl
      | (dsimp only [G,profile,R,as];ring))
  apply H.trans_eq
  dsimp only [profile,R,as]
  ring

end OAI.SKFluctuations.Cavity
