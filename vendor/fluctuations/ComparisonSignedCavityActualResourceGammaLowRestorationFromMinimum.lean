module

public import ComparisonSignedCavityInheritedBoundedDegreeGammaLowPrice
public import ComparisonSignedCavityActualResourceGammaRestorationReadout
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_resource_gamma_LOW_restoration_from_minimum
    (degree rBound : ℕ)
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
        |(W⁻¹)^k*nativeActualResourceGammaSecondRestoration M U P false| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*(actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)))*W^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_bounded_degree_gamma_LOW_restoration_price
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
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
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW _hW1 hmi hms hcut
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    x W hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
  let as:=finiteCutMasses us jGrid
  let profile:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ))*W^2
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hprofile : 0 ≤ profile:=by
    have HD : 0 ≤ nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ):=
      add_nonneg (Real.sqrt_nonneg _) (by positivity)
    exact mul_nonneg (mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) HD) (sq_nonneg W)
  have HliveDegree : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,
      List.length_map] at Hlen
    omega
  have HL:=hjC P.live.factors.length HliveDegree U T hU hT G (fun _=>.centered) I x W hx hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass x W hmi hms) P.live.test.target star hs
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.bf M.hf as=
      (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.bf M.hf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have H:=actual_resource_gamma_second_restoration_normalized_profile_le M hP hdepth ho hi
    hs false hA hx hxW (mul_nonneg hC.le hprofile) HP (by
      dsimp only
      convert HL using 1 <;> first
      | rfl
      | (dsimp only [G,profile,as,nativeGammaProjectedSecondRestoration,Bool.false_eq_true,ite_false];ring))
  apply H.trans_eq
  dsimp only [profile,as]
  ring

end OAI.SKFluctuations.Cavity
