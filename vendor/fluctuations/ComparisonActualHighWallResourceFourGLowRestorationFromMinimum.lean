module

public import ComparisonActualHighWallBoundedFourGLowRestorationProfile
public import ComparisonActualGeneralResourceJointHighRestorationReadout
public import ComparisonActualHighWallRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_high_wall_resource_four_G_low_restoration_from_minimum
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀a z : T.Slot,
        let R:=M.data.highErrorEnvelope M.alpha as U
        |(M.data.d⁻¹)^k*actualGeneralResourceJointHighRestoration .fourGLow M.bf M.hf U P a z| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
            (C*M.data.d*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              M.data.d*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_high_wall_bounded_degree_four_G_low_restoration_profile
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨A,hA,HA⟩:=eventually_actual_high_wall_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨C*A^degree,by positivity,?_⟩
  filter_upwards [HC,HA] with n hnC hnA
  intro M hwork L us hus hret hmesh
  filter_upwards [hnC M hwork L us hus hret hmesh,
    hnA M hwork L us hus hret hmesh] with jGrid hjC hjA
  dsimp only at hjC hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut a z
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    hmi hms 1 1 (by norm_num) (by norm_num)
  let as:=finiteCutMasses us jGrid
  let R:=M.data.highErrorEnvelope M.alpha as U
  let profile:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    M.data.d*(T.forkCost R+edgeBudget 0 as R)
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have HF : 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)):=
    add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HR : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hprofile : 0 ≤ profile:=add_nonneg HF (mul_nonneg (M.data.hd.le) HR)
  have HliveDegree : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,
      List.length_map] at Hlen
    omega
  have hmass (e : Fin P.live.factors.length) : G.sourceLowMass e ≤ Cmass*M.data.d:=by
    simpa only [sourceFactorScale,ite_self] using native_actual_resource_canonical_source_mass
      P.live hi (hs.trans_le hU) Cmass M.data.d M.data.d hmi hms e
  have HL:=hjC P.live.factors.length HliveDegree U T hU hT G (fun _=>.centered) hcut hmass a z
  have Hscale : nativeResourceScale M.data.d M.data.d 1 P.live.tags=M.data.d^P.live.factors.length:=by
    rw [←native_actual_resource_live_scale_eq_annotations,←source_factor_scale_product]
    simp only [sourceFactorScale,ite_self,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←Hscale] at HL
  have Hcenter : nativePhysicalResourceCenter n M.bf M.hf as=
      (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have H:=actual_general_resource_joint_HIGH_normalized_price_le .fourGLow M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hP hdepth ho hi
    (hs.trans_le hU) a z hA M.data.hd le_rfl (mul_nonneg (mul_nonneg hC.le M.data.hd.le) hprofile) HP (by
      dsimp only
      convert HL using 1 <;> first
      | rfl
      | (dsimp only [G,profile,R,as,nativeJointHighRestorationSource];ring))
  apply H.trans_eq
  dsimp only [profile,R,as]
  ring_nf

end OAI.SKFluctuations.Cavity
