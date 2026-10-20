module

public import ComparisonActualHighWallGammaFirstHighBoundedDegree
public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonSignedCavityGeneratedPairedFrozenScale
public import ComparisonActualGeneralResourceFirstHighReadout

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_resource_first_high_from_minimum
    (degree : ℕ) (Bclock Cmass Rmacro F : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.data.d
        ∀(T : ClockTree (Spin n×Bool) as) (i star U kGen rBound : ℕ)
          (seed : List NativeResourceMark) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed kGen T P → P.resources.length ≤ degree →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        let R:=M.data.highErrorEnvelope M.alpha as U
        |(W⁻¹)^kGen*actualGeneralResourceFirstHigh M.bf M.hf U P| ≤
          |P.coefficient| *C*nativeResourceScale M.data.d W 1 seed*W^2*
            nativeGammaFirstHighVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cl,hCl,HL⟩:=eventually_actual_high_wall_generated_first_high_bounded_degree
    (D:=D) degree Bclock Cmass Rmacro F hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  obtain ⟨A,hA,HA⟩:=eventually_actual_high_wall_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=Cl*A^degree
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HL,HA] with n hnL hnA
  intro M hwork L us hus hret hmesh
  filter_upwards [hnL M hwork L us hus hret hmesh,
    hnA M hwork L us hus hret hmesh] with jGrid hjL hjA
  dsimp only at hjL hjA ⊢
  intro T i star U kGen rBound seed P hP hdegree hi hs hlen hT hmacroW hsmall hmi hms
  let as:=finiteCutMasses us jGrid
  let W:=M.data.d
  let R:=M.data.highErrorEnvelope M.alpha as U
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let scalar:=P.scalar (fullWeight n) (fullFeature n) 0 q
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) 0
  let scale:=sourceMonomialScale M.xs W (nativeGeneratedCompleteInitial P.live.test i)
  let cost:=T.forkCost R+edgeBudget 0 as R
  let Dprice:=Cl*W^2*nativeGammaFirstHighVariation rBound*cost
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hx:=M.hxs
  have hxW:=hwork.le
  have hW:=M.data.hd
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost : 0 ≤ cost:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hprice : 0 ≤ Dprice:=by
    dsimp only [Dprice]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCl.le (sq_nonneg W))
      (nativeGammaFirstHighVariation_nonneg rBound)) hcost
  have hlive : P.live.test.edges.length ≤ degree:=by
    have HH:=P.live.realizes.length_eq
    have HL : P.live.tags.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append]
      omega
    simp only [List.length_map,NativeResourceMonomial.tags] at HH HL
    omega
  have Hlive:=hjL T i star U kGen rBound seed P hP hlive hi hs hlen hT hmacroW hsmall hmi hms
  have Hpair:=hjA U i star T P (by omega) (by omega) (by omega) (by simpa only [hwork] using hmi) hms
    1 1 (by norm_num) (by norm_num)
  have Hscalar:=P.scalar_mul_canonical_live_scale_le (fullWeight_pos n) (fullFeature n) ho
    0 q (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) 0 hA hx hxW hi (by omega) (by simpa only [hwork] using Hpair)
  have HLprice : |actualGeneralGeneratedFirstHigh M.bf M.hf T star U P.live.test| ≤ scale*Dprice:=by
    convert Hlive using 1
    dsimp only [scale,Dprice,cost,W,R,as]
    simp only [hwork,sourceMonomialScale_self]
    ring_nf
  have Hprod : |scalar*actualGeneralGeneratedFirstHigh M.bf M.hf T star U P.live.test| ≤
      |P.coefficient| *nativeResourceEnvelope A M.xs W 1 P.resources*Dprice:=by
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_left HLprice (abs_nonneg scalar)).trans
    have HH:=mul_le_mul_of_nonneg_right Hscalar hprice
    simpa only [scalar,scale,mul_assoc] using HH
  have Hnorm:=mul_le_mul_of_nonneg_left Hprod (show 0 ≤ (W⁻¹)^kGen by positivity)
  have HE : (W⁻¹)^kGen*(|P.coefficient| *nativeResourceEnvelope A M.xs W 1 P.resources*Dprice)=
      |P.coefficient| *A^P.resources.length*nativeResourceScale M.data.d W 1 seed*Dprice := by
    rw [nativeResourceEnvelope_scale]
    calc
      _=|P.coefficient| *A^P.resources.length*((W⁻¹)^kGen*nativeResourceScale M.xs W 1 P.resources)*Dprice:=by ring
      _=_:=by rw [hP.normalized_saved_scale M.xs W 1 hW.ne',one_pow,mul_one,hwork]
  rw [HE] at Hnorm
  have HApow:=pow_le_pow_right₀ hA hdegree
  have hseed : 0 ≤ nativeResourceScale M.data.d W 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos M.data.hd hW zero_lt_one).le
  have Hfinal:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left HApow (abs_nonneg P.coefficient)) hseed) hprice
  rw [←abs_of_nonneg (show 0 ≤ (W⁻¹)^kGen by positivity),←abs_mul] at Hnorm
  change |(W⁻¹)^kGen*actualGeneralResourceFirstHigh M.bf M.hf U P| ≤ _ at Hnorm
  apply (Hnorm.trans Hfinal).trans_eq
  dsimp only [C,Dprice,cost,W,R,as]
  ring_nf

end OAI.SKFluctuations.Cavity
