module

public import ComparisonSignedCavityActualBoundedResourceHighTaylorProfile
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_resource_HIGH_parts_from_minimum
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
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualResourceHigherHighPart M U P part a z l t| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_bounded_resource_HIGH_parts_profile
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
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a z l t hl ht part
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    x W hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have H:=hjC i star U k seed T P hP hi hs hU hT hdepth A x W hA hx hxW hW1 hmi hms hcut HP a z l t hl ht part
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity
