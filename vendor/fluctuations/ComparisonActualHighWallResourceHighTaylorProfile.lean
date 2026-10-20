module

public import ComparisonActualHighWallCanonicalHighTaylorProfile
public import ComparisonActualGeneralResourceHighTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 23000000

theorem eventually_actual_high_wall_resource_HIGH_parts_profile
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
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
        ∀(i star U k degree : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → P.live.factors.length=aDegree → seed.length+k ≤ degree →
        ∀A : ℝ,1 ≤ A →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as
            (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) 0 A M.data.d M.data.d 1 →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=M.data.highErrorEnvelope M.alpha as U
          |(M.data.d⁻¹)^k*actualGeneralResourceHigherHighPart M.bf M.hf U P part a z l t| ≤
            |P.coefficient| *A^degree*nativeResourceScale M.data.d M.data.d 1 seed*
              (C*M.data.d*((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
                M.data.d*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_canonical_HIGH_parts_profile
    (D:=D) aDegree rBound dOrder hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k degree seed T P hP hi hs hU hT hlen hdepth A hA hmi hms hcut Hpair
    a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hstar : star < as.length:=hs.trans_le hU
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let R:=M.data.highErrorEnvelope M.alpha as U
  let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    M.data.d*(T.forkCost R+edgeBudget 0 as R)
  have hW : 0 ≤ M.data.d:=M.data.hd.le
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF₁:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hF₂:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) (4/p)))
    (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) (4/p)))
  have hprice : 0 ≤ C*M.data.d*cost:=by dsimp only [cost];positivity
  apply actual_general_resource_HIGH_part_normalized_profile_le M.bf M.hf hP hdepth ho hi hstar part a z l t
    hA M.data.hd le_rfl hprice Hpair
  have Hgrid:=hj
  rw [←hlen] at Hgrid
  have hmass (e : Fin P.live.factors.length) : G.sourceLowMass e ≤ Cmass*M.data.d:=by
    simpa only [sourceFactorScale,ite_self] using
      native_actual_resource_canonical_source_mass P.live hi hstar Cmass M.data.d M.data.d hmi hms e
  have HL:=Hgrid U T hU hT G (fun _=>.centered) hcut hmass a z l t hl ht part
  have Hscale : nativeResourceScale M.data.d M.data.d 1 P.live.tags=M.data.d^P.live.factors.length:=by
    rw [←native_actual_resource_live_scale_eq_annotations,←source_factor_scale_product]
    simp only [sourceFactorScale,ite_self,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Hscale]
  apply HL.trans_eq
  dsimp only [cost,R,as]
  ring_nf

end OAI.SKFluctuations.Cavity
