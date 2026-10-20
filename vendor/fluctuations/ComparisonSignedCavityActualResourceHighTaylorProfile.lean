module

public import ComparisonSignedCavityActualAllDegreeHighTaylorProfile
public import ComparisonSignedCavityActualResourceHighTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 23000000

theorem eventually_actual_minimum_inherited_resource_HIGH_parts_profile
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
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
        ∀(i star U k degree : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → P.live.factors.length=aDegree → seed.length+k ≤ degree →
        ∀A x W : ℝ,1 ≤ A → M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as
            (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W 1 →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
          |(W⁻¹)^k*nativeActualResourceHigherHighPart M U P part a z l t| ≤
            |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*
              (C*W*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_all_degree_HIGH_parts_profile
    (D:=D) aDegree rBound dOrder hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k degree seed T P hP hi hs hU hT hlen hdepth A x W hA hx hxW hW1 hmi hms hcut Hpair
    a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hstar : star < as.length:=hs.trans_le hU
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let I:=nativeActualResourceInitialFactors P.live
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    W*(T.forkCost R+edgeBudget 0 as R)
  have hW : 0 ≤ W:=((M.hxs.trans_le hx).trans_le hxW).le
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF₁:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hF₂:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) (4/p)))
    (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) (4/p)))
  have hprice : 0 ≤ C*W*cost:=by dsimp only [cost];positivity
  apply actual_resource_HIGH_part_normalized_profile_le M hP hdepth ho hi hstar part a z l t
    hA hx hxW hprice Hpair
  have Hgrid:=hj
  rw [←hlen] at Hgrid
  have HL:=Hgrid U T hU hT G (fun _=>.centered) I x W hx hxW hW1 hcut
    (native_actual_resource_canonical_source_mass P.live hi hstar Cmass x W hmi hms) a z l t hl ht part
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  apply HL.trans_eq
  ring

end OAI.SKFluctuations.Cavity
