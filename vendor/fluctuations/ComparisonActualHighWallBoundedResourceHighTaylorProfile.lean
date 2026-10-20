module

public import ComparisonActualHighWallResourceHighTaylorProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_high_wall_bounded_resource_HIGH_parts_profile
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
        ∀(A : ℝ),1 ≤ A →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as
            (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) 0 A M.data.d M.data.d 1 →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
        let R:=M.data.highErrorEnvelope M.alpha as U
        |(M.data.d⁻¹)^k*actualGeneralResourceHigherHighPart M.bf M.hf U P part a z l t| ≤
          |P.coefficient| *A^degree*nativeResourceScale M.data.d M.data.d 1 seed*
            (C*M.data.d*((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
              M.data.d*(T.forkCost R+edgeBudget 0 as R))) := by
  classical
  have HP (a : Fin (degree+1)) :=
    eventually_actual_high_wall_resource_HIGH_parts_profile
      (D:=D) a.val dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  refine ⟨Cmax,hCmax,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC] with n hn
  intro M hwork L us hus hret hmesh
  have Hgrids a:=hn a M hwork L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth A hA hmi hms hcut Hpair aSlot z l t hl ht part
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,
      List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have H:=hj a i star U k degree seed T P hP hi hs hU hT rfl hdepth
    A hA hmi hms hcut Hpair aSlot z l t hl ht part
  have hx0:=M.data.hd
  have hW:=M.data.hd
  let as:=finiteCutMasses us jGrid
  let R:=M.data.highErrorEnvelope M.alpha as U
  let f2:=fun j=>(R j)^(4/p)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF2 : 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)):=
    add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have hF1 : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hseed:=actual_resource_raw_scale_pos seed hx0 hW
  have HD:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hdom a) hW.le)
    (show 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+M.data.d*(T.forkCost R+edgeBudget 0 as R) by positivity))
    (show 0 ≤ |P.coefficient| *A^degree*nativeResourceScale M.data.d M.data.d 1 seed by positivity)
  exact H.trans HD

end OAI.SKFluctuations.Cavity
