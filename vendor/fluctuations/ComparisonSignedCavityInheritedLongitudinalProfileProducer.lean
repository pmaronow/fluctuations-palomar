module

public import ComparisonSignedCavityInheritedGLongitudinalOriginalBudget
public import ComparisonSignedCavityOriginalLongitudinalProfileBudget

public import ComparisonSignedCavityActualLongitudinalProfileProducer
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_longitudinal_restoration_profile_budget
    (aDegree dOrder rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x→x ≤ W→
          partitionPoint 0 as U ≤ Ccut*W→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)→
        ∀a : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Ch^aDegree*
            sourceMonomialScale x W initial
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cl^aDegree*
            sourceMonomialScale x W initial
          |nativeOriginalLongitudinalRestoration n q U b h K S T
            (G.canonicalMinimumSource M forms).product a| ≤
            (pairForkVariation (rBound+3)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p))*
              nativeOriginalRestorationProfileVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
            (absJetVariation (rBound+3) 1*CL*(Cq*W))*forkVariation rBound 3*
              (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=
    eventually_actual_minimum_inherited_canonical_longitudinal_restoration_original_budget
      (D:=D) aDegree dOrder rBound ha hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let Mclock:=4*Cf+2*Temp
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Ch^aDegree*
    sourceMonomialScale x W initial
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cl^aDegree*
    sourceMonomialScale x W initial
  have hscale : 0 ≤ sourceMonomialScale x W initial := by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hCH : 0 ≤ CH:=by dsimp only [CH];positivity
  have hCL : 0 ≤ CL:=by dsimp only [CL];positivity
  have hW : 0 ≤ W:=(M.hxs.le.trans hxsx).trans hxW
  have Hwords:=native_original_G_word_restoration_sum_le_profiles T
    (finiteCutMasses_ordered us hus jGrid) U (rBound+3) rBound hT M.bf M.hf K a
    Mclock Temp p CH CL (Cq*W) hTemp hCH hCL (mul_nonneg hCq.le hW)
  exact (hgrid U T hU hT G forms initial x W hxsx hxW hcut hmass a).trans Hwords

end OAI.SKFluctuations.Cavity
