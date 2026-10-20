module

public import ComparisonSignedCavityInheritedLongitudinalProfileProducer
public import ComparisonSignedCavityInheritedConstantLongitudinalProfile
public import ComparisonSignedCavityActualSmallCutCanonicalOldMoment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

private theorem longitudinal_profile_price_le
    {S : Type} {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (R : ℕ→ℝ) (hR : ∀j,0 ≤ R j) (p A B Z W : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hW : 0 ≤ W) :
    A*Z*(T.forkCost (fun j=>((R j)^(2/p))^2)+edgeBudget 0 as (fun j=>((R j)^(2/p))^2))+
      B*Z*W*(T.forkCost R+edgeBudget 0 as R) ≤
    (A+B+1)*Z*((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
      W*(T.forkCost R+edgeBudget 0 as R)) := by
  have Hpow : (fun j=>((R j)^(2/p))^2)=(fun j=>(R j)^(4/p)):=by
    funext j
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  rw [Hpow]
  have HF : 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)):=
    add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HR : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have HA:=mul_le_mul_of_nonneg_right (show A ≤ A+B+1 by linarith) (mul_nonneg hZ HF)
  have HB:=mul_le_mul_of_nonneg_right (show B ≤ A+B+1 by linarith) (mul_nonneg (mul_nonneg hZ hW) HR)
  convert add_le_add HA HB using 1 <;> ring

theorem eventually_actual_minimum_inherited_all_degree_longitudinal_restoration_profile
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
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
          |nativeOriginalLongitudinalRestoration n q U b h K S T
            (G.canonicalMinimumSource M forms).product a| ≤
            C*sourceMonomialScale x W initial*
              ((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  by_cases ha : 0 < aDegree
  · obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=
      eventually_actual_minimum_inherited_canonical_longitudinal_restoration_profile_budget
        (D:=D) aDegree dOrder rBound ha hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
        hm hdelta hroom hcl hcu hAz hC0 hCt
    let A:=pairForkVariation (rBound+3)*
      (Real.exp (wholeLawRowComparisonConstant (rBound+3)*(4*Cf+2*Temp))*Ch^aDegree)*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*nativeOriginalRestorationProfileVariation rBound
    let B:=absJetVariation (rBound+3) 1*
      (Real.exp (wholeLawRowComparisonConstant (rBound+3)*(4*Cf+2*Temp))*Cl^aDegree)*
      Cq*forkVariation rBound 3
    have hA : 0 ≤ A:=by
      dsimp only [A]
      have :=pairForkVariation_nonneg (rBound+3)
      have :=nativeOriginalRestorationProfileVariation_nonneg rBound
      positivity
    have hB : 0 ≤ B:=by
      dsimp only [B]
      have :=absJetVariation_nonneg (rBound+3) 1
      have :=forkVariation_nonneg rBound 3
      positivity
    refine ⟨A+B+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hsource hxs L us hus hret hmesh
    filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial x W hxsx hxW hcut hmass a
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
    have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hZ : 0 ≤ sourceMonomialScale x W initial:=by
      rw [←source_factor_scale_product]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx)
        ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
    have Hnum:=longitudinal_profile_price_le T ho R hR p A B (sourceMonomialScale x W initial) W
      hA hB hZ ((M.hxs.le.trans hxsx).trans hxW)
    apply (hj U T hU hT G forms initial x W hxsx hxW hcut hmass a).trans
    convert Hnum using 1
    dsimp only [A,B,R,as]
    ring
  · have hz : aDegree=0:=by omega
    subst aDegree
    obtain ⟨Cq,hCq,H⟩:=eventually_actual_minimum_inherited_constant_longitudinal_restoration_profile
      (D:=D) rBound p hp Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
    let A:=pairForkVariation (rBound+3)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
      nativeOriginalRestorationProfileVariation rBound
    let B:=absJetVariation (rBound+3) 1*Cq*forkVariation rBound 3
    have hA : 0 ≤ A:=by
      dsimp only [A]
      have :=pairForkVariation_nonneg (rBound+3)
      have :=nativeOriginalRestorationProfileVariation_nonneg rBound
      positivity
    have hB : 0 ≤ B:=by
      dsimp only [B]
      have :=absJetVariation_nonneg (rBound+3) 1
      have :=forkVariation_nonneg rBound 3
      positivity
    refine ⟨A+B+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hsource hxs L us hus hret hmesh
    filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial x W hxsx hxW hcut _hmass a
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
    have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hZ : sourceMonomialScale x W initial=1:=by
      rw [←source_factor_scale_product]
      exact Fin.prod_univ_zero _
    have Hprod : (G.canonicalMinimumSource M forms).product=(fun _=>1):=
      funext (native_canonical_source_zero_degree_product G M forms)
    rw [Hprod]
    rw [hZ]
    have Hnum:=longitudinal_profile_price_le T ho R hR p A B 1 W
      hA hB zero_le_one ((M.hxs.le.trans hxsx).trans hxW)
    apply (hj U T hU hT W (hxsx.trans hxW) hcut a).trans
    convert Hnum using 1
    dsimp only [A,B,R,as]
    ring

end OAI.SKFluctuations.Cavity
