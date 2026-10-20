module

public import ComparisonSignedCavityJointHighRestorationSource
public import ComparisonSignedCavityInheritedCTwoHighProfileProducer
public import ComparisonSignedCavityInheritedFourGLowRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_canonical_joint_HIGH_restoration_price
    (kind : NativeJointHighRestorationKind) (aDegree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
          |nativeJointHighRestorationSource kind n q U b h K S T
            (G.canonicalMinimumSource M forms).restProduct a z| ≤
            C*W*sourceMonomialScale M.xs W initial*
              (T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  cases kind with
  | lowTwoHigh=>
    let Cgeom:=max Cmass Ccut
    have hCgeom : 0 ≤ Cgeom:=hCmass.trans (le_max_left _ _)
    obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_C_two_high_profile_budget
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cgeom hTemp hCf hCgeom
      hm hdelta hroom hcl hcu hAz hC0 hCt
    let base:=pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
      (Real.exp (wholeLawRowComparisonConstant (rBound+2)*(4*Cf+2*Temp))*Cp^(aDegree+1))*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*pairForkVariation rBound
    have hbase : 0 ≤ base:=by
      have HV0:=pairForkVariation_nonneg (rBound+2)
      have HV1:=pairForkVariation_nonneg (rBound+4)
      have HV2:=pairForkVariation_nonneg rBound
      have HP:=Real.rpow_nonneg (show 0 ≤ 2*Temp by positivity) ((p-2)/p)
      dsimp only [base]
      positivity
    refine ⟨base+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hsource hxs L us hus hret hmesh
    filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial W hxW hcut hmass a z haz
    have hW : 0 ≤ W:=M.hxs.le.trans hxW
    have hmass' e : G.sourceLowMass e ≤ Cgeom*sourceFactorScale M.xs W initial e:=
      (hmass e).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le)
    have hcut' : partitionPoint 0 (finiteCutMasses us jGrid) U ≤ Cgeom*W:=
      hcut.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hW)
    have Hraw:=hj U T hU hT G forms initial W hxW hcut' hmass' a z haz
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
    let Z:=sourceMonomialScale M.xs W initial
    let A:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
    let B:=T.forkCost R+edgeBudget 0 as R
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
          dsimp only [nativeOriginalCutLowErrorRadius]
          positivity)
    have hA : 0 ≤ A:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
    have hB : 0 ≤ B:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
    have hZ : 0 ≤ Z:=by
      rw [show Z=∏e,sourceFactorScale M.xs W initial e from (source_factor_scale_product _ _ _).symm]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
    have Hmajor:=mul_le_mul_of_nonneg_right (show base ≤ base+1 by linarith)
      (show 0 ≤ W*Z*A by positivity)
    have Hprice : base*W*Z*A ≤ (base+1)*W*Z*(A+W*B):=by
      have Hplus : 0 ≤ (base+1)*W*Z*(W*B):=by positivity
      nlinarith only [Hmajor,Hplus]
    apply Hraw.trans
    convert Hprice using 1
    dsimp only [base,R,Z,A,B,as,nativeJointHighRestorationSource]
    ring
  | fourGLow=>
    obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_canonical_four_G_low_restoration
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
    let bh:=2*pairForkVariation (rBound+4)*
      (Real.exp (wholeLawRowComparisonConstant (rBound+4)*(4*Cf+2*Temp))*Ch^(aDegree+1))*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)*pairForkVariation rBound
    let bl:=2*absJetVariation (rBound+4) 1*
      (Real.exp (wholeLawRowComparisonConstant (rBound+4)*(4*Cf+2*Temp))*Cl^(aDegree+1))*
      (Cq*(1+Ccut))*pairForkVariation (rBound+2)*pairForkVariation rBound
    have hbh : 0 ≤ bh:=by
      have HV0:=pairForkVariation_nonneg (rBound+4)
      have HV1:=pairForkVariation_nonneg (rBound+2)
      have HV2:=pairForkVariation_nonneg rBound
      have HP:=Real.rpow_nonneg (show 0 ≤ 2*Temp by positivity) ((p-2)/p)
      dsimp only [bh]
      positivity
    have hbl : 0 ≤ bl:=by
      have HV0:=absJetVariation_nonneg (rBound+4) 1
      have HV1:=pairForkVariation_nonneg (rBound+2)
      have HV2:=pairForkVariation_nonneg rBound
      dsimp only [bl]
      positivity
    refine ⟨bh+bl+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hsource hxs L us hus hret hmesh
    filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial W hxW hcut hmass a z _haz
    have Hraw:=hj U T hU hT G forms initial W hxW hcut hmass a z
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
    let Z:=sourceMonomialScale M.xs W initial
    let A:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
    let B:=T.forkCost R+edgeBudget 0 as R
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hW : 0 ≤ W:=M.hxs.le.trans hxW
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
          dsimp only [nativeOriginalCutLowErrorRadius]
          positivity)
    have Hpow : (fun j=>((R j)^(2/p))^2)=(fun j=>(R j)^(4/p)):=by
      funext j
      rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
      congr 1
      ring
    change |nativeJointHighRestorationSource .fourGLow n _ U _ _ _ _ T _ a z| ≤ _ at Hraw
    rw [Hpow] at Hraw
    have hA : 0 ≤ A:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
    have hB : 0 ≤ B:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
    have hZ : 0 ≤ Z:=by
      rw [show Z=∏e,sourceFactorScale M.xs W initial e from (source_factor_scale_product _ _ _).symm]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
    have Hmajor:=add_le_add
      (mul_le_mul_of_nonneg_right (show bh ≤ bh+bl+1 by linarith) (show 0 ≤ W*Z*A by positivity))
      (mul_le_mul_of_nonneg_right (show bl ≤ bh+bl+1 by linarith) (show 0 ≤ W^2*Z*B by positivity))
    apply Hraw.trans
    convert Hmajor using 1 <;> (try dsimp only [bh,bl,R,Z,A,B,as]) <;> ring

end OAI.SKFluctuations.Cavity
