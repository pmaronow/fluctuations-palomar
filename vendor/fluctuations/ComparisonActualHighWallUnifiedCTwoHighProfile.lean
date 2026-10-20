module

public import ComparisonActualHighWallCTwoHighProfileProducer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_high_wall_all_degree_C_two_high_profile
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (_hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let _Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀a z : T.Slot,T.splitIndex a z < U →
          let R:=M.data.highErrorEnvelope M.alpha as U
          |nativeCenteredLowGammaHighSecondRemainder n q U b h K S T
            (G.canonicalHighWallSource M forms).restProduct a z| ≤
            C*(M.data.d*M.data.d^aDegree)*
              ((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
                M.data.d*(T.forkCost R+edgeBudget 0 as R)) := by
  let Cgeom:=max Cmass Ccut
  have hCg : 0 ≤ Cgeom:=hCmass.trans (le_max_left _ _)
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_high_wall_canonical_C_two_high_profile_budget
    (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Cgeom hCg
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Bclock0:=max Bclock 0
  have hBclock0 : 0 ≤ Bclock0:=le_max_right _ _
  let Acoeff:=pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
    (Real.exp (wholeLawRowComparisonConstant (rBound+2)*(2*Bclock0))*Cp^(aDegree+1))*pairForkVariation rBound
  let A:=Acoeff*(2*Bclock0)^((p-2)/p)*(2*Bclock0)^((p-2)/p)
  have hAc : 0 ≤ Acoeff:=by
    dsimp only [Acoeff]
    have :=pairForkVariation_nonneg (rBound+4)
    have :=pairForkVariation_nonneg (rBound+2)
    have :=pairForkVariation_nonneg rBound
    positivity
  have hA : 0 ≤ A:=by dsimp only [A];positivity
  refine ⟨A+1,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T hU hT G forms hcut hmass a z haz
  let as:=finiteCutMasses us jGrid
  let R:=M.data.highErrorEnvelope M.alpha as U
  let Z:=M.data.d*M.data.d^aDegree
  let F2:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
  let F1:=T.forkCost R+edgeBudget 0 as R
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hZ : 0 ≤ Z:=mul_nonneg M.data.hd.le (pow_nonneg M.data.hd.le _)
  have hF2 : 0 ≤ F2:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
    (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have hF1 : 0 ≤ F1:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hcutg:=hcut.trans (mul_le_mul_of_nonneg_right (le_max_right Cmass Ccut) M.data.hd.le)
  have hmassg e:=(hmass e).trans (mul_le_mul_of_nonneg_right (le_max_left Cmass Ccut) M.data.hd.le)
  have Hraw:=hj U T hU hT G forms hcutg hmassg a z haz
  have HT : M.data.T ≤ Bclock0:=M.hT.trans (le_max_left _ _)
  have Hpow : (2*M.data.T)^((p-2)/p) ≤ (2*Bclock0)^((p-2)/p):=
    Real.rpow_le_rpow (by have HH:=M.data.hTpos.le;positivity)
      (mul_le_mul_of_nonneg_left HT (by norm_num)) (by positivity)
  have hTP : 0 ≤ (2*M.data.T)^((p-2)/p):=Real.rpow_nonneg (by have HH:=M.data.hTpos.le;positivity) _
  have hBP : 0 ≤ (2*Bclock0)^((p-2)/p):=Real.rpow_nonneg (by positivity) _
  have Hsq:=mul_le_mul Hpow Hpow hTP hBP
  have HH:=mul_le_mul_of_nonneg_left Hsq (mul_nonneg (mul_nonneg hAc hZ) hF2)
  have Hhigh : Acoeff*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*Z*F2 ≤ A*Z*F2:=by
    convert HH using 1
    all_goals first | dsimp only [A] | skip
    all_goals ring_nf
  have Hmajor : A*Z*F2 ≤ (A+1)*Z*(F2+M.data.d*F1):=by
    have Hextra:=mul_nonneg (mul_nonneg (add_nonneg hA (by norm_num : (0:ℝ)≤1)) hZ)
      (mul_nonneg M.data.hd.le hF1)
    have Hmono:=mul_le_mul_of_nonneg_right (show A ≤ A+1 by linarith) (mul_nonneg hZ hF2)
    nlinarith only [Hextra,Hmono]
  apply Hraw.trans
  apply le_trans ?_ Hmajor
  convert Hhigh using 1
  all_goals dsimp only [Acoeff,Bclock0,Z,F2,R,as]
  all_goals ring_nf

end OAI.SKFluctuations.Cavity
