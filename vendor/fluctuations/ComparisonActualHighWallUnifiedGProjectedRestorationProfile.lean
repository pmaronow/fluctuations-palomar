module

public import ComparisonActualHighWallGProjectedRestorationProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

private theorem actual_high_wall_GProjected_profile_price_le
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

theorem eventually_actual_high_wall_all_degree_G_projected_restoration_profile
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
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let _Mclock:=2*max Bclock 0
        ∀(star U : ℕ) (T : ClockTree (Spin n×Bool) as),star < U → U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀s : T.Slot,
          let R:=M.data.highErrorEnvelope M.alpha as U
          |nativeOriginalGProjectedDisplacementRestoration T s star U q b h K S
            (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
            (G.canonicalHighWallSource M forms).restProduct| ≤
            C*(M.data.d*M.data.d^aDegree)*
              ((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
                M.data.d*(T.forkCost R+edgeBudget 0 as R)) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_high_wall_canonical_G_projected_restoration_profile
    (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Bclock0:=max Bclock 0
  have hBclock0 : 0 ≤ Bclock0:=le_max_right _ _
  let Acoeff:=(4*((rBound:ℝ)+1)+1)*2*pairForkVariation (rBound+4)*(Real.exp (wholeLawRowComparisonConstant (rBound+4)*(2*Bclock0))*Ch^(aDegree+1))*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
  let A:=Acoeff*(2*Bclock0)^((p-2)/p)*(2*Bclock0)^((p-2)/p)
  let B:=(4*((rBound:ℝ)+1)+1)*2*absJetVariation (rBound+4) 1*(Real.exp (wholeLawRowComparisonConstant (rBound+4)*(2*Bclock0))*Cl^(aDegree+1))*Cq*pairForkVariation (rBound+2)
  have hAc : 0 ≤ Acoeff:=by
    dsimp only [Acoeff]
    have :=pairForkVariation_nonneg (rBound+4)
    have :=pairForkVariation_nonneg (rBound+2)
    have :=pairForkVariation_nonneg rBound
    positivity
  have hA : 0 ≤ A:=by dsimp only [A];positivity
  have hB : 0 ≤ B:=by
    dsimp only [B]
    have :=absJetVariation_nonneg (rBound+4) 1
    have :=pairForkVariation_nonneg (rBound+2)
    have :=pairForkVariation_nonneg rBound
    positivity
  refine ⟨A+B+1,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro star U T hs hU hT G forms hcut hmass s
  let as:=finiteCutMasses us jGrid
  let R:=M.data.highErrorEnvelope M.alpha as U
  let Z:=M.data.d*M.data.d^aDegree
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hZ : 0 ≤ Z:=mul_nonneg M.data.hd.le (pow_nonneg M.data.hd.le _)
  have Hnum:=actual_high_wall_GProjected_profile_price_le T ho R hR p A B Z M.data.d hA hB hZ M.data.hd.le
  have Hraw:=hj star U T hs hU hT G forms hcut hmass s
  have HT : M.data.T ≤ Bclock0:=M.hT.trans (le_max_left _ _)
  have Hpow : (2*M.data.T)^((p-2)/p) ≤ (2*Bclock0)^((p-2)/p):=
    Real.rpow_le_rpow (by have HH:=M.data.hTpos.le;positivity)
      (mul_le_mul_of_nonneg_left HT (by norm_num)) (by positivity)
  have hTP : 0 ≤ (2*M.data.T)^((p-2)/p):=Real.rpow_nonneg (by have HH:=M.data.hTpos.le;positivity) _
  have hBP : 0 ≤ (2*Bclock0)^((p-2)/p):=Real.rpow_nonneg (by positivity) _
  have Hsq:=mul_le_mul Hpow Hpow hTP hBP
  have HF2:=add_nonneg (T.forkCost_nonneg (fun j=>sq_nonneg ((R j)^(2/p))))
    (edgeBudget_nonneg ho (fun j=>sq_nonneg ((R j)^(2/p))))
  have HH:=mul_le_mul_of_nonneg_left Hsq (mul_nonneg (mul_nonneg hAc hZ) HF2)
  have Hhigh : Acoeff*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*Z*
      (T.forkCost (fun j=>((R j)^(2/p))^2)+edgeBudget 0 as (fun j=>((R j)^(2/p))^2)) ≤
      A*Z*(T.forkCost (fun j=>((R j)^(2/p))^2)+edgeBudget 0 as (fun j=>((R j)^(2/p))^2)):=by
    convert HH using 1
    all_goals first | dsimp only [A] | skip
    all_goals ring_nf
  apply Hraw.trans
  apply le_trans ?_ Hnum
  have Hmajor:=add_le_add Hhigh (le_refl (B*Z*M.data.d*(T.forkCost R+edgeBudget 0 as R)))
  convert Hmajor using 1
  all_goals dsimp only [Acoeff,B,Bclock0,Z,R,as]
  all_goals ring_nf

end OAI.SKFluctuations.Cavity
