module

public import ComparisonSignedCavityActualResourceGRestorationSource
public import ComparisonSignedCavityActualResourceGRestorationNorm
public import ComparisonSignedCavityInheritedGProjectedRestorationProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_minimum_inherited_resource_G_restoration_profile
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
        U ≤ as.length → T.leaves ≤ rBound → P.live.factors.length=aDegree →
        seed.length+k ≤ degree →
        ∀(A x W ε : ℝ),1 ≤ A → M.xs ≤ x → x ≤ W → 0 < ε → ε ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as
            (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W ε →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
        let f2:=fun j=>((R j)^(2/p))^2
        |(W⁻¹)^k*nativeActualResourceGaRestoration M U P| ≤
          |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost f2+edgeBudget 0 as f2+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,Hsource⟩:=
    eventually_actual_minimum_inherited_canonical_G_projected_restoration_profile
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let KH:=(4*((rBound:ℝ)+1)+1)*2*pairForkVariation (rBound+4)*
    (Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1))*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
  let KL:=(4*((rBound:ℝ)+1)+1)*2*absJetVariation (rBound+4) 1*
    (Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1))*
    (Cq*(1+Ccut))*pairForkVariation (rBound+2)
  have hpv1:=pairForkVariation_nonneg (rBound+4)
  have hpv2:=pairForkVariation_nonneg (rBound+2)
  have hav:=absJetVariation_nonneg (rBound+4) 1
  have hrp : 0 ≤ (2*Temp)^((p-2)/p):=Real.rpow_nonneg (by positivity) _
  have hKH : 0 ≤ KH:=by dsimp only [KH];positivity
  have hKL : 0 ≤ KL:=by dsimp only [KL];positivity
  let C:=KH+KL+1
  have hC : 0 < C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsource] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro i star U k degree seed T P hP hi hs hU hT hlen hdepth A x W ε hA hx hxW hε hε1 hmi hms hcut Hpair
  let as:=finiteCutMasses us jGrid
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hstar : star < as.length:=hs.trans_le hU
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let I:=nativeActualResourceInitialFactors P.live
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let F2:=T.forkCost f2+edgeBudget 0 as f2
  let F1:=T.forkCost R+edgeBudget 0 as R
  have hW : 0 ≤ W:=((M.hxs.trans_le hx).trans_le hxW).le
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF2 : 0 ≤ F2:=add_nonneg (T.forkCost_nonneg (fun j=>sq_nonneg _))
    (edgeBudget_nonneg ho (fun j=>sq_nonneg _))
  have hF1 : 0 ≤ F1:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hscale : 0 ≤ nativeResourceScale x W 1 P.live.tags:=
    (actual_resource_raw_scale_pos _ (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)).le
  have Hmass e : G.sourceLowMass e ≤ Cmass*sourceFactorScale x W I e:=
    native_actual_resource_canonical_source_mass P.live hi hstar Cmass x W hmi hms e
  have Hlive : |nativeActualGProjectedRestoration T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))| ≤
      nativeResourceScale x W 1 P.live.tags*(W*(KH*F2+KL*(W*F1))) := by
    have Hgrid:=hgrid
    rw [←hlen] at Hgrid
    have H:=Hgrid star U T hs hU hT G (fun _=>NativeSourceFactorForm.centered) I x W hx hxW
      hcut Hmass P.live.test.target
    rw [native_actual_resource_live_scale_eq_annotations] at H
    have HCh : Ch^(P.live.factors.length+1)=Ch^(aDegree+1):=by rw [hlen]
    have HCl : Cl^(P.live.factors.length+1)=Cl^(aDegree+1):=by rw [hlen]
    simp only [HCh,HCl] at H
    rw [native_actual_resource_G_restoration_eq_canonical_source hP hi hs ho M]
    convert H using 1
    dsimp only [G,R,f2,F1,F2,KH,KL,Mclock,as]
    ring
  have Hmajor : KH*F2+KL*(W*F1) ≤ C*(F2+W*F1):=by
    have H1:=mul_nonneg (show 0 ≤ C-KH by dsimp only [C];linarith) hF2
    have H2:=mul_nonneg (show 0 ≤ C-KL by dsimp only [C];linarith) (mul_nonneg hW hF1)
    nlinarith
  have Hlive':=Hlive.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left Hmajor hW) hscale)
  have Hprice : 0 ≤ C*W*(F2+W*F1):=by positivity
  apply actual_resource_Ga_restoration_normalized_profile_le M hP hdepth ho hi hstar
    hA hx hxW hε hε1 Hprice Hpair
  apply Hlive'.trans_eq
  ring

end OAI.SKFluctuations.Cavity
