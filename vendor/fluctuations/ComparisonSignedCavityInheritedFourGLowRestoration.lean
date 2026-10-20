module

public import ComparisonSignedCavityInheritedBondedLowGPairRestoration
public import ComparisonSignedCavityLowFactorGInsertedRestSource
public import ComparisonSignedCavityOriginalZeroRestoration
public import ComparisonSignedCavityActualOriginalGLowAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 22000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_canonical_four_G_low_restoration
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale M.xs W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale M.xs W initial)
          let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
          let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
          |nativeOriginalGKernelLowRestoration n q U b h K S T
            (G.canonicalMinimumSource M forms).restProduct a z (restCenteredLowKernel n U b S)|≤
            2*AH*pairForkVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
              2*AL*pairForkVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_low_factor_G_pair_restoration
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial W hxW hcut hmass a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale M.xs W initial)
  let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    ((rBound:ℝ)+5)*pairForkVariation (rBound+2)
  let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
  let P:=(G.canonicalMinimumSource M forms).restProduct
  let A:=restCenteredLowKernel n U b S
  let F:=fun (p0 : MarkedPlacement T) (r : MarkedPlacement p0.tree)=>
    fullScalarCutGamma r.tree U K (r.embed (p0.embed z)) r.mark*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed a)) (r.embed p0.mark)+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed z)) (r.embed p0.mark)*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed a)) r.mark+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed a)) (r.embed p0.mark)*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed z)) r.mark+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed a)) r.mark*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed z)) (r.embed p0.mark)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hscale : 0 ≤ sourceMonomialScale M.xs W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have hCH : 0≤CH:=by dsimp [CH];positivity
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hAH : 0≤AH:=by
    dsimp only [AH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pairForkVariation_nonneg _) hCH) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)) (by positivity)) (pairForkVariation_nonneg _)
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL)
    (by positivity)) (pairForkVariation_nonneg _)
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0≤f2 j:=sq_nonneg _
  have HF (p0 : MarkedPlacement T) (hp0 : p0∈T.markedAttach 0)
      (r : MarkedPlacement p0.tree) (hr : r∈p0.tree.markedAttach 0) :
      |F p0 r|≤4*AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+4*AL*(r.tree.forkCost R+edgeBudget 0 as R) := by
    let B:=AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+AL*(r.tree.forkCost R+edgeBudget 0 as R)
    have hB : 0≤B:=add_nonneg (mul_nonneg hAH (add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
      (mul_nonneg hAL (add_nonneg (r.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
    have Hpair (x y : r.tree.Slot) :
        |nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r) x y|≤B:=by
      by_cases hlow : r.tree.splitIndex (r.embed p0.mark) r.mark<U
      · have hcd : r.embed p0.mark≠r.mark:=by
          intro HH
          rw [HH,r.tree.splitIndex_self] at hlow
          omega
        let Gr:=(G.nativeCMarkedLift p0 hp0).nativeCMarkedLift r hr
        have hGr e : Gr.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e:=by
          simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
        have hleaf : r.tree.leaves≤rBound+2:=by
          have H1:=T.markedAttach_leaves 0 p0 hp0
          have H2:=p0.tree.markedAttach_leaves 0 r hr
          omega
        rw [show insertedRestTest P A p0 r=_ from G.native_inserted_canonical_low_rest_test M forms U b S p0 hp0 r hr hlow]
        have Hinner:=hgrid U r.tree hU hleaf Gr forms initial W hxW hcut hGr
          (r.embed p0.mark) r.mark x y hcd hlow
        convert Hinner using 1
        dsimp only [B,AH,AL,CH,CL,R,f2,Mclock,Gr]
        push_cast
        ring
      · have Hzero : ∀σ,insertedRestTest P A p0 r σ=0:=by
          intro σ
          simp only [insertedRestTest,A,restCenteredLowKernel,hlow,ite_false,mul_zero]
        rw [actual_minimum_original_high_pair_restoration_zero_payload M r.tree ho U _ Hzero x y,abs_zero]
        exact hB
    have Hterm (x y x' y' : r.tree.Slot) :
        |fullScalarCutGamma r.tree U K x y*
          nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r) x' y'|≤B:=by
      rw [abs_mul]
      have Hgam:=native_full_scalar_cut_moment_abs_le_one r.tree ho U K [x,y]
      exact (mul_le_mul Hgam (Hpair x' y') (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
    have H1:=Hterm (r.embed (p0.embed z)) r.mark (r.embed (p0.embed a)) (r.embed p0.mark)
    have H2:=Hterm (r.embed (p0.embed z)) (r.embed p0.mark) (r.embed (p0.embed a)) r.mark
    have H3:=Hterm (r.embed (p0.embed a)) (r.embed p0.mark) (r.embed (p0.embed z)) r.mark
    have H4:=Hterm (r.embed (p0.embed a)) r.mark (r.embed (p0.embed z)) (r.embed p0.mark)
    have Hsum : |F p0 r|≤4*B:=by
      dsimp only [F]
      exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add H1 H2)) H3)) H4)).trans_eq (by ring)
    simpa only [B,mul_add,mul_assoc] using Hsum
  have Hsum:=(T.signedPair_abs_le_pairAbsSum F).trans (T.pairAbsSum_mono HF)
  rw [T.pairAbsSum_add,T.pairAbsSum_const_mul (4*AH),T.pairAbsSum_const_mul (4*AL)] at Hsum
  have HH:=T.pairAbsSum_forkBudget_le ho hT hf2 (d:=0) (by norm_num)
  have HL:=T.pairAbsSum_forkBudget_le ho hT hR (d:=0) (by norm_num)
  simp only [add_zero] at HH HL
  have HX:=Hsum.trans (add_le_add (mul_le_mul_of_nonneg_left HH (mul_nonneg (by norm_num) hAH))
    (mul_le_mul_of_nonneg_left HL (mul_nonneg (by norm_num) hAL)))
  change |_/2|≤_
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  change |((T.markedAttach 0).map (fun p0=>p0.coeff*
    ((p0.tree.markedAttach 0).map (fun r=>r.coeff*F p0 r)).sum)).sum|/2≤_
  dsimp only [AH,AL,CH,CL,R,f2,q,b,h,K,S,Mclock,as] at HX ⊢
  nlinarith only [HX]

end OAI.SKFluctuations.Cavity
