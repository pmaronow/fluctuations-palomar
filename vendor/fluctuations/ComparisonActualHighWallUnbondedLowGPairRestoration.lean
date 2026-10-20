module

public import ComparisonActualHighWallUnbondedLowGRestoration
public import ComparisonActualGeneralUnbondedLowGMarkedSource
public import ComparisonActualGeneralOriginalZeroRestoration
public import ComparisonSignedCavityOriginalHighProfileYoung
public import ComparisonSignedCavityActualOriginalGPairRestoration

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_high_wall_unbonded_low_G_pair_restoration
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e≤Cmass*M.data.d) →
        ∀u z a c : T.Slot,u≠z → T.splitIndex u z<U →
          let R:=M.data.highErrorEnvelope M.alpha as U
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Ch^(aDegree+1)*
            (M.data.d*M.data.d^aDegree)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cl^(aDegree+1)*
            (M.data.d*M.data.d^aDegree)
          let AH:=pairForkVariation (rBound+2)*CH*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*((rBound:ℝ)+3)
          let AL:=absJetVariation (rBound+2) 1*CL*(Cq*M.data.d)
          let J:=fun σ=>(G.canonicalHighWallSource M forms).restProduct σ*
            (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot u),false))
              (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false))-S (T.splitIndex u z))
          |nativeOriginalHighPairRestoration n q U b h K S T J a c|≤
            AH*pairForkVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
              AL*pairForkVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_high_wall_unbonded_low_G_restoration
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms hcut hmass u z a c huz huzcut
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=2*max Bclock 0
  let R:=M.data.highErrorEnvelope M.alpha as U
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Ch^(aDegree+1)*
    (M.data.d*M.data.d^aDegree)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cl^(aDegree+1)*
    (M.data.d*M.data.d^aDegree)
  let AH0:=pairForkVariation (rBound+2)*CH*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)
  let AH:=AH0*((rBound:ℝ)+3)
  let AL:=absJetVariation (rBound+2) 1*CL*(Cq*M.data.d)
  let J:=fun σ=>(G.canonicalHighWallSource M forms).restProduct σ*
    (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot u),false))
      (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false))-S (T.splitIndex u z))
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    nativeActualLawRestorationRemainder n q U b h K r.tree
      (fun σ=>J (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
        nativeOriginalHighGAtom r.tree U K b S (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark σ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ M.data.d:=M.data.hd.le
  have hscale : 0 ≤ M.data.d^aDegree:=pow_nonneg M.data.hd.le _
  have hTemp:=M.data.hTpos.le
  have hAH0 : 0≤AH0:=by
    dsimp only [AH0,CH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hAH : 0≤AH:=mul_nonneg hAH0 (by positivity)
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL) (by positivity)
  have hR j : 0≤R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (2*M.data.T) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0≤f2 j:=sq_nonneg _
  have HF (p0 : MarkedPlacement T) (hp0 : p0∈T.markedAttach 0)
      (r : MarkedPlacement p0.tree) (hr : r∈p0.tree.markedAttach 0) :
      |F p0 r|≤AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+AL*(r.tree.forkCost R+edgeBudget 0 as R) := by
    by_cases hdiag : r.embed p0.mark=r.mark
    · have Hzero:=actual_general_original_G_diagonal_restoration_zero M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) r.tree ho U
        (fun σ=>J (p0.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)))
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) r.mark
      dsimp only [F]
      rw [hdiag,Hzero,abs_zero]
      exact add_nonneg (mul_nonneg hAH (add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
        (mul_nonneg hAL (add_nonneg (r.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
    · let Gr:=(G.nativeCMarkedLift p0 hp0).nativeCMarkedLift r hr
      have hGr e : Gr.sourceLowMass e≤Cmass*M.data.d:=by
        simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hleaf : r.tree.leaves≤rBound+2:=by
        have H1:=T.markedAttach_leaves 0 p0 hp0
        have H2:=p0.tree.markedAttach_leaves 0 r hr
        omega
      have hlow : r.tree.splitIndex (r.embed (p0.embed u)) (r.embed (p0.embed z))<U:=by
        rwa [(p0.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p0 hp0).2]
      have hdistinct : r.embed (p0.embed u)≠r.embed (p0.embed z):=by
        intro HH
        exact huz ((T.markedAttach_embed_preserves 0 p0 hp0).1 ((p0.tree.markedAttach_embed_preserves 0 r hr).1 HH))
      have Hrest:=hgrid U r.tree hU hleaf Gr forms hcut hGr
        (r.embed (p0.embed u)) (r.embed (p0.embed z))
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark hdistinct hlow hdiag
      have Htest:=G.physical_double_marked_unbonded_low_pair_test M.bf M.hf forms S u z p0 hp0 r hr
      change |nativeActualLawRestorationRemainder n q U b h K r.tree _|≤_
      have Hleft:=congrArg (fun J0 : r.tree.Assignment→ℝ=>
        nativeActualLawRestorationRemainder n q U b h K r.tree
          (fun σ=>J0 σ*nativeOriginalHighGAtom r.tree U K b S (r.embed (p0.embed a))
            (r.embed (p0.embed c)) (r.embed p0.mark) r.mark σ)) Htest
      rw [Hleft]
      apply Hrest.trans
      let ff:=fun j=>(R j)^(2/p)
      have hff j : 0≤ff j:=Real.rpow_nonneg (hR j) _
      have HY:=native_distinct_pair_profile_product_le r.tree ho ff (r.embed p0.mark) r.mark hdiag
      have HS:=r.tree.split_le_forkCost hR (r.embed p0.mark) r.mark hdiag
      have HE:=edgeBudget_nonneg ho hR
      have HP:=add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
      have hleafr : (r.tree.leaves:ℝ)+1≤(rBound:ℝ)+3:=by exact_mod_cast (by omega : r.tree.leaves+1≤rBound+3)
      have Hκ:=native_full_scalar_connected_four_abs_le_two r.tree ho U K
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark
      have Hκ' : |(1/2:ℝ)*fullScalarCutConnected4 r.tree U K
          (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark|≤1:=by
        rw [abs_mul]
        norm_num only [abs_of_nonneg (show (0:ℝ)≤1/2 by norm_num)]
        linarith
      have Hprod:=mul_le_mul_of_nonneg_left HY hAH0
      have Hleaf:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleafr hAH0) HP
      have Hlow:=mul_le_mul_of_nonneg_left (HS.trans (le_add_of_nonneg_right HE)) hAL
      have Hnonneg : 0≤AH0*(ff (r.tree.splitIndex (r.embed p0.mark) r.mark)*
          (r.tree.forkCost ff+edgeBudget 0 as ff))+AL*R (r.tree.splitIndex (r.embed p0.mark) r.mark):=by
        exact add_nonneg (mul_nonneg hAH0 (mul_nonneg (hff _)
          (add_nonneg (r.tree.forkCost_nonneg hff) (edgeBudget_nonneg ho hff)))) (mul_nonneg hAL (hR _))
      have Hscalar:=mul_le_of_le_one_left Hnonneg Hκ'
      dsimp only [Gr,CH,CL,AH0,AH,AL,R,ff,f2,Mclock] at Hprod Hleaf Hlow Hscalar ⊢
      nlinarith only [Hprod,Hleaf,Hlow,Hscalar]
  have Hsum:=(T.signedPair_abs_le_pairAbsSum F).trans (T.pairAbsSum_mono HF)
  rw [T.pairAbsSum_add,T.pairAbsSum_const_mul AH,T.pairAbsSum_const_mul AL] at Hsum
  have HH:=T.pairAbsSum_forkBudget_le ho hT hf2 (d:=0) (by norm_num)
  have HL:=T.pairAbsSum_forkBudget_le ho hT hR (d:=0) (by norm_num)
  simp only [add_zero] at HH HL
  have HB:=add_le_add (mul_le_mul_of_nonneg_left HH hAH) (mul_le_mul_of_nonneg_left HL hAL)
  apply Hsum.trans
  convert HB using 1
  dsimp only [F,J,AH,AH0,AL,CH,CL,R,f2,q,b,h,K,S,Mclock,as,nativeOriginalHighPairRestoration]
  ring

end OAI.SKFluctuations.Cavity
