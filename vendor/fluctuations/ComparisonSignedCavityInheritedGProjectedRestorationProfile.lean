module

public import ComparisonSignedCavityGProjectedRestorationSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

 theorem eventually_actual_minimum_inherited_canonical_G_projected_restoration_profile
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(star U : ℕ) (T : ClockTree (Spin n×Bool) as),star < U → U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀s : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
          let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
          |nativeOriginalGProjectedDisplacementRestoration T s star U q b h K S
            (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
            (G.canonicalMinimumSource M forms).restProduct| ≤
            (4*((rBound:ℝ)+1)+1)*
              (2*AH*(T.forkCost f2+edgeBudget 0 as f2)+2*AL*(T.forkCost R+edgeBudget 0 as R)) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_unbonded_low_G_pair_restoration
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro star U T hs hU hT G forms initial x W hxsx hxW hcut hmass s
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*(W*sourceMonomialScale x W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*(W*sourceMonomialScale x W initial)
  let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
  let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
  let g:=nativeFreshAtSlot T 0 s star
  let A:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let P:=(G.canonicalMinimumSource M forms).restProduct
  let E:=fun p : MarkedPlacement g.tree=>nativeOriginalHighPairRestoration n q U b h K S p.tree
    (nativeRestProjectedDisplacementTest T s star A P p) (p.embed (g.embed s)) p.mark
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 < W:=(M.hxs.trans_le hxsx).trans_le hxW
  have hscale : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hCH : 0 ≤ CH:=by dsimp [CH];positivity
  have hCL : 0 ≤ CL:=by dsimp [CL];positivity
  have hAH : 0 ≤ AH:=by
    dsimp only [AH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pairForkVariation_nonneg _) hCH) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)) (by positivity)) (pairForkVariation_nonneg _)
  have hAL : 0 ≤ AL:=mul_nonneg (mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL)
    (by positivity)) (pairForkVariation_nonneg _)
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by dsimp only [f2];rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)];ring
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HE (p0 : MarkedPlacement g.tree) (hp0 : p0∈g.tree.markedAttach 0) :
      |E p0| ≤ 2*AH*(p0.tree.forkCost f2+edgeBudget 0 as f2)+2*AL*(p0.tree.forkCost R+edgeBudget 0 as R) := by
    by_cases hhigh : U ≤ p0.tree.splitIndex (p0.embed (g.embed s)) p0.mark
    · let GP:=(G.nativeCMarkedLift g (nativeFreshAtSlot_mem T 0 s star)).nativeCMarkedLift p0 hp0
      have hGP e : GP.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e:=by
        simpa only [GP,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hleaf : p0.tree.leaves ≤ rBound+2:=by
        have H1:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s star)
        have H2:=g.tree.markedAttach_leaves 0 p0 hp0
        omega
      have Hsplits:=native_fresh_observed_endpoint_splits T s hs hU p0 hp0 hhigh
      have hsplit1 : p0.tree.splitIndex (p0.embed g.mark) p0.mark=star:=Hsplits.1
      have hsplit2 : p0.tree.splitIndex (p0.embed g.mark) (p0.embed (g.embed s))=star:=Hsplits.2
      have hsplit1' : p0.tree.splitIndex p0.mark (p0.embed g.mark)=star:=by
        rw [p0.tree.splitIndex_symm,hsplit1]
      have hsplit2' : p0.tree.splitIndex (p0.embed (g.embed s)) (p0.embed g.mark)=star:=by
        rw [p0.tree.splitIndex_symm,hsplit2]
      have hdistinct1 : p0.mark≠p0.embed g.mark:=by
        intro Hsame
        have HH:=Hsplits.1
        rw [←Hsame,p0.tree.splitIndex_self] at HH
        omega
      have hdistinct2 : p0.embed (g.embed s)≠p0.embed g.mark:=by
        intro Hsame
        have HH:=Hsplits.2
        rw [Hsame,p0.tree.splitIndex_self] at HH
        omega
      let J1:=fun σ : p0.tree.cavityLeft.Assignment=>(GP.canonicalMinimumSource M forms).restProduct σ*
        (A (p0.tree.cavityLeft.atSlot σ (p0.tree.cavityLeftSlot p0.mark))
          (p0.tree.cavityLeft.atSlot σ (p0.tree.cavityLeftSlot (p0.embed g.mark)))-S star)
      let J2:=fun σ : p0.tree.cavityLeft.Assignment=>(GP.canonicalMinimumSource M forms).restProduct σ*
        (A (p0.tree.cavityLeft.atSlot σ (p0.tree.cavityLeftSlot (p0.embed (g.embed s))))
          (p0.tree.cavityLeft.atSlot σ (p0.tree.cavityLeftSlot (p0.embed g.mark)))-S star)
      have H1:=hgrid U p0.tree hU hleaf GP forms initial x W hxsx hxW hcut hGP
        p0.mark (p0.embed g.mark) (p0.embed (g.embed s)) p0.mark hdistinct1
        (by rw [hsplit1'];exact hs)
      have H2:=hgrid U p0.tree hU hleaf GP forms initial x W hxsx hxW hcut hGP
        (p0.embed (g.embed s)) (p0.embed g.mark) (p0.embed (g.embed s)) p0.mark hdistinct2
        (by rw [hsplit2'];exact hs)
      have Hsource:=native_canonical_G_projected_displacement_source G M forms s star p0 hp0 S
      change nativeRestProjectedDisplacementTest T s star A P p0=(fun σ=>J1 σ-J2 σ) at Hsource
      have HL:=native_original_high_pair_restoration_test_linear n q U b h K S p0.tree ho
        J1 J2 (p0.embed (g.embed s)) p0.mark 1 (-1)
        (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
        (fun i=>by cases i <;> first | exact hbm | exact hhm)
        (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
      dsimp only [E]
      rw [Hsource]
      have HL' : nativeOriginalHighPairRestoration n q U b h K S p0.tree (fun σ=>J1 σ-J2 σ)
          (p0.embed (g.embed s)) p0.mark=
          nativeOriginalHighPairRestoration n q U b h K S p0.tree J1 (p0.embed (g.embed s)) p0.mark-
          nativeOriginalHighPairRestoration n q U b h K S p0.tree J2 (p0.embed (g.embed s)) p0.mark:=by
        simpa only [one_mul,neg_one_mul,←sub_eq_add_neg] using HL
      rw [HL',sub_eq_add_neg]
      apply (abs_add_le _ _).trans
      rw [abs_neg]
      have H1' : |nativeOriginalHighPairRestoration n q U b h K S p0.tree J1 (p0.embed (g.embed s)) p0.mark| ≤
          AH*(p0.tree.forkCost f2+edgeBudget 0 as f2)+AL*(p0.tree.forkCost R+edgeBudget 0 as R):=by
        convert H1 using 1 <;> dsimp only [J1,A,CH,CL,AH,AL,Mclock,R,f2] <;>
          (try simp only [hsplit1']) <;> push_cast <;> ring
      have H2' : |nativeOriginalHighPairRestoration n q U b h K S p0.tree J2 (p0.embed (g.embed s)) p0.mark| ≤
          AH*(p0.tree.forkCost f2+edgeBudget 0 as f2)+AL*(p0.tree.forkCost R+edgeBudget 0 as R):=by
        convert H2 using 1 <;> dsimp only [J2,A,CH,CL,AH,AL,Mclock,R,f2] <;>
          (try simp only [hsplit2']) <;> push_cast <;> ring
      exact (add_le_add H1' H2').trans_eq (by ring)
    · dsimp only [E]
      rw [native_original_high_pair_restoration_cross_zero n q U b h K S p0.tree ho
        _ (p0.embed (g.embed s)) p0.mark (lt_of_not_ge hhigh)
        (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
        (fun i=>by cases i <;> first | exact hbm | exact hhm)
        (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm,abs_zero]
      exact add_nonneg (mul_nonneg (by positivity) (add_nonneg (p0.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
        (mul_nonneg (by positivity) (add_nonneg (p0.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  exact native_current_restoring_rows_two_profiles_le T ho s hs hT f2 R hf2 hR hf2lo hRlo E
    (by positivity) (by positivity) HE

end OAI.SKFluctuations.Cavity
