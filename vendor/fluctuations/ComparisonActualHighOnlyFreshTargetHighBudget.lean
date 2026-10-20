module

public import ComparisonActualHighOnlyOriginalTaylorProfiles
public import ComparisonSignedCavityTransientForkCost

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 34000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
theorem eventually_actual_regular_target_constant_fresh_HIGH_parts_whole_budget_high_only
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
        M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ),i < U → U ≤ as.length →
        ∀x : ℝ,M.xs ≤ x → x ≤ 1 → partitionPoint 0 as U ≤ Ccut*x →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) i
          ∀(a z : g.tree.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
            |nativeActualHigherHighPart part n q U b h K g.tree (fun _=>1) a z l t| ≤
              C*x*edgeBudget 0 as (nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp) := by
  let p : ℝ:=4
  let dOrder : ℕ:=2
  have hp : 2<p:=by norm_num [p]
  have hd : 0<dOrder:=by norm_num [dOrder]
  have hOrder : p/(p-2)≤(dOrder:ℝ):=by norm_num [p,dOrder]
  obtain ⟨C,hC,Hparts⟩:=eventually_actual_minimum_inherited_constant_HIGH_parts_profile_high_only
    (D:=D) 2 dOrder hd p hp hOrder Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,hC.trans_le (by linarith),?_⟩
  filter_upwards [Hparts] with n hnParts
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnParts M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hjParts
  dsimp only at hjParts ⊢
  intro i U hs hU x hxsx hx1 hcutup seedMass a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) i
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  have hg : g.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves seedMass _
      (nativeFreshAtSlot_mem (single as) seedMass (singleSlot as) i)
    simpa only [g,single_leaves_exact] using H
  have hlo j (hj : j < U) : R j=0:=by
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have HF1 : g.tree.forkCost R=0:=native_initial_seed_high_forkCost as seedMass hs R hlo
  have HF2 : g.tree.forkCost (fun j=>(R j)^(4/p))=0:=by
    apply native_initial_seed_high_forkCost as seedMass hs
    intro j hj
    rw [hlo j hj,Real.zero_rpow (by positivity : (4:ℝ)/p≠0)]
  have hx : 0<x:=M.hxs.trans_le hxsx
  have H:=hjParts U g.tree hU hg x hxsx hx1 hcutup a z l t hl ht part
  change |nativeActualHigherHighPart part n _ U _ _ _ g.tree (fun _=>1) a z l t| ≤
    C*x*(g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
      x*(g.tree.forkCost R+edgeBudget 0 as R)) at H
  rw [HF1,HF2,zero_add,zero_add] at H
  have HR1 : (fun j=>(R j)^(4/p))=R:=by funext j;norm_num [p]
  rw [HR1] at H
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have HE0:=edgeBudget_nonneg ho hR
  have Hx:=mul_le_mul_of_nonneg_right hx1 HE0
  have HH:=mul_le_mul_of_nonneg_left (add_le_add (le_refl (edgeBudget 0 as R)) Hx) (show 0≤C*x by positivity)
  apply H.trans (HH.trans_eq _)
  dsimp only [R]
  ring

theorem eventually_actual_regular_target_constant_fresh_C_two_HIGH_whole_budget_high_only
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
        M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
        ∀x : ℝ,M.xs≤x → x≤1 → partitionPoint 0 as U ≤ Ccut*x →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,g.tree.splitIndex a z<U →
            |nativeCenteredLowGammaHighSecondRemainder n q U b h K
              (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) g.tree (fun _=>1) a z| ≤
              C*x*edgeBudget 0 as (nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp) := by
  let p : ℝ:=4
  let dOrder : ℕ:=2
  have hp : 2<p:=by norm_num [p]
  have hd : 0<dOrder:=by norm_num [dOrder]
  have hOrder : p/(p-2)≤(dOrder:ℝ):=by norm_num [p,dOrder]
  obtain ⟨Cp,hCp,Hparts⟩:=eventually_actual_minimum_inherited_canonical_C_two_high_profile_budget_high_only
    (D:=D) 0 dOrder 2 hd p hp hOrder Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mc:=4*Cf+2*Temp
  let Cjet:=pairForkVariation 4*pairForkVariation 6*
    (Real.exp (wholeLawRowComparisonConstant 4*Mc)*Cp)*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*pairForkVariation 2
  have hCjet : 0≤Cjet:=by
    dsimp only [Cjet]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pairForkVariation_nonneg _) (pairForkVariation_nonneg _)) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _))
      (pairForkVariation_nonneg _)
  let C:=Cjet+1
  have hC : 0<C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts] with n hnParts
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnParts M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hjParts
  dsimp only at hjParts ⊢
  intro star U hs hU x hxsx hx1 hcutup seedMass a z haz
  let as:=finiteCutMasses us jGrid
  let W:=x
  have hW : 0<W:=M.hxs.trans_le hxsx
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hg : g.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves seedMass _
      (nativeFreshAtSlot_mem (single as) seedMass (singleSlot as) star)
    simpa only [g,single_leaves_exact] using H
  have hlo j (hj : j < U) : R j=0:=by
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have HF1 : g.tree.forkCost R=0:=native_initial_seed_high_forkCost as seedMass hs R hlo
  have HF2 : g.tree.forkCost (fun j=>(R j)^(4/p))=0:=by
    apply native_initial_seed_high_forkCost as seedMass hs
    intro j hj
    rw [hlo j hj,Real.zero_rpow (by positivity : (4:ℝ)/p≠0)]
  let G : ActualNaturalBoundaryShape n 0 g.tree:=
    ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,(fun e=>Fin.elim0 e),(fun e=>Fin.elim0 e)⟩
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have HP : (G.canonicalHighOnlySource M forms).restProduct=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have H:=hjParts U g.tree hU hg G forms ∅ W hxsx
    hcutup (fun e=>Fin.elim0 e) a z haz
  rw [HP] at H
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] at H
  norm_num only [Nat.reduceAdd,pow_one] at H
  have Hnew : |nativeCenteredLowGammaHighSecondRemainder n q U b h K S g.tree (fun _=>1) a z| ≤
    pairForkVariation 4*pairForkVariation 6*(Real.exp (wholeLawRowComparisonConstant 4*Mc)*Cp*W)*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*pairForkVariation 2*
    (g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))) := by
    convert H using 1 <;> norm_num [p,Mc,R,as] <;> rfl
  have H:=Hnew
  rw [HF2,zero_add] at H
  have HR1 : (fun j=>(R j)^(4/p))=R:=by funext j;norm_num [p]
  rw [HR1] at H
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have HE0:=edgeBudget_nonneg (finiteCutMasses_ordered us hus jGrid) hR
  have Hsaved : |nativeCenteredLowGammaHighSecondRemainder n q U b h K S g.tree (fun _=>1) a z|≤
      Cjet*x*edgeBudget 0 as R:=by
    apply H.trans_eq
    dsimp only [Cjet,Mc,W]
    ring
  exact Hsaved.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by dsimp only [C];linarith : Cjet≤C) hW.le)
    HE0)

theorem eventually_actual_regular_target_constant_fresh_FOUR_G_LOW_whole_budget_high_only
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
        M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
        ∀x : ℝ,M.xs≤x → x≤1 → partitionPoint 0 as U ≤ Ccut*x →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,
            |nativeOriginalGKernelLowRestoration n q U b h K
              (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) g.tree (fun _=>1) a z
              (restCenteredLowKernel n U b (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)))| ≤
              C*x*edgeBudget 0 as (nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp) := by
  let p : ℝ:=4
  let dOrder : ℕ:=2
  have hp : 2<p:=by norm_num [p]
  have hd : 0<dOrder:=by norm_num [dOrder]
  have hOrder : p/(p-2)≤(dOrder:ℝ):=by norm_num [p,dOrder]
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,Hparts⟩:=eventually_actual_minimum_inherited_canonical_four_G_low_restoration_high_only
    (D:=D) 0 dOrder 2 hd p hp hOrder Bclock Temp Cf 0 Ccut hTemp hCf (by norm_num) hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mc:=4*Cf+2*Temp
  let Kh:=2*pairForkVariation 6*(Real.exp (wholeLawRowComparisonConstant 6*Mc)*Ch)*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*7*pairForkVariation 4*pairForkVariation 2
  let Kl:=2*absJetVariation 6 1*(Real.exp (wholeLawRowComparisonConstant 6*Mc)*Cl)*
    (Cq*(1+Ccut))*pairForkVariation 4*pairForkVariation 2
  have hKh : 0≤Kh:=by
    dsimp only [Kh]
    have H6:=pairForkVariation_nonneg 6
    have H4:=pairForkVariation_nonneg 4
    have H2:=pairForkVariation_nonneg 2
    positivity
  have hKl : 0≤Kl:=by
    dsimp only [Kl]
    have H6:=absJetVariation_nonneg 6 1
    have H4:=pairForkVariation_nonneg 4
    have H2:=pairForkVariation_nonneg 2
    positivity
  let C:=Kh+Kl+1
  have hC : 0<C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts] with n hnParts
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hnParts M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hjParts
  dsimp only at hjParts ⊢
  intro star U hs hU x hxsx hx1 hcutup seedMass a z
  let as:=finiteCutMasses us jGrid
  let W:=x
  have hx : 0<x:=M.hxs.trans_le hxsx
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hg : g.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves seedMass _
      (nativeFreshAtSlot_mem (single as) seedMass (singleSlot as) star)
    simpa only [g,single_leaves_exact] using H
  have hlo j (hj : j < U) : R j=0:=by
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have HF1 : g.tree.forkCost R=0:=native_initial_seed_high_forkCost as seedMass hs R hlo
  have HF2 : g.tree.forkCost (fun j=>(R j)^(4/p))=0:=by
    apply native_initial_seed_high_forkCost as seedMass hs
    intro j hj
    rw [hlo j hj,Real.zero_rpow (by positivity : (4:ℝ)/p≠0)]
  let G : ActualNaturalBoundaryShape n 0 g.tree:=
    ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,(fun e=>Fin.elim0 e),(fun e=>Fin.elim0 e)⟩
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have HP : (G.canonicalHighOnlySource M forms).restProduct=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have H:=hjParts U g.tree hU hg G forms ∅ W hxsx
    hcutup (fun e=>Fin.elim0 e) a z
  rw [HP] at H
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] at H
  norm_num only [Nat.reduceAdd,pow_one,Nat.cast_ofNat] at H
  let f2:=fun j=>((R j)^(2/p))^2
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hf : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    change ((R j)^(2/p))^2=(R j)^(4/p)
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hprofile : |nativeOriginalGKernelLowRestoration n q U b h K S g.tree (fun _=>1) a z (restCenteredLowKernel n U b S)|≤
      Kh*W*(g.tree.forkCost f2+edgeBudget 0 as f2)+Kl*W^2*(g.tree.forkCost R+edgeBudget 0 as R):=by
    convert H using 1
    · rfl
    · dsimp only [Kh,Kl,Mc,f2,R,W,as]
      norm_num [p]
      ring
  rw [Hf,HF1,HF2,zero_add,zero_add] at Hprofile
  have HR1 : (fun j=>(R j)^(4/p))=R:=by funext j;norm_num [p]
  rw [HR1] at Hprofile
  have HE0:=edgeBudget_nonneg (finiteCutMasses_ordered us hus jGrid) hR
  have HX : W^2≤W:=by dsimp only [W];nlinarith only [hx.le,hx1]
  have Hlo:=mul_le_mul_of_nonneg_right HX (mul_nonneg hKl HE0)
  have Hextra : 0≤W*edgeBudget 0 as R:=mul_nonneg hx.le HE0
  have Hpaid : Kh*W*edgeBudget 0 as R+Kl*W^2*edgeBudget 0 as R≤C*x*edgeBudget 0 as R:=by
    dsimp only [C,W] at Hlo Hextra ⊢
    nlinarith only [Hlo,Hextra]
  exact Hprofile.trans Hpaid

theorem eventually_actual_regular_target_constant_longitudinal_restoration_whole_budget_high_only
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
        M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),i<U → U≤as.length → M.xs≤x → x≤1 → partitionPoint 0 as U≤Ccut*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        ∀a : g.tree.Slot,
          |nativeOriginalLongitudinalRestoration n q U b h K S g.tree (fun _=>1) a|≤
            C*edgeBudget 0 as (nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp) := by
  let p : ℝ:=4
  let dOrder : ℕ:=2
  have hp : 2<p:=by norm_num [p]
  have hd : 0<dOrder:=by norm_num [dOrder]
  have hOrder : p/(p-2)≤(dOrder:ℝ):=by norm_num [p,dOrder]
  obtain ⟨Cq,hCq,HP⟩:=eventually_actual_minimum_inherited_constant_longitudinal_restoration_profile_high_only
    (D:=D) 2 p hp Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ch:=pairForkVariation 5*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*nativeOriginalRestorationProfileVariation 2
  let Cl:=absJetVariation 5 1*Cq*forkVariation 2 3
  have hCh : 0≤Ch:=by
    dsimp only [Ch]
    have :=pairForkVariation_nonneg 5
    have :=nativeOriginalRestorationProfileVariation_nonneg 2
    positivity
  have hCl : 0≤Cl:=by
    dsimp only [Cl]
    have :=absJetVariation_nonneg 5 1
    have :=forkVariation_nonneg 2 3
    positivity
  let C:=Ch+Cl+1
  have hC : 0<C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs HS hxs1 L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs HS hxs1 L us hus hret hmesh] with jGrid hpnet
  dsimp only at hpnet ⊢
  intro i U x hi hU hxsx hx1 hcut a
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  have hx : 0<x:=M.hxs.trans_le hxsx
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [single_leaves_exact] using H
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 : (fun j=>((R j)^(2/p))^2)=(fun j=>(R j)^(4/p)):=by
    funext j
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have HF : g.tree.forkCost R=0:=native_initial_seed_high_forkCost as 0 hi R
    (by intro j hj;simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true])
  have HF2 : g.tree.forkCost (fun j=>(R j)^(4/p))=0:=by
    apply native_initial_seed_high_forkCost as 0 hi
    intro j hj
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true,Real.zero_rpow (by positivity : (4:ℝ)/p≠0)]
  have H:=hpnet U g.tree hU hg x hxsx hcut a
  change _≤Ch*(g.tree.forkCost (fun j=>((R j)^(2/p))^2)+edgeBudget 0 as (fun j=>((R j)^(2/p))^2))+
    (absJetVariation 5 1*(Cq*x))*forkVariation 2 3*(g.tree.forkCost R+edgeBudget 0 as R) at H
  rw [hf2,HF,HF2,zero_add,zero_add] at H
  have HR1 : (fun j=>(R j)^(4/p))=R:=by funext j;norm_num [p]
  rw [HR1] at H
  have HE0:=edgeBudget_nonneg ho hR
  have Hx:=mul_le_mul_of_nonneg_right hx1 HE0
  have Hp1:=mul_le_mul_of_nonneg_left Hx hCl
  have Hp2 : 0≤edgeBudget 0 as R:=HE0
  have Hp3 : 0≤(edgeBudget 0 as R):=HE0
  have Hpaid : Ch*edgeBudget 0 as R+
      (absJetVariation 5 1*(Cq*x))*forkVariation 2 3*edgeBudget 0 as R≤C*edgeBudget 0 as R:=by
    dsimp only [C,Cl] at Hp1 ⊢
    nlinarith only [Hp1,Hp2]
  exact H.trans Hpaid

end OAI.SKFluctuations.Cavity
