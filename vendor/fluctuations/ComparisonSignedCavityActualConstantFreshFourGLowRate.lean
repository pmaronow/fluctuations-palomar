module

public import ComparisonSignedCavityInheritedFourGLowRestoration
public import ComparisonSignedCavityContinuumMixedClock
public import ComparisonNativeActualInheritedHighTailPowers
public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_shell_history_constant_fresh_FOUR_G_LOW_rate
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs → M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,
            |nativeOriginalGKernelLowRestoration n q U b h K
              (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) g.tree (fun _=>1) a z
              (restCenteredLowKernel n U b (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)))| ≤
              C*M.context.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,Hparts⟩:=eventually_actual_minimum_inherited_canonical_four_G_low_restoration
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
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts,Htail] with n hnParts hnTail
  intro M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnParts M hsource hxs1 L us hus hret hmesh,
    hnTail M Tbase epsilon shell ts hb hh hsmall hW1 us hus] with jGrid hjParts hjTail
  dsimp only at hjParts hjTail ⊢
  intro star U hs hU hcutlo hcutup seedMass a z
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
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
  have HP : (G.canonicalMinimumSource M forms).restProduct=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have H:=hjParts U g.tree hU hg G forms ∅ W M.canonical_direct_test_band_ge_scale
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
      ring
  rw [Hf,HF1,HF2,zero_add,zero_add] at Hprofile
  have HE:=hjTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have HE' : edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R ≤
      M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=HE
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Htheta0 : 0≤edgeBudget 0 as (fun j=>(R j)^(4/p)):=edgeBudget_nonneg ho
    (fun j=>Real.rpow_nonneg (hR j) _)
  have HE10 : 0≤edgeBudget 0 as R:=edgeBudget_nonneg ho hR
  have Hkh:=mul_le_mul_of_nonneg_right (show Kh≤C by dsimp only [C];linarith)
    (mul_nonneg M.canonical_direct_test_band_pos.le Htheta0)
  have Hkl:=mul_le_mul_of_nonneg_right (show Kl≤C by dsimp only [C];linarith)
    (mul_nonneg (sq_nonneg W) HE10)
  have Hpaid : |nativeOriginalGKernelLowRestoration n q U b h K S g.tree (fun _=>1) a z (restCenteredLowKernel n U b S)|≤
      C*W*(edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R):=by
    apply Hprofile.trans
    convert add_le_add Hkh Hkl using 1 <;> ring
  apply Hpaid.trans
  have HH:=mul_le_mul_of_nonneg_left HE' (mul_nonneg hC.le M.canonical_direct_test_band_pos.le)
  convert HH using 1; ring

end OAI.SKFluctuations.Cavity
