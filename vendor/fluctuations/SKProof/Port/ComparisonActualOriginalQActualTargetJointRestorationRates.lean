module

public import SKProof.Port.ComparisonActualOriginalQPullbackFourProducers
public import SKProof.Port.ComparisonActualOriginalQTargetHighTailPowers
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetReadout
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetB0
public import SKProof.Port.ComparisonActualOriginalQOriginalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQCavityCategoryReduction

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.ActualThetaZeroOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_regular_target_constant_fresh_C_two_HIGH_rate_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h M.data.rmin 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.data.d M.lam M.xs → M.directTestWorkingScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.directTestWorkingScale
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
        ∀x : ℝ,M.xs≤x → x≤W →
          2*c*x ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*x →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,g.tree.splitIndex a z<U →
            |nativeCenteredLowGammaHighSecondRemainder n q U b h K
              (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)) g.tree (fun _=>1) a z| ≤
              C*M.data.N^(-(actualMassSavingExponent m delta/256))*x^3 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨Cp,hCp,Hparts⟩:=eventually_actual_minimum_inherited_canonical_C_two_high_profile_budget_original_q
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
  have Htail:=eventually_actual_regular_original_target_high_envelope_powers_original_q (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts,Htail] with n hnParts hnTail
  intro M hclock hs0 hsxs hs64 hsource hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnParts M hs0 hsxs hsource hxs1 L us hus hret hmesh,
    hnTail M hclock hs0 hsxs hs64 hsmall hW1 us hus] with jGrid hjParts hjTail
  dsimp only at hjParts hjTail ⊢
  intro star U hs hU x hxsx hxW hcutlo hcutup seedMass a z haz
  let as:=finiteCutMasses us jGrid
  let W:=x
  have hW : 0<W:=M.hxs.trans_le hxsx
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
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
  have HP : (G.canonicalOriginalQSource M forms).restProduct=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have H:=hjParts U g.tree hU hg G forms ∅ W hxsx
    hcutup (fun e=>Fin.elim0 e) a z haz
  rw [HP] at H
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] at H
  norm_num only [Nat.reduceAdd,pow_one] at H
  change |nativeCenteredLowGammaHighSecondRemainder n q U b h K S g.tree (fun _=>1) a z| ≤
    pairForkVariation 4*pairForkVariation 6*(Real.exp (wholeLawRowComparisonConstant 4*Mc)*Cp*W)*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*pairForkVariation 2*
    (g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))) at H
  rw [HF2,zero_add] at H
  have HE:=hjTail U hU ((mul_le_mul_of_nonneg_left hxsx (by positivity)).trans hcutlo) (4/p) htheta1 htheta2.le hdeficit
  have HE' : edgeBudget 0 as (fun j=>(R j)^(4/p))+M.directTestWorkingScale*edgeBudget 0 as R ≤
      M.data.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=HE
  have Hextra : 0≤M.directTestWorkingScale*edgeBudget 0 as R:=mul_nonneg M.canonical_direct_test_band_pos.le
    (edgeBudget_nonneg (finiteCutMasses_ordered us hus jGrid) (by
      intro j
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))))
  have HEtheta : edgeBudget 0 as (fun j=>(R j)^(4/p))≤
      M.data.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=by linarith only [HE',Hextra]
  have HH:=mul_le_mul_of_nonneg_left HEtheta (mul_nonneg hCjet (M.hxs.trans_le hxsx).le)
  have Hsaved : |nativeCenteredLowGammaHighSecondRemainder n q U b h K S g.tree (fun _=>1) a z|≤
      Cjet*M.data.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2:=by
    apply H.trans
    convert HH using 1 <;> dsimp only [Cjet,Mc] <;> ring
  have HC:=mul_le_mul_of_nonneg_right (show Cjet≤C by dsimp only [C];linarith)
    (show 0≤M.data.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2 by positivity)
  have Hscale:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ M.hxs.le hxsx 2)
    (show 0≤C*M.data.N^(-(actualMassSavingExponent m delta/256))*x by positivity)
  have HC' : Cjet*M.data.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2≤
      C*M.data.N^(-(actualMassSavingExponent m delta/256))*W*M.xs^2:=by
    simpa only [mul_assoc] using HC
  apply Hsaved.trans (HC'.trans _)
  convert Hscale using 1; ring

theorem eventually_actual_regular_target_constant_fresh_FOUR_G_LOW_rate_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h M.data.rmin 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.data.d M.lam M.xs → M.directTestWorkingScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.directTestWorkingScale
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(star U : ℕ),star < U → U ≤ as.length →
        ∀x : ℝ,M.xs≤x → x≤W →
          2*c*x ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*x →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
          ∀a z : g.tree.Slot,
            |nativeOriginalGKernelLowRestoration n q U b h K
              (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)) g.tree (fun _=>1) a z
              (restCenteredLowKernel n U b (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)))| ≤
              C*M.data.N^(-(actualMassSavingExponent m delta/256))*x^3 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,Hparts⟩:=eventually_actual_minimum_inherited_canonical_four_G_low_restoration_original_q
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
  have Htail:=eventually_actual_regular_original_target_high_envelope_powers_original_q (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts,Htail] with n hnParts hnTail
  intro M hclock hs0 hsxs hs64 hsource hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnParts M hs0 hsxs hsource hxs1 L us hus hret hmesh,
    hnTail M hclock hs0 hsxs hs64 hsmall hW1 us hus] with jGrid hjParts hjTail
  dsimp only at hjParts hjTail ⊢
  intro star U hs hU x hxsx hxW hcutlo hcutup seedMass a z
  let as:=finiteCutMasses us jGrid
  let W:=x
  have hx : 0<x:=M.hxs.trans_le hxsx
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) star
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
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
  have HP : (G.canonicalOriginalQSource M forms).restProduct=(fun _=>1):=by
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
      ring
  rw [Hf,HF1,HF2,zero_add,zero_add] at Hprofile
  have HE:=hjTail U hU ((mul_le_mul_of_nonneg_left hxsx (by positivity)).trans hcutlo) (4/p) htheta1 htheta2.le hdeficit
  have HE' : edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R ≤
      M.data.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=by
    have Hx:=mul_le_mul_of_nonneg_right hxW
      (edgeBudget_nonneg (finiteCutMasses_ordered us hus jGrid) hR)
    exact (add_le_add le_rfl Hx).trans HE
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Htheta0 : 0≤edgeBudget 0 as (fun j=>(R j)^(4/p)):=edgeBudget_nonneg ho
    (fun j=>Real.rpow_nonneg (hR j) _)
  have HE10 : 0≤edgeBudget 0 as R:=edgeBudget_nonneg ho hR
  have Hkh:=mul_le_mul_of_nonneg_right (show Kh≤C by dsimp only [C];linarith)
    (mul_nonneg (M.hxs.trans_le hxsx).le Htheta0)
  have Hkl:=mul_le_mul_of_nonneg_right (show Kl≤C by dsimp only [C];linarith)
    (mul_nonneg (sq_nonneg W) HE10)
  have Hpaid : |nativeOriginalGKernelLowRestoration n q U b h K S g.tree (fun _=>1) a z (restCenteredLowKernel n U b S)|≤
      C*W*(edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R):=by
    apply Hprofile.trans
    convert add_le_add Hkh Hkl using 1 <;> ring
  apply Hpaid.trans
  have HH:=mul_le_mul_of_nonneg_left HE' (mul_nonneg hC.le (M.hxs.trans_le hxsx).le)
  have Hscale:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ M.hxs.le hxsx 2)
    (show 0≤C*x*M.data.N^(-(actualMassSavingExponent m delta/256)) by positivity)
  apply HH.trans
  convert Hscale using 1 <;> ring

end OAI.SKFluctuations.Cavity
