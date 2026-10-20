module

public import ComparisonActualHighOnlyPullbackFourProducers
public import ComparisonActualHighOnlyTargetHighTailPowers
public import ComparisonActualHighOnlyOriginalTargetReadout
public import ComparisonActualHighOnlyOriginalTargetB0
public import ComparisonActualHighOnlyOriginalTaylorProfiles
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyCavityCategoryReduction

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighOnlyOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_regular_target_constant_longitudinal_restoration_rate_high_only
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,
      ∀(M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf →
        M.xs^2≤Cs*laplaceComparisonStrength M.context.d M.lam M.xs → M.canonicalDirectTestBandScale≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),i<U → U≤as.length → M.xs≤x → x≤M.canonicalDirectTestBandScale →
          2*c*x≤partitionPoint 0 as U → partitionPoint 0 as U≤Ccut*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        ∀a : g.tree.Slot,
          |nativeOriginalLongitudinalRestoration n q U b h K S g.tree (fun _=>1) a|≤
            C*M.context.N^(-(actualMassSavingExponent m delta/256))*x^2 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
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
  have HT:=eventually_actual_regular_original_target_high_envelope_powers_high_only (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [HP,HT] with n hnP hnT
  intro M hclock hs0 hsxs hs64 HS hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnP M hs0 hsxs HS hxs1 L us hus hret hmesh,hnT M hclock hs0 hsxs hs64 hsmall hW1 us hus]
    with jGrid hpnet htnet
  dsimp only at hpnet htnet ⊢
  intro i U x hi hU hxsx hxW hcutlo hcut a
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
  have HE:=htnet U hU ((mul_le_mul_of_nonneg_left hxsx (by positivity)).trans hcutlo)
    (4/p) htheta1 htheta2.le hdeficit
  have HEx : edgeBudget 0 as (fun j=>(R j)^(4/p))+x*edgeBudget 0 as R≤
      M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hxW (edgeBudget_nonneg ho hR))).trans HE
  have HE2 : 0≤edgeBudget 0 as (fun j=>(R j)^(4/p)):=edgeBudget_nonneg ho
    (fun j=>Real.rpow_nonneg (hR j) _)
  have HE1 : 0≤x*edgeBudget 0 as R:=mul_nonneg hx.le (edgeBudget_nonneg ho hR)
  have Hch:=mul_le_mul_of_nonneg_right (show Ch≤C by dsimp only [C];linarith) HE2
  have Hcl:=mul_le_mul_of_nonneg_right (show Cl≤C by dsimp only [C];linarith) HE1
  have Hpaid : Ch*edgeBudget 0 as (fun j=>(R j)^(4/p))+
      (absJetVariation 5 1*(Cq*x))*forkVariation 2 3*edgeBudget 0 as R≤C*(edgeBudget 0 as (fun j=>(R j)^(4/p))+x*edgeBudget 0 as R):=by
    dsimp only [Cl] at Hcl
    nlinarith only [Hch,Hcl]
  have Hscale:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ M.hxs.le hxsx 2)
    (show 0≤C*M.context.N^(-(actualMassSavingExponent m delta/256)) by positivity)
  apply H.trans (Hpaid.trans ((mul_le_mul_of_nonneg_left HEx hC.le).trans _))
  convert Hscale using 1; ring

end OAI.SKFluctuations.Cavity
