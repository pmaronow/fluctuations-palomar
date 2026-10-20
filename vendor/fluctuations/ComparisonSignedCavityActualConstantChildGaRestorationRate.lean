module

public import ComparisonSignedCavityActualFourGaRestorationSeedAtoms
public import ComparisonSignedCavityActualConstantChildHighProfile
public import ComparisonSignedCavityActualConstantJointFourReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000

theorem eventually_actual_shell_history_constant_child_G_restoration_forest_rate
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell Ttotal : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Ttotal) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀star U : ℕ,∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        (((nativeActualConstantSourceChildren M as star U hs hU).flatMap
          (fun st=>nativeActualMinimumFourCenteredForest M hs hU W depth [st])).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨p,hp,htheta1,htheta2,hdeficit,Csrc,hCsrc,Hsource⟩:=
    eventually_actual_shell_history_resource_G_restoration_forest_with_seed_atoms
      (D:=D) (Cs:=Cs) 0 1 3 depth Bclock Temp Cf Cmass Ccut cK
      hTemp hCf hCmass hCcut hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let J:=1+nativeActualProfileOpVariation 1 .highRow
  have hJ : 0 ≤ J:=by
    dsimp only [J,nativeActualProfileOpVariation]
    positivity
  let C:=Csrc*(J+6)+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M Tbase epsilon shell Ttotal ts hsource hb hh htotal hsmall hW1 L us hus hret hmesh
  filter_upwards [hnSource M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh,
    hnTail M Tbase epsilon shell ts hb hh hsmall hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro star U hs hU hcutlo hcutup hmassstar hstarK
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let Nrate:=M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=M.canonical_direct_test_band_pos.le
  have hNrate : 0 ≤ Nrate:=by dsimp only [Nrate];positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg Hchi.1];exact Hchi.2
  have Hfamily (f : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j < U → f j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
        J*edgeBudget 0 as f:=by
    exact native_actual_constant_child_family_wholeProfile_le ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi f hf hlo
  have Hfork (f : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hlo : ∀j,j < U → f j=0) :
      (children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost f)).sum ≤ J*edgeBudget 0 as f:=by
    apply (List.sum_le_sum (fun Q _=>mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (edgeBudget_nonneg ho hf)) (abs_nonneg Q.term.coefficient))).trans
    exact Hfamily f hf hlo
  have Hcoeff:=nativeActualConstantSourceChildren_coefficient_variation M htotal ho hs hU
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ Nrate:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    exact hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have Hrow Q (hQ : Q∈children) :
      ((nativeActualMinimumFourCenteredForest M hs hU W depth [Q]).map
        (fun P=>|nativeActualOriginalFourGaRestorationError M U W P|)).sum ≤
      Csrc*(|Q.term.coefficient| *(Q.tree.forkCost f2+W*Q.tree.forkCost R+Nrate)):=by
    have Hvalid:=nativeActualConstantSourceChildren_valid M hs hU Q hQ
    have Hgen:=nativeActualConstantSourceChildren_generation M hs hU Q hQ
    have Hleaf:=nativeActualConstantSourceChildren_leaves M hs hU Q hQ
    have H:=hgridSource 0 star U [] Q (by simp) Hgen Hleaf Hvalid (Nat.zero_le star)
      hs hU hcutlo hcutup hmassstar hstarK M.xs le_rfl M.canonical_direct_test_band_ge_scale
      (by
        simp only [partitionPoint,partitionValues_zero,id_eq]
        exact mul_nonneg hCmass M.hxs.le)
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
    apply H.trans_eq
    ring
  simp only [List.map_flatMap,native_sum_flatMap]
  apply (List.sum_le_sum Hrow).trans
  have HE : (children.map (fun Q=>Csrc*(|Q.term.coefficient| *
      (Q.tree.forkCost f2+W*Q.tree.forkCost R+Nrate)))).sum=
      Csrc*((children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost f2)).sum+
        W*(children.map (fun Q=>|Q.term.coefficient| *Q.tree.forkCost R)).sum+
        Nrate*(children.map (fun Q=>|Q.term.coefficient|)).sum):=by
    simp only [←List.sum_map_mul_left,←List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  rw [HE]
  have Hbound:=mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (Hfork f2 hf2 hf2lo) (mul_le_mul_of_nonneg_left (Hfork R hR hRlo) hW))
      (mul_le_mul_of_nonneg_left Hcoeff hNrate)) hCsrc.le
  have Htotal:=mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left Hrate hJ) (le_refl (6*Nrate))) hCsrc.le
  have Hlast : Csrc*(J*Nrate+6*Nrate) ≤ C*Nrate:=by
    have H:=mul_nonneg hNrate (show 0 ≤ C-Csrc*(J+6) by dsimp only [C];linarith)
    nlinarith only [H]
  apply Hbound.trans
  have Htotal' : Csrc*(J*edgeBudget 0 as f2+W*(J*edgeBudget 0 as R)+Nrate*6) ≤
      Csrc*(J*Nrate+6*Nrate):=by
    convert Htotal using 1
    ring
  simpa only [Nrate,mul_assoc] using Htotal'.trans Hlast

end OAI.SKFluctuations.Cavity
