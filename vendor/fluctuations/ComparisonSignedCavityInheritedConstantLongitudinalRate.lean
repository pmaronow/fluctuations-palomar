module

public import ComparisonSignedCavityInheritedConstantLongitudinalProfile
public import ComparisonNativeActualInheritedHighTailPowers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_shell_history_constant_longitudinal_restoration_rate
    (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → T.forkCost f=0) →∀a : T.Slot,
          |nativeOriginalLongitudinalRestoration n q U b h K S T (fun _=>1) a| ≤
            C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  obtain ⟨p,_dOrder,hp,_hdOrder,_hOrder,htheta1,htheta2,hdeficit⟩:=exists_native_high_profile_holder_orders heta
  obtain ⟨Cq,hCq,Hprofile⟩:=eventually_actual_minimum_inherited_constant_longitudinal_restoration_profile
    (D:=D) rBound p hp Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let KH:=pairForkVariation (rBound+3)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    nativeOriginalRestorationProfileVariation rBound
  let KL:=absJetVariation (rBound+3) 1*Cq*forkVariation rBound 3
  have hKH : 0 ≤ KH:=by
    dsimp only [KH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)) (nativeOriginalRestorationProfileVariation_nonneg _)
  have hKL : 0 ≤ KL:=by
    dsimp only [KL]
    exact mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCq.le) (forkVariation_nonneg _ _)
  let C:=KH+KL+1
  have hC : 0 < C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Hprofile,Htail] with n hnProfile hnTail
  intro M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh
  have hxs1 : M.xs ≤ 1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnProfile M hsource hxs1 L us hus hret hmesh,
    hnTail M Tbase epsilon shell ts hb hh hsmall hW1 us hus] with jGrid hgridProfile hgridTail
  dsimp only at hgridProfile hgridTail ⊢
  intro U T hU hT hcutlo hcutup hFork a
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=M.canonical_direct_test_band_pos.le
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ M.context.N^(-eta/256)*M.xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    simpa only [W,as,eta,neg_div] using hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have HS:=hgridProfile U T hU hT W M.canonical_direct_test_band_ge_scale hcutup a
  change _ ≤ KH*(T.forkCost f2+edgeBudget 0 as f2)+
    (absJetVariation (rBound+3) 1*(Cq*W))*forkVariation rBound 3*
      (T.forkCost R+edgeBudget 0 as R) at HS
  have Heq : (absJetVariation (rBound+3) 1*(Cq*W))*forkVariation rBound 3*
      (T.forkCost R+edgeBudget 0 as R)=KL*(W*(T.forkCost R+edgeBudget 0 as R)):=by
    dsimp only [KL]
    ring
  rw [Heq] at HS
  rw [hFork f2 hf2lo,hFork R hRlo,zero_add,zero_add] at HS
  have HE2 : 0 ≤ edgeBudget 0 as f2:=edgeBudget_nonneg ho (fun j=>sq_nonneg _)
  have HE1 : 0 ≤ W*edgeBudget 0 as R:=mul_nonneg hW (edgeBudget_nonneg ho hR)
  have Hmajor : KH*edgeBudget 0 as f2+KL*(W*edgeBudget 0 as R) ≤
      C*(edgeBudget 0 as f2+W*edgeBudget 0 as R):=by
    have H1:=mul_nonneg (show 0 ≤ C-KH by dsimp only [C];linarith) HE2
    have H2:=mul_nonneg (show 0 ≤ C-KL by dsimp only [C];linarith) HE1
    nlinarith
  exact HS.trans (Hmajor.trans (by
    simpa only [eta,neg_div,mul_assoc] using mul_le_mul_of_nonneg_left Hrate hC.le))

end OAI.SKFluctuations.Cavity
