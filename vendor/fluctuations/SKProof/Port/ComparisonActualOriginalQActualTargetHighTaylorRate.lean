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

theorem eventually_actual_regular_target_constant_fresh_HIGH_parts_rate_original_q
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
        ∀(i U : ℕ),i < U → U ≤ as.length →
        ∀x : ℝ,M.xs ≤ x → x ≤ W →
          2*c*x ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*x →
        ∀seedMass : ℝ,
          let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) i
          ∀(a z : g.tree.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
            |nativeActualHigherHighPart part n q U b h K g.tree (fun _=>1) a z l t| ≤
              C*M.data.N^(-(actualMassSavingExponent m delta/256))*x^3 := by
  obtain ⟨p,dOrder,hp,hd,hOrder,htheta1,htheta2,hdeficit⟩:=
    exists_native_high_profile_holder_orders (actualMassSavingExponent_pos hm hdelta)
  obtain ⟨C,hC,Hparts⟩:=eventually_actual_minimum_inherited_constant_HIGH_parts_profile_original_q
    (D:=D) 2 dOrder hd p hp hOrder Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_regular_original_target_high_envelope_powers_original_q (D:=D) (Cs:=Cs)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [Hparts,Htail] with n hnParts hnTail
  intro M hclock hs0 hsxs hs64 hsource hsmall hW1 L us hus hret hmesh
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnParts M hs0 hsxs hsource hxs1 L us hus hret hmesh,
    hnTail M hclock hs0 hsxs hs64 hsmall hW1 us hus] with jGrid hjParts hjTail
  dsimp only at hjParts hjTail ⊢
  intro i U hs hU x hxsx hxW hcutlo hcutup seedMass a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  let W:=M.directTestWorkingScale
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) seedMass (singleSlot as) i
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
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
  have H:=hjParts U g.tree hU hg x hxsx (hxW.trans hW1) hcutup a z l t hl ht part
  change |nativeActualHigherHighPart part n _ U _ _ _ g.tree (fun _=>1) a z l t| ≤
    C*x*(g.tree.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
      x*(g.tree.forkCost R+edgeBudget 0 as R)) at H
  rw [HF1,HF2,zero_add,zero_add] at H
  have HE:=hjTail U hU ((mul_le_mul_of_nonneg_left hxsx (by positivity)).trans hcutlo) (4/p) htheta1 htheta2.le hdeficit
  have HE' : edgeBudget 0 as (fun j=>(R j)^(4/p))+W*edgeBudget 0 as R ≤
      M.data.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=HE
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hxfirst:=mul_le_mul_of_nonneg_right hxW
    (edgeBudget_nonneg (finiteCutMasses_ordered us hus jGrid) hR)
  have Hsum:=(add_le_add le_rfl Hxfirst).trans HE'
  have Hprice:=mul_le_mul_of_nonneg_left Hsum (mul_nonneg hC.le hx.le)
  have Hxs : M.xs^2≤x^2:=pow_le_pow_left₀ M.hxs.le hxsx 2
  have Hlast:=mul_le_mul_of_nonneg_left Hxs
    (show 0≤C*x*M.data.N^(-(actualMassSavingExponent m delta/256)) by positivity)
  apply H.trans (Hprice.trans _)
  convert Hlast using 1 <;> ring

end OAI.SKFluctuations.Cavity
