module

public import SKProof.Port.ComparisonActualOriginalQSecondLowInheritedCloneProductRate
public import ComparisonSignedCavitySecondLowInheritedClassifiedCloneSumBudget
public import SKProof.Port.ComparisonActualOriginalQClassifiedFarCanonicalTransport
public import SKProof.Port.ComparisonActualOriginalQLowUnpairedResamplingSourceAlong
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import ComparisonSignedCavitySecondLowClassifiedCloneSumLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
attribute [local instance] nativeSecondLowSlotFintype

theorem eventually_actual_minimum_inherited_second_low_classified_clone_sum_budget_original_q
    (a : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃Cp Cq : ℝ,1 ≤ Cp ∧ 1 ≤ Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (f c z : T.Slot) (U cut : ℕ) (x v : ℝ)
          (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z 0 q 0),
          pre.length+mid.length < U → U ≤ (pre++(mid++tail)).length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          T.splitIndex f c < U → T.splitIndex c z < U → U ≤ cut →
          M.xs ≤ x → x ≤ W → 0 < v → W ≤ Rmacro/2 → cut ≤ as.length →
          (∀(d : E.source.D.Slot) e,T.splitIndex (E.originalSlot d) (G.i e) < cut) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.sweepRadius (partitionPoint 0 as cut) →
          M.z ≤ min (M.sweepRadius (partitionPoint 0 as cut)/8) (Rmacro/4) →
          (∀(d : E.source.D.Slot) e,cut ≤ T.splitIndex (E.originalSlot d) (G.j e) →
            M.sweepRadius (G.sourceLowMass e) ≤ min (M.sweepRadius (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          M.sweepRadius (partitionPoint 0 as (T.splitIndex f c)) ≤
            min (M.sweepRadius (partitionPoint 0 as cut)/8) (Rmacro/4) →
          M.sweepRadius (partitionPoint 0 as (T.splitIndex z c)) ≤
            min (M.sweepRadius (partitionPoint 0 as cut)/8) (Rmacro/4) →
          v ≤ partitionPoint 0 as cut →
        (∫r,∑d:E.source.D.Slot,nativeSecondLowClassifiedCloneConditional E d cut q
          (fun σ τ=>((G.canonicalOriginalQSource M forms).restProduct σ-
            (G.canonicalOriginalQSource M forms).restProduct τ)^2) r
          ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
          (E.source.D.leaves:ℝ)*((a:ℝ)*(1+Temp)*
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v)/x*
            (Cp^a*sourceMonomialScale x W initial))^2 ∧
        (∫r,∑d:E.source.D.Slot,nativeSecondLowClassifiedCloneConditional E d cut q
          (fun σ τ=>(
            ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M f (E.originalSlot d) σ*
              ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M z (E.originalSlot d) σ-
            ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M f (E.originalSlot d) τ*
              ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M z (E.originalSlot d) τ)^2) r
          ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
          (E.source.D.leaves:ℝ)*(4*(1+Temp)*Cq^2*W*
            ((n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v))^2 := by
  obtain ⟨Cp,Cq,hCp,hCq,H⟩:=eventually_actual_minimum_inherited_second_low_clone_sum_budget_original_q
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hparts T G forms initial f c z U cut x v E
    hstar hU hT Hfc Hcz hUcut hxsx hxW hv hWmacro hcut
    hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz hvmass
  have ho : MassOrdered 0 (pre++(mid++tail)):=hparts ▸ finiteCutMasses_ordered us hus k
  have HC:pre.length+mid.length < cut:=hstar.trans_le hUcut
  have Hslots:=fun d=>E.outside_splits_at_originalSlot hstar hU hT Hfc Hcz d
  have Hcf:∀d,T.splitIndex (E.originalSlot d) f < cut:=by
    intro d
    rw [T.splitIndex_symm,(Hslots d).1]
    exact Hfc.trans_le hUcut
  have Hcz:∀d,T.splitIndex (E.originalSlot d) z < cut:=by
    intro d
    rw [(Hslots d).2]
    exact Hcz.trans_le hUcut
  have Hmf':∀d,partitionPoint 0 (finiteCutMasses us k) (T.splitIndex f (E.originalSlot d)) ≤
      Cmass*max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs)):=by
    intro d
    rw [(Hslots d).1]
    exact Hmf
  have Hmz':∀d,partitionPoint 0 (finiteCutMasses us k) (T.splitIndex z (E.originalSlot d)) ≤
      Cmass*max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs)):=by
    intro d
    rw [T.splitIndex_symm,(Hslots d).2,T.splitIndex_symm c z]
    exact Hmz
  have Hrf':∀d,M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) (T.splitIndex f (E.originalSlot d))) ≤
      min (M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) cut)/8) (Rmacro/4):=by
    intro d
    rw [(Hslots d).1]
    exact Hrf
  have Hrz':∀d,M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) (T.splitIndex z (E.originalSlot d))) ≤
      min (M.sweepRadius (partitionPoint 0 (finiteCutMasses us k) cut)/8) (Rmacro/4):=by
    intro d
    rw [T.splitIndex_symm,(Hslots d).2,T.splitIndex_symm c z]
    exact Hrz
  rw [hparts] at hk
  have HH:=hk T G forms initial E.source.D.Slot E.originalSlot f z cut x v
    hxsx (by simpa only [←hparts] using hxW) hv (by simpa only [←hparts] using hWmacro)
    (by simpa only [←hparts] using hcut) hout
    (by simpa only [←hparts] using hmass) (by simpa only [←hparts] using hhigh)
    (by simpa only [←hparts] using hz) (by simpa only [←hparts] using hlow) Hcf Hcz
    (by simpa only [←hparts] using Hmf') (by simpa only [←hparts] using Hmz')
    (by simpa only [←hparts] using Hrf') (by simpa only [←hparts] using Hrz')
    (by simpa only [←hparts] using hvmass)
  rw [native_second_low_slot_fintype_card_eq_leaves E.source.D] at HH
  constructor
  · rw [native_second_low_classified_integrated_square_sum_eq_original E ho cut HC]
    simpa only [hparts] using HH.1
  · rw [native_second_low_classified_integrated_square_sum_eq_original E ho cut HC]
    simpa only [hparts] using HH.2

end OAI.SKFluctuations.Cavity
