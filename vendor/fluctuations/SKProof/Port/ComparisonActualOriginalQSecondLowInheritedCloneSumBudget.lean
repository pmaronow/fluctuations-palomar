module

public import ComparisonSignedCavitySecondLowInheritedCloneSumBudget
public import SKProof.Port.ComparisonActualOriginalQClassifiedFarCanonicalTransport
public import SKProof.Port.ComparisonActualOriginalQLowUnpairedResamplingSourceAlong
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import SKProof.Port.ComparisonActualOriginalQSecondLowInheritedTwoLowCloneBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_second_low_clone_sum_budget_original_q
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
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (J : Type) [Fintype J] (targets : J→T.Slot) (f z : T.Slot) (cut : ℕ) (x v : ℝ),
          M.xs ≤ x → x ≤ W → 0 < v → W ≤ Rmacro/2 → cut ≤ as.length →
          (∀d e,T.splitIndex (targets d) (G.i e) < cut) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.sweepRadius (partitionPoint 0 as cut) →
          M.z ≤ min (M.sweepRadius (partitionPoint 0 as cut)/8) (Rmacro/4) →
          (∀d e,cut ≤ T.splitIndex (targets d) (G.j e) →
            M.sweepRadius (G.sourceLowMass e) ≤ min (M.sweepRadius (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          (∀d,T.splitIndex (targets d) f < cut) →
          (∀d,T.splitIndex (targets d) z < cut) →
          (∀d,partitionPoint 0 as (T.splitIndex f (targets d)) ≤ Cmass*W) →
          (∀d,partitionPoint 0 as (T.splitIndex z (targets d)) ≤ Cmass*W) →
          (∀d,M.sweepRadius (partitionPoint 0 as (T.splitIndex f (targets d))) ≤
            min (M.sweepRadius (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          (∀d,M.sweepRadius (partitionPoint 0 as (T.splitIndex z (targets d))) ≤
            min (M.sweepRadius (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          v ≤ partitionPoint 0 as cut →
        (∑d:J,nativeSecondLowRestCloneSquare n T (targets d) cut q
            (G.canonicalOriginalQSource M forms).restProduct) ≤
          (Fintype.card J:ℝ)*((a:ℝ)*(1+Temp)*
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v)/x*
            (Cp^a*sourceMonomialScale x W initial))^2 ∧
        (∑d:J,nativeSecondLowRestCloneSquare n T (targets d) cut q
            (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M f (targets d) σ*
              ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M z (targets d) σ)) ≤
          (Fintype.card J:ℝ)*(4*(1+Temp)*Cq^2*W*
            ((n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v))^2 := by
  classical
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_rest_clone_budget_original_q
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_two_LOW_rest_clone_budget_original_q
    (D:=D) Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs HS hxs hcompare L us hus hret hmesh,
    hnQ M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hkP hkQ
  dsimp only at hkP hkQ ⊢
  intro T G forms initial J _ targets f z cut x v hxsx hxW hv hWmacro hcut
    hout hmass hhigh hz hlow Hcf Hcz Hmf Hmz Hrf Hrz hvmass
  constructor
  · calc
      _ ≤ ∑_d:J,((a:ℝ)*(1+Temp)*
          (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) _ v)/x*
          (Cp^a*sourceMonomialScale x _ initial))^2 := by
        apply Finset.sum_le_sum
        intro d _
        exact hkP T G forms initial (targets d) cut x v hxsx hxW hv hWmacro hcut
          (hout d) hmass hhigh hz (hlow d) hvmass
      _ = _ := by simp
  · calc
      _ ≤ ∑_d:J,(4*(1+Temp)*Cq^2*_*
          ((n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) _ v))^2 := by
        apply Finset.sum_le_sum
        intro d _
        exact hkQ T f (targets d) z cut v hv hWmacro hcut (Hcf d) (Hcz d)
          (Hmf d) (Hmz d) hhigh hz (Hrf d) (Hrz d) hvmass
      _ = _ := by simp

end OAI.SKFluctuations.Cavity
