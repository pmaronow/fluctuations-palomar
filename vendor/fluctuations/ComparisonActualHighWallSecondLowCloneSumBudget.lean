module

public import ComparisonActualHighWallSecondLowTwoLowCloneBudget
public import ComparisonSignedCavitySecondLowInheritedCloneSumBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_second_low_clone_sum_budget
    (a : ℕ) (Bclock Cmass Rmacro F : ℝ)
    (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃Cp Cq : ℝ,1 ≤ Cp ∧ 1 ≤ Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=M.data.d
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (J : Type) [Fintype J] (targets : J→T.Slot) (f z : T.Slot) (cut : ℕ) (x v : ℝ),
          M.xs ≤ x → x ≤ W → 0 < v → W ≤ Rmacro/2 → cut ≤ as.length →
          (∀d e,T.splitIndex (targets d) (G.i e) < cut) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.data.wallRadius M.alpha (partitionPoint 0 as cut) →
          M.z ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as cut)/8) (Rmacro/4) →
          (∀d e,cut ≤ T.splitIndex (targets d) (G.j e) →
            M.data.wallRadius M.alpha (G.sourceLowMass e) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          (∀d,T.splitIndex (targets d) f < cut) →
          (∀d,T.splitIndex (targets d) z < cut) →
          (∀d,partitionPoint 0 as (T.splitIndex f (targets d)) ≤ Cmass*W) →
          (∀d,partitionPoint 0 as (T.splitIndex z (targets d)) ≤ Cmass*W) →
          (∀d,M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex f (targets d))) ≤
            min (M.data.wallRadius M.alpha (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          (∀d,M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex z (targets d))) ≤
            min (M.data.wallRadius M.alpha (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          v ≤ partitionPoint 0 as cut →
        (∑d:J,nativeSecondLowRestCloneSquare n T (targets d) cut q
            (G.canonicalHighWallSource M forms).restProduct) ≤
          (Fintype.card J:ℝ)*((a:ℝ)*(1+max Bclock 0)*
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v)/x*
            (Cp^a*sourceMonomialScale x W initial))^2 ∧
        (∑d:J,nativeSecondLowRestCloneSquare n T (targets d) cut q
            (fun σ=>ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor M.bf M.hf f (targets d) σ*
              ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor M.bf M.hf z (targets d) σ)) ≤
          (Fintype.card J:ℝ)*(4*(1+max Bclock 0)*Cq^2*W*
            ((n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v))^2 := by
  classical
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_rest_clone_budget
    (D:=D) a Bclock Cmass Rmacro F hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_high_wall_two_LOW_rest_clone_budget
    (D:=D) Bclock Cmass Rmacro F hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,
    hnQ M hwork L us hus hret hmesh] with k hkP hkQ
  dsimp only at hkP hkQ ⊢
  intro T G forms initial J _ targets f z cut x v hxsx hxW hv hWmacro hcut
    hout hmass hhigh hz hlow Hcf Hcz Hmf Hmz Hrf Hrz hvmass
  constructor
  · calc
      _ ≤ ∑_d:J,((a:ℝ)*(1+max Bclock 0)*
          (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) _ v)/x*
          (Cp^a*sourceMonomialScale x _ initial))^2 := by
        apply Finset.sum_le_sum
        intro d _
        exact hkP T G forms initial (targets d) cut x v hxsx hxW hv hWmacro hcut
          (hout d) hmass hhigh hz (hlow d) hvmass
      _ = _ := by simp
  · calc
      _ ≤ ∑_d:J,(4*(1+max Bclock 0)*Cq^2*_*
          ((n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) _ v))^2 := by
        apply Finset.sum_le_sum
        intro d _
        exact hkQ T f (targets d) z cut v hv hWmacro hcut (Hcf d) (Hcz d)
          (Hmf d) (Hmz d) hhigh hz (Hrf d) (Hrz d) hvmass
      _ = _ := by simp

end OAI.SKFluctuations.Cavity
