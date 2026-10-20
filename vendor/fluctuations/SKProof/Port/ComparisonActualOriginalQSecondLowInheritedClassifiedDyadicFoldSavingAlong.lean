module

public import ComparisonSignedCavitySecondLowInheritedClassifiedDyadicFoldSavingAlong
public import SKProof.Port.ComparisonActualOriginalQClassifiedFarCanonicalTransport
public import SKProof.Port.ComparisonActualOriginalQLowUnpairedResamplingSourceAlong
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import SKProof.Port.ComparisonActualOriginalQSecondLowInheritedClassifiedDyadicFoldSaving

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_second_low_classified_dyadic_fold_saving_along_original_q
    (a : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1), (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (G : ActualNaturalBoundaryShape (dim n) a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (f c z : T.Slot) (U : ℕ) (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass)
          (E : NativeSecondLowClassifiedRetainedWholeCSource (dim n) pre mid tail T f c z 0 q 0),
          pre.length+mid.length < U → U ≤ (pre++(mid++tail)).length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          T.splitIndex f c < U → T.splitIndex c z < U →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀(d : E.source.D.Slot) e,T.splitIndex (E.originalSlot d) (G.i e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.sweepRadius (partitionPoint 0 as U) →
          M.z ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀(d : E.source.D.Slot) e,U ≤ T.splitIndex (E.originalSlot d) (G.j e) →
            M.sweepRadius (G.sourceLowMass e) ≤ min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4)) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          M.sweepRadius (partitionPoint 0 as (T.splitIndex f c)) ≤
            min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.sweepRadius (partitionPoint 0 as (T.splitIndex z c)) ≤
            min (M.sweepRadius (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass →
          NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowClassifiedCompleteCFold E U q
          (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)+
            (M.sweepBf (partitionPoint 0 as j):ℝ)*orderedPathS (dim n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j))
          (G.canonicalOriginalQSource M forms).restProduct| ≤
          C*(E.source.D.leaves:ℝ)^2*(dim n:ℝ)^(-eta)*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_classified_dyadic_fold_saving_original_q
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  exact ⟨C,hC,hdim.eventually H⟩
end OAI.SKFluctuations.Cavity
