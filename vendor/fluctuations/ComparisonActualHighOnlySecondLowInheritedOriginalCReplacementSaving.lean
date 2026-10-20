module

public import ComparisonSignedCavitySecondLowInheritedOriginalCReplacementSaving
public import ComparisonActualHighOnlyClassifiedFarCanonicalTransport
public import ComparisonActualHighOnlyLowUnpairedResamplingSourceAlong
public import ComparisonActualHighOnlyPhysicalSourceProfiles
public import ComparisonSignedCavitySecondLowOriginalClassifiedReplacementIntegral
public import ComparisonActualHighOnlySecondLowInheritedClassifiedDyadicFoldSavingAlong

@[expose] public section

noncomputable section
set_option maxHeartbeats 50000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum

theorem eventually_actual_minimum_inherited_second_low_original_c_replacement_saving_high_only
    (a : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1), (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (f c z : T.Slot) (U : ℕ) (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass)
          (E : NativeSecondLowClassifiedHighWholeCSource n pre mid tail T f c z 0 q 0),
          pre.length+mid.length < U → U ≤ (pre++(mid++tail)).length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          T.splitIndex f c < U → T.splitIndex c z < U →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀(d : E.source.core.D.Slot) e,T.splitIndex (E.toRetainedCSource.originalSlot d) (G.i e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.R (partitionPoint 0 as U) →
          M.z ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀(d : E.source.core.D.Slot) e,U ≤ T.splitIndex (E.toRetainedCSource.originalSlot d) (G.j e) →
            M.R (G.sourceLowMass e) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4)) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          M.R (partitionPoint 0 as (T.splitIndex f c)) ≤
            min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex z c)) ≤
            min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass →
          NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowUnweightedCReplacementRow n q U
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
            (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))
          T f c z (G.canonicalHighOnlySource M forms).restProduct| ≤
          C*(E.source.core.D.leaves:ℝ)^2*(n:ℝ)^(-eta)*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_classified_dyadic_fold_saving_high_only
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hparts T G forms initial f c z U x sourceMass hsourceMass E
    hstar hU hT Hfc Hcz hxsx hxW hWmacro hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz hfloor Hchain
  have ho : MassOrdered 0 (pre++(mid++tail)):=hparts ▸ finiteCutMasses_ordered us hus k
  rw [native_second_low_original_unweighted_c_replacement_eq_classified_complete_fold
    n pre mid tail T f c z _ U _ _ _ ho hstar hU Hfc Hcz E]
  exact hk pre mid tail hparts T G forms initial f c z U x sourceMass hsourceMass E.toRetainedCSource
    hstar hU hT Hfc Hcz hxsx hxW hWmacro hout hmass hhigh hz hlow Hmf Hmz Hrf Hrz hfloor Hchain

end OAI.SKFluctuations.Cavity
