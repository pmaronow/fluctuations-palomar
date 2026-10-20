module

public import ComparisonSignedCavitySecondLowInheritedClassifiedDyadicFoldSaving

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_second_low_classified_dyadic_fold_saving_along
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
      ∀M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1), (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
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
          4*W ≤ M.R (partitionPoint 0 as U) →
          M.z ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀(d : E.source.D.Slot) e,U ≤ T.splitIndex (E.originalSlot d) (G.j e) →
            M.R (G.sourceLowMass e) ≤ min (M.R (partitionPoint 0 as U)/8) (Rmacro/4)) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          M.R (partitionPoint 0 as (T.splitIndex f c)) ≤
            min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex z c)) ≤
            min (M.R (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass →
          NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowClassifiedCompleteCFold E U q
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
            (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 as j))
          (G.canonicalMinimumSource M forms).restProduct| ≤
          C*(E.source.D.leaves:ℝ)^2*(dim n:ℝ)^(-eta)*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_classified_dyadic_fold_saving
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F Cx hCx heta hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  exact ⟨C,hC,hdim.eventually H⟩

theorem classified_dyadic_fold_saving_amplitude_tendsto_zero_along
    (C eta : ℝ) (heta : 0 < eta) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n=>C*(dim n:ℝ)^(-eta)) atTop (𝓝 0) := by
  simpa only [Function.comp_def,mul_zero] using
    (((tendsto_rpow_neg_atTop heta).comp (tendsto_natCast_atTop_atTop.comp hdim)).const_mul C)

end OAI.SKFluctuations.Cavity
