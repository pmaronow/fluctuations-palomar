module

public import SKProof.Port.ComparisonActualOriginalQCavityNumericConsumers
public import ComparisonSignedCavityActualInitialFullB0OnStrongCutsAlong
public import ComparisonSignedCavitySecondLowGeneratedFullB0Geometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
variable {dim : ℕ→ℕ}

def ActualInitialFullB0OnStrongGivenCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        let old:=pre++(mid++tail)
        let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf old
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum_original_q (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
            [nativeActualInitialState old pre.length (pre.length+mid.length) seedMass (by dsimp only [old];omega)])
          .secondLow|/(chi*K (pre.length+mid.length)) ≤
            Ci*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+
              1/(dim n+1:ℕ))+err n*(M n).xs^3

def ActualInitialFullB0ResidualOnStrongGivenCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        nativeActualInitialFullB0ResidualEnvelope_original_q (M n) hs hU (W n) depth
          [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) seedMass (by omega)] ≤
            Ci*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+
              1/(dim n+1:ℕ))+err n*(M n).xs^3

def ActualInitialJointLowRestorationOnGivenCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(i : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
      ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as i ≤ A*x → ∀seedMass : ℝ,
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
      let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum_original_q (M n) U (W n)
        (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth [st])
        .jointLowRestoration|/(chi*K star) ≤ err n*x*(M n).xs^2

theorem native_actual_resource_canonical_source_radius_gate_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hs : star < as.length)
    (bound : ℝ) (Hi : M.sweepRadius (partitionPoint 0 as i) ≤ bound)
    (Hs : M.sweepRadius (partitionPoint 0 as star) ≤ bound) (e : Fin P.factors.length) :
    M.sweepRadius ((nativeActualResourceCanonicalShape P hi hs).sourceLowMass e) ≤ bound := by
  rcases native_actual_resource_canonical_source_mass_initial_or_star P hi hs e with H|H
  · rw [H];exact Hi
  · rw [H];exact Hs

end OAI.SKFluctuations.Cavity
