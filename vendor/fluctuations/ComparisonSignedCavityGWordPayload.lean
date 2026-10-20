module

public import ComparisonSignedCavityGWordIndices
public import ComparisonSignedCavityGSpineRestLaw
public import ComparisonSignedCavityObservedFreshDisplacementFold

@[expose] public section

noncomputable section
open scoped NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeGWordNewSpin (n : ℕ) (us : List (Spin n)) : Spin n :=
  us[2]?.getD (fun _=>false)

def nativeGWordError (n : ℕ) (U j : ℕ) (b h K : ℕ→ℝ) (us : List (Spin n)) : ℝ :=
  restHighKernel n U b h K j (us[1]?.getD (fun _=>false)) (us[0]?.getD (fun _=>false))

def nativeGWordOldSelector {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (base : NativeGeneratedTest T)
    (_y : RestCoordinate n→ℝ) (σ : T.cavityLeft.Assignment) (_us : List (Spin n)) : Spin n :=
  T.cavityLeft.atSlot σ (T.cavityLeftSlot base.target)

def nativeGWordNewSelector {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (_y : RestCoordinate n→ℝ)
    (_σ : T.cavityLeft.Assignment) (us : List (Spin n)) : Spin n :=nativeGWordNewSpin n us

def nativeGWordDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (base : NativeGeneratedTest T) (star : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (A : Spin n→Spin n→ℝ)
    (y : RestCoordinate n→ℝ) (σ : T.cavityLeft.Assignment) (us : List (Spin n)) : ℝ :=
  nativeStarPairFactor (restWeight n) (restFeature n) as star
    (cumulativeIncrements (q 0) (fun j=>q (j+1))) A y (nativeGWordNewSpin n us)-
  nativeStarPairFactor (restWeight n) (restFeature n) as star
    (cumulativeIncrements (q 0) (fun j=>q (j+1))) A y
      (T.cavityLeft.atSlot σ (T.cavityLeftSlot base.target))

def nativeGWordOldPayload {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (base : NativeGeneratedTest T) (star U j : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (A R : Spin n→Spin n→ℝ)
    (y : RestCoordinate n→ℝ) (σ : T.cavityLeft.Assignment) (us : List (Spin n)) : ℝ :=
  nativeGWordDisplacement T base star q A y σ us*nativeRestGeneratedTestValue T base R C σ*
    nativeGWordError n U j b h K us

def nativeGWordNewPayload {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (base : NativeGeneratedTest T) (star U j : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ) (A R : Spin n→Spin n→ℝ)
    (y : RestCoordinate n→ℝ) (σ : T.cavityLeft.Assignment) (us : List (Spin n)) : ℝ :=
  nativeGWordDisplacement T base star q A y σ us*
    nativeRestGeneratedTestValue T base R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot base.target) σ (nativeGWordNewSpin n us))*
    nativeGWordError n U j b h K us

end OAI.SKFluctuations.Cavity
