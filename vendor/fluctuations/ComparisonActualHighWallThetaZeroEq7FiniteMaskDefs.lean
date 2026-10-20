module

public import ComparisonActualHighWallThetaZeroWholeCapCoverPositiveOrigin
public import ComparisonActualHighWallThetaZeroRetainedRowsBasics
public import ComparisonNativeDyadicContactCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

def eq7InnerDyadMass (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock)
    (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)) : ℝ :=
  comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)

def eq7InnerDyadRight (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock)
    (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)) : ℝ :=
  min (16*Q.eq7InnerDyadMass j) 1

def eq7InnerWallStart (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock)
    (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)) : ℝ :=
  max (Q.data.s+comparisonSmallMass Q.data.N Q.data.E) (Q.eq7InnerDyadMass j)

def eq7InnerPrefixEnd (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock) : ℝ :=
  let U := comparisonSmallMass Q.data.N Q.data.E
  if Q.data.s < U then min (24*U) 1 else min (Q.data.s+2*U) 1

abbrev Eq7InnerDyad (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock) (h : ℝ) :=
  {j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E) //
    Q.eq7InnerDyadMass j ≤ h}

abbrev Eq7InnerLowDyad (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock) (h : ℝ) :=
  {j : Eq7InnerDyad Q h //
    comparisonSmallMass Q.data.N Q.data.E ≤ Q.data.s ∧
      Q.eq7InnerDyadMass j.val ≤ 2*Q.data.s ∧
      Q.data.s ≤ Q.eq7InnerDyadRight j.val}

abbrev Eq7InnerPostDyad (Q : ActualThetaZeroOverlapMinimum
    (n+1) m delta cl cu Az C0 Ct D Bclock) (h : ℝ) :=
  {j : Eq7InnerDyad Q h //
    (Q.data.s < comparisonSmallMass Q.data.N Q.data.E ∨
      2*Q.data.s < Q.eq7InnerDyadMass j.val) ∧
    Q.eq7InnerWallStart j.val < Q.eq7InnerDyadRight j.val}

def eq7InnerCapBroad {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    (i : ι) : Prop :=
  8*max (Q.alpha.val.val (c i).left) Q.positiveOriginMassCoverBase <
    Q.alpha.val.val (c i).right

abbrev Eq7InnerBroadCapIndex {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) :=
  {i : ι // eq7InnerCapBroad c i}

def eq7InnerBroadSampler {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) (i : Eq7InnerBroadCapIndex c) :
    PositiveOriginWholeCapBroadSampler (c i.val) :=
  Classical.choice (exists_critical_whole_cap_broad_sampler (c i.val) i.property)

abbrev Eq7InnerBroadSliceIndex {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) :=
  Σ i : Eq7InnerBroadCapIndex c, Fin (eq7InnerBroadSampler c i).count

def eq7InnerBroadSlice {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) (p : Eq7InnerBroadSliceIndex c) : Set ℝ :=
  (eq7InnerBroadSampler c p.1).slice p.2

abbrev Eq7InnerRelevantBroadSlice {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) (h : ℝ) :=
  {p : Eq7InnerBroadSliceIndex c //
    ∃ u ∈ Icc Q.data.s h, Q.shiftedNativeModel.R u ∈ eq7InnerBroadSlice c p}

abbrev Eq7InnerLowCapIndex {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (j : Eq7InnerLowDyad Q h) :=
  {i : ι //
    ¬eq7InnerCapBroad c i ∧
    Q.eq7InnerDyadMass j.val.val ≤ Q.alpha.val.val (c i).left ∧
    Q.alpha.val.val (c i).right ≤ Q.eq7InnerDyadRight j.val.val ∧
    ((c i).left ≠ Q.data.rmin ∨
      comparisonSmallMass Q.data.N Q.data.E ≤
        Q.alpha.val.val (c i).right-Q.alpha.val.val (c i).left)}

abbrev Eq7InnerPostCapIndex {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (j : Eq7InnerPostDyad Q h) :=
  {i : ι //
    ¬eq7InnerCapBroad c i ∧
    Q.eq7InnerWallStart j.val.val ≤ Q.alpha.val.val (c i).left ∧
    Q.alpha.val.val (c i).right ≤ Q.eq7InnerDyadRight j.val.val}

def eq7InnerLowSupport {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (j : Eq7InnerLowDyad Q h) : Set ℝ :=
  P.retainedSupport (fun i : Eq7InnerLowCapIndex c j => c i.val)
    Q.data.rmin (Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val))

def eq7InnerPostSupport {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (j : Eq7InnerPostDyad Q h) : Set ℝ :=
  P.retainedSupport (fun i : Eq7InnerPostCapIndex c j => c i.val)
    (Q.shiftedNativeModel.R (Q.eq7InnerWallStart j.val.val))
    (Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val))

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
