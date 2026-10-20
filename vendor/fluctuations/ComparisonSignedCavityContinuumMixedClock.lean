module

public import ComparisonSignedCavityActualSharpSlowWindowSequence
public import ComparisonSignedCavityCanonicalLowFactor

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

def nativeContinuumMixedClock (n : ℕ) (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) (j : ℕ) : ℝ :=
  (hf (partitionPoint 0 as j):ℝ)+(bf (partitionPoint 0 as j):ℝ)*
    orderedPathS (n+1) bf hf (partitionPoint 0 as j)

theorem native_continuum_mixed_clock_nonneg (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) : ∀j,0 ≤ nativeContinuumMixedClock n bf hf as j := by
  intro j
  have HS:=physicalOrderedPathS_mem_unit n bf hf hb hh (partitionPoint_mem as ho j)
  exact add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) HS.1)

theorem native_continuum_mixed_clock_monotone (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) : Monotone (nativeContinuumMixedClock n bf hf as) := by
  intro i j hij
  have hbi : (bf (partitionPoint 0 as i):ℝ) ≤ bf (partitionPoint 0 as j):=
    hb (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  have hhi : (hf (partitionPoint 0 as i):ℝ) ≤ hf (partitionPoint 0 as j):=
    hh (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  have HSi:=physicalOrderedPathS_mem_unit n bf hf hb hh (partitionPoint_mem as ho i)
  have HSm:=physicalOrderedPathS_monotone_unit n bf hf hb hh
    (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij)
  exact add_le_add hhi (mul_le_mul hbi HSm HSi.1 (NNReal.coe_nonneg _))

theorem native_continuum_mixed_clock_terminal_le (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    nativeContinuumMixedClock n bf hf as as.length ≤ (hf 1:ℝ)+(bf 1:ℝ) := by
  have hu:=partitionPoint_mem as ho as.length
  have HS:=physicalOrderedPathS_mem_unit n bf hf hb hh hu
  have HB : (bf (partitionPoint 0 as as.length):ℝ) ≤ bf 1:=hb hu (by norm_num) hu.2
  have HH : (hf (partitionPoint 0 as as.length):ℝ) ≤ hf 1:=hh hu (by norm_num) hu.2
  exact add_le_add HH ((mul_le_of_le_one_right (NNReal.coe_nonneg _) HS.2).trans HB)

theorem native_continuum_mixed_clock_eq_original_center (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (j : ℕ) :
    nativeContinuumMixedClock n bf hf as j=
      (hf (partitionPoint 0 as j):ℝ)+(bf (partitionPoint 0 as j):ℝ)*nativePhysicalResourceCenter n bf hf as j := by
  unfold nativeContinuumMixedClock nativePhysicalResourceCenter
  rw [native_ordered_source_center_eq_completed n bf hf hb hh (partitionPoint_mem as ho j)]

theorem native_continuum_mixed_clock_retained_eq (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (u : PositiveMass) (hu : u∈as) :
    nativeContinuumMixedClock n bf hf as (retainedMassPrefixIndex u.val as)=
      actualMixedClock (n+1) bf hf u.val := by
  unfold nativeContinuumMixedClock actualMixedClock
  rw [nativeRetainedCut_partitionPoint as ho u hu]

end OAI.SKFluctuations.Cavity
