module

public import ComparisonSignedCavityActualTargetMeanCorrections

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped NNReal
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def nativeActualTargetOriginalTaylorPart
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark

theorem actual_target_mean_eq_correction_response_transport_taylor
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativePhysicalResourceCenter n M.bf M.hf as i-nativeOriginalScalarPairMean as K i=
      nativeActualTargetOriginalMeanCorrection M as i U+
      2*(M.bf (partitionPoint 0 as i):ℝ)*chi*nativeActualTargetLongitudinalResponse M as i V+
      nativeActualTargetMeanTransportError M as i U V+
      nativeActualTargetOriginalTaylorPart M as i U := by
  dsimp only
  have H:=actual_minimum_continuum_gap_eq_calibration_response_and_corrections M as i U V hi hU ho
  dsimp only at H
  unfold nativeActualTargetOriginalMeanCorrection nativeActualTargetOriginalConstantPart
    nativeActualConstantSourceMeanPart nativeActualTargetOriginalTaylorPart
  dsimp only
  linear_combination H

theorem actual_target_mean_gap_abs_le_four_parts
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativePhysicalResourceCenter n M.bf M.hf as i-nativeOriginalScalarPairMean as K i|≤
      |nativeActualTargetOriginalMeanCorrection M as i U|+
      2*(M.bf (partitionPoint 0 as i):ℝ)*chi*|nativeActualTargetLongitudinalResponse M as i V|+
      |nativeActualTargetMeanTransportError M as i U V|+
      |nativeActualTargetOriginalTaylorPart M as i U| := by
  dsimp only
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid M as ho U (by omega) hU
  rw [actual_target_mean_eq_correction_response_transport_taylor M as i U V hi hU ho]
  have Hcoef : 0≤2*(M.bf (partitionPoint 0 as i):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n M.bf M.hf as)))).H 0 0:=
    mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1
  have Habs (a b c d : ℝ) : |a+b+c+d|≤|a|+|b|+|c|+|d|:=
    (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  apply (Habs _ _ _ _).trans_eq
  rw [abs_mul,abs_of_nonneg Hcoef]

theorem actual_target_mean_gap_abs_le_of_bounds
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) (Emean R Etransport Etaylor : ℝ)
    (Hmean : |nativeActualTargetOriginalMeanCorrection M as i U|≤Emean)
    (Hresponse : |nativeActualTargetLongitudinalResponse M as i V|≤R)
    (Htransport : |nativeActualTargetMeanTransportError M as i U V|≤Etransport)
    (Htaylor : |nativeActualTargetOriginalTaylorPart M as i U|≤Etaylor) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativePhysicalResourceCenter n M.bf M.hf as i-nativeOriginalScalarPairMean as K i|≤
      Emean+2*(M.bf (partitionPoint 0 as i):ℝ)*chi*R+Etransport+Etaylor := by
  dsimp only
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid M as ho U (by omega) hU
  apply (actual_target_mean_gap_abs_le_four_parts M as i U V hi hU ho).trans
  exact add_le_add (add_le_add (add_le_add Hmean
    (mul_le_mul_of_nonneg_left Hresponse
      (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1))) Htransport) Htaylor

end OAI.SKFluctuations.Cavity
