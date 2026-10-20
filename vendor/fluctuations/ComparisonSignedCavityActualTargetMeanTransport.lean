module

public import ComparisonSignedCavityActualTargetGCutAsymptoticAlong
public import ComparisonSignedCavityActualTargetCutConditionalMean
public import ComparisonSignedCavityActualTargetGOriginalReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped NNReal
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def nativeActualTargetMeanTransportError
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  2*(M.bf (partitionPoint 0 as i):ℝ)*chi*
    (nativeActualTargetLongitudinalResponse M as i U-nativeActualTargetLongitudinalResponse M as i V)

theorem actual_minimum_continuum_chi_mem_unit_on_any_grid
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ)
    (hU0 : 0<U) (hU : U≤as.length) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0∈Icc (0:ℝ) 1 := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp only [relocatedClock,hU0,ite_true,zero_mul])
    (B:=K as.length) (by simp only [relocatedClock,not_lt.mpr hU,ite_false,le_refl])
  exact ⟨((Real.exp_pos (-4*K as.length)).le.trans HH.1),HH.2⟩

theorem actual_inherited_target_mean_transport_error_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0≤Temp) (hsource : NativeActualSmallSourceClocks M Temp Cf)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U V : ℕ)
    (hi : i<U) (hU : U≤as.length) :
    abs (nativeActualTargetMeanTransportError M as i U V)≤2*Temp*
      abs (nativeActualTargetLongitudinalResponse M as i U-nativeActualTargetLongitudinalResponse M as i V) := by
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid M as ho U
    (Nat.zero_le i |>.trans_lt hi) hU
  have Hb:=(hsource _ (partitionPoint_mem as ho i)).1
  have HB:=mul_le_mul Hb Hchi.2 Hchi.1 hTemp
  simp only [mul_one] at HB
  unfold nativeActualTargetMeanTransportError
  dsimp only
  rw [abs_mul,abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  simpa only [←mul_assoc] using mul_le_mul_of_nonneg_left HB (by norm_num : (0:ℝ)≤2)

theorem actual_minimum_continuum_gap_eq_calibration_response_and_corrections
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let T:=single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    C i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      -(chi^2*b i*finitePhysicalMean (n+1) as b h i/(n+1:ℕ))+
      (chi^2*b i-1)*(finitePhysicalMean (n+1) as b h i-C i)+
      2*b i*chi*nativeActualTargetLongitudinalResponse M as i V+
      nativeActualTargetMeanTransportError M as i U V+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  have H:=actual_minimum_continuum_gap_eq_conditional_insertion_and_corrections M as i U hi hU ho
  dsimp only at H
  rw [←native_actual_target_conditional_original_readout M as ho i U hi hU,
    ←native_actual_target_longitudinal_eq_conditional M as ho i U hi hU] at H
  unfold nativeActualTargetMeanTransportError
  dsimp only
  linear_combination H

end OAI.SKFluctuations.Cavity
