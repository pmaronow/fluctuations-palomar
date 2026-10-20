module

public import ComparisonActualGeneralFourSummability
public import ComparisonSignedCavityActualMinimumConstantMeanExchange
public import ComparisonSignedCavityActualTargetInitialFourReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter MeasureTheory ProbabilityTheory LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_constant_gap_eq_twice_old_longitudinal
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i
    finitePhysicalMean (n+1) as b h i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      chi^2*b i*(finitePhysicalMean (n+1) as b h i-
        finitePhysicalMean (n+1) as b h i/(n+1:ℕ)-C i)+
      2*b i*chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hbf hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hhf hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n bf hf
    hbf hhf as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n bf hf
    hbf hhf as ho
  have hKC : ∀j,K j=h j+b j*C j:=native_continuum_mixed_clock_eq_original_center n bf hf
    hbf hhf as ho
  have H:=actual_original_constant_gap_eq_twice_old_longitudinal n as i U hi hU ho b h K C
    hKC hb hh hK hbm hhm hKm
  dsimp only at H
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1 :=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  rw [HQ] at H
  exact H

theorem actual_general_continuum_chi_mem_unit_on_any_grid
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ)
    (hU0 : 0<U) (hU : U≤as.length) :
    let K:=nativeContinuumMixedClock n bf hf as
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0∈Icc (0:ℝ) 1 := by
  dsimp only
  let K:=nativeContinuumMixedClock n bf hf as
  have hKm:=native_continuum_mixed_clock_monotone n bf hf hbf
    hhf as ho
  have hK0:=native_continuum_mixed_clock_nonneg n bf hf hbf
    hhf as ho
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp only [relocatedClock,hU0,ite_true,zero_mul])
    (B:=K as.length) (by simp only [relocatedClock,not_lt.mpr hU,ite_false,le_refl])
  exact ⟨((Real.exp_pos (-4*K as.length)).le.trans HH.1),HH.2⟩

section Readers
variable {n : ℕ} (bf hf : ℝ→ℝ≥0)

def actualGeneralTargetLongitudinalResponse (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s i
  nativeOriginalLongitudinalPairing n 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 U K b C g.tree
    (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
      (joinSpin (g.spin σ))-C i) (g.embed s)

def actualGeneralTargetOriginalConstantPart (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s i
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*K i*(nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
    nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)

def actualGeneralTargetOriginalMeanCorrection (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let mean:=finitePhysicalMean (n+1) as b h i
  actualGeneralTargetOriginalConstantPart (n:=n) bf hf as i U+
    chi^2*b i*(mean-mean/(n+1:ℕ)-C i)-(mean-C i)

def actualGeneralTargetOriginalTaylorPart (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s i
  nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark

def actualGeneralTargetMeanTransportError (as : List PositiveMass) (i U V : ℕ) : ℝ :=
  let K:=nativeContinuumMixedClock n bf hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  2*(bf (partitionPoint 0 as i):ℝ)*chi*
    (actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U-
      actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i V)

end Readers

theorem actual_general_target_mean_eq_correction_response_transport_taylor
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativePhysicalResourceCenter n bf hf as i-nativeOriginalScalarPairMean as K i=
      actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as i U+
      2*(bf (partitionPoint 0 as i):ℝ)*chi*actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i V+
      actualGeneralTargetMeanTransportError (n:=n) bf hf as i U V+
      actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as i U := by
  have H:=actual_general_constant_gap_eq_twice_old_longitudinal (n:=n) bf hf hbf hhf as i U hi hU ho
  dsimp only at H ⊢
  unfold actualGeneralTargetOriginalMeanCorrection actualGeneralTargetOriginalConstantPart
    actualGeneralTargetMeanTransportError actualGeneralTargetLongitudinalResponse
    actualGeneralTargetOriginalTaylorPart
  dsimp only
  linear_combination H

end OAI.SKFluctuations.Cavity
