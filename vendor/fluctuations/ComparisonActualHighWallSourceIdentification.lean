module

public import ComparisonActualHighWallOverlapAmplitude
public import ComparisonSignedCavityActualConstantJointSourceLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open LaplaceWindowFormalization
open scoped BigOperators NNReal Topology
set_option maxHeartbeats 12000000

theorem actual_joint_constant_source_tendsto_original_gap
    {T : ℝ} (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (u : PositiveMass) (hu : u∈us)
    (U : ℕ→ℕ)
    (hcut : ∀ᶠ k : ℕ in atTop,retainedMassPrefixIndex u.val (finiteCutMasses us k)<U k ∧
      U k≤(finiteCutMasses us k).length) :
    Tendsto (fun k=>
      let as:=finiteCutMasses us k
      nativeActualConstantJointStarSource n as (retainedMassPrefixIndex u.val as) (U k)
        (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ))
        (nativeContinuumMixedClock n bf hf as) (nativePhysicalResourceCenter n bf hf as))
      atTop (𝓝 (orderedPathS (n+1) bf hf u.val-
        scalarCovarianceResponse hT (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal)
          (actualMixedClock (n+1) bf hf u.val))) := by
  apply (continuum_retained_scalar_mean_gap_tendsto n bf hf hbf hhf hroot hT htotal
    us hus u hu).congr'
  filter_upwards [hcut] with k hk
  let as:=finiteCutMasses us k
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let S:=nativePhysicalResourceCenter n bf hf as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hKS : ∀j,K j=h j+b j*S j:=
    native_continuum_mixed_clock_eq_original_center n bf hf hbf hhf as ho
  have hb : ∀j,0≤b j:=fun j=>NNReal.coe_nonneg _
  have hh : ∀j,0≤h j:=fun j=>NNReal.coe_nonneg _
  have hbm : Monotone b:=by
    intro i j hij
    exact hbf (partitionPoint_mem as ho i) (partitionPoint_mem as ho j)
      (partitionPoint_mono as ho hij)
  have hhm : Monotone h:=by
    intro i j hij
    exact hhf (partitionPoint_mem as ho i) (partitionPoint_mem as ho j)
      (partitionPoint_mono as ho hij)
  have hK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
  have hKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
  exact (native_actual_constant_joint_source_eq_original_mean_gap n as
    (retainedMassPrefixIndex u.val as) (U k) hk.1 hk.2 ho b h K S hKS hb hh hK hbm hhm hKm).symm

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallData
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped BigOperators NNReal Topology
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData (n+1) delta)

theorem hTpos : 0 < a.T := a.hepsilon.1.trans a.hepsilon.2

def scalarMassProfile (alpha : a.Profile) : boundedMassProfiles :=
  actualMixedMassProfile a.hTpos (n+1) a.hn (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) (a.total_clock_le alpha)

theorem joint_constant_source_tendsto_actual_residual
    (alpha : a.Profile) (us : List PositiveMass) (hus : ∀u∈us,u.val≤1)
    (u : PositiveMass) (hu : u∈us) (U : ℕ→ℕ)
    (hcut : ∀ᶠ k : ℕ in atTop,retainedMassPrefixIndex u.val (finiteCutMasses us k)<U k ∧
      U k≤(finiteCutMasses us k).length) :
    Tendsto (fun k=>
      let as:=finiteCutMasses us k
      nativeActualConstantJointStarSource n as (retainedMassPrefixIndex u.val as) (U k)
        (fun j=>(a.bf alpha (partitionPoint 0 as j):ℝ))
        (fun j=>(a.hf alpha (partitionPoint 0 as j):ℝ))
        (nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as)
        (nativePhysicalResourceCenter n (a.bf alpha) (a.hf alpha) as))
      atTop (𝓝 (orderedPathS (n+1) (a.bf alpha) (a.hf alpha) u.val-
        scalarCovarianceResponse a.hTpos (a.scalarMassProfile alpha)
          (actualMixedClock (n+1) (a.bf alpha) (a.hf alpha) u.val))) :=
  actual_joint_constant_source_tendsto_original_gap n (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) (a.root_field_zero alpha) a.hTpos
    (a.total_clock_le alpha) us hus u hu U hcut

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallData
