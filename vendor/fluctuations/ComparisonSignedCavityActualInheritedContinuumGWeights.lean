module

public import ComparisonSignedCavityActualOriginalContinuumWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem actual_continuum_G_weight_bound_of_total_clock
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp W cK : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i star U : ℕ} (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*cK) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterminal : K as.length≤Temp :=
    (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans (M.inherited_total_clock_le htotal 1 (by norm_num))
  have hbeta:=nativeOriginalClockGBranchBeta_bound M htotal ho hs hU K hK hKm st tag
  have H:=native_full_gamma_recursion_coefficient_bound n st.tree ho 0 ho U (by omega)
    hU K hKm hK hterminal st.term.live.test.target hW hcK hstarK hbeta
  dsimp only at H ⊢
  unfold nativeOriginalClockParentWeight
  dsimp only
  rw [abs_mul,abs_of_pos hW]
  apply (mul_le_mul_of_nonneg_left H hW.le).trans
  apply le_of_eq
  field_simp

theorem actual_retained_continuum_G_weight_bound_of_total_clock
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp W cK : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK)
    (u : PositiveMass) (hclock : cK*W≤actualMixedClock (n+1) M.bf M.hf u.val)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hu : u∈as)
    {i U : ℕ} (hs : retainedMassPrefixIndex u.val as<U) (hU : U≤as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex u.val as))
    (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockGBranchBeta U K b st tag)|≤
      Temp/(Real.exp (-4*Temp)*cK) := by
  apply actual_continuum_G_weight_bound_of_total_clock M htotal hW hcK as ho hs hU _ st tag
  rw [native_continuum_mixed_clock_retained_eq n M.bf M.hf as ho u hu]
  exact hclock

end OAI.SKFluctuations.Cavity
