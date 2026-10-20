module

public import ComparisonSignedCavityScalarNativeRemainder
public import ComparisonSignedCavityStarClockTransport

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity GaussianCalculus Scalar
set_option maxHeartbeats 3500000

theorem laplaceComparisonField_strictMonoOn {d lam : ℝ}
    (hd : d≠0) (hlam : 0<lam) :
    StrictMonoOn (fun r=>laplaceComparisonStrength d lam r*r) (Icc (0:ℝ) 1) := by
  let g:=laplaceComparisonStrength d lam
  have hg : Differentiable ℝ g := (laplaceComparisonStrength_contDiff d lam).differentiable (by norm_num)
  apply strictMonoOn_of_deriv_pos (convex_Icc (0:ℝ) 1) (hg.continuous.mul continuous_id).continuousOn
  intro r _
  have heq : deriv (fun t=>g t*t) r=g r*(1-comparisonLogSlope g r) := by
    change deriv (g*id) r=g r*(1-comparisonLogSlope g r)
    rw [((hg r).hasDerivAt.mul (hasDerivAt_id r)).deriv]
    unfold comparisonLogSlope
    have hp : g r≠0 := (laplaceComparisonStrength_pos d hlam r).ne'
    simp only [id_eq]
    field_simp [hp]
    ring
  change 0<deriv (fun t=>g t*t) r
  rw [heq]
  exact mul_pos (laplaceComparisonStrength_pos d hlam r)
    (sub_pos.mpr (laplaceComparisonStrength_logSlope_mem hd hlam.ne' r).2)

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem scalar_buffer_field_strictMonoOn
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :
    StrictMonoOn M.hf (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  have hR := comparisonSweepQuantile_strictMono M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hu hv huv
  have huR := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hvR := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha v
  have hfield := laplaceComparisonField_strictMonoOn M.context.hd.ne' M.hlam huR hvR hR
  have hh := M.hh hu hv huv.le
  have hu0 : 0≤M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u :=
    add_nonneg (M.hh0.trans (M.hh (by norm_num) hu hu.1))
      (mul_nonneg (laplaceComparisonStrength_pos _ M.hlam _).le huR.1)
  have hv0 : 0≤M.h v+laplaceComparisonStrength M.context.d M.lam (M.R v)*M.R v :=
    add_nonneg (M.hh0.trans (M.hh (by norm_num) hv hv.1))
      (mul_nonneg (laplaceComparisonStrength_pos _ M.hlam _).le hvR.1)
  apply NNReal.coe_lt_coe.mp
  change ((M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u).toNNReal:ℝ)<
    ((M.h v+laplaceComparisonStrength M.context.d M.lam (M.R v)*M.R v).toNNReal:ℝ)
  rw [Real.coe_toNNReal _ hu0,Real.coe_toNNReal _ hv0]
  linarith

theorem scalar_buffer_retained_mixed_clock_gap
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i j : ℕ)
    (hmass : partitionPoint 0 as i<partitionPoint 0 as j) :
    retainedStarMixedClock n M.bf M.hf as i<retainedStarMixedClock n M.bf M.hf as j := by
  have hidx : i≤j := by
    by_contra H
    have H' := partitionPoint_mono as ho (le_of_not_ge H)
    exact (not_le_of_gt hmass) H'
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hb:=NNReal.coe_le_coe.mpr (toNNReal_monotoneOn had.1
    (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) (partitionPoint_mono as ho hidx))
  have hh:=NNReal.coe_lt_coe.mpr (M.scalar_buffer_field_strictMonoOn
    (partitionPoint_mem as ho i) (partitionPoint_mem as ho j) hmass)
  have hm:=finitePhysicalMean_monotone (n+1) ho (retainedStarMatrix M.bf as)
    (retainedStarField M.hf as) hidx
  have H:=mul_le_mul hb hm
    (finitePhysicalMean_nonneg (n+1) as (retainedStarMatrix M.bf as) (retainedStarField M.hf as) i)
    (M.bf (partitionPoint 0 as j)).coe_nonneg
  change (M.hf (partitionPoint 0 as i):ℝ)+(M.bf (partitionPoint 0 as i):ℝ)*
      finitePhysicalMean (n+1) as (retainedStarMatrix M.bf as) (retainedStarField M.hf as) i<
    (M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
      finitePhysicalMean (n+1) as (retainedStarMatrix M.bf as) (retainedStarField M.hf as) j
  linarith

theorem native_scalar_low_remainder_of_actual_minimum_buffer
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {W A R Ru : ℝ} (hW : 0≤W) (hA : 0≤A) (hR : 0≤R) (hRu : 0≤Ru)
    (before after : List PositiveMass) (a : PositiveMass)
    (ho : MassOrdered 0 (before++a::after))
    (j V : ℕ) (hj : j<before.length+1) (hUV : before.length+1≤V)
    (hV : V≤(before++a::after).length)
    (hbuffer : a.val<partitionPoint 0 (before++a::after) V)
    (hsize : partitionPoint 0 (before++a::after) V≤A*W)
    (hzero : retainedStarMixedClock n M.bf M.hf (before++a::after) 0=0)
    (hjclock : retainedStarMixedClock n M.bf M.hf (before++a::after) j≤R*W)
    (hUclock : retainedStarMixedClock n M.bf M.hf (before++a::after) (before.length+1)≤Ru*W)
    (hsmall : retainedStarMixedClock n M.bf M.hf (before++a::after) j≤1)
    (tree : ClockTree (Spin n×Bool) (before++a::after))
    (start : ℝ) (hoa : MassOrdered start (before++a::after)) (s : tree.Slot) :
    let K:=retainedStarMixedClock n M.bf M.hf (before++a::after)
    let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree (before.length+1) K (p.embed s) p.mark)).sum
    |nativeOriginalScalarPairMean (before++a::after) K j-chi^2*K j|≤
      nativeScalarLowRemainderConstant A R Ru*W^3 := by
  let as:=before++a::after
  let K:=retainedStarMixedClock n M.bf M.hf as
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hKm := retainedStarMixedClock_monotone n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) as ho
  have hmass : partitionPoint 0 as (before.length+1)<partitionPoint 0 as V := by
    rw [partitionPoint_after_before_one]
    exact hbuffer
  have hgap := M.scalar_buffer_retained_mixed_clock_gap as ho (before.length+1) V hmass
  have hpos : 0<K as.length := by
    have h0:=retainedStarMixedClock_nonneg n M.bf M.hf as (before.length+1)
    exact (h0.trans_lt hgap).trans_le (hKm hV)
  exact native_gamma_row_scalar_low_remainder_of_buffer n hpos before after a ho K hKm hzero rfl
    hW hA hR hRu j V hj hUV hV hgap hsize hjclock hUclock hsmall tree start hoa s

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
