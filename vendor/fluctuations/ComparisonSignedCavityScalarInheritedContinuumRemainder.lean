module

public import ComparisonSignedCavityScalarNativeRemainder
public import ComparisonSignedCavityScalarMinimumBuffer
public import ComparisonSignedCavityPhysicalBareRootZero
public import ComparisonSignedCavityInheritedCanonicalSourceMoments
public import ComparisonSignedCavityContinuumMixedClock
public import ComparisonNativeActualMeanRawUpper

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem scalar_buffer_original_continuum_clock_gap
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i j : ℕ)
    (hmass : partitionPoint 0 as i < partitionPoint 0 as j) :
    nativeContinuumMixedClock n M.bf M.hf as i < nativeContinuumMixedClock n M.bf M.hf as j := by
  have hij : i ≤ j := by
    by_contra H
    exact (not_le_of_gt hmass) (partitionPoint_mono as ho (le_of_not_ge H))
  have hu:=partitionPoint_mem as ho i
  have hv:=partitionPoint_mem as ho j
  have huv:=partitionPoint_mono as ho hij
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have hb:=NNReal.coe_le_coe.mpr (hbf hu hv huv)
  have hh:=NNReal.coe_lt_coe.mpr (M.scalar_buffer_field_strictMonoOn hu hv hmass)
  have hm:=physicalOrderedPathS_monotone_unit n M.bf M.hf hbf hhf hu hv huv
  have hS0:=(physicalOrderedPathS_mem_unit n M.bf M.hf hbf hhf hu).1
  have H:=mul_le_mul hb hm hS0 (NNReal.coe_nonneg _)
  unfold nativeContinuumMixedClock
  nlinarith only [hh,H]

theorem original_continuum_mixed_clock_zero_of_root_field
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (hroot : M.h 0 = 0) :
    nativeContinuumMixedClock n M.bf M.hf as 0 = 0 := by
  simp [nativeContinuumMixedClock,partitionPoint,M.bare_root_field_zero hroot,
    orderedPathS,orderedPathPair_zero]

end NativeOverlapMinimum

theorem eventually_actual_minimum_inherited_original_continuum_scalar_remainder
    (Bclock Temp Cf A : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hA : 0 ≤ A)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃R : ℝ,0 < R ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.h 0 = 0 →
      ∀(before after : List PositiveMass) (a : PositiveMass),
        MassOrdered 0 (before++a::after) →
      ∀W : ℝ,0 ≤ W → M.xs ≤ W → R*W ≤ 1 →
      ∀j V : ℕ,j < before.length+1 → before.length+1 ≤ V →
        V ≤ (before++a::after).length →
        a.val < partitionPoint 0 (before++a::after) V →
        partitionPoint 0 (before++a::after) V ≤ A*W →
      ∀(tree : ClockTree (Spin n×Bool) (before++a::after))
        (start : ℝ) (_hoa : MassOrdered start (before++a::after)) (s : tree.Slot),
      let K:=nativeContinuumMixedClock n M.bf M.hf (before++a::after)
      let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree (before.length+1) K (p.embed s) p.mark)).sum
      |nativeOriginalScalarPairMean (before++a::after) K j-chi^2*K j| ≤
        nativeScalarLowRemainderConstant A R R*W^3 := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ck:=Cf+Temp*Cs
  have hCk : 0 ≤ Ck:=by dsimp only [Ck];positivity
  let R:=Ck*(1+A)+1
  have hR : 0 < R:=by dsimp only [R];positivity
  refine ⟨R,hR,?_⟩
  filter_upwards [HS] with n hn
  intro M hsource hroot before after a ho W hW hxW hsmall j V hj hUV hV hbuffer hsize tree start hoa s
  let as:=before++a::after
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf hbf hhf as ho
  have hK0 : ∀l,0 ≤ K l:=native_continuum_mixed_clock_nonneg n M.bf M.hf hbf hhf as ho
  have Hclock l : K l ≤ Ck*(M.xs+partitionPoint 0 as l) := by
    have hu:=partitionPoint_mem as ho l
    have HS' : orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as l) ≤
        Cs*(M.xs+partitionPoint 0 as l):=by
      by_cases hp : 0 < partitionPoint 0 as l
      · exact hn M _ ⟨hp,hu.2⟩
      · have hz : partitionPoint 0 as l=0:=le_antisymm (le_of_not_gt hp) hu.1
        rw [hz,orderedPathS,orderedPathPair_zero]
        simpa only [add_zero] using mul_nonneg hCs.le M.hxs.le
    have HC:=hsource _ hu
    have Hprod:=mul_le_mul HC.1 HS' (physicalOrderedPathS_mem_unit n M.bf M.hf hbf hhf hu).1 hT
    dsimp only [K,nativeContinuumMixedClock,Ck]
    nlinarith only [HC.2,Hprod]
  have Hbound l (hl : l ≤ V) : K l ≤ R*W := by
    have Hmass:=partitionPoint_mono as ho hl
    have Hsize : M.xs+partitionPoint 0 as l ≤ (1+A)*W:=by nlinarith only [hxW,hsize,Hmass]
    have H:=(Hclock l).trans (mul_le_mul_of_nonneg_left Hsize hCk)
    dsimp only [R]
    nlinarith only [H,hW]
  have hmass : partitionPoint 0 as (before.length+1) < partitionPoint 0 as V:=by
    simpa only [as,partitionPoint_after_before_one] using hbuffer
  have hgap:=M.scalar_buffer_original_continuum_clock_gap as ho (before.length+1) V hmass
  have htotal : 0 < K as.length:=(lt_of_le_of_lt (hK0 _) hgap).trans_le (hKm hV)
  have hzero : K 0 = 0:=M.original_continuum_mixed_clock_zero_of_root_field as hroot
  exact native_gamma_row_scalar_low_remainder_of_buffer n htotal before after a ho K hKm hzero rfl
    hW hA hR.le hR.le j V hj hUV hV hgap hsize
    (Hbound j (hj.le.trans hUV)) (Hbound (before.length+1) hUV)
    ((Hbound j (hj.le.trans hUV)).trans hsmall) tree start hoa s

end OAI.SKFluctuations.LaplaceWindowFormalization
