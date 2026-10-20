module

public import ComparisonActualHighWallScalarClockGap
public import ComparisonActualGeneralScalarBufferCut

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

 theorem eventually_actual_high_wall_original_scalar_remainder_of_buffer
    (Bclock A : ℝ) (hA : 0 ≤ A) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃R : ℝ,0 < R ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(as : List PositiveMass),MassOrdered 0 as →
      ∀W : ℝ,0 ≤ W → M.xs ≤ W → R*W ≤ 1 →
      ∀(j U V : ℕ),j < U → U ≤ V → V ≤ as.length →
        M.data.s ≤ partitionPoint 0 as U →
        partitionPoint 0 as U < partitionPoint 0 as V →
        partitionPoint 0 as V ≤ A*W →
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeOriginalScalarPairMean as K j-chi^2*K j| ≤ nativeScalarLowRemainderConstant A R R*W^3 := by
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_high_wall_continuum_clock_mass_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let R:=CK*(1+A)+1
  have hR : 0 < R:=by dsimp only [R];positivity
  refine ⟨R,hR,?_⟩
  filter_upwards [HK] with n hnK
  intro M hwork as ho W hW hxW hsmall j U V hj hUV hV hhigh hbuffer hsize
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho
  have hK0 : ∀l,0 ≤ K l:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho
  have Hbound l (hl : l ≤ V) : K l ≤ R*W:=by
    have Hmass:=partitionPoint_mono as ho hl
    have Hsize : M.xs+partitionPoint 0 as l ≤ (1+A)*W:=by nlinarith only [hxW,hsize,Hmass]
    have H:=(hnK M hwork as ho l).trans (mul_le_mul_of_nonneg_left Hsize hCK.le)
    dsimp only [R]
    nlinarith only [H,hW]
  have hgap:=M.scalar_buffer_original_clock_gap_above_wall as ho U V hhigh hbuffer
  have htotal : 0 < K as.length:=(lt_of_le_of_lt (hK0 U) hgap).trans_le (hKm hV)
  have hzero : K 0=0:=by
    dsimp only [K]
    simp [nativeContinuumMixedClock,partitionPoint,M.data.root_field_zero M.alpha,
      orderedPathS,orderedPathPair_zero]
  exact actual_general_scalar_pair_low_remainder_of_buffer_cut htotal as ho K hKm hzero rfl
    hW hA hR.le hR.le j U V hj hUV hV hgap hsize
    (Hbound j (hj.le.trans hUV)) (Hbound U hUV)
    ((Hbound j (hj.le.trans hUV)).trans hsmall)

 theorem eventually_actual_high_wall_original_scalar_remainder_of_buffer_along
    (Bclock A : ℝ) (hA : 0 ≤ A) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃R : ℝ,0 < R ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(as : List PositiveMass),MassOrdered 0 as →
      ∀W : ℝ,0 ≤ W → M.xs ≤ W → R*W ≤ 1 →
      ∀(j U V : ℕ),j < U → U ≤ V → V ≤ as.length →
        M.data.s ≤ partitionPoint 0 as U →
        partitionPoint 0 as U < partitionPoint 0 as V →
        partitionPoint 0 as V ≤ A*W →
      let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeOriginalScalarPairMean as K j-chi^2*K j| ≤ nativeScalarLowRemainderConstant A R R*W^3 := by
  obtain ⟨R,hR,H⟩:=eventually_actual_high_wall_original_scalar_remainder_of_buffer
    (D:=D) Bclock A hA hm hdelta hroom hcl hcu hAz hC0 hCt
  exact ⟨R,hR,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity
