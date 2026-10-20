module

public import ComparisonSignedCavityMassInnovation
public import ComparisonNativeStarBufferSelection

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization NativeStarBuffer

theorem exists_actual_star_buffer_with_native_innovation
    (n : ℕ) (i₀ : Fin n) (Nblocks : ℕ) (hblocks : 0<Nblocks)
    {c N d lam M₀ g₀ a eta : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (b : ℝ→ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2)
    (hM₀ : 0<M₀) (hg₀ : 0<g₀) (ha : 0 ≤ a) (heta : 0 ≤ eta)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (q0 : FeatureIndex n→ℝ≥0) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let steps := nativeSampledPhysicalSteps n bf hf as
    ∀ C : CutBlocks n steps Nblocks,
      a ≤ C.start →
      (∀ j ≤ 4*Nblocks,M (partitionPoint 0 as (C.cut j)) ≤ M₀) →
      (∀ j ≤ 4*Nblocks,g₀ ≤ laplaceComparisonStrength d lam
        (R (partitionPoint 0 as (C.cut j)))) →
      physicalPathSecondMoment n steps q0 (C.cut (4*Nblocks))-
        physicalPathSecondMoment n steps q0 (C.cut 0) ≤ (Nblocks:ℝ)*eta →
      ∃ i : ℕ,∃ _hi : i<Nblocks,
        ∃ B : PhysicalStarBufferData n steps q0 (C.fork i) (C.central i)
          (physicalPathSecondMoment n steps q0 (C.fork i)),
          B.km=physicalWindowWeight steps 0 (C.pastRows i) ∧
          B.kp=physicalWindowWeight steps 0 (C.futureRows i) ∧ B.eta=eta ∧
          physicalWindowMass steps 0 (C.pastRows i)=C.quarter ∧
          physicalWindowMass steps 0 (C.futureRows i)=C.quarter ∧
          let D := physicalFieldDuration (fun st=>st.2 (Sum.inl i₀))
            (cutSlice steps (C.fork i) (C.central i))
          0<D ∧ 2*g₀*C.quarter/(3*M₀*Real.log N) ≤ D ∧
            PhysicalProjectionClock n steps (C.fork i) (C.central i)
              (as.length+1) a D := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let steps := nativeSampledPhysicalSteps n bf hf as
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered _ _ ho
  dsimp only
  intro C hstart hcap hstrength hvariation
  have hquarter : 0<C.quarter := C.quarter_pos
  obtain ⟨i,hi,B,hBm,hBp,hBe,hpast,hfuture⟩ := C.exists_star_buffer_data hs q0 hblocks heta hvariation
  have hfj : 4*i+1 ≤ 4*Nblocks := by omega
  have hcj : 4*i+3 ≤ 4*Nblocks := by omega
  have hfork : C.fork i ≤ C.central i := C.monotone (by omega)
  have hcentral : C.central i ≤ as.length := by
    simpa only [CutBlocks.central,steps,nativeSampledPhysicalSteps,sampleClockSteps_length] using C.bound _ hcj
  have hpoint (j : ℕ) (hj : j ≤ 4*Nblocks) :
      partitionPoint 0 as (C.cut j)=C.start+(j:ℝ)*C.quarter := by
    have hjlen : C.cut j ≤ as.length := by
      simpa only [steps,nativeSampledPhysicalSteps,sampleClockSteps_length] using C.bound j hj
    have H := C.cut_mass j hj
    change physicalCutMass 0 (nativeSampledPhysicalSteps n bf hf as) (C.cut j)=
      C.start+(j:ℝ)*C.quarter at H
    unfold nativeSampledPhysicalSteps at H
    rw [physicalCutMass_sampleClockSteps _ _ _ _ hjlen] at H
    exact H
  have hmassgap : 2*C.quarter=partitionPoint 0 as (C.central i)-partitionPoint 0 as (C.fork i) := by
    rw [CutBlocks.central,CutBlocks.fork,hpoint _ hcj,hpoint _ hfj]
    push_cast
    ring
  have hanchor : a ≤ partitionPoint 0 as (C.fork i) := by
    rw [CutBlocks.fork,hpoint _ hfj]
    exact hstart.trans (le_add_of_nonneg_right (by positivity))
  have H := actual_comparison_native_mass_innovation_clock n i₀ hc hk hkc hm hM α b hb hlb
    hN hlog hd hnd hlam hld
    (gap:=2*C.quarter) (M₀:=M₀) (g₀:=g₀) (by positivity) hM₀ hg₀.le as ho
    (fork:=C.fork i) (pre:=C.fork i) (v:=C.central i) (w:=as.length+1)
    le_rfl hfork (hcentral.trans (by omega)) hcentral le_rfl ha hanchor
    (hcap _ hcj) hmassgap.le (hstrength _ hcj)
  dsimp only at H
  have hDpos : 0<physicalFieldDuration (fun st=>st.2 (Sum.inl i₀))
      (cutSlice steps (C.fork i) (C.central i)) := by
    apply lt_of_lt_of_le _ H.1
    have hlog0 : 0<Real.log N := zero_lt_one.trans_le hlog
    positivity
  refine ⟨i,hi,B,hBm,hBp,hBe,hpast,hfuture,hDpos,?_,H.2⟩
  convert H.1 using 1 <;> ring

end OAI.SKFluctuations.Cavity
