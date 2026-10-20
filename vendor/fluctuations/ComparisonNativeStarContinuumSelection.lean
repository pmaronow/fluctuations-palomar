module

public import ComparisonNativeStarActualBuffers
public import ComparisonNativeStarBufferMoments
public import ComparisonNativeRadiusRawEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
namespace NativeStarBuffer
open LaplaceWindowFormalization

def massNode (start quarter : ℝ) (j : ℕ) := start+(j:ℝ)*quarter

theorem exists_continuum_profile_block (S:ℝ → ℝ) (hS:MonotoneOn S (Icc (0:ℝ) 1))
    {start quarter eta:ℝ} {N:ℕ} (hstart:0 ≤ start) (hquarter:0 < quarter)
    (hend:massNode start quarter (4*N) ≤ 1) (hN:0 < N)
    (hvariation:S (massNode start quarter (4*N))-S start ≤ (N:ℝ)*eta) :
    ∃i<N,∀u∈Icc (massNode start quarter (4*i)) (massNode start quarter (4*(i+1))),
      ∀v∈Icc (massNode start quarter (4*i)) (massNode start quarter (4*(i+1))),|S u-S v| ≤ eta := by
  have hnodeMono:Monotone (massNode start quarter) := by
    intro j k hjk
    unfold massNode
    have hh:(j:ℝ) ≤ (k:ℝ):=by exact_mod_cast hjk
    exact add_le_add_right (mul_le_mul_of_nonneg_right hh hquarter.le) _
  have hnodeI j (hj:j ≤ 4*N):massNode start quarter j∈Icc (0:ℝ) 1 :=
    ⟨(by unfold massNode;positivity), (hnodeMono hj).trans hend⟩
  let P:=fun j:ℕ=>S (massNode start quarter (min j (4*N)))
  have hP:Monotone P := by
    intro j k hjk
    exact hS (hnodeI _ (min_le_right _ _)) (hnodeI _ (min_le_right _ _))
      (hnodeMono (min_le_min_right _ hjk))
  have hv:P (4*N)-P 0 ≤ (N:ℝ)*eta := by simpa [P,massNode] using hvariation
  obtain ⟨i,hi,hosc⟩:=exists_buffered_profile_window P hP hN hv
  have hiN:i<N:=Finset.mem_range.mp hi
  have hlo:4*i ≤ 4*N:=by omega
  have hhi:4*(i+1) ≤ 4*N:=by omega
  have he:=hosc (4*(i+1)) ⟨by omega,le_rfl⟩ (4*i) ⟨le_rfl,by omega⟩
  simp only [P,min_eq_left hlo,min_eq_left hhi] at he
  refine ⟨i,hiN,?_⟩
  intro u hu v hv
  have huI:u∈Icc (0:ℝ) 1:=⟨(hnodeI _ hlo).1.trans hu.1,hu.2.trans (hnodeI _ hhi).2⟩
  have hvI:v∈Icc (0:ℝ) 1:=⟨(hnodeI _ hlo).1.trans hv.1,hv.2.trans (hnodeI _ hhi).2⟩
  have hlu:=hS (hnodeI _ hlo) huI hu.1
  have hhu:=hS huI (hnodeI _ hhi) hu.2
  have hlv:=hS (hnodeI _ hlo) hvI hv.1
  have hhv:=hS hvI (hnodeI _ hhi) hv.2
  exact abs_le.mpr ⟨by linarith [(abs_le.mp he).2],by linarith [(abs_le.mp he).2]⟩

theorem finite_profile_abs_le_of_continuum_endpoints {n:ℕ}
    (steps:List (GaussianStep (FeatureIndex n))) (ha:OrderedSteps 0 steps)
    (q0:FeatureIndex n → ℝ≥0) {p q j:ℕ} (hq:q ≤ steps.length)
    (hpj:p ≤ j) (hjq:j ≤ q) {S A B eta err:ℝ}
    (hA:|physicalPathSecondMoment n steps q0 p-A| ≤ err)
    (hB:|physicalPathSecondMoment n steps q0 q-B| ≤ err)
    (hAS:|A-S| ≤ eta) (hBS:|B-S| ≤ eta) :
    |physicalPathSecondMoment n steps q0 j-S| ≤ eta+err := by
  have hlo:=physicalPathSecondMoment_mono n steps ha q0 hpj (hjq.trans hq)
  have hhi:=physicalPathSecondMoment_mono n steps ha q0 hjq hq
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hA).1,(abs_le.mp hAS).1],
    by linarith [(abs_le.mp hB).2,(abs_le.mp hBS).2]⟩

namespace CutBlocks

theorem star_buffer_data_of_profile_bound {n N:ℕ}
    {steps:List (GaussianStep (FeatureIndex n))} (D:CutBlocks n steps N)
    (ha:OrderedSteps 0 steps) (q0:FeatureIndex n → ℝ≥0) {i:ℕ} (hi:i<N)
    {S eta:ℝ} (heta:0 ≤ eta)
    (hprofile:∀j∈Icc (D.cut (4*i)) (D.cut (4*(i+1))),
      |physicalPathSecondMoment n steps q0 j-S| ≤ eta) :
    ∃B:PhysicalStarBufferData n steps q0 (D.fork i) (D.central i) S,
      B.km=physicalWindowWeight steps 0 (D.pastRows i) ∧
      B.kp=physicalWindowWeight steps 0 (D.futureRows i) ∧ B.eta=eta := by
  have hq:4*(i+1) ≤ 4*N:=by omega
  have hm:0 < physicalWindowMass steps 0 (D.pastRows i):=by rw [D.past_mass hi];exact D.quarter_pos
  have hp:0 < physicalWindowMass steps 0 (D.futureRows i):=by rw [D.future_mass hi];exact D.quarter_pos
  have pastI j (hj:j∈D.pastRows i):j.val∈Icc (D.cut (4*i)) (D.cut (4*(i+1))) := by
    have hj':=(mem_physicalIntervalCells steps _ _ j).mp hj
    exact ⟨hj'.1,hj'.2.le.trans (D.monotone (by omega))⟩
  have futureI j (hj:j∈D.futureRows i):j.val∈Icc (D.cut (4*i)) (D.cut (4*(i+1))) := by
    have hj':=(mem_physicalIntervalCells steps _ _ j).mp hj
    exact ⟨(D.monotone (by omega)).trans hj'.1,hj'.2.le⟩
  have hPast j (hj:pathMassDifferences steps 0 j*physicalWindowWeight steps 0 (D.pastRows i) j ≠ 0):
      j∈D.pastRows i := by by_contra hn;simp [physicalWindowWeight,hn] at hj
  have hFuture j (hj:pathMassDifferences steps 0 j*physicalWindowWeight steps 0 (D.futureRows i) j ≠ 0):
      j∈D.futureRows i := by by_contra hn;simp [physicalWindowWeight,hn] at hj
  let B:PhysicalStarBufferData n steps q0 (D.fork i) (D.central i) S := {
    km:=physicalWindowWeight steps 0 (D.pastRows i),kp:=physicalWindowWeight steps 0 (D.futureRows i),eta:=eta
    nonnegm:=physicalWindowWeight_nonneg steps ha _,nonnegp:=physicalWindowWeight_nonneg steps ha _
    normalizedm:=physicalWindowWeight_normalized steps 0 _ hm,normalizedp:=physicalWindowWeight_normalized steps 0 _ hp
    forkBound:=(D.bound _ (by omega)).trans (by omega),centralBound:=(D.bound _ (by omega)).trans (by omega)
    forkPast:=by intro j hj;exact ((mem_physicalIntervalCells steps _ _ j).mp (hPast j hj)).2.le
    centralPast:=by intro j hj;exact ((mem_physicalIntervalCells steps _ _ j).mp (hPast j hj)).2.le.trans (D.monotone (by omega))
    forkFuture:=by intro j hj;exact (D.monotone (by omega)).trans ((mem_physicalIntervalCells steps _ _ j).mp (hFuture j hj)).1
    centralFuture:=by intro j hj;exact ((mem_physicalIntervalCells steps _ _ j).mp (hFuture j hj)).1
    etaNonneg:=heta
    meanPast:=window_mean_abs_le steps ha q0 _ hm heta (fun j hj=>hprofile j.val (pastI j hj))
    meanFuture:=window_mean_abs_le steps ha q0 _ hp heta (fun j hj=>hprofile j.val (futureI j hj)) }
  exact ⟨B,rfl,rfl,rfl⟩

end CutBlocks

theorem sampled_continuum_node_error (n:ℕ) (b h:ℝ → ℝ≥0)
    (hb:MonotoneOn b (Icc (0:ℝ) 1)) (hh:MonotoneOn h (Icc (0:ℝ) 1))
    (as:List PositiveMass) (ho:MassOrdered 0 as) (he:partitionEnd 0 as=1)
    {mesh u:ℝ} (hm:PartitionMesh mesh 0 as) (i:ℕ) (hi:i ≤ as.length)
    (hnode:partitionPoint 0 as i=u) (hu:0 < u) :
    |physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
      (completedPathClock (n+1) b h 0) i-orderedPathS (n+1) b h u| ≤
    mesh*(2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n)
      (completedPathClock (n+1) b h)) := by
  have h:=physicalSampledNodeSecondMoment_error n b h hb hh as ho he hm i hi (by simpa only [hnode] using hu)
  simpa only [hnode] using h

end NativeStarBuffer
end OAI.SKFluctuations
