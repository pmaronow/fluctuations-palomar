module

public import CavityBufferPolynomial
public import PhysicalWindowTraceAggregation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000

namespace NativeStarBuffer

theorem interval_mass_eq {n : ℕ} (steps : List (GaussianStep (FeatureIndex n)))
    {p q : ℕ} (hpq : p ≤ q) (hq : q ≤ steps.length+1) :
    physicalWindowMass steps 0 (physicalIntervalCells steps p q)=
      physicalCutMass 0 steps q-physicalCutMass 0 steps p := by
  have hs := LaplaceWindowFormalization.physicalWindowCellSum_eq_Ico steps 0 (p:=p) hq (fun _=>1)
  simp only [mul_one] at hs
  have hm : physicalWindowMass steps 0 (physicalIntervalCells steps p q)=
      ∑ j,physicalWindowCellMass steps 0 (physicalIntervalCells steps p q) j := by
    simp only [physicalWindowMass,physicalWindowCellMass,Finset.sum_ite_mem,Finset.univ_inter]
  rw [hm,hs]
  exact Finset.sum_Ico_sub (fun j=>physicalCutMass 0 steps j) hpq

theorem window_mean_abs_le {n : ℕ} (steps : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 steps) (q0 : FeatureIndex n→ℝ≥0)
    (J : Finset (Fin (steps.length+1))) (hmass : 0<physicalWindowMass steps 0 J)
    {S eta : ℝ} (_heta : 0 ≤ eta)
    (hprofile : ∀j∈J,|physicalPathSecondMoment n steps q0 j.val-S| ≤ eta) :
    |(∑j,pathMassDifferences steps 0 j*physicalWindowWeight steps 0 J j*
      physicalPathSecondMoment n steps q0 j.val)-S| ≤ eta := by
  let a := fun j:Fin (steps.length+1)=>pathMassDifferences steps 0 j*physicalWindowWeight steps 0 J j
  have ha0 j : 0 ≤ a j := mul_nonneg (pathMassDifferences_nonneg steps ha j)
    (physicalWindowWeight_nonneg steps ha J j)
  have hanorm : ∑j,a j=1 := physicalWindowWeight_normalized steps 0 J hmass
  have heq : (∑j,a j*physicalPathSecondMoment n steps q0 j.val)-S=
      ∑j,a j*(physicalPathSecondMoment n steps q0 j.val-S) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hanorm,one_mul]
  change |(∑j,a j*physicalPathSecondMoment n steps q0 j.val)-S| ≤ eta
  rw [heq]
  calc
    _ ≤ ∑j,|a j*(physicalPathSecondMoment n steps q0 j.val-S)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑j,a j*eta := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hJ : j∈J
      · rw [abs_mul,abs_of_nonneg (ha0 j)]
        exact mul_le_mul_of_nonneg_left (hprofile j hJ) (ha0 j)
      · simp [a,physicalWindowWeight,hJ]
    _ = eta := by rw [←Finset.sum_mul,hanorm,one_mul]

structure CutBlocks (n : ℕ) (steps : List (GaussianStep (FeatureIndex n))) (N : ℕ) where
  cut : ℕ→ℕ
  monotone : Monotone cut
  bound : ∀j ≤ 4*N,cut j ≤ steps.length
  start : ℝ
  quarter : ℝ
  quarter_pos : 0<quarter
  cut_mass : ∀j ≤ 4*N,physicalCutMass 0 steps (cut j)=start+(j:ℝ)*quarter

namespace CutBlocks

variable {n N : ℕ} {steps : List (GaussianStep (FeatureIndex n))}

def pastRows (D : CutBlocks n steps N) (i : ℕ) :=
  physicalIntervalCells steps (D.cut (4*i)) (D.cut (4*i+1))
def futureRows (D : CutBlocks n steps N) (i : ℕ) :=
  physicalIntervalCells steps (D.cut (4*i+3)) (D.cut (4*(i+1)))
def fork (D : CutBlocks n steps N) (i : ℕ) := D.cut (4*i+1)
def central (D : CutBlocks n steps N) (i : ℕ) := D.cut (4*i+3)

theorem past_mass (D : CutBlocks n steps N) {i : ℕ} (hi : i<N) :
    physicalWindowMass steps 0 (D.pastRows i)=D.quarter := by
  have hq : 4*i+1 ≤ 4*N := by omega
  have hp : 4*i ≤ 4*N := by omega
  rw [pastRows,interval_mass_eq steps (D.monotone (by omega)) ((D.bound _ hq).trans (by omega)),
    D.cut_mass _ hq,D.cut_mass _ hp]
  push_cast
  ring

theorem future_mass (D : CutBlocks n steps N) {i : ℕ} (hi : i<N) :
    physicalWindowMass steps 0 (D.futureRows i)=D.quarter := by
  have hq : 4*(i+1) ≤ 4*N := by omega
  have hp : 4*i+3 ≤ 4*N := by omega
  rw [futureRows,interval_mass_eq steps (D.monotone (by omega)) ((D.bound _ hq).trans (by omega)),
    D.cut_mass _ hq,D.cut_mass _ hp]
  push_cast
  ring

theorem exists_good_block (ha : OrderedSteps 0 steps) (q0 : FeatureIndex n→ℝ≥0)
    (D : CutBlocks n steps N) (hN : 0<N) {eta : ℝ}
    (hvariation : physicalPathSecondMoment n steps q0 (D.cut (4*N))-
      physicalPathSecondMoment n steps q0 (D.cut 0) ≤ (N:ℝ)*eta) :
    ∃i<N,∀j∈Set.Icc (D.cut (4*i)) (D.cut (4*(i+1))),
      ∀k∈Set.Icc (D.cut (4*i)) (D.cut (4*(i+1))),
        |physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 k| ≤ eta := by
  let S := fun j:ℕ=>physicalPathSecondMoment n steps q0 (D.cut (min j (4*N)))
  have hS : Monotone S := by
    intro j k hjk
    exact physicalPathSecondMoment_mono n steps ha q0
      (D.monotone (min_le_min_right _ hjk)) (D.bound _ (min_le_right _ _))
  have hv : S (4*N)-S 0 ≤ (N:ℝ)*eta := by
    simpa only [S,min_self,min_eq_left (Nat.zero_le _)] using hvariation
  obtain ⟨i,hi,hosc⟩ := exists_buffered_profile_window S hS hN hv
  have hiN : i<N := Finset.mem_range.mp hi
  have hp : 4*i ≤ 4*N := by omega
  have hq : 4*(i+1) ≤ 4*N := by omega
  have hend := hosc (4*(i+1)) ⟨by omega,le_rfl⟩ (4*i) ⟨le_rfl,by omega⟩
  simp only [S,min_eq_left hp,min_eq_left hq] at hend
  refine ⟨i,hiN,?_⟩
  intro j hj k hk
  have hloJ := physicalPathSecondMoment_mono n steps ha q0 hj.1 (hj.2.trans (D.bound _ hq))
  have hhiJ := physicalPathSecondMoment_mono n steps ha q0 hj.2 (D.bound _ hq)
  have hloK := physicalPathSecondMoment_mono n steps ha q0 hk.1 (hk.2.trans (D.bound _ hq))
  have hhiK := physicalPathSecondMoment_mono n steps ha q0 hk.2 (D.bound _ hq)
  have he := abs_le.mp hend
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem exists_star_buffer_data (ha : OrderedSteps 0 steps) (q0 : FeatureIndex n→ℝ≥0)
    (D : CutBlocks n steps N) (hN : 0<N) {eta : ℝ} (heta : 0 ≤ eta)
    (hvariation : physicalPathSecondMoment n steps q0 (D.cut (4*N))-
      physicalPathSecondMoment n steps q0 (D.cut 0) ≤ (N:ℝ)*eta) :
    ∃i : ℕ,∃_hi : i<N,∃B : PhysicalStarBufferData n steps q0 (D.fork i) (D.central i)
      (physicalPathSecondMoment n steps q0 (D.fork i)),
      B.km=physicalWindowWeight steps 0 (D.pastRows i) ∧
      B.kp=physicalWindowWeight steps 0 (D.futureRows i) ∧ B.eta=eta ∧
      physicalWindowMass steps 0 (D.pastRows i)=D.quarter ∧
      physicalWindowMass steps 0 (D.futureRows i)=D.quarter := by
  obtain ⟨i,hi,hosc⟩ := exists_good_block ha q0 D hN hvariation
  have hq : 4*(i+1) ≤ 4*N := by omega
  have hm : 0<physicalWindowMass steps 0 (D.pastRows i) := by rw [D.past_mass hi];exact D.quarter_pos
  have hp : 0<physicalWindowMass steps 0 (D.futureRows i) := by rw [D.future_mass hi];exact D.quarter_pos
  have forkI : D.fork i∈Icc (D.cut (4*i)) (D.cut (4*(i+1))) :=
    ⟨D.monotone (by omega),D.monotone (by omega)⟩
  have pastI j (hj : j∈D.pastRows i) : j.val∈Icc (D.cut (4*i)) (D.cut (4*(i+1))) := by
    have hj' := (mem_physicalIntervalCells steps _ _ j).mp hj
    exact ⟨hj'.1,hj'.2.le.trans (D.monotone (by omega))⟩
  have futureI j (hj : j∈D.futureRows i) : j.val∈Icc (D.cut (4*i)) (D.cut (4*(i+1))) := by
    have hj' := (mem_physicalIntervalCells steps _ _ j).mp hj
    exact ⟨(D.monotone (by omega)).trans hj'.1,hj'.2.le⟩
  have hPast j (hj : pathMassDifferences steps 0 j*physicalWindowWeight steps 0 (D.pastRows i) j ≠ 0) :
      j∈D.pastRows i := by
    by_contra hn
    simp [physicalWindowWeight,hn] at hj
  have hFuture j (hj : pathMassDifferences steps 0 j*physicalWindowWeight steps 0 (D.futureRows i) j ≠ 0) :
      j∈D.futureRows i := by
    by_contra hn
    simp [physicalWindowWeight,hn] at hj
  have hmmean := window_mean_abs_le steps ha q0 (D.pastRows i) hm heta
    (fun j hj=>hosc j.val (pastI j hj) (D.fork i) forkI)
  have hpmean := window_mean_abs_le steps ha q0 (D.futureRows i) hp heta
    (fun j hj=>hosc j.val (futureI j hj) (D.fork i) forkI)
  let B : PhysicalStarBufferData n steps q0 (D.fork i) (D.central i)
      (physicalPathSecondMoment n steps q0 (D.fork i)) := {
    km:=physicalWindowWeight steps 0 (D.pastRows i)
    kp:=physicalWindowWeight steps 0 (D.futureRows i)
    eta:=eta
    nonnegm:=physicalWindowWeight_nonneg steps ha _
    nonnegp:=physicalWindowWeight_nonneg steps ha _
    normalizedm:=physicalWindowWeight_normalized steps 0 _ hm
    normalizedp:=physicalWindowWeight_normalized steps 0 _ hp
    forkBound:=(D.bound _ (by omega)).trans (by omega)
    centralBound:=(D.bound _ (by omega)).trans (by omega)
    forkPast:=by
      intro j hj
      exact ((mem_physicalIntervalCells steps _ _ j).mp (hPast j hj)).2.le
    centralPast:=by
      intro j hj
      exact ((mem_physicalIntervalCells steps _ _ j).mp (hPast j hj)).2.le.trans (D.monotone (by omega))
    forkFuture:=by
      intro j hj
      exact (D.monotone (by omega)).trans ((mem_physicalIntervalCells steps _ _ j).mp (hFuture j hj)).1
    centralFuture:=by
      intro j hj
      exact ((mem_physicalIntervalCells steps _ _ j).mp (hFuture j hj)).1
    etaNonneg:=heta
    meanPast:=hmmean
    meanFuture:=hpmean }
  exact ⟨i,hi,B,rfl,rfl,rfl,D.past_mass hi,D.future_mass hi⟩

end CutBlocks
end NativeStarBuffer
end OAI.SKFluctuations
