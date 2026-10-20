module

public import CavityActualPairTransfer
public import CavityPhysicalJetBounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem coordinateProfile_eq_rowCovarianceKernel (n : ℕ) (d : ℕ → FullCoordinate n → ℝ)
    (j : ℕ) (σ τ : Spin n × Bool) :
    ReplicaTree.coordinateProfile (fullFeature n) d j σ τ = rowCovarianceKernel n (d j) σ τ := by
  classical
  simp only [ReplicaTree.coordinateProfile,rowCovarianceKernel,fullFeature_single]
  apply Finset.sum_congr rfl
  intro i _
  rw [fullFeature_single_any_decidable,fullFeature_single_any_decidable]

 theorem cutTSlope_zero_covariance (n U : ℕ) (b h K : ℕ → ℝ)
    (j : ℕ) (σ τ : Spin n × Bool) :
    ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ =
      if j<U then 0 else spinValue σ.2*spinValue τ.2*
        (h j+b j*deletedOverlap n (joinSpin σ) (joinSpin τ)-K j) := by
  rw [coordinateProfile_eq_rowCovarianceKernel]
  unfold cutTSlope relocatedClock
  by_cases hj : j<U
  · simp only [hj,ite_true,zero_mul]
    rw [rowInterpolationSlope_covariance]
    ring
  · simp only [hj,ite_false]
    exact rowInterpolationSlope_covariance n (b j) (h j) (K j) σ τ

 theorem cutTSlope_zero_covariance_abs_le (n U N : ℕ) (b h K : ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ j, j≤N → |h j|+|b j|+|K j|≤M)
    (j : ℕ) (hj : j≤N) (σ τ : Spin n × Bool) :
    |ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ|≤M := by
  rw [coordinateProfile_eq_rowCovarianceKernel]
  unfold cutTSlope relocatedClock
  by_cases hc : j<U
  · simp only [hc,ite_true,zero_mul]
    rw [rowInterpolationSlope_covariance]
    simpa using hM
  · simp only [hc,ite_false]
    exact (rowInterpolationSlope_kernel_abs_le n (b j) (h j) (K j) σ τ).trans (hbound j hj)

 theorem cutTSlope_zero_centered_square (n U : ℕ) (b h S : ℕ → ℝ)
    (j : ℕ) (σ τ : Spin n × Bool) :
    (ReplicaTree.coordinateProfile (fullFeature n)
      (cutTSlope n U 0 b h (fun j => h j+b j*S j)) j σ τ)^2 =
    if j<U then 0 else (b j)^2*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S j)^2 := by
  rw [cutTSlope_zero_covariance]
  by_cases hj : j<U
  · simp only [hj,ite_true,zero_pow (by norm_num : (2:ℕ)≠0)]
  · simp only [hj,ite_false]
    have he : h j+b j*deletedOverlap n (joinSpin σ) (joinSpin τ)-(h j+b j*S j)=
        b j*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S j) := by ring
    rw [he]
    have hs (s : Bool) : spinValue s^2=1 := by simpa only [pow_two] using spinValue_sq s
    simp only [mul_pow,hs,one_mul]

 theorem cutHighError_pair_second_le_physicalStar (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (b h S : ℕ → ℝ)
    (hb : Monotone b) (hh : Monotone h) (hK : Monotone (fun j => h j+b j*S j))
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j) (hK0 : ∀ j, 0≤h j+b j*S j)
    (j : ℕ) (hj : j≤as.length) :
    let K := fun j => h j+b j*S j
    let q := physicalCompletedClock (n+1) b h
    let steps := diagonalBoundarySteps as (q 0) (fun k => q (k+1))
    let μ := Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (q 0 i)))
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) U 0 t b h K)
      (fun σ => (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) 0 ≤
      (b j)^2*Real.exp (220*(K as.length+b as.length+h as.length))*2*
        (Real.exp (110*b as.length)*physicalStarPairMoment (n+1) 1 steps μ id measurable_id j (S j)+
          (1/(n+1:ℕ):ℝ)^2) := by
  dsimp only
  have H := cavityPath_pairDeleted_moment_le_physicalStar n 1 U ho
    (show (0:ℝ) ∈ Icc 0 1 by norm_num) ht hb hh hK hb0 hh0 hK0 j hj (S j)
  dsimp only at H
  change (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) U 0 t b h (fun j=>h j+b j*S j))
      (fun σ => |deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^(2*1)) 0 ≤ _ at H
  have hpos : 0≤(ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) U 0 t b h (fun j=>h j+b j*S j))
      (fun σ => |deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^2) 0 := by
    unfold ClockTree.disorderExpect
    exact Finset.sum_nonneg (fun σ _ => mul_nonneg
      (((ClockTree.pairClock as j).disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 _ 0).1 σ)
      (sq_nonneg _))
  have HH := mul_le_mul_of_nonneg_left H (sq_nonneg (b j))
  simp only [Nat.mul_one,show 2-1=1 by omega,pow_one,cavityPath,sq_abs] at HH hpos
  unfold ClockTree.disorderExpect
  simp only [cutTSlope_zero_centered_square]
  by_cases hc : j<U
  · simp only [hc,ite_true,mul_zero,Finset.sum_const_zero]
    have HB := (mul_nonneg (sq_nonneg (b j)) hpos).trans HH
    simpa only [mul_assoc] using HB
  · simp only [hc,ite_false]
    simpa only [ClockTree.disorderExpect,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm,cutFullVariance] using HH

end OAI.SKFluctuations.Cavity
