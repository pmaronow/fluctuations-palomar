module

public import ComparisonSignedCavityWholeLawProfileBudgets
public import CavityCutErrorMoments
public import ComparisonSignedCavityActualMixedProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeWholeLawErrorSecond (n : ℕ) (as : List PositiveMass)
    (q : ℕ→FullCoordinate n→ℝ) (A : ℕ→FullCoordinate n→ℝ) (j : ℕ) : ℝ :=
  (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
    (fun σ=>(ReplicaTree.coordinateProfile (fullFeature n) A j
      (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) 0

def nativeWholeLawErrorRadius (n : ℕ) (as : List PositiveMass)
    (q : ℕ→FullCoordinate n→ℝ) (A : ℕ→FullCoordinate n→ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (nativeWholeLawErrorSecond n as q A j)

theorem nativeWholeLawErrorSecond_nonneg (n : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (q : ℕ→FullCoordinate n→ℝ) (A : ℕ→FullCoordinate n→ℝ) (j : ℕ) :
    0 ≤ nativeWholeLawErrorSecond n as q A j := by
  exact ClockTree.wholeLaw_disorderExpect_nonneg (fullWeight_pos n) (fullFeature n)
    (ClockTree.pairClock as j) ho 0 q _ (fun _=>sq_nonneg _) 0

theorem nativeWholeLawErrorRadius_nonneg (n : ℕ) (as : List PositiveMass)
    (q : ℕ→FullCoordinate n→ℝ) (A : ℕ→FullCoordinate n→ℝ) (j : ℕ) :
    0 ≤ nativeWholeLawErrorRadius n as q A j:=Real.sqrt_nonneg _

theorem nativeWholeLawErrorSecond_eq_radius_sq (n : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (q : ℕ→FullCoordinate n→ℝ) (A : ℕ→FullCoordinate n→ℝ) (j : ℕ) :
    nativeWholeLawErrorSecond n as q A j=(nativeWholeLawErrorRadius n as q A j)^2 :=
  (Real.sq_sqrt (nativeWholeLawErrorSecond_nonneg n ho q A j)).symm

def nativeWholeLawProfileCost (n : ℕ) {as : List PositiveMass}
    (q : ℕ→FullCoordinate n→ℝ) (A : ℕ→FullCoordinate n→ℝ)
    (T : ClockTree (Spin n×Bool) as) (e : ℝ) : ℝ :=
  T.forkCost (fun j=>(nativeWholeLawErrorRadius n as q A j)^e)+
    (∫u,ClockTree.edgeDensity 0 as (fun j=>(nativeWholeLawErrorRadius n as q A j)^e) u)

theorem nativeWholeLawProfileCost_eq_budget (n : ℕ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (q : ℕ→FullCoordinate n→ℝ) (A : ℕ→FullCoordinate n→ℝ)
    (T : ClockTree (Spin n×Bool) as) (e : ℝ) :
    nativeWholeLawProfileCost n q A T e=
      T.forkCost (fun j=>(nativeWholeLawErrorRadius n as q A j)^e)+
        ClockTree.edgeBudget 0 as (fun j=>(nativeWholeLawErrorRadius n as q A j)^e) := by
  rw [nativeWholeLawProfileCost,ClockTree.edgeDensity_integral ho]

theorem nativeWholeLaw_centered_error_pair_second_le_star (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (b h S : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hK : Monotone (fun j=>h j+b j*S j))
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) (hK0 : ∀j,0 ≤ h j+b j*S j)
    (A : ℕ→FullCoordinate n→ℝ) (j : ℕ) (hj : j ≤ as.length)
    (hA : ∀σ τ,(ReplicaTree.coordinateProfile (fullFeature n) A j σ τ)^2 ≤
      (b j)^2*|deletedOverlap n (joinSpin σ) (joinSpin τ)-S j|^2) :
    let K:=fun j=>h j+b j*S j
    let q:=physicalCompletedClock (n+1) b h
    let steps:=diagonalBoundarySteps as (q 0) (fun k=>q (k+1))
    let μ:=Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))
    nativeWholeLawErrorSecond n as
      (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K) A j ≤
      (b j)^2*Real.exp (220*(K as.length+b as.length+h as.length))*2*
        (Real.exp (110*b as.length)*physicalStarPairMoment (n+1) 1 steps μ id measurable_id j (S j)+
          (1/(n+1:ℕ):ℝ)^2) := by
  dsimp only
  let K:=fun j=>h j+b j*S j
  let q:=cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K
  have H:=cavityPath_pairDeleted_moment_le_physicalStar n 1 U ho hl ht hb hh hK hb0 hh0 hK0 j hj (S j)
  dsimp only at H
  change (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
    (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
      (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^(2*1)) 0 ≤ _ at H
  have HH:=mul_le_mul_of_nonneg_left H (sq_nonneg (b j))
  simp only [Nat.mul_one,show 2-1=1 by omega,pow_one] at HH
  have HP : nativeWholeLawErrorSecond n as q A j ≤ (b j)^2*
      (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
          (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^2) 0 := by
    unfold nativeWholeLawErrorSecond ClockTree.disorderExpect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    have HW:=((ClockTree.pairClock as j).disorderWeight_probability (fullWeight_pos n)
      (fullFeature n) ho 0 q 0).1 σ
    simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left
      (hA (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) HW
  exact HP.trans (by simpa only [K,q,mul_assoc] using HH)

theorem cutLowError_centered_square (n U : ℕ) (b h S : ℕ→ℝ)
    (j : ℕ) (σ τ : Spin n×Bool) :
    (ReplicaTree.coordinateProfile (fullFeature n)
      (cutLowError n U b h (fun j=>h j+b j*S j)) j σ τ)^2 =
    if j<U then (b j)^2*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S j)^2 else 0 := by
  rw [coordinateProfile_eq_rowCovarianceKernel]
  unfold cutLowError
  by_cases hj : j<U
  · simp only [hj,ite_true]
    rw [rowInterpolationSlope_covariance]
    have he : h j+b j*deletedOverlap n (joinSpin σ) (joinSpin τ)-(h j+b j*S j)=
        b j*(deletedOverlap n (joinSpin σ) (joinSpin τ)-S j) := by ring
    rw [he]
    have hs (s : Bool) : spinValue s^2=1 := by simpa only [pow_two] using spinValue_sq s
    simp only [mul_pow,hs,one_mul]
  · simp only [hj,ite_false]
    simp only [rowCovarianceKernel,Pi.zero_apply,zero_mul,Finset.sum_const_zero,
      zero_pow (by norm_num : (2:ℕ)≠0)]

theorem cutLowError_covariance_abs_le (n U N : ℕ) (b h K : ℕ→ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀j,j ≤ N → |h j|+|b j|+|K j| ≤ M)
    (j : ℕ) (hj : j ≤ N) (σ τ : Spin n×Bool) :
    |ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) j σ τ| ≤ M := by
  rw [coordinateProfile_eq_rowCovarianceKernel]
  unfold cutLowError
  by_cases hc : j<U
  · simp only [hc,ite_true]
    exact (rowInterpolationSlope_kernel_abs_le n (b j) (h j) (K j) σ τ).trans (hbound j hj)
  · simp only [hc,ite_false,rowCovarianceKernel,Pi.zero_apply,zero_mul,Finset.sum_const_zero,abs_zero]
    exact hM

theorem nativeWholeLaw_low_error_pair_second_le_star (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (b h S : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hK : Monotone (fun j=>h j+b j*S j))
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) (hK0 : ∀j,0 ≤ h j+b j*S j)
    (j : ℕ) (hj : j ≤ as.length) :
    let K:=fun j=>h j+b j*S j
    let q:=physicalCompletedClock (n+1) b h
    let steps:=diagonalBoundarySteps as (q 0) (fun k=>q (k+1))
    let μ:=Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))
    nativeWholeLawErrorSecond n as
      (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
      (cutLowError n U b h K) j ≤
      (b j)^2*Real.exp (220*(K as.length+b as.length+h as.length))*2*
        (Real.exp (110*b as.length)*physicalStarPairMoment (n+1) 1 steps μ id measurable_id j (S j)+
          (1/(n+1:ℕ):ℝ)^2) := by
  apply nativeWholeLaw_centered_error_pair_second_le_star n U ho hl ht b h S hb hh hK hb0 hh0 hK0
    (cutLowError n U b h (fun j=>h j+b j*S j)) j hj
  intro σ τ
  rw [cutLowError_centered_square,sq_abs]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem nativeWholeLaw_high_error_pair_second_le_star (n U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {l t : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (b h S : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hK : Monotone (fun j=>h j+b j*S j))
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) (hK0 : ∀j,0 ≤ h j+b j*S j)
    (j : ℕ) (hj : j ≤ as.length) :
    let K:=fun j=>h j+b j*S j
    let q:=physicalCompletedClock (n+1) b h
    let steps:=diagonalBoundarySteps as (q 0) (fun k=>q (k+1))
    let μ:=Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))
    nativeWholeLawErrorSecond n as
      (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
      (cutTSlope n U 0 b h K) j ≤
      (b j)^2*Real.exp (220*(K as.length+b as.length+h as.length))*2*
        (Real.exp (110*b as.length)*physicalStarPairMoment (n+1) 1 steps μ id measurable_id j (S j)+
          (1/(n+1:ℕ):ℝ)^2) := by
  apply nativeWholeLaw_centered_error_pair_second_le_star n U ho hl ht b h S hb hh hK hb0 hh0 hK0
    (cutTSlope n U 0 b h (fun j=>h j+b j*S j)) j hj
  intro σ τ
  rw [cutTSlope_zero_centered_square,sq_abs]
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact le_rfl

end OAI.SKFluctuations.Cavity
