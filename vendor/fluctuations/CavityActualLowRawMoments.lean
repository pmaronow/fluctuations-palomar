module

public import CavityPhysicalRawCentering
public import CavityPhysicalErrorRadius
public import CavityLowKernelMoments
public import CavityRealMomentMonotonicity

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def finitePhysicalLowKernel (n U : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) :=
  ReplicaTree.coordinateProfile (fullFeature n)
    (cutLSlope n U 1 b h (finitePhysicalMixedClock (n+1) as b h))

def finitePhysicalDeletedRawBudget (n l : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (j : ℕ) : ℝ :=
  let K := finitePhysicalMixedClock (n+1) as b h
  let q := physicalCompletedClock (n+1) b h
  let steps := diagonalBoundarySteps as (q 0) (fun k=>q (k+1))
  let μ := Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))
  Real.exp (220*(K as.length+b as.length+h as.length))*(2:ℝ)^(2*l-1)*
    (Real.exp (110*b as.length)*physicalOverlapMoment (n+1) l steps μ id measurable_id j+
      (1/(n+1:ℕ):ℝ)^(2*l))

def finitePhysicalLowRawBudget (n l : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (j : ℕ) : ℝ :=
  (2:ℝ)^(2*l-1)*(|h j|^(2*l)+|b j|^(2*l)*finitePhysicalDeletedRawBudget n l as b h j)

theorem finitePhysicalLowKernel_at_low (n U : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ)
    {j : ℕ} (hj : j<U) (σ τ : Spin n × Bool) :
    finitePhysicalLowKernel n U as b h j σ τ=
      rowCovarianceKernel n (fullVariance n 0 1 (b j) (h j) (h j)) σ τ := by
  rw [finitePhysicalLowKernel,coordinateProfile_eq_rowCovarianceKernel]
  simp only [cutLSlope,hj,ite_true]
  rw [fullVariance_row_covariance,fullVariance_row_covariance]
  norm_num

theorem finitePhysicalLowKernel_at_high (n U : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ)
    {j : ℕ} (hj : ¬j<U) (σ τ : Spin n × Bool) :
    finitePhysicalLowKernel n U as b h j σ τ=0 := by
  rw [finitePhysicalLowKernel,coordinateProfile_eq_rowCovarianceKernel]
  simp only [cutLSlope,hj,ite_false,rowCovarianceKernel,Pi.zero_apply,zero_mul,Finset.sum_const_zero]

theorem finitePhysicalDeleted_moment_le_raw (n l U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j) (j : ℕ) (hj : j≤as.length) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)|^(2*l)) 0≤
      finitePhysicalDeletedRawBudget n l as b h j := by
  have H := cavityPath_pairDeleted_moment_le_physicalStar n l U ho (a:=0) (by norm_num) ht hb hh
    (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0) hb0 hh0
    (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0) j hj 0
  dsimp only at H
  rw [physicalStarPairMoment_zero_eq_raw (n+1) l as ho _ j hj] at H
  simp only [sub_zero] at H
  exact H

theorem finitePhysicalLow_integer_moment_le_raw (n l U : ℕ) (hl : 0<l)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j) (j : ℕ) (hj : j≤as.length) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>|finitePhysicalLowKernel n U as b h j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*l)) 0≤
      finitePhysicalLowRawBudget n l as b h j := by
  by_cases hlow : j<U
  · simp_rw [finitePhysicalLowKernel_at_low n U as b h hlow]
    have H := actual_low_row_moment_le n (2*l) (ClockTree.pairClock as j) ho 0
      (finitePhysicalCavityVariance n U as b h t) 0
      (ClockTree.pairLeftSlot as j) (ClockTree.pairRightSlot as j) (b j) (h j) 0 1
    simp only [ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot,mul_zero,add_zero,
      one_mul,abs_one,one_pow,sub_zero] at H
    apply H.trans
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (finitePhysicalDeleted_moment_le_raw n l U ho ht b h hb hh hb0 hh0 j hj)
        (by positivity))) (by positivity)
  · simp_rw [finitePhysicalLowKernel_at_high n U as b h hlow,abs_zero,
      zero_pow (by omega : 2*l≠0)]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    have hB : 0≤finitePhysicalDeletedRawBudget n l as b h j := by
      unfold finitePhysicalDeletedRawBudget
      apply mul_nonneg (by positivity)
      apply add_nonneg _ (by positivity)
      apply mul_nonneg (by positivity)
      exact integral_nonneg fun p=>conditionalPathAverage_nonneg _ _ _ _ _
        (fun q=>pow_nonneg (abs_nonneg _) _) p
    dsimp only [finitePhysicalLowRawBudget]
    positivity

theorem finitePhysicalLow_real_moment_le_raw (n l U : ℕ) (hl : 0<l)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j) (j : ℕ) (hj : j≤as.length)
    {p rho : ℝ} (hp : 0<p) (hpr : p≤(2*l:ℕ)) (hrho : 0≤rho)
    (hbudget : finitePhysicalLowRawBudget n l as b h j≤rho^(2*l)) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>|finitePhysicalLowKernel n U as b h j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^p) 0≤rho^p := by
  apply (ClockTree.pairClock as j).disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n)
    ho 0 (finitePhysicalCavityVariance n U as b h t) 0 _ hp hpr hrho
  simpa only [Real.rpow_natCast] using
    (finitePhysicalLow_integer_moment_le_raw n l U hl ho ht b h hb hh hb0 hh0 j hj).trans hbudget

end OAI.SKFluctuations.Cavity
