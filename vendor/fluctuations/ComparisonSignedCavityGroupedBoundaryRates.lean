module

public import ComparisonSignedCavityGroupedPrefixLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeBoundaryRowFactor (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (b h : ℕ→ℝ) : ℝ :=
  let K := finitePhysicalMixedClock (n+1) as b h
  Real.exp (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*
    (K as.length+b as.length+h as.length))

def nativeBoundaryCompletionFactor (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (b : ℕ→ℝ) : ℝ :=
  let R := T.relabelSpin (spinEquiv n)
  Real.exp (2*(7*(R.leaves:ℝ)+8*(R.leaves:ℝ)^2*(R.leaves+1:ℝ))*(b as.length/2))

def nativeBoundaryReplacementBudget (n l : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (b h : ℕ→ℝ) (low high : ℕ) : ℝ :=
  |b low|^(2*l)*nativeBoundaryRowFactor n T b h*(2:ℝ)^(2*l-1)*
    (nativeBoundaryCompletionFactor n T b*
      originalBoundaryResamplingMoment (n+1) l as (physicalCompletedClock (n+1) b h) low high+
      (2/(n+1:ℕ):ℝ)^(2*l))

theorem actual_full_boundary_edge_resampling_le (n l U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j,0 ≤ b j) (hh0 : ∀ j,0 ≤ h j)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (i j k : T.Slot) (hjk : j ≠ k)
    (hlow : T.splitIndex i j=T.splitIndex i k)
    (hgap : T.splitIndex i j<T.splitIndex j k) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>|b (T.splitIndex i j)*(deletedOverlap n (joinSpin (T.atSlot σ j))
        (joinSpin (T.atSlot σ i))-deletedOverlap n (joinSpin (T.atSlot σ k))
          (joinSpin (T.atSlot σ i)))|^(2*l)) 0 ≤
      nativeBoundaryReplacementBudget n l T b h (T.splitIndex i j) (T.splitIndex j k) := by
  let K := finitePhysicalMixedClock (n+1) as b h
  let R := T.relabelSpin (spinEquiv n)
  let i' := T.relabelSlot (spinEquiv n) i
  let j' := T.relabelSlot (spinEquiv n) j
  let k' := T.relabelSlot (spinEquiv n) k
  have hjk' : j' ≠ k' := fun H=>hjk ((T.relabelSlot (spinEquiv n)).injective H)
  have hlo' : R.splitIndex i' j'=R.splitIndex i' k' := by
    simpa only [R,i',j',k',ClockTree.splitIndex_relabel] using hlow
  have hgap' : R.splitIndex i' j'<R.splitIndex j' k' := by
    simpa only [R,i',j',k',ClockTree.splitIndex_relabel] using hgap
  have H := cavityPath_boundary_difference_le_physical n (2*l) U T ho
    (by norm_num : (0:ℝ) ∈ Icc 0 1) ht hb hh
    (finitePhysicalMixedClock_monotone (n+1) ho b h hb hh hb0)
    hb0 hh0 (finitePhysicalMixedClock_nonneg (n+1) as b h hb0 hh0) i j k
  dsimp only at H
  have hsym (σ τ : Spin (n+1)) : orderedOverlap (n+1) σ τ=orderedOverlap (n+1) τ σ := by
    unfold orderedOverlap; congr 1; apply Finset.sum_congr rfl; intro z _; ring
  have hobs : (fun σ:R.Assignment=>
      |orderedOverlap (n+1) (R.atSlot σ j') (R.atSlot σ i')-
        orderedOverlap (n+1) (R.atSlot σ k') (R.atSlot σ i')|^(2*l)) =
      fun σ=>|orderedOverlap (n+1) (R.atSlot σ i') (R.atSlot σ j')-
        orderedOverlap (n+1) (R.atSlot σ i') (R.atSlot σ k')|^(2*l) := by
    funext σ
    rw [hsym (R.atSlot σ j') (R.atSlot σ i'),hsym (R.atSlot σ k') (R.atSlot σ i')]
  change T.disorderExpect _ _ _ _ _ _ ≤ _*_*(_*R.disorderExpect _ _ _ _ _ _+_) at H
  rw [hobs] at H
  rw [←original_boundary_resampling_eq_full_tree (n+1) l R ho
    (physicalCompletedClock (n+1) b h) i' j' k' hjk' hlo' hgap'] at H
  dsimp only [R,i',j',k'] at H
  simp only [ClockTree.splitIndex_relabel] at H
  have HM := mul_le_mul_of_nonneg_left H (pow_nonneg (abs_nonneg (b (T.splitIndex i j))) (2*l))
  have hq : cavityPath n U 0 t (fun z=>Sum.elim (fun _=>b z) (fun _=>h z)) b h K=
      finitePhysicalCavityVariance n U as b h t := by
    funext z c; rfl
  rw [hq] at HM
  have he : (fun σ=>|b (T.splitIndex i j)*(deletedOverlap n (joinSpin (T.atSlot σ j))
      (joinSpin (T.atSlot σ i))-deletedOverlap n (joinSpin (T.atSlot σ k))
        (joinSpin (T.atSlot σ i)))|^(2*l)) =
      fun σ=>|b (T.splitIndex i j)|^(2*l)*
        |deletedOverlap n (joinSpin (T.atSlot σ j)) (joinSpin (T.atSlot σ i))-
          deletedOverlap n (joinSpin (T.atSlot σ k)) (joinSpin (T.atSlot σ i))|^(2*l) := by
    funext σ; rw [abs_mul,mul_pow]
  rw [he,T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  simpa only [nativeBoundaryReplacementBudget,nativeBoundaryRowFactor,
    nativeBoundaryCompletionFactor,K,mul_assoc] using HM

theorem actual_full_boundary_polynomial_from_physical_resampling (n U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j,0 ≤ b j) (hh0 : ∀ j,0 ≤ h j)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    {a : ℕ} (ha : 0<a) (i j k : Fin a→T.Slot)
    (hij : ∀ e,i e ≠ j e) (hik : ∀ e,i e ≠ k e) (hjk : ∀ e,j e ≠ k e)
    (hlow : ∀ e,T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e))
    (hgap : ∀ e,T.splitIndex (i e) (j e)<T.splitIndex (j e) (k e))
    (hcut : ∀ e,T.splitIndex (i e) (j e) ≤ as.length ∧ T.splitIndex (i e) (j e)<U)
    (rho : Fin a→ℝ) (hrho : ∀ e,0<rho e) {xi : ℝ} (hxi : 0<xi)
    (hraw : ∀ e,finitePhysicalLowRawBudget n a as b h (T.splitIndex (i e) (j e)) ≤ (rho e)^(2*a))
    (hphysical : ∀ e,nativeBoundaryReplacementBudget n a T b h
      (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e)) ≤ (xi*rho e)^(2*a)) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ=>(fullBoundaryAffineProduct n
        (fun e=>h (T.splitIndex (i e) (j e))) (fun e=>b (T.splitIndex (i e) (j e)))
          (fun e=>T.atSlot σ (j e)) (fun e=>T.atSlot σ (i e))-
        fullBoundaryAffineProduct n
        (fun e=>h (T.splitIndex (i e) (j e))) (fun e=>b (T.splitIndex (i e) (j e)))
          (fun e=>T.atSlot σ (k e)) (fun e=>T.atSlot σ (i e)))^2) 0 ≤
      ((a:ℝ)*xi*(∏ e,rho e))^2 := by
  apply actual_full_boundary_polynomial_resampling_square n U T ho b h hb hh hb0 hh0 ht
    ha i j k hij hik hjk hlow hgap hcut rho hrho hxi hraw
  intro e
  let C := ClockTree.boundaryTripleClock (S := Spin n×Bool) as
    (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e))
  have H := actual_full_boundary_edge_resampling_le n a U T ho b h hb hh hb0 hh0 ht
    (i e) (j e) (k e) (hjk e) (hlow e) (hgap e)
  rw [T.disorderExpect_boundary_threeAtSlot (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavityVariance n U as b h t) 0 (i e) (j e) (k e) (hjk e) (hlow e) (hgap e)
    (fun d c f=>|b (T.splitIndex (i e) (j e))*(deletedOverlap n (joinSpin c) (joinSpin d)-
      deletedOverlap n (joinSpin f) (joinSpin d))|^(2*a))] at H
  exact H.trans (hphysical e)

end OAI.SKFluctuations.Cavity
