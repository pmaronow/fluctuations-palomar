module

public import CavityBoundaryResamplingMoments
public import CavityActualLowRawMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def fullBoundaryAffineFactor (n : ℕ) (h b : ℝ) (c d : Spin n × Bool) : ℝ :=
  h+b*deletedOverlap n (joinSpin c) (joinSpin d)

def fullBoundaryAffineProduct (n : ℕ) {a : ℕ}
    (h b : Fin a → ℝ) (c d : Fin a → Spin n × Bool) : ℝ :=
  ∏ i, fullBoundaryAffineFactor n (h i) (b i) (c i) (d i)

theorem full_boundary_affine_abs_eq_low_kernel (n U : ℕ) (as : List PositiveMass)
    (b h : ℕ → ℝ) {j : ℕ} (hj : j<U) (σ τ : Spin n × Bool) :
    |fullBoundaryAffineFactor n (h j) (b j) σ τ| =
      |finitePhysicalLowKernel n U as b h j σ τ| := by
  rw [finitePhysicalLowKernel_at_low n U as b h hj,fullVariance_row_covariance]
  simp only [mul_one,mul_zero,add_zero,zero_add,abs_mul,abs_spinValue,one_mul,
    fullBoundaryAffineFactor,sub_self,zero_mul]

theorem full_boundary_affine_pair_moment_le_raw (n l U : ℕ) (hl : 0<l)
    {as : List PositiveMass} (ho : MassOrdered 0 as) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j)
    (j : ℕ) (hj : j≤as.length) (hjU : j<U) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavityVariance n U as b h t)
      (fun σ => |fullBoundaryAffineFactor n (h j) (b j)
        (ClockTree.pairSpin as j σ).2 (ClockTree.pairSpin as j σ).1|^(2*l)) 0 ≤
      finitePhysicalLowRawBudget n l as b h j := by
  simp_rw [full_boundary_affine_abs_eq_low_kernel n U as b h hjU]
  have hs : (fun σ => |finitePhysicalLowKernel n U as b h j
      (ClockTree.pairSpin as j σ).2 (ClockTree.pairSpin as j σ).1|^(2*l)) =
      fun σ => |finitePhysicalLowKernel n U as b h j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*l) := by
    funext σ
    simp only [finitePhysicalLowKernel,ReplicaTree.coordinateProfile]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  exact finitePhysicalLow_integer_moment_le_raw n l U hl ho ht b h hb hh hb0 hh0 j hj

theorem actual_full_boundary_polynomial_resampling_square (n U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    {a : ℕ} (ha : 0<a) (i j k : Fin a → T.Slot)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e)
    (hlow : ∀ e, T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e))
    (hgap : ∀ e, T.splitIndex (i e) (j e) < T.splitIndex (j e) (k e))
    (hcut : ∀ e, T.splitIndex (i e) (j e)≤as.length ∧ T.splitIndex (i e) (j e)<U)
    (rho : Fin a → ℝ) (hrho : ∀ e, 0<rho e) {xi : ℝ} (hxi : 0<xi)
    (hraw : ∀ e, finitePhysicalLowRawBudget n a as b h (T.splitIndex (i e) (j e))≤(rho e)^(2*a))
    (herror : ∀ e, (ClockTree.boundaryTripleClock (S := Spin n × Bool) as
      (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e))).disorderExpect
      (fullWeight n) (fullFeature n) 0 (finitePhysicalCavityVariance n U as b h t)
      (fun σ => let z := (ClockTree.boundaryTripleSpin as
        (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e)) σ);
        |b (T.splitIndex (i e) (j e))*(deletedOverlap n (joinSpin z.2.1) (joinSpin z.1)-
          deletedOverlap n (joinSpin z.2.2) (joinSpin z.1))|^(2*a)) 0 ≤
      (xi*rho e)^(2*a)) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (finitePhysicalCavityVariance n U as b h t)
      (fun σ => (fullBoundaryAffineProduct n
        (fun e=>h (T.splitIndex (i e) (j e))) (fun e=>b (T.splitIndex (i e) (j e)))
        (fun e => T.atSlot σ (j e)) (fun e => T.atSlot σ (i e))-
        fullBoundaryAffineProduct n
          (fun e=>h (T.splitIndex (i e) (j e))) (fun e=>b (T.splitIndex (i e) (j e)))
          (fun e => T.atSlot σ (k e)) (fun e => T.atSlot σ (i e)))^2) 0 ≤
      ((a:ℝ)*xi*(∏ e, rho e))^2 := by
  let q := finitePhysicalCavityVariance n U as b h t
  let f := fun e σ => fullBoundaryAffineFactor n (h (T.splitIndex (i e) (j e)))
    (b (T.splitIndex (i e) (j e))) (T.atSlot σ (j e)) (T.atSlot σ (i e))
  let g := fun e σ => fullBoundaryAffineFactor n (h (T.splitIndex (i e) (j e)))
    (b (T.splitIndex (i e) (j e))) (T.atSlot σ (k e)) (T.atSlot σ (i e))
  apply finite_weighted_resampled_product_square ha
    (fun σ => T.disorderWeight (fullWeight n) (fullFeature n) 0 q σ 0) f g
    (T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 q 0).1 rho hrho hxi
  · intro e
    change T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ => |f e σ|^(2*a)) 0 ≤ _
    rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 q 0
      (i e) (j e) (hij e)
      (fun d c => |fullBoundaryAffineFactor n (h (T.splitIndex (i e) (j e)))
        (b (T.splitIndex (i e) (j e))) c d|^(2*a))]
    exact (full_boundary_affine_pair_moment_le_raw n a U ha ho ht b h hb hh hb0 hh0 _
      (hcut e).1 (hcut e).2).trans (hraw e)
  · intro e
    change T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ => |g e σ|^(2*a)) 0 ≤ _
    rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 q 0
      (i e) (k e) (hik e)
      (fun d c => |fullBoundaryAffineFactor n (h (T.splitIndex (i e) (j e)))
        (b (T.splitIndex (i e) (j e))) c d|^(2*a)),←hlow e]
    exact (full_boundary_affine_pair_moment_le_raw n a U ha ho ht b h hb hh hb0 hh0 _
      (hcut e).1 (hcut e).2).trans (hraw e)
  · intro e
    change T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ => |f e σ-g e σ|^(2*a)) 0 ≤ _
    have he : (fun σ => |f e σ-g e σ|^(2*a)) =
        fun σ => |b (T.splitIndex (i e) (j e))*(deletedOverlap n (joinSpin (T.atSlot σ (j e)))
          (joinSpin (T.atSlot σ (i e)))-deletedOverlap n (joinSpin (T.atSlot σ (k e)))
          (joinSpin (T.atSlot σ (i e))))|^(2*a) := by
      funext σ
      congr 2
      dsimp [f,g,fullBoundaryAffineFactor]
      ring
    rw [he,T.disorderExpect_boundary_threeAtSlot (fullWeight_pos n) (fullFeature n) ho 0 q 0
      (i e) (j e) (k e) (hjk e) (hlow e) (hgap e)
      (fun d c f => |b (T.splitIndex (i e) (j e))*(deletedOverlap n (joinSpin c) (joinSpin d)-
        deletedOverlap n (joinSpin f) (joinSpin d))|^(2*a))]
    exact herror e

end OAI.SKFluctuations.Cavity
