module

public import CavityFullBoundaryProducts
public import CavityEndpointLaw
public import CavityCompletedScalar

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem deleted_boundary_difference_power_le (n m : ℕ) (d c f : Spin (n+1)) :
    |deletedOverlap n c d-deletedOverlap n f d|^m ≤
      (2:ℝ)^(m-1)*(|orderedOverlap (n+1) c d-orderedOverlap (n+1) f d|^m+
        (2/(n+1:ℕ):ℝ)^m) := by
  have H : |deletedOverlap n c d-deletedOverlap n f d| ≤
      |orderedOverlap (n+1) c d-orderedOverlap (n+1) f d|+2/(n+1:ℕ) := by
    calc
      _ = |(orderedOverlap (n+1) c d-orderedOverlap (n+1) f d)+
          ((deletedOverlap n c d-orderedOverlap (n+1) c d)-
            (deletedOverlap n f d-orderedOverlap (n+1) f d))| := by congr 1; ring
      _ ≤ |orderedOverlap (n+1) c d-orderedOverlap (n+1) f d|+
          |(deletedOverlap n c d-orderedOverlap (n+1) c d)-
            (deletedOverlap n f d-orderedOverlap (n+1) f d)| := abs_add_le _ _
      _ ≤ |orderedOverlap (n+1) c d-orderedOverlap (n+1) f d|+
          (|deletedOverlap n c d-orderedOverlap (n+1) c d|+
            |deletedOverlap n f d-orderedOverlap (n+1) f d|) :=
        add_le_add_right (abs_sub _ _) _
      _ = _ := by rw [abs_deletedOverlap_sub,abs_deletedOverlap_sub]; ring
  exact (pow_le_pow_left₀ (abs_nonneg _) H m).trans
    (add_pow_le (abs_nonneg _) (by positivity : (0:ℝ)≤2/(n+1:ℕ)) m)

theorem disorder_deleted_boundary_difference_power_le (n m : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n → ℝ) (q : ℕ → FullCoordinate n → ℝ) (x : FullCoordinate n → ℝ)
    (i j k : T.Slot) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>|deletedOverlap n (joinSpin (T.atSlot σ j)) (joinSpin (T.atSlot σ i))-
        deletedOverlap n (joinSpin (T.atSlot σ k)) (joinSpin (T.atSlot σ i))|^m) x ≤
    (2:ℝ)^(m-1)*(T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>|orderedOverlap (n+1) (joinSpin (T.atSlot σ j)) (joinSpin (T.atSlot σ i))-
        orderedOverlap (n+1) (joinSpin (T.atSlot σ k)) (joinSpin (T.atSlot σ i))|^m) x+
      (2/(n+1:ℕ):ℝ)^m) := by
  let w := fun σ=>T.disorderWeight (fullWeight n) (fullFeature n) v q σ x
  have hw := T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x
  change (∑ σ, w σ*_)≤_
  calc
    _ ≤ ∑ σ, w σ*((2:ℝ)^(m-1)*
        (|orderedOverlap (n+1) (joinSpin (T.atSlot σ j)) (joinSpin (T.atSlot σ i))-
          orderedOverlap (n+1) (joinSpin (T.atSlot σ k)) (joinSpin (T.atSlot σ i))|^m+
          (2/(n+1:ℕ):ℝ)^m)) := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (deleted_boundary_difference_power_le n m _ _ _) (hw.1 σ)
    _ = _ := by
      change (∑ σ, w σ*((2:ℝ)^(m-1)*(_+(2/(n+1:ℕ):ℝ)^m))) = _
      simp only [mul_add,Finset.sum_add_distrib]
      rw [←Finset.sum_mul]
      rw [show ∑ σ, w σ=1 from hw.2,one_mul]
      simp only [ClockTree.disorderExpect,Finset.mul_sum]
      apply congrArg (fun z=>z+(2:ℝ)^(m-1)*(2/(n+1:ℕ):ℝ)^m)
      apply Finset.sum_congr rfl
      intro σ _
      ring

theorem fullEndpoint_boundary_difference_eq_nullCompleted (n m U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (i j k : T.Slot) :
    let R := T.relabelSpin (spinEquiv n)
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun z=>Sum.elim (fun _=>b z) (fun _=>h z)) b h K)
      (fun σ=>|orderedOverlap (n+1) (joinSpin (T.atSlot σ j)) (joinSpin (T.atSlot σ i))-
        orderedOverlap (n+1) (joinSpin (T.atSlot σ k)) (joinSpin (T.atSlot σ i))|^m) 0 =
    R.disorderExpect (uniformWeight (n+1)) (finiteFeature (n+1)) 0
      (nullCompletedClock (n+1) b h)
      (fun σ=>|orderedOverlap (n+1) (R.atSlot σ (T.relabelSlot (spinEquiv n) j))
          (R.atSlot σ (T.relabelSlot (spinEquiv n) i))-
        orderedOverlap (n+1) (R.atSlot σ (T.relabelSlot (spinEquiv n) k))
          (R.atSlot σ (T.relabelSlot (spinEquiv n) i))|^m) 0 := by
  dsimp only
  have H := fullEndpointExpect_eq_nullCompleted n U b h K T
    (fun σ=>|orderedOverlap (n+1)
      ((T.relabelSpin (spinEquiv n)).atSlot σ (T.relabelSlot (spinEquiv n) j))
      ((T.relabelSpin (spinEquiv n)).atSlot σ (T.relabelSlot (spinEquiv n) i))-
      orderedOverlap (n+1)
      ((T.relabelSpin (spinEquiv n)).atSlot σ (T.relabelSlot (spinEquiv n) k))
      ((T.relabelSpin (spinEquiv n)).atSlot σ (T.relabelSlot (spinEquiv n) i))|^m)
  simp only [ClockTree.atSlot_relabel] at H
  exact H

theorem cavityPath_boundary_difference_le_physical (n m U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    {b h K : ℕ → ℝ} (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (hb0 : ∀ j, 0≤b j) (hh0 : ∀ j, 0≤h j) (hK0 : ∀ j, 0≤K j)
    (i j k : T.Slot) :
    let R := T.relabelSpin (spinEquiv n)
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U l t (fun z=>Sum.elim (fun _=>b z) (fun _=>h z)) b h K)
      (fun σ=>|deletedOverlap n (joinSpin (T.atSlot σ j)) (joinSpin (T.atSlot σ i))-
        deletedOverlap n (joinSpin (T.atSlot σ k)) (joinSpin (T.atSlot σ i))|^m) 0 ≤
    Real.exp (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*
      (K as.length+b as.length+h as.length))*(2:ℝ)^(m-1)*
      (Real.exp (2*(7*(R.leaves:ℝ)+8*(R.leaves:ℝ)^2*(R.leaves+1:ℝ))*(b as.length/2))*
        R.disorderExpect (uniformWeight (n+1)) (finiteFeature (n+1)) 0
          (physicalCompletedClock (n+1) b h)
          (fun σ=>|orderedOverlap (n+1) (R.atSlot σ (T.relabelSlot (spinEquiv n) j))
              (R.atSlot σ (T.relabelSlot (spinEquiv n) i))-
            orderedOverlap (n+1) (R.atSlot σ (T.relabelSlot (spinEquiv n) k))
              (R.atSlot σ (T.relabelSlot (spinEquiv n) i))|^m) 0+
        (2/(n+1:ℕ):ℝ)^m) := by
  dsimp only
  have hq : ∀ z : RestCoordinate n, Monotone (fun j=>Sum.elim (fun _=>b j) (fun _=>h j) z) := by
    intro z; cases z <;> first | exact hb | exact hh
  have hq0 : ∀ j (z : RestCoordinate n), 0≤Sum.elim (fun _=>b j) (fun _=>h j) z := by
    intro j z; cases z <;> first | exact hb0 j | exact hh0 j
  have H := cavityPath_expect_close n U T ho hl ht (by norm_num : (1:ℝ)∈Icc 0 1)
    (by norm_num : (1:ℝ)∈Icc 0 1) hq hb hh hK hq0 hb0 hh0 hK0
    (fun σ=>|deletedOverlap n (joinSpin (T.atSlot σ j)) (joinSpin (T.atSlot σ i))-
      deletedOverlap n (joinSpin (T.atSlot σ k)) (joinSpin (T.atSlot σ i))|^m)
    (fun _=>pow_nonneg (abs_nonneg _) _) 0
  apply H.le_mul.trans
  have HD := disorder_deleted_boundary_difference_power_le n m T ho 0
    (cavityPath n U 1 1 (fun z=>Sum.elim (fun _=>b z) (fun _=>h z)) b h K) 0 i j k
  rw [fullEndpoint_boundary_difference_eq_nullCompleted n m U b h K T i j k] at HD
  have HC := completed_scalar_expect_close (n+1) (T.relabelSpin (spinEquiv n)) ho hb hh hb0 hh0
    (fun σ=>|orderedOverlap (n+1)
      ((T.relabelSpin (spinEquiv n)).atSlot σ (T.relabelSlot (spinEquiv n) j))
      ((T.relabelSpin (spinEquiv n)).atSlot σ (T.relabelSlot (spinEquiv n) i))-
      orderedOverlap (n+1)
      ((T.relabelSpin (spinEquiv n)).atSlot σ (T.relabelSlot (spinEquiv n) k))
      ((T.relabelSpin (spinEquiv n)).atSlot σ (T.relabelSlot (spinEquiv n) i))|^m)
    (fun _=>pow_nonneg (abs_nonneg _) _)
  apply (mul_le_mul_of_nonneg_left HD (Real.exp_pos _).le).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (add_le_add HC.le_mul le_rfl) (mul_nonneg (Real.exp_pos _).le (by positivity : (0:ℝ)≤2^(m-1)))

end OAI.SKFluctuations.Cavity
