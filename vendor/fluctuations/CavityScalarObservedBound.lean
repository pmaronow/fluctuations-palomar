module

public import CavityScalarPairClock
public import CavityScalarRowBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Cavity
open scoped Topology NNReal BigOperators

def scalarClockIncrements (q : ℕ → ℝ) : ℕ → Fin 1 → ℝ≥0 :=
  cumulativeIncrements (fun _ => q 0) (fun j _ => q (j + 1))

theorem actual_scalar_pair_eq_realized {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as) (q : ℕ → ℝ) (hq0 : q 0 = 0)
    (s t : T.Slot) :
    T.disorderExpect (fun _ => (1/2 : ℝ)) scalarFeature
      (fun _ => 0) (fun j _ => q j)
      (fun σ => scalarFeature (T.atSlot σ s) (fun _ => 1) *
        scalarFeature (T.atSlot σ t) (fun _ => 1)) 0 =
    (T.realize (scalarClockIncrements q)).expect (fun _ => (1/2 : ℝ)) scalarFeature
      (fun σ => scalarFeature ((T.realize (scalarClockIncrements q)).atSlot σ
          (T.slotEquiv (scalarClockIncrements q) s)) (fun _ => 1) *
        scalarFeature ((T.realize (scalarClockIncrements q)).atSlot σ
          (T.slotEquiv (scalarClockIncrements q) t)) (fun _ => 1)) 0 := by
  rw [T.disorderExpect_integral (by intro σ; norm_num) scalarFeature ho]
  simp only [hq0, sub_zero, Real.toNNReal_zero, isotropicGaussian_zero,
    zeroContinuation, integral_dirac, add_zero]
  have hi : cumulativeIncrements (fun _ : Fin 1 => (0 : ℝ))
      (fun j _ => q (j + 1)) = scalarClockIncrements q := by
    unfold scalarClockIncrements
    rw [hq0]
  rw [hi]
  rw [T.expect_realize]
  congr 1
  funext σ
  have hs := T.realize_atSlot (scalarClockIncrements q)
    ((T.assignmentEquiv (scalarClockIncrements q)).symm σ) s
  have ht := T.realize_atSlot (scalarClockIncrements q)
    ((T.assignmentEquiv (scalarClockIncrements q)).symm σ) t
  simp only [Equiv.apply_symm_apply] at hs ht
  rw [hs, ht]

theorem actual_scalar_realized_pair_bounds {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as) (q : ℕ → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (s t : T.Slot) (hst : s ≠ t) :
    0 ≤ (T.realize (scalarClockIncrements q)).expect (fun _ => (1/2 : ℝ)) scalarFeature
      (fun σ => scalarFeature ((T.realize (scalarClockIncrements q)).atSlot σ
          (T.slotEquiv (scalarClockIncrements q) s)) (fun _ => 1) *
        scalarFeature ((T.realize (scalarClockIncrements q)).atSlot σ
          (T.slotEquiv (scalarClockIncrements q) t)) (fun _ => 1)) 0 ∧
    (T.realize (scalarClockIncrements q)).expect (fun _ => (1/2 : ℝ)) scalarFeature
      (fun σ => scalarFeature ((T.realize (scalarClockIncrements q)).atSlot σ
          (T.slotEquiv (scalarClockIncrements q) s)) (fun _ => 1) *
        scalarFeature ((T.realize (scalarClockIncrements q)).atSlot σ
          (T.slotEquiv (scalarClockIncrements q) t)) (fun _ => 1)) 0 ≤
      q (T.splitIndex s t) := by
  rw [← actual_scalar_pair_eq_realized T ho q hq0 s t]
  exact actual_scalar_distinct_pair_bounds T ho q hq hq0 s t hst

theorem scalarPlacementGamma_realized_bounds {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as) (q : ℕ → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (s : T.Slot)
    (p : ClockTree.MarkedPlacement T) (hnon : p.embed s ≠ p.mark) :
    0 ≤ scalarPlacementGamma (T.realize (scalarClockIncrements q))
      (T.slotEquiv (scalarClockIncrements q) s) (p.realize (scalarClockIncrements q)) 0 ∧
    scalarPlacementGamma (T.realize (scalarClockIncrements q))
      (T.slotEquiv (scalarClockIncrements q) s) (p.realize (scalarClockIncrements q)) 0 ≤
      q (p.tree.splitIndex (p.embed s) p.mark) := by
  simpa only [scalarPlacementGamma, ClockTree.MarkedPlacement.realize,
    Equiv.symm_apply_apply, Pi.zero_def] using
    actual_scalar_realized_pair_bounds p.tree ho q hq hq0 (p.embed s) p.mark hnon

theorem scalarPlacementGamma_realized_abs_le {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as) (q : ℕ → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (s : T.Slot)
    (p : ClockTree.MarkedPlacement T) (hnon : p.embed s ≠ p.mark)
    {C v : ℝ} (hclock : q (p.tree.splitIndex (p.embed s) p.mark) ≤ C * v) :
    |scalarPlacementGamma (T.realize (scalarClockIncrements q))
      (T.slotEquiv (scalarClockIncrements q) s) (p.realize (scalarClockIncrements q)) 0| ≤
      C * v := by
  have hg := scalarPlacementGamma_realized_bounds T ho q hq hq0 s p hnon
  rw [abs_of_nonneg hg.1]
  exact hg.2.trans hclock

end OAI.SKFluctuations.LaplaceWindowFormalization
