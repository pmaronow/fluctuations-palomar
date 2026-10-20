module

public import ComparisonSignedCavityOriginalGMean
public import ComparisonSignedCavityThreeRowVariation

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeOriginalLongitudinalMean {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K b h C : ℕ → ℝ) (a : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p => p.coeff*
    ((p.tree.markedAttach 0).map (fun r => r.coeff*
      ((r.tree.markedAttach 0).map (fun z => z.coeff*
        z.tree.disorderExpect (fullWeight n) (fullFeature n) 0
          (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
          (nativeOriginalHighGAtom z.tree U K b C
            (z.embed (r.embed (p.embed a))) (z.embed (r.embed p.mark))
            (z.embed r.mark) z.mark) 0)).sum)).sum)).sum

theorem native_original_longitudinal_mean_abs_le {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K b h C : ℕ → ℝ) (a : T.Slot) {Temp eps : ℝ}
    (hTemp : 0 ≤ Temp) (heps : 0 ≤ eps)
    (hb : ∀j ≤ as.length,|b j| ≤ Temp)
    (hC : ∀j ≤ as.length,|finitePhysicalMean (n+1) as b h j-C j| ≤ eps) :
    |nativeOriginalLongitudinalMean T U K b h C a| ≤
      (8*(T.leaves:ℝ)*(T.leaves+1)*(T.leaves+2))*Temp*(1/(n+1:ℕ)+eps) := by
  have HH := T.marked_three_row_abs_le ho
    (fun p r z => z.tree.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (nativeOriginalHighGAtom z.tree U K b C
        (z.embed (r.embed (p.embed a))) (z.embed (r.embed p.mark))
        (z.embed r.mark) z.mark) 0)
    (show 0 ≤ Temp*(1/(n+1:ℕ)+eps) by positivity)
  have HH' := HH (by
    intro p _ r _ z _
    have hlen := z.tree.splitIndex_le_clockLength (z.embed r.mark) z.mark
    have H := native_original_high_g_atom_mean_abs_le z.tree ho U K b h C
      (z.embed (r.embed (p.embed a))) (z.embed (r.embed p.mark))
      (z.embed r.mark) z.mark hTemp (hb _ hlen)
    exact H.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (hC _ hlen)) hTemp))
  simpa only [nativeOriginalLongitudinalMean,mul_assoc] using HH'

theorem native_original_longitudinal_physical_mean_abs_le {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K b h : ℕ → ℝ) (a : T.Slot) {Temp : ℝ}
    (hTemp : 0 ≤ Temp) (hb : ∀j ≤ as.length,|b j| ≤ Temp) :
    |nativeOriginalLongitudinalMean T U K b h (finitePhysicalMean (n+1) as b h) a| ≤
      (8*(T.leaves:ℝ)*(T.leaves+1)*(T.leaves+2))*Temp/(n+1:ℕ) := by
  simpa only [add_zero,mul_one_div] using native_original_longitudinal_mean_abs_le
    T ho U K b h (finitePhysicalMean (n+1) as b h) a hTemp (le_refl 0) hb
    (fun _ _ => by simp)

end OAI.SKFluctuations.Cavity
