module

public import ComparisonSignedCavityOriginalEndpointMean
public import ComparisonSignedCavityActualTerminalGAtom

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_original_high_g_atom_mean_abs_le {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K b h C : ℕ → ℝ) (a c e f : T.Slot) {Temp : ℝ}
    (hTemp : 0 ≤ Temp) (hb : |b (T.splitIndex e f)| ≤ Temp) :
    |T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (nativeOriginalHighGAtom T U K b C a c e f) 0| ≤
      Temp*(1/(n+1:ℕ)+|finitePhysicalMean (n+1) as b h (T.splitIndex e f)-C (T.splitIndex e f)|) := by
  unfold nativeOriginalHighGAtom
  split_ifs with H
  · rw [T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho,abs_mul]
    have Hmean := fullEndpoint_deleted_centered_mean_abs_le n U b h K T ho e f H.2.2.2
      (C (T.splitIndex e f))
    have Hscalar := native_full_scalar_connected_four_abs_le_two T ho U K a c e f
    have Hcoeff : |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f*b (T.splitIndex e f)| ≤ Temp := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      have H1 := mul_le_mul_of_nonneg_left Hscalar (by norm_num : (0:ℝ) ≤ 1/2)
      have H2 := mul_le_mul H1 hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2*2)
      simpa using H2
    exact mul_le_mul Hcoeff Hmean (abs_nonneg _) hTemp
  · simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero,abs_zero]
    positivity

theorem native_original_high_g_atom_physical_mean_abs_le {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K b h : ℕ → ℝ) (a c e f : T.Slot) {Temp : ℝ}
    (hTemp : 0 ≤ Temp) (hb : |b (T.splitIndex e f)| ≤ Temp) :
    |T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (nativeOriginalHighGAtom T U K b (finitePhysicalMean (n+1) as b h) a c e f) 0| ≤
      Temp/(n+1:ℕ) := by
  simpa only [sub_self,abs_zero,add_zero,mul_one_div] using
    native_original_high_g_atom_mean_abs_le T ho U K b h (finitePhysicalMean (n+1) as b h)
      a c e f hTemp hb

end OAI.SKFluctuations.Cavity
