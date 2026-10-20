module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Set
open scoped Topology
set_option maxHeartbeats 2000000

theorem exists_abs_le_of_initial_integral_lt
    (f : ℝ→ℝ) {a b x : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hab : a < b)
    (hf : IntervalIntegrable f volume 0 (b*x))
    (hsmall : (∫u in 0..b*x, |f u|) < (b-a)*x^4) :
    ∃u∈Ioo (a*x) (b*x), |f u| ≤ x^3 := by
  by_contra hnone
  push Not at hnone
  have hax : 0 ≤ a*x:=mul_nonneg ha hx.le
  have hband : a*x < b*x:=mul_lt_mul_of_pos_right hab hx
  have hsub : uIcc (a*x) (b*x) ⊆ uIcc (0:ℝ) (b*x) := by
    rw [uIcc_of_le hband.le,uIcc_of_le (hax.trans hband.le)]
    exact Icc_subset_Icc hax le_rfl
  have hfband : IntervalIntegrable (fun u=>|f u|) volume (a*x) (b*x):=
    hf.abs.mono_set hsub
  have Hlow : (b-a)*x^4 ≤ ∫u in a*x..b*x, |f u| := by
    have H:=intervalIntegral.integral_mono_on_of_le_Ioo hband.le
      (show IntervalIntegrable (fun _ : ℝ=>x^3) volume (a*x) (b*x) from intervalIntegrable_const)
      hfband (fun u hu=>(hnone u hu).le)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at H
    convert H using 1; ring
  have Hup : (∫u in a*x..b*x, |f u|) ≤ ∫u in 0..b*x, |f u|:=
    intervalIntegral.integral_mono_interval hax hband.le le_rfl
      (ae_of_all _ (fun _=>abs_nonneg _)) hf.abs
  exact (not_lt_of_ge (Hlow.trans Hup)) hsmall

end OAI.SKFluctuations.LaplaceWindowFormalization
