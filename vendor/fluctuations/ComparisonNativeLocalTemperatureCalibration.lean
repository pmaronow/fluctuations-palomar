module

public import ComparisonNativeActualInheritedCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal

theorem scalar_calibration_at_local_temperature
    (Gamma : ℝ → ℝ) {Tloc x S K c Cs Ck Cr : ℝ}
    (hTloc : 0 < Tloc) (hx : 0 < x) (hx1 : x ≤ 1)
    (hCk : 0 ≤ Ck) (hSlo : c*x ≤ S) (hShi : S ≤ Cs*x)
    (hclock : |K-Tloc*S| ≤ Ck*x^3)
    (hsmall : Ck*x^2 ≤ Tloc*c/2)
    (hres : |S-Gamma K| ≤ Cr*x^3) :
    c/2*x ≤ K/Tloc ∧ K/Tloc ≤ (Cs+Ck/Tloc)*x ∧
      |Gamma (Tloc*(K/Tloc))-K/Tloc| ≤ (Cr+Ck/Tloc)*x^3 := by
  have hcomp : |K/Tloc-S| ≤ (Ck/Tloc)*x^3 := by
    have hid : K/Tloc-S=(K-Tloc*S)/Tloc := by field_simp
    rw [hid,abs_div,abs_of_pos hTloc]
    exact (div_le_div_of_nonneg_right hclock hTloc.le).trans_eq (by ring)
  have hK : Tloc*(c/2)*x ≤ K := by
    have Habs := (abs_le.mp hclock).1
    have Hsmall := mul_le_mul_of_nonneg_right hsmall hx.le
    have Hmean := mul_le_mul_of_nonneg_left hSlo hTloc.le
    nlinarith only [Habs,Hsmall,Hmean]
  have hx2 : x^2 ≤ 1 := by nlinarith only [hx,hx1,sq_nonneg (x-1)]
  have hx3 : x^3 ≤ x := by nlinarith only [mul_le_mul_of_nonneg_right hx2 hx.le]
  refine ⟨(le_div_iff₀ hTloc).mpr (by nlinarith only [hK]),?_,?_⟩
  · have H := le_abs_self (K/Tloc-S)
    have Hsmall := mul_le_mul_of_nonneg_left hx3 (div_nonneg hCk hTloc.le)
    linarith only [hShi,H,Hsmall,hcomp]
  · rw [mul_div_cancel₀ _ hTloc.ne']
    have H := abs_sub_le (Gamma K) S (K/Tloc)
    rw [abs_sub_comm (Gamma K) S,abs_sub_comm S (K/Tloc)] at H
    exact H.trans (by linarith only [hres,hcomp])

end OAI.SKFluctuations.LaplaceWindowFormalization
