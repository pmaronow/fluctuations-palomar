module

public import ComparisonNativeActualVirtualControl

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

 theorem native_numeric_scaled_gradient_bound
    {e ep s q t E D Cs Cq B : ℝ}
    (hE : 0 ≤ E) (hD : 0 ≤ D) (_hCs : 0 ≤ Cs) (_hCq : 0 ≤ Cq) (hB : 0 ≤ B)
    (he : |e| ≤ E) (hep : |ep| ≤ D) (hs : |s| ≤ Cs) (hq : |q| ≤ Cq) (ht : |t| ≤ B) :
    |ep*(q-2*t*s+t^2)+2*e*(t-s)| ≤ D*(Cq+2*B*Cs+B^2)+2*E*(B+Cs) := by
  have HT : |t^2| ≤ B^2 := by
    rw [abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  have HTS : |2*t*s| ≤ 2*B*Cs := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have H:=mul_le_mul ht hs (abs_nonneg _) hB
    nlinarith only [H]
  have HQ : |q-2*t*s+t^2| ≤ Cq+2*B*Cs+B^2 := by
    have H:=(abs_add_le (q-2*t*s) (t^2)).trans (add_le_add (abs_sub q (2*t*s)) le_rfl)
    linarith only [H,hq,HTS,HT]
  have Hdiff : |t-s| ≤ B+Cs := (abs_sub t s).trans (add_le_add ht hs)
  have HA := mul_le_mul hep HQ (abs_nonneg _) hD
  have HB := mul_le_mul he Hdiff (abs_nonneg _) hE
  have H := abs_add_le (ep*(q-2*t*s+t^2)) (2*e*(t-s))
  rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at H
  nlinarith only [H,HA,HB]

end OAI.SKFluctuations.LaplaceWindowFormalization
