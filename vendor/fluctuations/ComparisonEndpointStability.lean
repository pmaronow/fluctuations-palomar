module

public import ActualComparisonScalarUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem pathCompensatedPressure_l1_endpoint_comparison (n : ℕ) (hn : 0 < n)
    (b h b' h' e r : ℝ → ℝ)
    (hb : MonotoneOn (fun u => b u-e u) (Icc (0:ℝ) 1))
    (hh : MonotoneOn (fun u => h u+e u*r u) (Icc (0:ℝ) 1))
    (hb' : MonotoneOn (fun u => b' u-e u) (Icc (0:ℝ) 1))
    (hh' : MonotoneOn (fun u => h' u+e u*r u) (Icc (0:ℝ) 1))
    (hb0 : 0 ≤ b 0-e 0) (hh0 : 0 ≤ h 0+e 0*r 0)
    (hb0' : 0 ≤ b' 0-e 0) (hh0' : 0 ≤ h' 0+e 0*r 0) :
    |pathCompensatedPressure n b h e r 0-pathCompensatedPressure n b' h' e r 0| ≤
      (1/4:ℝ)*(∫u in (0:ℝ)..1,|b u-b' u|)+(1/2:ℝ)*(∫u in (0:ℝ)..1,|h u-h' u|) := by
  have hp := realOrderedSKPathPressure_l1_comparison n hn (fun u => b u-e u)
    (fun u => h u+e u*r u) (fun u => b' u-e u) (fun u => h' u+e u*r u)
    hb hh hb' hh' hb0 hh0 hb0' hh0' 0
  have hbi : (∫u in (0:ℝ)..1,|b u-e u-(b' u-e u)|)=(∫u in (0:ℝ)..1,|b u-b' u|) := by
    congr 1; funext u; congr 1; ring
  have hhi : (∫u in (0:ℝ)..1,|h u+e u*r u-(h' u+e u*r u)|)=
      (∫u in (0:ℝ)..1,|h u-h' u|) := by
    congr 1; funext u; congr 1; ring
  rw [hbi,hhi] at hp
  simpa only [pathCompensatedPressure,add_sub_add_right_eq_sub] using hp

theorem actualComparisonPressure_tendsto_of_endpoint_l1
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (bseq hseq eseq rseq : ℕ → ℝ → ℝ) (T V : ℝ)
    (hvalue : Tendsto (fun n => pathCompensatedPressure (N n) (fun _ => T)
      (fun _ => 0) (eseq n) (rseq n) 0) atTop (𝓝 V))
    (hb : ∀ n, MonotoneOn (fun u => bseq n u-eseq n u) (Icc (0:ℝ) 1))
    (hh : ∀ n, MonotoneOn (fun u => hseq n u+eseq n u*rseq n u) (Icc (0:ℝ) 1))
    (hb' : ∀ n, MonotoneOn (fun u => T-eseq n u) (Icc (0:ℝ) 1))
    (hh' : ∀ n, MonotoneOn (fun u => eseq n u*rseq n u) (Icc (0:ℝ) 1))
    (hb0 : ∀ n, 0 ≤ bseq n 0-eseq n 0)
    (hh0 : ∀ n, 0 ≤ hseq n 0+eseq n 0*rseq n 0)
    (hb0' : ∀ n, 0 ≤ T-eseq n 0) (hh0' : ∀ n, 0 ≤ eseq n 0*rseq n 0)
    (hbdist : Tendsto (fun n => ∫u in (0:ℝ)..1,|bseq n u-T|) atTop (𝓝 0))
    (hhdist : Tendsto (fun n => ∫u in (0:ℝ)..1,|hseq n u|) atTop (𝓝 0)) :
    Tendsto (fun n => pathCompensatedPressure (N n) (bseq n) (hseq n) (eseq n) (rseq n) 0)
      atTop (𝓝 V) := by
  have hd : Tendsto (fun n => pathCompensatedPressure (N n) (bseq n) (hseq n) (eseq n) (rseq n) 0-
      pathCompensatedPressure (N n) (fun _ => T) (fun _ => 0) (eseq n) (rseq n) 0) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _
      (show Tendsto (fun n => (1/4:ℝ)*(∫u in (0:ℝ)..1,|bseq n u-T|)+
        (1/2:ℝ)*(∫u in (0:ℝ)..1,|hseq n u|)) atTop (𝓝 0) by
          simpa using (hbdist.const_mul (1/4:ℝ)).add (hhdist.const_mul (1/2:ℝ)))
    filter_upwards [hN.eventually (eventually_gt_atTop (0:ℕ))] with n hn
    simpa only [zero_add,sub_zero] using pathCompensatedPressure_l1_endpoint_comparison (N n) hn
      (bseq n) (hseq n) (fun _ => T) (fun _ => 0) (eseq n) (rseq n)
      (hb n) (hh n) (hb' n) (by simpa only [zero_add] using hh' n)
      (hb0 n) (hh0 n) (hb0' n) (by simpa only [zero_add] using hh0' n)
  simpa only [sub_add_cancel,zero_add] using hd.add hvalue

end OAI.SKFluctuations.LaplaceWindowFormalization
