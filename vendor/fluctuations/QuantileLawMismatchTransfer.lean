module

public import ScalarProfileL1Stability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem quantileMassProfile_l1_le (q r : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1)) (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hqb : ∀ u ∈ Icc (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1)
    (hrb : ∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1) :
    (∫ t in (0:ℝ)..1, |(quantileMassProfile q hqb).val t-
      (quantileMassProfile r hrb).val t|) ≤ ∫ u in (0:ℝ)..1, |q u-r u| := by
  let lo : ℝ → ℝ := fun u => min (q u) (r u)
  let hi : ℝ → ℝ := fun u => max (q u) (r u)
  have hlo : MonotoneOn lo (Icc (0:ℝ) 1) := hq.min hr
  have hhi : MonotoneOn hi (Icc (0:ℝ) 1) := hq.max hr
  have hlob : ∀ u ∈ Icc (0:ℝ) 1, lo u ∈ Icc (0:ℝ) 1 := by
    intro u hu
    exact ⟨le_min (hqb u hu).1 (hrb u hu).1, (min_le_left _ _).trans (hqb u hu).2⟩
  have hhib : ∀ u ∈ Icc (0:ℝ) 1, hi u ∈ Icc (0:ℝ) 1 := by
    intro u hu
    exact ⟨(hqb u hu).1.trans (le_max_left _ _), max_le (hqb u hu).2 (hrb u hu).2⟩
  have hscalar (t : ℝ) :
      |(quantileMassProfile q hqb).val t-(quantileMassProfile r hrb).val t| ≤
        |(quantileMassProfile lo hlob).val t-(quantileMassProfile hi hhib).val t| := by
    have hloq := quantileMassProfile_antitone lo q hlo hq hlob hqb (fun u _ => min_le_left _ _) t
    have hlor := quantileMassProfile_antitone lo r hlo hr hlob hrb (fun u _ => min_le_right _ _) t
    have hqhi := quantileMassProfile_antitone q hi hq hhi hqb hhib (fun u _ => le_max_left _ _) t
    have hrhi := quantileMassProfile_antitone r hi hr hhi hrb hhib (fun u _ => le_max_right _ _) t
    have hlohi := quantileMassProfile_antitone lo hi hlo hhi hlob hhib
      (fun u _ => min_le_max) t
    rw [abs_of_nonneg (sub_nonneg.mpr hlohi)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ ∫ t in (0:ℝ)..1,
        |(quantileMassProfile lo hlob).val t-(quantileMassProfile hi hhib).val t| :=
      intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
        (((quantileMassProfile q hqb).property.2.intervalIntegrable).sub
          ((quantileMassProfile r hrb).property.2.intervalIntegrable)).abs
        (((quantileMassProfile lo hlob).property.2.intervalIntegrable).sub
          ((quantileMassProfile hi hhib).property.2.intervalIntegrable)).abs
        (fun t _ => hscalar t)
    _ = ∫ u in (0:ℝ)..1, |lo u-hi u| :=
      quantileMassProfile_ordered_l1 lo hi hlo hhi hlob hhib (fun u _ => min_le_max)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only [lo,hi]
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr min_le_max), max_sub_min_eq_abs']

theorem scalar_quantile_value_l1 {T : ℝ} (hT : 0 < T) (q r : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1)) (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hqb : ∀ u ∈ Icc (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1)
    (hrb : ∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1) :
    |scalarParisiValue hT (quantileMassProfile q hqb)-
      scalarParisiValue hT (quantileMassProfile r hrb)| ≤ T*(∫u in (0:ℝ)..1, |q u-r u|) :=
  (scalarParisiValue_L1_comparison hT _ _).trans
    (mul_le_mul_of_nonneg_left (quantileMassProfile_l1_le q r hq hr hqb hrb) hT.le)

end OAI.SKFluctuations.LaplaceWindowFormalization
