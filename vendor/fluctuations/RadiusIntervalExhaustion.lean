module

public import RadiusCellEnergySupport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

theorem radius_measure_open_le_inner {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hdom : μ ≤ volume) {a p q z : ℝ} (hap : a ≤ p) (hpq : p ≤ q) (hqz : q ≤ z) :
    μ.real (Ioo a z) ≤ μ.real (Ioo p q)+(p-a)+(z-q) := by
  have hcover : Ioo a z⊆Ioo p q∪(Ioc a p∪Icc q z) := by
    intro r hr
    by_cases hpr : r ≤ p
    · exact Or.inr (Or.inl ⟨hr.1,hpr⟩)
    · by_cases hrq : r < q
      · exact Or.inl ⟨lt_of_not_ge hpr,hrq⟩
      · exact Or.inr (Or.inr ⟨le_of_not_gt hrq,hr.2.le⟩)
  have hmain := (measureReal_mono (μ:=μ) hcover).trans
    (measureReal_union_le (μ:=μ) (Ioo p q) (Ioc a p∪Icc q z))
  have hsub := measureReal_union_le (μ:=μ) (Ioc a p) (Icc q z)
  have hleft : μ.real (Ioc a p) ≤ p-a := by
    have ht := ENNReal.toReal_mono (by simp : volume (Ioc a p)≠⊤) (hdom (Ioc a p))
    change μ.real (Ioc a p) ≤ volume.real (Ioc a p) at ht
    rwa [Real.volume_real_Ioc_of_le hap] at ht
  have hright : μ.real (Icc q z) ≤ z-q := by
    have ht := ENNReal.toReal_mono (by simp : volume (Icc q z)≠⊤) (hdom (Icc q z))
    change μ.real (Icc q z) ≤ volume.real (Icc q z) at ht
    rwa [Real.volume_real_Icc_of_le hqz] at ht
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
