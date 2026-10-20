module

public import SKConstants.Completion.LC1.SignedFubini
public import SKConstants.ScalarStieltjesRiemann

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem stieltjes_integral_primitive (f : StieltjesFunction ℝ) (p : ℝ → ℝ)
    (hp : Measurable p) (C : ℝ≥0) (hC : ∀ u, |p u| ≤ C)
    (S T : ℝ) (hST : S ≤ T) :
    (∫ r in S..T, (∫ u in S..r, p u) ∂f.measure) =
      ∫ u in S..T, p u * (f T-f u) := by
  let μ := f.measure.restrict (Ioc S T)
  let ν := volume.restrict (Ioc S T)
  let _ : IsFiniteMeasure μ := ⟨by
    change (f.measure.restrict (Ioc S T)) univ < ⊤
    rw [Measure.restrict_apply_univ,f.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  let K : ℝ × ℝ → ℝ := fun q => if q.2 < q.1 then p q.2 else 0
  have hK : Measurable K := Measurable.ite
    (measurableSet_lt measurable_snd measurable_fst) (hp.comp measurable_snd) measurable_const
  have hi : Integrable K (μ.prod ν) := by
    apply Integrable.of_bound hK.aestronglyMeasurable C
    apply ae_of_all
    intro q
    dsimp [K]
    split_ifs
    · simpa only [Real.norm_eq_abs] using hC q.2
    · simp
  have inner (r : ℝ) (hr : r ∈ Ioc S T) :
      (∫ u in Ioc S T, K (r,u)) = ∫ u in S..r, p u := by
    have he : (fun u => K (r,u)) = (Iio r).indicator p := by
      funext u
      rfl
    rw [he,setIntegral_indicator measurableSet_Iio]
    have hs : Ioc S T ∩ Iio r = Ioo S r := by
      ext u
      simp only [mem_inter_iff,mem_Ioc,mem_Iio,mem_Ioo]
      constructor
      · rintro ⟨⟨hSu,_⟩,hur⟩
        exact ⟨hSu,hur⟩
      · rintro ⟨hSu,hur⟩
        exact ⟨⟨hSu,hur.le.trans hr.2⟩,hur⟩
    rw [hs,intervalIntegral.integral_of_le hr.1.le,integral_Ioc_eq_integral_Ioo]
  have outer (u : ℝ) (hu : u ∈ Ioc S T) :
      (∫ r in Ioc S T, K (r,u) ∂f.measure) = p u * (f T-f u) := by
    have he : (fun r => K (r,u)) = (Ioi u).indicator (fun _ => p u) := by
      funext r
      rfl
    rw [he,setIntegral_indicator measurableSet_Ioi]
    have hs : Ioc S T ∩ Ioi u = Ioc u T := by
      ext r
      simp only [mem_inter_iff,mem_Ioc,mem_Ioi]
      constructor
      · rintro ⟨⟨_,hrT⟩,hur⟩
        exact ⟨hur,hrT⟩
      · rintro ⟨hur,hrT⟩
        exact ⟨⟨hu.1.trans hur,hrT⟩,hur⟩
    rw [hs,setIntegral_const]
    simp only [Measure.real,f.measure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono hu.2)),smul_eq_mul]
    ring
  calc
    _ = ∫ r in Ioc S T, (∫ u in Ioc S T, K (r,u)) ∂f.measure := by
      rw [intervalIntegral.integral_of_le hST]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      exact (inner r hr).symm
    _ = ∫ u in Ioc S T, ∫ r in Ioc S T, K (r,u) ∂f.measure :=
      integral_integral_swap (μ:=μ) (ν:=ν) (f:=fun r u => K (r,u)) hi
    _ = _ := by
      rw [intervalIntegral.integral_of_le hST]
      apply setIntegral_congr_fun measurableSet_Ioc
      exact outer

theorem stieltjes_weighted_primitive (f : StieltjesFunction ℝ) (hf : Continuous f)
    (p : ℝ → ℝ) (hp : Measurable p) (C : ℝ≥0) (hC : ∀ u, |p u| ≤ C)
    (S T : ℝ) (hST : S ≤ T) :
    f T * (∫ u in S..T, p u) - (∫ r in S..T, (∫ u in S..r, p u) ∂f.measure) =
      ∫ u in S..T, f u * p u := by
  have hi : IntervalIntegrable p volume S T := by
    apply intervalIntegrable_iff.mpr
    let _ : IsFiniteMeasure (volume.restrict (uIoc S T)) := isFiniteMeasure_restrict.mpr (by simp [uIoc])
    exact Integrable.of_bound hp.aestronglyMeasurable C
      (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using hC u))
  have hiWeight : IntervalIntegrable (fun u => p u * (f T-f u)) volume S T :=
    hi.mul_continuousOn (continuous_const.sub hf).continuousOn
  rw [stieltjes_integral_primitive f p hp C hC S T hST, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hi.const_mul (f T)) hiWeight]
  apply intervalIntegral.integral_congr
  intro u _
  ring

end SKConstants.Completion.LC1
