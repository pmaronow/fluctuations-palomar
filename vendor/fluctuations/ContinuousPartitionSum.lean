module

public import SKFluctuationsOAI.Probability.SKFluctuations.OrderedSKRateDirection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology

theorem continuous_partitionSum_tendsto {q : ℝ→ℝ}
    (hq : ContinuousOn q (Icc (0:ℝ) 1)) :
    Tendsto (fun k=>massStepSum (uniformMasses k) 0
      (fun j=>q (partitionPoint 0 (uniformMasses k) j))) atTop
        (𝓝 (∫u in (0:ℝ)..1,q u)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have hlim : Tendsto (fun k=>∫u in (0:ℝ)..1,partitionSample q 0 (uniformMasses k) u)
      atTop (𝓝 (∫u in (0:ℝ)..1,q u)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := fun k u=>partitionSample q 0 (uniformMasses k) u) (f := q)
      (μ := volume) (a := (0:ℝ)) (b := 1) (fun _=>C)
    · apply Eventually.of_forall
      intro k
      exact (partitionSample_intervalIntegrable q 0 (uniformMasses k) 0 1).def'.aestronglyMeasurable
    · apply Eventually.of_forall
      intro k
      apply Eventually.of_forall
      intro u hu
      have hu' : u∈Icc (0:ℝ) 1 := (by simpa only [uIoc_of_le zero_le_one] using hu : u∈Ioc (0:ℝ) 1).1.le |> fun h=>⟨h,(by simpa only [uIoc_of_le zero_le_one] using hu : u∈Ioc (0:ℝ) 1).2⟩
      have hb := partitionSample_id_bounds (uniformMasses k) (uniformMasses_ordered k)
        (uniformMasses_mesh k) hu'
      rw [partitionSample_comp]
      exact hC _ ⟨hb.1,hb.2.1.trans hu'.2⟩
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro u hu
      have hu' : u∈Icc (0:ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at hu
        exact ⟨hu.1.le,hu.2⟩
      exact uniformSample_tendsto hu' (hq u hu')
  have he (k : ℕ) : (∫u in (0:ℝ)..1,partitionSample q 0 (uniformMasses k) u)=
      massStepSum (uniformMasses k) 0 (fun j=>q (partitionPoint 0 (uniformMasses k) j)) := by
    unfold partitionSample
    rw [massStepFunction_integral _ _ _ (uniformMasses_ordered k)]
    congr 1
    funext j
    exact partitionValues_point q 0 (uniformMasses k) j
  simpa only [he] using hlim

end OAI.SKFluctuations.LaplaceWindowFormalization
