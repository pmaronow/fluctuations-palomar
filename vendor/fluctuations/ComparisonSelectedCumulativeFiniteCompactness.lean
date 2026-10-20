module

public import ComparisonSelectedCumulativeCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 1800000

theorem boundedLipschitzCumulative_finite_exists_uniform_subseq
    {β : Type*} [Fintype β] {B : ℝ} (hB : 0≤B)
    (F : ℕ→β→(Icc (0:ℝ) 1→ᵇℝ))
    (hLip : ∀j b,LipschitzWith B.toNNReal (F j b))
    (hb : ∀j b r,F j b r∈Icc (0:ℝ) B) :
    ∃f : β→(Icc (0:ℝ) 1→ᵇℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀b,Tendsto (fun j=>F (φ j) b) atTop (𝓝 (f b)) := by
  let A := fun b=>Set.range (fun j=>F j b)
  have hc : ∀b,IsCompact (closure (A b)) := by
    intro b
    have hEqui : Equicontinuous (fun f : A b=>fun r=>f.val r) := by
      apply (Metric.uniformEquicontinuous_of_continuity_modulus
        (fun t=>B*t) (by simpa using
          ((tendsto_id : Tendsto (fun t : ℝ=>t) (𝓝 0) (𝓝 0)).const_mul B)) _ _).equicontinuous
      intro r s f
      obtain ⟨j,hj⟩ := f.property
      simpa only [←hj,Real.coe_toNNReal _ hB] using (hLip j b).dist_le_mul r s
    exact BoundedContinuousFunction.arzela_ascoli (Icc (0:ℝ) B) isCompact_Icc (A b)
      (fun f r hf=>by obtain ⟨j,rfl⟩:=hf;exact hb j b r) hEqui
  have hproduct : IsCompact (Set.univ.pi (fun b=>closure (A b))) := isCompact_univ_pi hc
  obtain ⟨f,_,φ,hφ,hlim⟩ := hproduct.tendsto_subseq
    (fun j b _=>subset_closure (show F j b∈A b from ⟨j,rfl⟩))
  exact ⟨f,φ,hφ,fun b=>tendsto_pi_nhds.mp hlim b⟩

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonSelectedCumulative_finite_exists_uniform_subseq
    {β : Type*} {ι : Type} [Fintype β]
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (J : ∀j,β→Finset (Fin ((sampleClockSteps q 0 (as j)).length+1))) :
    ∃f : β→(Icc (0:ℝ) 1→ᵇℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀b,Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM
        q α (as (φ j)) (ho (φ j)) (J (φ j) b)) atTop (𝓝 (f b)) := by
  apply boundedLipschitzCumulative_finite_exists_uniform_subseq hM
    (fun j b=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α (as j) (ho j) (J j b))
  · intro j b
    exact cumulativeCellMass_lipschitz hM _
      (comparisonSelectedMassDensity_integrable hc hk hkc hm hM q α (as j) (ho j) (J j b))
      (fun r _=>by
        have hh := comparisonSelectedMassDensity_mem_Icc hc hk hkc hm hM q α (as j) (ho j) (J j b) r
        rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
        exact hh.2)
  · intro j b r
    exact cumulativeCellMass_mem_Icc hM _
      (comparisonSelectedMassDensity_integrable hc hk hkc hm hM q α (as j) (ho j) (J j b))
      (fun t _=>comparisonSelectedMassDensity_mem_Icc hc hk hkc hm hM q α (as j) (ho j) (J j b) t) r

end
end OAI.SKFluctuations.LaplaceWindowFormalization
