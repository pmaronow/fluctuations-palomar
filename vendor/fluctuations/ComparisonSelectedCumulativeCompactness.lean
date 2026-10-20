module

public import ComparisonNativeUnitColumns
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 1800000

def cumulativeCellMass (g : ℝ → ℝ) (r : ℝ) : ℝ := ∫t in (0:ℝ)..r,g t

theorem cumulativeCellMass_lipschitz {B : ℝ} (hB : 0≤B)
    (g : ℝ → ℝ) (hi : IntegrableOn g (Icc (0:ℝ) 1))
    (hb : ∀r∈Icc (0:ℝ) 1,‖g r‖≤B) :
    LipschitzWith B.toNNReal (fun r : Icc (0:ℝ) 1=>cumulativeCellMass g r.val) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  have hir : IntervalIntegrable g volume 0 r.val :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le r.property.1).mpr
      (hi.mono_set (Icc_subset_Icc le_rfl r.property.2))
  have his : IntervalIntegrable g volume 0 s.val :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le s.property.1).mpr
      (hi.mono_set (Icc_subset_Icc le_rfl s.property.2))
  rw [Real.dist_eq,cumulativeCellMass,cumulativeCellMass,
    intervalIntegral.integral_interval_sub_left hir his,←Real.norm_eq_abs]
  have hsub : uIoc s.val r.val⊆Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨lt_of_le_of_lt (le_min s.property.1 r.property.1) ht.1 |>.le,
      ht.2.trans (max_le s.property.2 r.property.2)⟩
  simpa only [Real.coe_toNNReal _ hB,Subtype.dist_eq,Real.dist_eq,abs_sub_comm]
    using intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht=>hb t (hsub ht))

theorem cumulativeCellMass_mem_Icc {B : ℝ} (hB : 0≤B)
    (g : ℝ → ℝ) (hi : IntegrableOn g (Icc (0:ℝ) 1))
    (hb : ∀r∈Icc (0:ℝ) 1,g r∈Icc (0:ℝ) B) (r : Icc (0:ℝ) 1) :
    cumulativeCellMass g r.val∈Icc (0:ℝ) B := by
  have hnonneg : 0≤cumulativeCellMass g r.val :=
    intervalIntegral.integral_nonneg r.property.1 (fun t ht=>
      (hb t ⟨ht.1,ht.2.trans r.property.2⟩).1)
  have hLip := cumulativeCellMass_lipschitz hB g hi (fun t ht=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb t ht).1]
    exact (hb t ht).2)
  have hh := hLip.dist_le_mul r ⟨0,by simp⟩
  simp only [cumulativeCellMass,intervalIntegral.integral_same,Real.dist_eq,
    sub_zero,Subtype.dist_eq,Real.coe_toNNReal _ hB,abs_of_nonneg r.property.1] at hh
  have hmul : B*r.val≤B := by nlinarith [r.property.2]
  exact ⟨hnonneg,(le_abs_self _).trans (hh.trans hmul)⟩

theorem boundedLipschitzCumulative_exists_uniform_subseq
    {B : ℝ} (hB : 0≤B)
    (F : ℕ → (Icc (0:ℝ) 1 →ᵇ ℝ))
    (hLip : ∀j,LipschitzWith B.toNNReal (F j))
    (hb : ∀j r,F j r∈Icc (0:ℝ) B) :
    ∃ f : Icc (0:ℝ) 1 →ᵇ ℝ,∃ φ : ℕ→ℕ,
      StrictMono φ ∧ Tendsto (F∘φ) atTop (𝓝 f) := by
  let A := Set.range F
  have hEqui : Equicontinuous (fun f : A=>fun r=>f.val r) := by
    apply (Metric.uniformEquicontinuous_of_continuity_modulus
      (fun t=>B*t) (by simpa using
        ((tendsto_id : Tendsto (fun t : ℝ=>t) (𝓝 0) (𝓝 0)).const_mul B)) _ _).equicontinuous
    intro r s f
    obtain ⟨j,hj⟩ := f.property
    simpa only [←hj,Real.coe_toNNReal _ hB] using (hLip j).dist_le_mul r s
  have hCompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (0:ℝ) B) isCompact_Icc A
      (fun f r hf=>by obtain ⟨j,rfl⟩:=hf;exact hb j r) hEqui
  obtain ⟨f,_,φ,hφ,hlim⟩ := hCompact.tendsto_subseq
    (fun j=>subset_closure (show F j∈A from ⟨j,rfl⟩))
  exact ⟨f,φ,hφ,hlim⟩

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

def comparisonSelectedMassDensity {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) : ℝ→ℝ :=
  (Ioo (0:ℝ) 1).indicator (fun r=>deriv α.val.val r*
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J
      (fun _=>(0:Fin 1)) (fun _=>1) r)

theorem comparisonSelectedMassDensity_mem_Icc {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) (r : ℝ) :
    comparisonSelectedMassDensity hc hk hkc hm hM q α as J r∈Icc (0:ℝ) (M 1) := by
  unfold comparisonSelectedMassDensity
  by_cases hr:r∈Ioo (0:ℝ) 1
  · rw [indicator_of_mem hr]
    have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr.1 hr.2)
      (inverseIntegralConstraints_lipschitz hm hM α.property)
    have hd0 := α.val.property.2.deriv_nonneg (x:=r)
    have hw : comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J
        (fun _=>(0:Fin 1)) (fun _=>1) r∈Icc (0:ℝ) 1 := by
      apply radiusCellEnergyDensity_mem_Icc_bound _
        (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho _ (by norm_num)
      intro i
      unfold nativeSelectedColumn
      split_ifs <;> norm_num
    refine ⟨mul_nonneg hd0 hw.1,?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg hd0] at hd
    exact (mul_le_mul hd hw.2 hw.1 hM).trans_eq (mul_one _)
  · rw [indicator_of_notMem hr]
    exact ⟨le_rfl,hM⟩

theorem comparisonSelectedMassDensity_stronglyMeasurable {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) :
    StronglyMeasurable (comparisonSelectedMassDensity hc hk hkc hm hM q α as J) := by
  apply StronglyMeasurable.indicator _ measurableSet_Ioo
  exact (stronglyMeasurable_deriv α.val.val).mul
    (comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α as J
      (fun _=>(0:Fin 1)) (fun _=>1)).stronglyMeasurable

theorem comparisonSelectedMassDensity_integrable {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) :
    IntegrableOn (comparisonSelectedMassDensity hc hk hkc hm hM q α as J)
      (Icc (0:ℝ) 1) := by
  have h1 : IntegrableOn (fun _ : ℝ=>(1:ℝ)) (Icc (0:ℝ) 1) :=
    integrableOn_const (by simp)
  have hbound : ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
      ‖comparisonSelectedMassDensity hc hk hkc hm hM q α as J r‖≤M 1 := by
    apply ae_of_all
    intro r
    have hh := comparisonSelectedMassDensity_mem_Icc hc hk hkc hm hM q α as ho J r
    rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
    exact hh.2
  simpa only [IntegrableOn,mul_one] using h1.bdd_mul
    (comparisonSelectedMassDensity_stronglyMeasurable hc hk hkc hm hM q α as J).aestronglyMeasurable.restrict hbound

def comparisonSelectedCumulativeMap {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) : Icc (0:ℝ) 1 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨
    fun r=>cumulativeCellMass (comparisonSelectedMassDensity hc hk hkc hm hM q α as J) r.val,
    (cumulativeCellMass_lipschitz hM _
      (comparisonSelectedMassDensity_integrable hc hk hkc hm hM q α as ho J)
      (fun r _=>by
        have hh := comparisonSelectedMassDensity_mem_Icc hc hk hkc hm hM q α as ho J r
        rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
        exact hh.2)).continuous⟩

theorem comparisonSelectedCumulative_exists_uniform_subseq {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1))) :
    ∃ f : Icc (0:ℝ) 1 →ᵇ ℝ,∃ φ : ℕ→ℕ,StrictMono φ ∧
      Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM
        q α (as (φ j)) (ho (φ j)) (J (φ j))) atTop (𝓝 f) := by
  apply boundedLipschitzCumulative_exists_uniform_subseq hM
    (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α (as j) (ho j) (J j))
  · intro j
    exact cumulativeCellMass_lipschitz hM _
      (comparisonSelectedMassDensity_integrable hc hk hkc hm hM q α (as j) (ho j) (J j))
      (fun r _=>by
        have hh := comparisonSelectedMassDensity_mem_Icc hc hk hkc hm hM q α (as j) (ho j) (J j) r
        rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
        exact hh.2)
  · intro j r
    exact cumulativeCellMass_mem_Icc hM _
      (comparisonSelectedMassDensity_integrable hc hk hkc hm hM q α (as j) (ho j) (J j))
      (fun t _=>comparisonSelectedMassDensity_mem_Icc hc hk hkc hm hM q α (as j) (ho j) (J j) t) r

end
end OAI.SKFluctuations.LaplaceWindowFormalization
