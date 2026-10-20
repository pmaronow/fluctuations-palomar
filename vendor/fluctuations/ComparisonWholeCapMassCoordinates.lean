module

public import ComparisonWholeCapEndpointMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set MeasureTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem ordConnectedComponent_preimage_continuous_monotone (q : ℝ → ℝ)
    (hq : Continuous q) (hm : Monotone q) (U : Set ℝ) (u : ℝ) :
    ordConnectedComponent (q⁻¹' U) u=q⁻¹' ordConnectedComponent U (q u) := by
  ext v
  simp only [mem_preimage,mem_ordConnectedComponent]
  constructor
  · intro h z hz
    obtain ⟨t,ht,he⟩ := intermediate_value_uIcc hq.continuousOn hz
    exact he ▸ h ht
  · intro h t ht
    exact h (hm.mapsTo_uIcc ht)

section
variable {c : ℝ} {k M : ℝ → ℝ} (hc : 0 < c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

 theorem comparisonSweepQuantile_at_profile (α : inverseIntegralConstraints 0 0 k M)
    {r : ℝ} (hr:r∈Icc (0:ℝ) 1) :
    comparisonSweepQuantile hc hk hkc hm hM α (α.val.val r)=r := by
  have hspec := comparisonSweepQuantile_spec hc hk hkc hm hM α (α.val.property.1 r)
  exact (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α _) hr hspec

 theorem comparisonSweepQuantile_endpoints (α : inverseIntegralConstraints 0 0 k M) :
    comparisonSweepQuantile hc hk hkc hm hM α 0=0 ∧
      comparisonSweepQuantile hc hk hkc hm hM α 1=1 := by
  constructor
  · simpa only [α.property.1] using comparisonSweepQuantile_at_profile hc hk hkc hm hM α
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)
  · simpa only [α.property.2.1] using comparisonSweepQuantile_at_profile hc hk hkc hm hM α
      (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)

 theorem comparisonSweepQuantile_preimage_open_interval
    (α : inverseIntegralConstraints 0 0 k M) {a b : ℝ}
    (ha:a∈Icc (0:ℝ) 1) (hb:b∈Icc (0:ℝ) 1) :
    (comparisonSweepQuantile hc hk hkc hm hM α)⁻¹' Ioo a b=
      Ioo (α.val.val a) (α.val.val b) := by
  let q := comparisonSweepQuantile hc hk hkc hm hM α
  have hqm : Monotone q := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hqe := comparisonSweepQuantile_endpoints hc hk hkc hm hM α
  change q 0=0 ∧ q 1=1 at hqe
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property
  ext u
  change q u∈Ioo a b ↔ u∈Ioo (α.val.val a) (α.val.val b)
  constructor
  · intro hu
    have hu0 : 0<u := by
      by_contra hno
      have hle := hqm (le_of_not_gt hno)
      change q u≤q 0 at hle
      rw [hqe.1] at hle
      linarith [hu.1,ha.1]
    have hu1 : u<1 := by
      by_contra hno
      have hle := hqm (le_of_not_gt hno)
      change q 1≤q u at hle
      rw [hqe.2] at hle
      linarith [hu.2,hb.2]
    have hspec := comparisonSweepQuantile_spec hc hk hkc hm hM α ⟨hu0.le,hu1.le⟩
    have hlo := hstrict ha (comparisonSweepQuantile_bounds hc hk hkc hm hM α u) hu.1
    have hhi := hstrict (comparisonSweepQuantile_bounds hc hk hkc hm hM α u) hb hu.2
    rw [hspec] at hlo hhi
    exact ⟨hlo,hhi⟩
  · intro hu
    have hub : u∈Icc (0:ℝ) 1 :=
      ⟨(α.val.property.1 a).1.trans hu.1.le,hu.2.le.trans (α.val.property.1 b).2⟩
    have hspec := comparisonSweepQuantile_spec hc hk hkc hm hM α hub
    constructor
    · by_contra hno
      have hle := α.val.property.2 (le_of_not_gt hno)
      change α.val.val (q u)≤α.val.val a at hle
      rw [hspec] at hle
      exact hu.1.not_ge hle
    · by_contra hno
      have hle := α.val.property.2 (le_of_not_gt hno)
      change α.val.val b≤α.val.val (q u) at hle
      rw [hspec] at hle
      exact hu.2.not_ge hle

 theorem comparisonSweepQuantile_preimage_open_subset
    (α : inverseIntegralConstraints 0 0 k M) {U : Set ℝ}
    (hU:U⊆Ioo (0:ℝ) 1) :
    (comparisonSweepQuantile hc hk hkc hm hM α)⁻¹' U⊆Ioo (0:ℝ) 1 := by
  have hsub := preimage_mono hU (f:=comparisonSweepQuantile hc hk hkc hm hM α)
  rw [comparisonSweepQuantile_preimage_open_interval hc hk hkc hm hM α
    (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) (show (1:ℝ)∈Icc (0:ℝ) 1 by simp),
    α.property.1,α.property.2.1] at hsub
  exact hsub

 theorem comparisonWholeCap_mass_component (α : inverseIntegralConstraints 0 0 k M)
    {U : Set ℝ} (hopen:IsOpen U) (hU:U⊆Icc (0:ℝ) 1) {r : ℝ} (hr:r∈U) :
    let q := comparisonSweepQuantile hc hk hkc hm hM α
    let C := ordConnectedComponent U r
    ordConnectedComponent (q⁻¹' U) (α.val.val r)=
      Ioo (α.val.val (sInf C)) (α.val.val (sSup C)) := by
  dsimp only
  obtain ⟨hlo,hlr,hrz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hopen hU hr
  have hla : sInf (ordConnectedComponent U r)∈Icc (0:ℝ) 1 :=
    ⟨hlo,hlr.le.trans (hU hr).2⟩
  have hlb : sSup (ordConnectedComponent U r)∈Icc (0:ℝ) 1 :=
    ⟨(hU hr).1.trans hrz.le,hhi⟩
  rw [ordConnectedComponent_preimage_continuous_monotone _
    (comparisonSweepQuantile_continuous hc hk hkc hm hM α)
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α),
    comparisonSweepQuantile_at_profile hc hk hkc hm hM α (hU hr)]
  conv_lhs => rw [heq]
  rw [comparisonSweepQuantile_preimage_open_interval hc hk hkc hm hM α hla hlb]

def comparisonWholeCapMassRepresentative (α : inverseIntegralConstraints 0 0 k M)
    (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1) (r : ordConnectedSection U) :
    ordConnectedSection ((comparisonSweepQuantile hc hk hkc hm hM α)⁻¹' U) := by
  let q := comparisonSweepQuantile hc hk hkc hm hM α
  have hr : r.val∈U := ordConnectedSection_subset r.property
  have hmU : α.val.val r.val∈q⁻¹' U := by
    change comparisonSweepQuantile hc hk hkc hm hM α (α.val.val r.val)∈U
    rw [comparisonSweepQuantile_at_profile hc hk hkc hm hM α (hU hr)]
    exact hr
  exact ⟨ordConnectedProj (q⁻¹' U) ⟨α.val.val r.val,hmU⟩,⟨⟨α.val.val r.val,hmU⟩,rfl⟩⟩

def comparisonWholeCapMassSelection (α : inverseIntegralConstraints 0 0 k M)
    (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1) (F : Finset (ordConnectedSection U)) :
    Finset (ordConnectedSection ((comparisonSweepQuantile hc hk hkc hm hM α)⁻¹' U)) :=
  F.image (comparisonWholeCapMassRepresentative hc hk hkc hm hM α U hU)

theorem comparisonWholeCapMassRepresentative_component
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1)
    (r : ordConnectedSection U) :
    let q := comparisonSweepQuantile hc hk hkc hm hM α
    ordConnectedComponent (q⁻¹' U)
      (comparisonWholeCapMassRepresentative hc hk hkc hm hM α U hU r).val=
      q⁻¹' ordConnectedComponent U r.val := by
  dsimp only
  let q := comparisonSweepQuantile hc hk hkc hm hM α
  have hr : r.val∈U := ordConnectedSection_subset r.property
  have hmU : α.val.val r.val∈q⁻¹' U := by
    change comparisonSweepQuantile hc hk hkc hm hM α (α.val.val r.val)∈U
    rw [comparisonSweepQuantile_at_profile hc hk hkc hm hM α (hU hr)]
    exact hr
  have hp : α.val.val r.val∈ordConnectedComponent (q⁻¹' U)
      (comparisonWholeCapMassRepresentative hc hk hkc hm hM α U hU r).val :=
    mem_ordConnectedComponent_ordConnectedProj (q⁻¹' U) ⟨α.val.val r.val,hmU⟩
  rw [ordConnectedComponent_eq hp,
    ordConnectedComponent_preimage_continuous_monotone _
      (comparisonSweepQuantile_continuous hc hk hkc hm hM α)
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α),
    comparisonSweepQuantile_at_profile hc hk hkc hm hM α (hU hr)]

theorem comparisonWholeCapMassSelection_union
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1)
    (F : Finset (ordConnectedSection U)) :
    let q := comparisonSweepQuantile hc hk hkc hm hM α
    wholeCapFiniteUnion (q⁻¹' U)
      (comparisonWholeCapMassSelection hc hk hkc hm hM α U hU F)=
      q⁻¹' wholeCapFiniteUnion U F := by
  dsimp only
  ext u
  constructor
  · intro hu
    obtain ⟨z,hz,huz⟩ := mem_iUnion₂.mp hu
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hz
    subst z
    rw [comparisonWholeCapMassRepresentative_component hc hk hkc hm hM α U hU r] at huz
    exact mem_iUnion₂.mpr ⟨r,hr,huz⟩
  · intro hu
    obtain ⟨r,hr,hur⟩ := mem_iUnion₂.mp hu
    apply mem_iUnion₂.mpr
    refine ⟨comparisonWholeCapMassRepresentative hc hk hkc hm hM α U hU r,
      Finset.mem_image.mpr ⟨r,hr,rfl⟩,?_⟩
    rw [comparisonWholeCapMassRepresentative_component hc hk hkc hm hM α U hU r]
    exact hur

def comparisonWholeCapEndpointMasses (α : inverseIntegralConstraints 0 0 k M)
    (U : Set ℝ) (F : Finset (ordConnectedSection U)) : Finset ℝ :=
  F.biUnion (fun r => {α.val.val (sInf (ordConnectedComponent U r.val)),
    α.val.val (sSup (ordConnectedComponent U r.val))})

theorem comparisonWholeCapEndpointMasses_bound
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ) (F : Finset (ordConnectedSection U)) :
    ∀d∈comparisonWholeCapEndpointMasses α U F,d∈Icc (0:ℝ) 1 := by
  intro d hd
  obtain ⟨r,hr,hd⟩ := Finset.mem_biUnion.mp hd
  rcases Finset.mem_insert.mp hd with rfl|hd
  · exact α.val.property.1 _
  · have he := Finset.mem_singleton.mp hd
    subst d
    exact α.val.property.1 _

theorem comparisonWholeCapEndpointMasses_contains
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) {r : ordConnectedSection U} (hr:r∈F) :
    α.val.val (sInf (ordConnectedComponent U r.val))∈comparisonWholeCapEndpointMasses α U F ∧
      α.val.val (sSup (ordConnectedComponent U r.val))∈comparisonWholeCapEndpointMasses α U F := by
  constructor <;> apply Finset.mem_biUnion.mpr <;> exact ⟨r,hr,by simp⟩

theorem comparisonWholeCap_retained_grid_mass {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) {U : Set ℝ}
    (hopen:IsOpen U) (hU:U⊆Icc (0:ℝ) 1) (F : Finset (ordConnectedSection U))
    (m : ℕ) {r : ordConnectedSection U} (hr:r∈F) :
    let D := comparisonWholeCapEndpointMasses α U F
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    physicalWindowMass steps 0 (completeMassCapCells steps
      (α.val.val (sInf (ordConnectedComponent U r.val)))
      (α.val.val (sSup (ordConnectedComponent U r.val))))=
      (wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
        (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real
        (ordConnectedComponent U r.val) := by
  dsimp only
  have hrU := ordConnectedSection_subset r.property
  obtain ⟨hlo,hlr,hrz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hopen hU hrU
  have hla : sInf (ordConnectedComponent U r.val)∈Icc (0:ℝ) 1 :=
    ⟨hlo,hlr.le.trans (hU hrU).2⟩
  have hlb : sSup (ordConnectedComponent U r.val)∈Icc (0:ℝ) 1 :=
    ⟨(hU hrU).1.trans hrz.le,hhi⟩
  have hab := inverseConstraint_strictMonoOn hc hk hkc α.property hla hlb (hlr.trans hrz)
  have hend := comparisonWholeCapEndpointMasses_contains α U F hr
  rw [finiteBoundaryMass_complete_cap_mass clock _ (comparisonWholeCapEndpointMasses_bound α U F)
    m hend.1 hend.2 hab]
  conv_rhs => rw [heq]
  exact (wholeCap_actual_comparison_mass_Ioo hc hk hkc hm hM α (hlr.trans hrz)).symm

def comparisonWholeCapOriginalBin {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (m bins : ℕ) (w : ℝ) (j : ℕ) :=
  let q := comparisonSweepQuantile hc hk hkc hm hM α
  let as := finiteCutMasses (finiteBoundaryMassNodes (comparisonWholeCapEndpointMasses α U F)) m
  let steps := sampleClockSteps clock 0 as
  selectedWholeUnitBinCells steps (physicalCellMassMidpoint steps) (q⁻¹' U)
    (comparisonWholeCapMassSelection hc hk hkc hm hM α U hU F) (S∘q) 0 1 bins w j

theorem comparisonWholeCapOriginalBin_partition {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (m bins : ℕ) (w : ℝ) (j : ℕ)
    (hJ : (comparisonWholeCapOriginalBin hc hk hkc hm hM clock α U hU F S m bins w j).Nonempty) :
    let q := comparisonSweepQuantile hc hk hkc hm hM α
    let as := finiteCutMasses (finiteBoundaryMassNodes (comparisonWholeCapEndpointMasses α U F)) m
    let steps := sampleClockSteps clock 0 as
    let J := comparisonWholeCapOriginalBin hc hk hkc hm hM clock α U hU F S m bins w j
    ∃ (K : ℕ) (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ),
      0 < K ∧ x 0=0 ∧ x K=physicalWindowMass steps 0 J ∧
      (∀u:Fin K,x u.val < x (u.val+1)) ∧
      (∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val) ∧
      (∀i∈J,∀t∈J,unit i=unit t ↔
        wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps i)=
          wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps t)) ∧
      MonotoneOn unit (J:Set (Fin (steps.length+1))) := by
  dsimp only
  let as := finiteCutMasses (finiteBoundaryMassNodes (comparisonWholeCapEndpointMasses α U F)) m
  let steps := sampleClockSteps clock 0 as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered clock as
    (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound _
      (fun d hd => (comparisonWholeCapEndpointMasses_bound α U F d hd).2)) m)
  exact selectedWholeUnitBin_exists_coordinates steps ho (physicalCellMassMidpoint steps)
    (physicalCellMassMidpoint_monotone steps ho) _ _ _ 0 1 bins w j hJ

end
end OAI.SKFluctuations.WholeUnitSideKernel
