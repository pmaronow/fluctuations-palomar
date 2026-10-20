module

public import ComparisonBinBoundaryGrid

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

theorem selectedWholeUnitBin_restricted_exists_coordinates {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (r : Fin (steps.length+1) → ℝ) (hr : Monotone r) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (a b : ℝ) (k : ℕ) (w : ℝ) (j : ℕ) (B : Finset (Fin (steps.length+1)))
    (hJ:((selectedWholeUnitBinCells steps r U F S a b k w j)\B).Nonempty) :
    let J := (selectedWholeUnitBinCells steps r U F S a b k w j)\B
    ∃ (K : ℕ) (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ),
      0 < K ∧ x 0=0 ∧ x K=physicalWindowMass steps 0 J ∧
      (∀u:Fin K,x u.val < x (u.val+1)) ∧
      (∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val) ∧
      (∀i∈J,∀t∈J,unit i=unit t ↔ wholeUnit U (r i)=wholeUnit U (r t)) ∧
      MonotoneOn unit (J:Set (Fin (steps.length+1))) := by
  dsimp only
  obtain ⟨K,unit,x,hK,h0,hend,hx,hmass,hclass,horder⟩ :=
    exists_finite_selected_unit_coordinates steps ha _ hJ
      (fun i hi => ((mem_selectedWholeUnitBinCells _ _ _ _ _ _ _ _ _ _ _).mp
        (Finset.mem_sdiff.mp hi).1).1)
      (firstWholeUnitCell U r) ((firstWholeUnitCell_monotone U r hr).monotoneOn _)
  refine ⟨K,unit,x,hK,h0,hend,hx,hmass,?_,horder⟩
  intro i hi t ht
  exact (hclass i hi t ht).trans (firstWholeUnitCell_eq_iff U r i t)

theorem selectedWholeUnitBin_restricted_cap_unit_mass {ι V : Type}
    [Fintype V] [DecidableEq V] (steps : List (GaussianStep ι))
    (r : Fin (steps.length+1) → ℝ) {U : Set ℝ} {a b : ℝ} (hU:U⊆Icc a b)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) (j : ℕ)
    (B : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → V)
    (hclass:∀i∈(selectedWholeUnitBinCells steps r U F S a b bins w j)\B,
      ∀t∈(selectedWholeUnitBinCells steps r U F S a b bins w j)\B,
      unit i=unit t ↔ wholeUnit U (r i)=wholeUnit U (r t))
    {i : Fin (steps.length+1)}
    (hi:i∈(selectedWholeUnitBinCells steps r U F S a b bins w j)\B) (hir:r i∈U) :
    physicalSelectedUnitMass steps ((selectedWholeUnitBinCells steps r U F S a b bins w j)\B)
      unit (unit i)=physicalWindowMass steps 0
      ((Finset.univ.filter (fun t => 0 < pathMassDifferences steps 0 t ∧
        r t∈ordConnectedComponent U (r i)))\B) := by
  rw [physicalSelectedUnitMass_eq_window_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
  constructor
  · intro ht
    have htJ := (Finset.mem_sdiff.mpr ht.1)
    have he := (hclass t htJ i hi).mp ht.2
    have hm:r t∈wholeUnit U (r i) := he ▸ self_mem_wholeUnit U (r t)
    exact ⟨⟨((mem_selectedWholeUnitBinCells _ _ _ _ _ _ _ _ _ _ _).mp ht.1.1).1,
      by simpa [wholeUnit,hir] using hm⟩,ht.1.2⟩
  · intro ht
    have hm:r t∈wholeUnit U (r i) := by simpa [wholeUnit,hir] using ht.1.2
    have htJ := selectedWholeUnitBinCells_complete steps r hU F S bins w j
      (Finset.mem_sdiff.mp hi).1 ht.1.1 hm
    exact ⟨⟨htJ,ht.2⟩,(hclass t (Finset.mem_sdiff.mpr ⟨htJ,ht.2⟩) i hi).mpr
      (wholeUnit_eq_of_mem U hm)⟩

theorem physicalWindowObservable_restriction_add_removed {ι : Type}
    (steps : List (GaussianStep ι)) (J B : Finset (Fin (steps.length+1)))
    (obs : Fin (steps.length+1) → ℝ) :
    (∑i∈J\B,pathMassDifferences steps 0 i*obs i)+
      (∑i∈J∩B,pathMassDifferences steps 0 i*obs i)=
        ∑i∈J,pathMassDifferences steps 0 i*obs i := by
  have hd:Disjoint (J\B) (J∩B) := by
    rw [Finset.disjoint_left]
    intro i hi ht
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp ht).2
  have he:(J\B)∪(J∩B)=J := by
    ext i
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [←Finset.sum_union hd,he]

theorem selectedWholeUnitBinCells_restricted_weighted_decomposition {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (r : Fin (steps.length+1) → ℝ) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (a b : ℝ) {k : ℕ} (hk : 0 < k) (w : ℝ)
    (B : Finset (Fin (steps.length+1))) (obs : Fin (steps.length+1) → ℝ) :
    (∑j∈Finset.range k,∑i∈(selectedWholeUnitBinCells steps r U F S a b k w j)\B,
      pathMassDifferences steps 0 i*obs i)=
      ∑i∈(retainedWholeUnitCells steps r U F a b)\B,pathMassDifferences steps 0 i*obs i := by
  unfold selectedWholeUnitBinCells retainedWholeUnitCells
  simp_rw [Finset.sdiff_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hB:i∈B
  · simp [hB]
  · simp only [hB,not_false_eq_true,ite_true]
    by_cases hp : 0 < pathMassDifferences steps 0 i
    · by_cases hr : r i∈wholeCapRetainedRegion a b U F
      · simp only [hp,hr,true_and,ite_true]
        rw [Finset.sum_eq_single (capHeightBin U S k w (r i))]
        · simp
        · intro j hj hne
          simp only [Ne.symm hne,ite_false]
        · intro hnot
          exact False.elim (hnot (Finset.mem_range.mpr (heightBin_lt hk w _)))
      · simp [hr]
    · have hz:pathMassDifferences steps 0 i=0 := le_antisymm (le_of_not_gt hp)
        (pathMassDifferences_nonneg steps ha i)
      simp [hz]

section
variable {c : ℝ} {k M : ℝ → ℝ} (hc:0<c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)

theorem comparisonWholeCapBinOriginalBin_restricted_partition {ι : Type}
    (clock : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1) (F : Finset (ordConnectedSection U))
    (S : ℝ → ℝ) (m bins : ℕ) (w : ℝ) (j : ℕ)
    (hJ:
      let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
      let as := finiteCutMasses (finiteBoundaryMassNodes D) m
      ((comparisonWholeCapBinOriginalBin hc hk hkc hm hM clock α U hU F S m bins w j)\
        fixedEndpointRows clock as D).Nonempty) :
    let q := comparisonSweepQuantile hc hk hkc hm hM α
    let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    let J := (comparisonWholeCapBinOriginalBin hc hk hkc hm hM clock α U hU F S m bins w j)\
      fixedEndpointRows clock as D
    ∃ (K : ℕ) (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ),
      0 < K ∧ x 0=0 ∧ x K=physicalWindowMass steps 0 J ∧
      (∀u:Fin K,x u.val < x (u.val+1)) ∧
      (∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val) ∧
      (∀i∈J,∀t∈J,unit i=unit t ↔
        wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps i)=
          wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps t)) ∧
      MonotoneOn unit (J:Set (Fin (steps.length+1))) := by
  dsimp only at hJ ⊢
  let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps clock 0 as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered clock as
    (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound D
      (fun d hd => (comparisonWholeCapBinEndpointMasses_bound hc hk hkc hm hM α U F S bins w d hd).2)) m)
  exact selectedWholeUnitBin_restricted_exists_coordinates steps ho (physicalCellMassMidpoint steps)
    (physicalCellMassMidpoint_monotone steps ho) _ _ _ 0 1 bins w j _ hJ

theorem comparisonWholeCapBin_restricted_cap_unit_mass {ι V : Type}
    [Fintype V] [DecidableEq V]
    (clock : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) {U : Set ℝ}
    (hopen:IsOpen U) (hU:U⊆Ioo (0:ℝ) 1) (F : Finset (ordConnectedSection U))
    (S : ℝ → ℝ) (m bins : ℕ) (w : ℝ) (j : ℕ)
    {r : ordConnectedSection U} (hr:r∈F) :
    let q := comparisonSweepQuantile hc hk hkc hm hM α
    let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    let J := (comparisonWholeCapBinOriginalBin hc hk hkc hm hM clock α U
      (hU.trans Ioo_subset_Icc_self) F S m bins w j)\fixedEndpointRows clock as D
    let a := α.val.val (sInf (ordConnectedComponent U r.val))
    let b := α.val.val (sSup (ordConnectedComponent U r.val))
    ∀(unit:Fin (steps.length+1)→V),
      (∀i∈J,∀t∈J,unit i=unit t ↔
        wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps i)=
          wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps t)) →
      ∀i∈J,physicalCellMassMidpoint steps i∈Ioo a b →
        physicalSelectedUnitMass steps J unit (unit i)=
          (wholeCapRadiusMass q (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real
            (ordConnectedComponent U r.val)-pathMassDifferences steps 0 (finiteBoundaryClockCell clock as a) := by
  dsimp only
  let q := comparisonSweepQuantile hc hk hkc hm hM α
  let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps clock 0 as
  intro unit hclass i hi hmid
  have hUcc:=hU.trans Ioo_subset_Icc_self
  let J := selectedWholeUnitBinCells steps (physicalCellMassMidpoint steps) (q⁻¹' U)
    (comparisonWholeCapMassSelection hc hk hkc hm hM α U hUcc F) (S∘q) 0 1 bins w j
  change ∀i∈J\fixedEndpointRows clock as D,∀t∈J\fixedEndpointRows clock as D,
    unit i=unit t ↔ wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps i)=
      wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps t) at hclass
  change i∈J\fixedEndpointRows clock as D at hi
  change physicalSelectedUnitMass steps (J\fixedEndpointRows clock as D) unit (unit i)=
    (wholeCapRadiusMass q (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real
      (ordConnectedComponent U r.val)-pathMassDifferences steps 0
        (finiteBoundaryClockCell clock as (α.val.val (sInf (ordConnectedComponent U r.val))))
  dsimp only [J]
  have hrU := ordConnectedSection_subset r.property
  have heC := comparisonWholeCap_mass_component hc hk hkc hm hM α hopen hUcc hrU
  have hmC:physicalCellMassMidpoint steps i∈ordConnectedComponent (q⁻¹' U) (α.val.val r.val) := by
    rw [heC]
    exact hmid
  have hmassSub := (comparisonSweepQuantile_preimage_open_subset hc hk hkc hm hM α hU).trans
    Ioo_subset_Icc_self
  rw [selectedWholeUnitBin_restricted_cap_unit_mass steps (physicalCellMassMidpoint steps)
    hmassSub _ (S∘q) bins w j (fixedEndpointRows clock as D) unit hclass hi
    (ordConnectedComponent_subset hmC)]
  rw [←ordConnectedComponent_eq hmC,heC]
  simpa only [completeMassCapCells,q,D,as,steps] using
    comparisonWholeCapBin_grid_mass_after_discard hc hk hkc hm hM clock α hopen hU F S m bins w hr

end

end OAI.SKFluctuations.WholeUnitSideKernel
