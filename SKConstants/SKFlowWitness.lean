module

public import SKConstants.SKFlowReduction
public import SKConstants.HeatBathBoundary
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical Matrix.Norms.L2Operator

namespace SKConstants

instance spinCutOptionMeasurableSpace (n : ℕ) :
    MeasurableSpace (Option (Finset (Spin n))) := ⊤

instance spinCutOptionMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (Option (Finset (Spin n))) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

@[expose] def lowFlowCut {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Spin n)) : Prop :=
  epsilon ≤ cutMass (gibbsProbability beta W) S ∧
    cutMass (gibbsProbability beta W) S ≤ 1 - epsilon ∧
    cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ ≤ B

theorem measurableSet_lowFlowCut {n : ℕ} (beta epsilon B : ℝ)
    (S : Finset (Spin n)) : MeasurableSet {W | lowFlowCut beta epsilon B W S} :=
  (measurableSet_le measurable_const
    (continuous_cutMass_gibbsProbability beta S).measurable).inter
    ((measurableSet_le (continuous_cutMass_gibbsProbability beta S).measurable
      measurable_const).inter
      (measurableSet_le (continuous_cutFlow_continuousHeatBath beta S Sᶜ).measurable
        measurable_const))

@[expose] def spinCutEnumeration (n : ℕ) :
    Fin (Fintype.card (Finset (Spin n))) ≃ Finset (Spin n) :=
  (Fintype.equivFin (Finset (Spin n))).symm

@[expose] def lowFlowCutSearch {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (j : ℕ) : Prop :=
  if hj : j < Fintype.card (Finset (Spin n)) then
    lowFlowCut beta epsilon B W (spinCutEnumeration n ⟨j, hj⟩)
  else j = Fintype.card (Finset (Spin n))

theorem lowFlowCutSearch_exists {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ∃ j, lowFlowCutSearch beta epsilon B W j :=
  ⟨Fintype.card (Finset (Spin n)), by simp [lowFlowCutSearch]⟩

@[expose] def firstLowFlowCutIndex {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  Nat.find (lowFlowCutSearch_exists beta epsilon B W)

theorem firstLowFlowCutIndex_spec {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    lowFlowCutSearch beta epsilon B W (firstLowFlowCutIndex beta epsilon B W) :=
  Nat.find_spec (lowFlowCutSearch_exists beta epsilon B W)

theorem firstLowFlowCutIndex_le {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (j : ℕ) (hj : lowFlowCutSearch beta epsilon B W j) :
    firstLowFlowCutIndex beta epsilon B W ≤ j :=
  Nat.find_min' (lowFlowCutSearch_exists beta epsilon B W) hj

theorem measurable_firstLowFlowCutIndex {n : ℕ} (beta epsilon B : ℝ) :
    Measurable (firstLowFlowCutIndex (n := n) beta epsilon B) := by
  apply measurable_find
  intro j
  by_cases hj : j < Fintype.card (Finset (Spin n))
  · simpa only [lowFlowCutSearch, dite_eq_left hj] using
      measurableSet_lowFlowCut beta epsilon B (spinCutEnumeration n ⟨j, hj⟩)
  · simp only [lowFlowCutSearch, dite_eq_right hj]
    by_cases h : j = Fintype.card (Finset (Spin n)) <;> simp [h]

@[expose] def decodeSpinCutIndex (n j : ℕ) : Option (Finset (Spin n)) :=
  if hj : j < Fintype.card (Finset (Spin n)) then
    some (spinCutEnumeration n ⟨j, hj⟩) else none

@[expose] def selectedLowFlowCut {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : Option (Finset (Spin n)) :=
  decodeSpinCutIndex n (firstLowFlowCutIndex beta epsilon B W)

theorem measurable_selectedLowFlowCut {n : ℕ} (beta epsilon B : ℝ) :
    Measurable (selectedLowFlowCut (n := n) beta epsilon B) :=
  (measurable_of_countable (decodeSpinCutIndex n)).comp
    (measurable_firstLowFlowCutIndex beta epsilon B)

theorem selectedLowFlowCut_some_spec {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Spin n))
    (hS : selectedLowFlowCut beta epsilon B W = some S) : lowFlowCut beta epsilon B W S := by
  unfold selectedLowFlowCut decodeSpinCutIndex at hS
  split_ifs at hS with hj
  · have hs := firstLowFlowCutIndex_spec beta epsilon B W
    simp only [lowFlowCutSearch, dite_eq_left hj] at hs
    exact (Option.some.inj hS) ▸ hs

theorem selectedLowFlowCut_none_iff {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    selectedLowFlowCut beta epsilon B W = none ↔ W ∈ flowGood beta epsilon B := by
  constructor
  · intro hnone S hmass hmassupper
    by_contra hflow
    let j := (spinCutEnumeration n).symm S
    have hj : lowFlowCutSearch beta epsilon B W j.val := by
      simp only [lowFlowCutSearch, dite_eq_left j.isLt]
      change lowFlowCut beta epsilon B W ((spinCutEnumeration n) ((spinCutEnumeration n).symm S))
      rw [Equiv.apply_symm_apply]
      exact ⟨hmass, hmassupper, le_of_not_gt hflow⟩
    have hlt : firstLowFlowCutIndex beta epsilon B W < Fintype.card (Finset (Spin n)) :=
      (firstLowFlowCutIndex_le beta epsilon B W j.val hj).trans_lt j.isLt
    simp only [selectedLowFlowCut, decodeSpinCutIndex, dite_eq_left hlt] at hnone
    contradiction
  · intro hgood
    unfold selectedLowFlowCut decodeSpinCutIndex
    split_ifs with hj
    · have hcut := firstLowFlowCutIndex_spec beta epsilon B W
      simp only [lowFlowCutSearch, dite_eq_left hj] at hcut
      exact False.elim ((hgood _ hcut.1 hcut.2.1).not_ge hcut.2.2)
    · rfl

theorem selectedLowFlowCut_first {n : ℕ} (beta epsilon B : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (S U : Finset (Spin n))
    (hS : selectedLowFlowCut beta epsilon B W = some S)
    (hU : lowFlowCut beta epsilon B W U) :
    ((spinCutEnumeration n).symm S).val ≤ ((spinCutEnumeration n).symm U).val := by
  let j := (spinCutEnumeration n).symm U
  have hj : lowFlowCutSearch beta epsilon B W j.val := by
    simp only [lowFlowCutSearch, dite_eq_left j.isLt]
    change lowFlowCut beta epsilon B W ((spinCutEnumeration n) ((spinCutEnumeration n).symm U))
    rw [Equiv.apply_symm_apply]
    exact hU
  have hle := firstLowFlowCutIndex_le beta epsilon B W j.val hj
  unfold selectedLowFlowCut decodeSpinCutIndex at hS
  split_ifs at hS with hs
  · have hdecode := Option.some.inj hS
    have heq : ((spinCutEnumeration n).symm S).val = firstLowFlowCutIndex beta epsilon B W := by
      rw [← hdecode, Equiv.symm_apply_apply]
    simpa only [heq] using hle

@[expose] def selectedLowFlowCutWithinNorm {n : ℕ} (beta epsilon B C : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : Option (Finset (Spin n)) :=
  if ‖W‖ ≤ C then selectedLowFlowCut beta epsilon B W else none

theorem measurable_selectedLowFlowCutWithinNorm {n : ℕ} (beta epsilon B C : ℝ) :
    Measurable (selectedLowFlowCutWithinNorm (n := n) beta epsilon B C) :=
  Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const)
    (measurable_selectedLowFlowCut beta epsilon B) measurable_const

@[expose] def selectedEnlargedBoundary {n : ℕ} (beta epsilon B C : ℝ) (r : ℕ)
    (W : Matrix (Fin n) (Fin n) ℝ) : Finset (Spin n) :=
  (selectedLowFlowCutWithinNorm beta epsilon B C W).elim ∅
    (fun S ↦ spinHammingEnlargement (spinBoundary S) r)

theorem measurable_selectedEnlargedBoundary {n : ℕ} (beta epsilon B C : ℝ) (r : ℕ) :
    Measurable (selectedEnlargedBoundary (n := n) beta epsilon B C r) :=
  (measurable_of_finite (fun o : Option (Finset (Spin n)) ↦
    o.elim ∅ (fun S ↦ spinHammingEnlargement (spinBoundary S) r))).comp
    (measurable_selectedLowFlowCutWithinNorm beta epsilon B C)

theorem selectedEnlargedBoundary_witness {n : ℕ} (beta epsilon B C : ℝ) (r : ℕ)
    (W : Matrix (Fin n) (Fin n) ℝ) (hnorm : ‖W‖ ≤ C)
    (hflow : W ∉ flowGood beta epsilon B) :
    ∃ S : Finset (Spin n), selectedLowFlowCutWithinNorm beta epsilon B C W = some S ∧
      lowFlowCut beta epsilon B W S ∧
      selectedEnlargedBoundary beta epsilon B C r W =
        spinHammingEnlargement (spinBoundary S) r := by
  cases hS : selectedLowFlowCut beta epsilon B W with
  | none => exact False.elim (hflow ((selectedLowFlowCut_none_iff beta epsilon B W).mp hS))
  | some S =>
    have hsel : selectedLowFlowCutWithinNorm beta epsilon B C W = some S := by
      simp only [selectedLowFlowCutWithinNorm, ite_eq_left hnorm, hS]
    refine ⟨S, hsel, selectedLowFlowCut_some_spec beta epsilon B W S hS, ?_⟩
    simp only [selectedEnlargedBoundary, hsel, Option.elim_some]

theorem selectedEnlargedBoundary_empty_of_flowGood {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hflow : W ∈ flowGood beta epsilon B) :
    selectedEnlargedBoundary beta epsilon B C r W = ∅ := by
  have hnone := (selectedLowFlowCut_none_iff beta epsilon B W).mpr hflow
  unfold selectedEnlargedBoundary selectedLowFlowCutWithinNorm
  split_ifs <;> simp [hnone]

theorem selectedEnlargedBoundary_empty_of_norm_failure {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hnorm : C < ‖W‖) : selectedEnlargedBoundary beta epsilon B C r W = ∅ := by
  simp only [selectedEnlargedBoundary, selectedLowFlowCutWithinNorm,
    ite_eq_right (not_le.mpr hnorm), Option.elim_none]

theorem measurableSet_selectedEnlargedBoundary_mem {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) :
    MeasurableSet {z : Matrix (Fin n) (Fin n) ℝ × Spin n |
      z.2 ∈ selectedEnlargedBoundary beta epsilon B C r z.1} := by
  have heq : {z : Matrix (Fin n) (Fin n) ℝ × Spin n |
      z.2 ∈ selectedEnlargedBoundary beta epsilon B C r z.1} =
      ⋃ x : Spin n, {z | z.2 = x} ∩ {z | x ∈ selectedEnlargedBoundary beta epsilon B C r z.1} := by
    ext z
    simp
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  have hx : MeasurableSet {W : Matrix (Fin n) (Fin n) ℝ |
      x ∈ selectedEnlargedBoundary beta epsilon B C r W} :=
    (measurable_selectedEnlargedBoundary beta epsilon B C r) (measurableSet_mem_finset x)
  exact (measurableSet_eq_fun measurable_snd measurable_const).inter (hx.preimage measurable_fst)

@[expose] def lowFlowWitnessEvent {n : ℕ} (beta epsilon B C : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  (flowGood beta epsilon B)ᶜ ∩ {W | ‖W‖ ≤ C}

theorem measurableSet_lowFlowWitnessEvent {n : ℕ} (beta epsilon B C : ℝ) :
    MeasurableSet (lowFlowWitnessEvent (n := n) beta epsilon B C) :=
  (measurableSet_flowGood beta epsilon B).compl.inter
    (measurableSet_le continuous_norm.measurable measurable_const)

theorem lowFlowWitnessEvent_iff_selected {n : ℕ} (beta epsilon B C : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    W ∈ lowFlowWitnessEvent beta epsilon B C ↔
      ∃ S, selectedLowFlowCutWithinNorm beta epsilon B C W = some S := by
  constructor
  · intro hW
    obtain ⟨S, hs, _, _⟩ := selectedEnlargedBoundary_witness beta epsilon B C 0 W hW.2 hW.1
    exact ⟨S, hs⟩
  · rintro ⟨S, hs⟩
    unfold selectedLowFlowCutWithinNorm at hs
    split_ifs at hs with hn
    have hflow : W ∉ flowGood beta epsilon B := by
      intro hgood
      rw [(selectedLowFlowCut_none_iff beta epsilon B W).mpr hgood] at hs
      contradiction
    exact ⟨hflow, hn⟩

@[expose] def selectedBoundaryMassBound (n : ℕ) (beta B C : ℝ) (r : ℕ) : ℝ :=
  4 * (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) * B *
    Real.exp (2 * |beta| * Real.sqrt (n : ℝ) * C * (Real.sqrt (r : ℝ) + 1))

theorem heatBath_enlarged_boundary_mass_le_uniform {n : ℕ} (hn : 0 < n)
    (beta B C : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Spin n)) (r : ℕ)
    (hB : 0 ≤ B) (hnorm : ‖W‖ ≤ C)
    (hflow : cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ ≤ B) :
    cutMass (gibbsProbability beta W) (spinHammingEnlargement (spinBoundary S) r) ≤
      selectedBoundaryMassBound n beta B C r := by
  let Q := cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ
  have h := heatBath_enlarged_boundary_mass_le_opNorm hn beta W S r
  have hrate : 2 * Q / heatBathMinimumRate beta (2 * Real.sqrt (n : ℝ) * ‖W‖) =
      4 * Q * Real.exp (|beta| * (2 * Real.sqrt (n : ℝ) * ‖W‖)) := by
    unfold heatBathMinimumRate
    rw [neg_mul, Real.exp_neg]
    field_simp
    ring
  change cutMass (gibbsProbability beta W) (spinHammingEnlargement (spinBoundary S) r) ≤
      (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) *
        Real.exp (|beta| * (2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖)) *
          (2 * Q / heatBathMinimumRate beta (2 * Real.sqrt (n : ℝ) * ‖W‖)) at h
  rw [hrate] at h
  have heq : (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) *
        Real.exp (|beta| * (2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖)) *
        (4 * Q * Real.exp (|beta| * (2 * Real.sqrt (n : ℝ) * ‖W‖))) =
      4 * (((r + 1) * (n + 1) ^ r : ℕ) : ℝ) * Q *
        Real.exp (2 * |beta| * Real.sqrt (n : ℝ) * ‖W‖ * (Real.sqrt (r : ℝ) + 1)) := by
    rw [show 2 * |beta| * Real.sqrt (n : ℝ) * ‖W‖ * (Real.sqrt (r : ℝ) + 1) =
      |beta| * (2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖) +
      |beta| * (2 * Real.sqrt (n : ℝ) * ‖W‖) by ring, Real.exp_add]
    ring
  rw [heq] at h
  apply h.trans
  unfold selectedBoundaryMassBound
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hflow (by positivity)
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (by positivity)) (by positivity)
  · positivity
  · positivity

theorem selectedEnlargedBoundary_mass_le {n : ℕ} (hn : 0 < n)
    (beta epsilon B C : ℝ) (r : ℕ) (W : Matrix (Fin n) (Fin n) ℝ) (hB : 0 ≤ B) :
    cutMass (gibbsProbability beta W) (selectedEnlargedBoundary beta epsilon B C r W) ≤
      selectedBoundaryMassBound n beta B C r := by
  by_cases hnorm : ‖W‖ ≤ C
  · cases hS : selectedLowFlowCut beta epsilon B W with
    | none =>
      have hgood := (selectedLowFlowCut_none_iff beta epsilon B W).mp hS
      rw [selectedEnlargedBoundary_empty_of_flowGood beta epsilon B C r W hgood]
      simp only [cutMass, Finset.sum_empty]
      unfold selectedBoundaryMassBound
      positivity
    | some S =>
      have hcut := selectedLowFlowCut_some_spec beta epsilon B W S hS
      have heq : selectedEnlargedBoundary beta epsilon B C r W =
          spinHammingEnlargement (spinBoundary S) r := by
        simp only [selectedEnlargedBoundary, selectedLowFlowCutWithinNorm,
          ite_eq_left hnorm, hS, Option.elim_some]
      rw [heq]
      exact heatBath_enlarged_boundary_mass_le_uniform hn beta B C W S r hB hnorm hcut.2.2
  · rw [selectedEnlargedBoundary_empty_of_norm_failure beta epsilon B C r W
      (lt_of_not_ge hnorm)]
    simp only [cutMass, Finset.sum_empty]
    unfold selectedBoundaryMassBound
    positivity

theorem measurable_cutMass_selectedEnlargedBoundary {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) :
    Measurable (fun W : Matrix (Fin n) (Fin n) ℝ ↦
      cutMass (gibbsProbability beta W) (selectedEnlargedBoundary beta epsilon B C r W)) := by
  have heq : (fun W : Matrix (Fin n) (Fin n) ℝ ↦
      cutMass (gibbsProbability beta W) (selectedEnlargedBoundary beta epsilon B C r W)) =
      (fun W ↦ ∑ x : Spin n, if x ∈ selectedEnlargedBoundary beta epsilon B C r W then
        gibbsProbability beta W x else 0) := by
    funext W
    simp [cutMass]
  rw [heq]
  apply Finset.measurable_sum
  intro x _
  exact Measurable.ite
    ((measurable_selectedEnlargedBoundary beta epsilon B C r) (measurableSet_mem_finset x))
    (continuous_gibbsProbability beta x).measurable measurable_const

theorem jointGibbs_selectedEnlargedBoundary_probability_le {n : ℕ} (hn : 0 < n)
    (beta epsilon B C : ℝ) (r : ℕ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ] (hB : 0 ≤ B) :
    (jointGibbsMeasure beta μ).real {z |
      z.2 ∈ selectedEnlargedBoundary beta epsilon B C r z.1} ≤
      selectedBoundaryMassBound n beta B C r := by
  let E : Set (Matrix (Fin n) (Fin n) ℝ × Spin n) :=
    {z | z.2 ∈ selectedEnlargedBoundary beta epsilon B C r z.1}
  have hE : MeasurableSet E := measurableSet_selectedEnlargedBoundary_mem beta epsilon B C r
  have hf : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) (jointGibbsMeasure beta μ) :=
    (integrable_const 1).indicator hE
  calc
    _ = ∫ z, E.indicator (fun _ ↦ (1 : ℝ)) z ∂jointGibbsMeasure beta μ :=
      (integral_indicator_one hE).symm
    _ = ∫ W, cutMass (gibbsProbability beta W)
        (selectedEnlargedBoundary beta epsilon B C r W) ∂μ := by
      rw [jointGibbsMeasure, Measure.integral_compProd hf]
      congr 1
      funext W
      rw [integral_gibbsKernel]
      simp [E, Set.indicator_apply, cutMass]
    _ ≤ ∫ _, selectedBoundaryMassBound n beta B C r ∂μ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun W ↦
          cutMass_nonneg _ _ (fun x ↦ (gibbsProbability_pos beta W x).le))
      · exact integrable_const _
      · exact Filter.Eventually.of_forall (fun W ↦ selectedEnlargedBoundary_mass_le hn
          beta epsilon B C r W hB)
    _ = _ := by simp

theorem flow_failure_probability_le_witness_and_norm {n : ℕ}
    (beta epsilon B C : ℝ) (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ] :
    μ.real (flowGood beta epsilon B)ᶜ ≤
      μ.real (lowFlowWitnessEvent beta epsilon B C) + μ.real {W | C < ‖W‖} := by
  calc
    _ ≤ μ.real (lowFlowWitnessEvent beta epsilon B C ∪ {W | C < ‖W‖}) := by
      apply measureReal_mono ?_ (measure_ne_top μ _)
      intro W hW
      by_cases hn : ‖W‖ ≤ C
      · exact Or.inl ⟨hW, hn⟩
      · exact Or.inr (lt_of_not_ge hn)
    _ ≤ _ := measureReal_union_le _ _

theorem selectedEnlargedBoundary_mass_under_perturbation_le {n : ℕ} (hn : 0 < n)
    (beta epsilon B C L : ℝ) (r : ℕ)
    (W V : Matrix (Fin n) (Fin n) ℝ) (hB : 0 ≤ B)
    (henergy : ∀ x, |quadraticHamiltonian V x - quadraticHamiltonian W x| ≤ L) :
    cutMass (gibbsProbability beta V) (selectedEnlargedBoundary beta epsilon B C r W) ≤
      Real.exp (2 * |beta| * L) * selectedBoundaryMassBound n beta B C r := by
  calc
    _ ≤ ∑ x ∈ selectedEnlargedBoundary beta epsilon B C r W,
        Real.exp (2 * |beta| * L) * gibbsProbability beta W x := by
      exact Finset.sum_le_sum (fun x _ ↦ gibbsProbability_comparison beta L V W henergy x)
    _ = Real.exp (2 * |beta| * L) *
        cutMass (gibbsProbability beta W) (selectedEnlargedBoundary beta epsilon B C r W) := by
      rw [cutMass, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (selectedEnlargedBoundary_mass_le hn
      beta epsilon B C r W hB) (Real.exp_pos _).le

theorem sk_flow_failure_decay_of_witness_and_norm (beta q d : ℝ) (C : ℕ → ℝ)
    (hwitness : Filter.Tendsto (fun n : ℕ ↦ (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-d))
        (Real.exp (-((n : ℝ) ^ (1 - q)))) (C n))) Filter.atTop (nhds 0))
    (hnorm : Filter.Tendsto (fun n : ℕ ↦ (skDisorderLaw n).real
      {W | C n < ‖W‖}) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ ↦ (skDisorderLaw n).real
      (flowGood beta ((n : ℝ) ^ (-d)) (Real.exp (-((n : ℝ) ^ (1 - q)))))ᶜ)
      Filter.atTop (nhds 0) := by
  have hlim := hwitness.add hnorm
  simp only [zero_add] at hlim
  exact squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun n ↦ flow_failure_probability_le_witness_and_norm beta _ _ (C n) (skDisorderLaw n)) hlim

theorem sk_joint_bad_start_decay_of_witness_and_norm (beta c q d delta : ℝ)
    (C : ℕ → ℝ) (hcq : c < q) (hq : q < 1) (hd : 0 < d) (hdelta : 0 < delta)
    (hwitness : Filter.Tendsto (fun n : ℕ ↦ (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-d))
        (Real.exp (-((n : ℝ) ^ (1 - q)))) (C n))) Filter.atTop (nhds 0))
    (hnorm : Filter.Tendsto (fun n : ℕ ↦ (skDisorderLaw n).real
      {W | C n < ‖W‖}) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ ↦ (skJointLaw n beta).real
      {z | delta < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) Filter.atTop (nhds 0) :=
  sk_joint_bad_start_decay_of_flow_decay beta c q d delta hcq hq hd hdelta
    (sk_flow_failure_decay_of_witness_and_norm beta q d C hwitness hnorm)

theorem probability_selectedLowFlowCut_coarse_avoidance_bad_mass {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (beta epsilon B C : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : W ∈ lowFlowWitnessEvent beta epsilon B C)
    (q : Spin n → ℝ) (f : Ω → ℕ → Spin n)
    (coarse : Ω → ℕ → Prop) (good : Set Ω) (N r : ℕ) (K : ℝ)
    (hepsilon : 0 < epsilon) (hq : ∀ x, 0 < q x) (hqsum : ∑ x, q x = 1)
    (hKL : finiteKL (gibbsProbability beta W) q ≤ K)
    (hX : Measurable (fun ω ↦ f ω 0)) (hY : Measurable (fun ω ↦ f ω N))
    (hind : IndepFun (fun ω ↦ f ω 0) (fun ω ↦ f ω N) μ)
    (hXmarg : ∀ x, μ.real {ω | f ω 0 = x} = q x)
    (hYmarg : ∀ x, μ.real {ω | f ω N = x} = q x)
    (hgood : MeasurableSet good)
    (hsteps : ∀ ω ∈ good, ∀ i < N, hammingDist (f ω i) (f ω (i + 1)) ≤ r)
    (hcoarse : ∀ ω ∈ good, ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω ∈ good, ∀ i ≤ N, coarse ω i →
      f ω i ∉ selectedEnlargedBoundary beta epsilon B C r W) :
    Real.exp (-2 * (K + Real.log 2) / epsilon) ≤ μ.real goodᶜ ∧
      μ.real good ≤ 1 - Real.exp (-2 * (K + Real.log 2) / epsilon) := by
  obtain ⟨S, _, hcut, hD⟩ := selectedEnlargedBoundary_witness beta epsilon B C r W hW.2 hW.1
  have hSc : epsilon ≤ cutMass (gibbsProbability beta W) Sᶜ := by
    rw [cutMass_compl _ S (gibbsProbability_sum beta W)]
    linarith [hcut.2.1]
  exact probability_spinGibbs_balanced_coarse_avoidance_bad_mass μ beta W q S
    f coarse good N r K epsilon hq hqsum hKL hepsilon hcut.1 hSc hX hY hind
    hXmarg hYmarg hgood hsteps hcoarse
    (fun ω hω i hi hc ↦ by simpa only [hD] using havoid ω hω i hi hc)

end SKConstants
