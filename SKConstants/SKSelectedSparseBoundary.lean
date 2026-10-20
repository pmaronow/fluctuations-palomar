module

public import SKConstants.SKSparseBoundaryRate
public import SKConstants.SKFlowWitness
public import SKConstants.OptimizedRate

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators Classical Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def selectedSparseBoundary {n : ℕ} (beta epsilon B C : ℝ) (r : ℕ) (A : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : Finset (Spin n) :=
  (selectedLowFlowCutWithinNorm beta epsilon B C
    (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z)).elim ∅
    (fun S => sparseFieldExcludedSet S r A z)

theorem measurableSet_selectedSparseBoundary_mem {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) (A : ℝ) (x : Spin n) :
    MeasurableSet {z | x ∈ selectedSparseBoundary beta epsilon B C r A z} := by
  let sel := fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
    selectedLowFlowCutWithinNorm beta epsilon B C
      (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z)
  have hs : Measurable sel := (measurable_selectedLowFlowCutWithinNorm beta epsilon B C).comp
    (continuous_goeMatrix _).measurable
  have he : {z | x ∈ selectedSparseBoundary beta epsilon B C r A z} =
      ⋃ S : Finset (Spin n), {z | sel z = some S} ∩
        {z | x ∈ spinHammingEnlargement (spinBoundary S) r ∨ z ∈ sparseFieldBadSet x r A} := by
    ext z
    change (x ∈ (sel z).elim ∅ (fun S => sparseFieldExcludedSet S r A z)) ↔ _
    cases h : sel z <;> simp [h, sparseFieldExcludedSet]
  rw [he]
  apply MeasurableSet.iUnion
  intro S
  apply (hs (measurableSet_singleton (some S))).inter
  by_cases hx : x ∈ spinHammingEnlargement (spinBoundary S) r
  · simp only [hx, true_or]
    exact MeasurableSet.univ
  · simpa [hx] using measurableSet_sparseFieldBadSet x r A

theorem selectedSparseBoundary_gibbs_mass_le {n r : ℕ} (hn : 0 < n)
    (beta epsilon B C A : ℝ) (hB : 0 ≤ B)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    cutMass (gibbsProbability beta (GaussianProposal.goeMatrix
      (1 / Real.sqrt (2 * (n : ℝ))) z)) (selectedSparseBoundary beta epsilon B C r A z) ≤
      sparseBoundaryMassBound n beta B C r A +
      cutMass (gibbsProbability beta (GaussianProposal.goeMatrix
        (1 / Real.sqrt (2 * (n : ℝ))) z))
        (Finset.univ.filter (fun x => z ∈ sparseFieldBadSet x r A)) := by
  let W := GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z
  cases hs : selectedLowFlowCutWithinNorm beta epsilon B C W with
  | none =>
    simp only [selectedSparseBoundary, show GaussianProposal.goeMatrix
      (1 / Real.sqrt (2 * (n : ℝ))) z = W from rfl, hs, Option.elim_none,
      cutMass, Finset.sum_empty]
    exact add_nonneg (by unfold sparseBoundaryMassBound; positivity)
      (Finset.sum_nonneg (fun x _ => (gibbsProbability_pos beta W x).le))
  | some S =>
    have hnrm : ‖W‖ ≤ C := by
      by_contra h
      simp only [selectedLowFlowCutWithinNorm, ite_eq_right h] at hs
      contradiction
    have hsel : selectedLowFlowCut beta epsilon B W = some S := by
      simpa only [selectedLowFlowCutWithinNorm, ite_eq_left hnrm] using hs
    have hcut := selectedLowFlowCut_some_spec beta epsilon B W S hsel
    simpa only [selectedSparseBoundary, show GaussianProposal.goeMatrix
      (1 / Real.sqrt (2 * (n : ℝ))) z = W from rfl, hs, Option.elim_some] using
      sparseFieldExcludedSet_gibbs_mass_le_uniform hn beta B C A hB S z hnrm hcut.2.2

theorem measurable_primitive_gibbs_cutMass {n : ℕ} (beta sigma : ℝ)
    (D : EuclideanSpace ℝ (Fin n × Fin n) → Finset (Spin n))
    (hD : ∀ x, MeasurableSet {z | x ∈ D z}) :
    Measurable (fun z => cutMass (gibbsProbability beta (GaussianProposal.goeMatrix sigma z)) (D z)) := by
  have he : (fun z => cutMass (gibbsProbability beta (GaussianProposal.goeMatrix sigma z)) (D z)) =
      fun z => ∑ x : Spin n, if x ∈ D z then
        gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x else 0 := by
    funext z
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp
  rw [he]
  exact Finset.measurable_sum _ (fun x _ => Measurable.ite (hD x)
    ((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).measurable measurable_const)

theorem integrable_primitive_gibbs_cutMass {n : ℕ} (beta sigma : ℝ)
    (D : EuclideanSpace ℝ (Fin n × Fin n) → Finset (Spin n))
    (hD : ∀ x, MeasurableSet {z | x ∈ D z}) :
    Integrable (fun z => cutMass (gibbsProbability beta (GaussianProposal.goeMatrix sigma z)) (D z))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_primitive_gibbs_cutMass beta sigma D hD).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (cutMass_nonneg _ _
      (fun x => (gibbsProbability_pos beta _ x).le))]
    exact cutMass_le_one _ (D z) (fun x => (gibbsProbability_pos beta _ x).le)
      (gibbsProbability_sum beta _))

theorem primitiveJointGibbs_probability_eq_integral_cutMass {n : ℕ} (beta sigma : ℝ)
    (D : EuclideanSpace ℝ (Fin n × Fin n) → Finset (Spin n))
    (hD : ∀ x, MeasurableSet {z | x ∈ D z}) :
    (primitiveJointGibbsLaw n beta sigma).real {p | p.2 ∈ D p.1} =
      ∫ z, cutMass (gibbsProbability beta (GaussianProposal.goeMatrix sigma z)) (D z)
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
  let E : Set (EuclideanSpace ℝ (Fin n × Fin n) × Spin n) := {p | p.2 ∈ D p.1}
  have hE : MeasurableSet E := measurableSet_spin_dependent_event
    (fun x => {z | x ∈ D z}) hD
  have hf := (integrable_const (1 : ℝ) (μ := primitiveJointGibbsLaw n beta sigma)).indicator hE
  rw [← integral_indicator_one hE]
  change (∫ p, E.indicator (fun _ => (1 : ℝ)) p ∂primitiveJointGibbsLaw n beta sigma) = _
  rw [primitiveJointGibbsLaw, Measure.integral_compProd hf]
  congr 1
  funext z
  simp only [Kernel.comap_apply]
  rw [integral_gibbsKernel]
  simp [E, Set.indicator_apply, cutMass]

theorem primitiveJointGibbs_selectedSparseBoundary_probability_le {n r : ℕ} (hn : 0 < n)
    (beta epsilon B C A : ℝ) (hB : 0 ≤ B) :
    (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).real
      {p | p.2 ∈ selectedSparseBoundary beta epsilon B C r A p.1} ≤
      sparseBoundaryMassBound n beta B C r A +
      (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).real
        (annealedSparseFieldBadSet n r A) := by
  let sig : ℝ := 1 / Real.sqrt (2 * (n : ℝ))
  let Bad := fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
    Finset.univ.filter (fun x : Spin n => z ∈ sparseFieldBadSet x r A)
  have hBad : ∀ x, MeasurableSet {z | x ∈ Bad z} := by
    intro x
    simpa [Bad] using
      measurableSet_sparseFieldBadSet x r A
  rw [primitiveJointGibbs_probability_eq_integral_cutMass beta sig _
    (measurableSet_selectedSparseBoundary_mem beta epsilon B C r A)]
  have hi := integral_mono
    (integrable_primitive_gibbs_cutMass beta sig _
      (measurableSet_selectedSparseBoundary_mem beta epsilon B C r A))
    ((integrable_const (sparseBoundaryMassBound n beta B C r A)).add
      (integrable_primitive_gibbs_cutMass beta sig Bad hBad))
    (fun z => selectedSparseBoundary_gibbs_mass_le hn beta epsilon B C A hB z)
  apply hi.trans_eq
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) (integrable_primitive_gibbs_cutMass beta sig Bad hBad)]
  simp only [integral_const, probReal_univ, one_smul]
  rw [← primitiveJointGibbs_probability_eq_integral_cutMass beta sig Bad hBad]
  congr 1
  congr 1
  ext p
  simp [Bad, annealedSparseFieldBadSet]

theorem primitiveJointGibbs_selectedSparseBoundary_stretched_tail
    (beta epsilon rho u q s : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hu : u < rho) (hqu : q < u) (hqhalf : q < 1 / 2) (hqs : q < s)
    (hfieldRate : 2 * u - rho < s) :
    ∀ᶠ n : ℕ in atTop,
      (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).real
        {p | p.2 ∈ selectedSparseBoundary beta epsilon
          (Real.exp (-(n : ℝ)^(1 - q))) 12 (sparseFieldRadius rho n)
          ((n : ℝ)^(1 - u)) p.1} ≤ 2 * Real.exp (-(n : ℝ)^(1 - s)) := by
  have hfield := primitiveJointGibbs_sparseFieldBadSet_stretched_tail beta rho u s
    hrho hrho1 hu hfieldRate
  have hboundary := sparseBoundaryMassBound_stretched_decay beta rho u q s
    hrho hrho1 hu hqu hqhalf hqs
  filter_upwards [hfield, hboundary, eventually_ge_atTop (1 : ℕ)]
    with n hf hb hn
  have hi := primitiveJointGibbs_selectedSparseBoundary_probability_le (r := sparseFieldRadius rho n)
    (show 0 < n by omega) beta epsilon (Real.exp (-(n : ℝ)^(1 - q))) 12
      ((n : ℝ)^(1 - u)) (Real.exp_pos _).le
  linarith

theorem primitiveJointGibbs_optimized_selectedSparseBoundary_stretched_tail
    (beta c : ℝ) (hc : 0 < c) (hquarter : c < 1 / 4) :
    let p := optimizedParameters c
    let s := (p.q + p.e) / 2
    ∀ᶠ n : ℕ in atTop,
      (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).real
        {z | z.2 ∈ selectedSparseBoundary beta ((n : ℝ)^(-p.d))
          (Real.exp (-(n : ℝ)^(1 - p.q))) 12 (sparseFieldRadius p.r n)
          ((n : ℝ)^(1 - p.uField)) z.1} ≤ 2 * Real.exp (-(n : ℝ)^(1 - s)) := by
  let p := optimizedParameters c
  have hp := optimizedParameters_feasible c hc hquarter
  change Feasible c p at hp
  unfold Feasible at hp
  have hr : 0 < p.r := by tauto
  have hu : p.uField < p.r := by tauto
  have hqu : p.q < p.uField := by tauto
  have hqhalf : p.q < 1 / 2 := by tauto
  have hqe : p.q < p.e := by tauto
  have huf : 2 * p.uField - p.r < p.sField := by tauto
  have hfq : p.sField < p.q := by tauto
  have hx : 0 < p.a ∧ p.a + p.f / 2 < 1 ∧ p.b < p.f ∧ p.r < p.b / 2 := by tauto
  have hr1 : p.r < 1 := by rcases hx with ⟨ha, haf, hbf, hrb⟩; linarith
  have hfield := primitiveJointGibbs_sparseFieldBadSet_stretched_tail beta p.r p.uField
    ((p.q + p.e) / 2) hr hr1 hu (by linarith)
  have hboundary := sparseBoundaryMassBound_stretched_decay beta p.r p.uField p.q
    ((p.q + p.e) / 2) hr hr1 hu hqu hqhalf (by linarith)
  filter_upwards [hfield, hboundary, eventually_ge_atTop (1 : ℕ)] with n hf hb hn
  have hi := primitiveJointGibbs_selectedSparseBoundary_probability_le (r := sparseFieldRadius p.r n)
    (show 0 < n by omega) beta ((n : ℝ)^(-p.d)) (Real.exp (-(n : ℝ)^(1 - p.q))) 12
      ((n : ℝ)^(1 - p.uField)) (Real.exp_pos _).le
  linarith

end SKConstants
