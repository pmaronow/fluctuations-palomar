module

public import SKConstants.GaussianHamiltonian
public import SKConstants.GaussianPressureConcentration
public import SKConstants.SKSelectedSparseBoundary
public import SKConstants.ConditionalGibbsDisintegration
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem goeSpinHamiltonian_affine {n : ℕ} (sigma c s : ℝ) (x : Spin n)
    (G Z : EuclideanSpace ℝ (Fin n × Fin n)) :
    goeSpinHamiltonian sigma x (c • G+s • Z) =
      c*goeSpinHamiltonian sigma x G+s*goeSpinHamiltonian sigma x Z := by
  have hlin : GaussianProposal.goeBilinear sigma (signedSpin x) (signedSpin x) (c • G+s • Z) =
      c*GaussianProposal.goeBilinear sigma (signedSpin x) (signedSpin x) G +
      s*GaussianProposal.goeBilinear sigma (signedSpin x) (signedSpin x) Z := by
    unfold GaussianProposal.goeBilinear
    simp only [←GaussianProposal.linearFormCLM_apply, map_add, map_smul, smul_eq_mul]
  simp only [goeSpinHamiltonian_eq_half_bilinear]
  rw [hlin]
  ring

theorem sk_seed_hamiltonian_exponential_moment {n : ℕ} (hn : 0<n)
    (x : Spin n) (theta : ℝ) :
    (∫ Z, Real.exp (theta*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x Z)
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) =
      Real.exp (theta^2*(n : ℝ)/4) := by
  have hG := goeSpinHamiltonian_gaussian (1/Real.sqrt (2*(n : ℝ))) x
  have hLaw : HasLaw (goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x)
      (gaussianReal 0 ((n : ℝ)/2).toNNReal)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
    refine ⟨hG.aemeasurable,?_⟩
    simpa only [goeSpinHamiltonian_mean,sk_seed_hamiltonian_variance hn x] using hG.map_eq_gaussianReal
  change mgf (goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x) _ theta = _
  rw [mgf_gaussianReal hLaw, Real.toNNReal_of_nonneg (by positivity)]
  simp only [NNReal.coe_mk, zero_mul, zero_add]
  congr 1
  ring

theorem sk_seed_hamiltonian_affine_exponential_moment {n : ℕ} (hn : 0<n)
    (beta c s : ℝ) (x : Spin n) (G : EuclideanSpace ℝ (Fin n × Fin n)) :
    (∫ Z, Real.exp (beta*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x (c • G+s • Z))
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) =
      Real.exp (beta*c*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x G+
        beta^2*s^2*(n : ℝ)/4) := by
  have he (Z) : Real.exp (beta*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x (c • G+s • Z)) =
      Real.exp (beta*c*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x G)*
      Real.exp ((beta*s)*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x Z) := by
    rw [goeSpinHamiltonian_affine, ←Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul, sk_seed_hamiltonian_exponential_moment hn x, ←Real.exp_add]
  congr 1
  ring

theorem sk_seed_hamiltonian_exp_integrable {n : ℕ} (hn : 0<n)
    (x : Spin n) (theta : ℝ) :
    Integrable (fun Z => Real.exp (theta*goeSpinHamiltonian
      (1/Real.sqrt (2*(n : ℝ))) x Z))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  have hG := goeSpinHamiltonian_gaussian (1/Real.sqrt (2*(n : ℝ))) x
  have hLaw : HasLaw (goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x)
      (gaussianReal 0 ((n : ℝ)/2).toNNReal)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
    refine ⟨hG.aemeasurable,?_⟩
    simpa only [goeSpinHamiltonian_mean,sk_seed_hamiltonian_variance hn x] using hG.map_eq_gaussianReal
  exact hLaw.integrable_comp (integrable_exp_mul_gaussianReal theta)

theorem sk_seed_hamiltonian_affine_exp_integrable {n : ℕ} (hn : 0<n)
    (beta c s : ℝ) (x : Spin n) (G : EuclideanSpace ℝ (Fin n × Fin n)) :
    Integrable (fun Z => Real.exp (beta*goeSpinHamiltonian
      (1/Real.sqrt (2*(n : ℝ))) x (c • G+s • Z)))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  have he (Z) : Real.exp (beta*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x (c • G+s • Z)) =
      Real.exp (beta*c*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x G)*
      Real.exp ((beta*s)*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x Z) := by
    rw [goeSpinHamiltonian_affine, ←Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  exact (sk_seed_hamiltonian_exp_integrable hn x (beta*s)).const_mul _

theorem gibbs_weight_sum_eq_partition_mul_cutMass {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (D : Finset (Spin n)) :
    (∑ x ∈ D, Real.exp (beta*quadraticHamiltonian W x)) =
      gibbsPartition beta W * cutMass (gibbsProbability beta W) D := by
  unfold cutMass gibbsProbability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  field_simp [(gibbsPartition_pos beta W).ne']

theorem gaussianRegression_intrinsic_boundary_mass_le {n : ℕ} (hn : 0<n)
    (beta c s P L Perr C : ℝ) (hc : c ≤ 1)
    (q : EuclideanSpace ℝ (Fin n × Fin n) → Spin n → ℝ)
    (hq : ∀ x, Measurable (fun z => q z x))
    (hq0 : ∀ z x, 0 ≤ q z x) (hq1 : ∀ z x, q z x ≤ 1)
    (hdom : ∀ z x, q z x ≤ Real.exp (-(n : ℝ)*P+L+
      beta*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x z))
    (G : EuclideanSpace ℝ (Fin n × Fin n))
    (hNorm : ‖GaussianProposal.goeMatrix (1/Real.sqrt (2*(n : ℝ))) G‖ ≤ C)
    (hPressure : primitiveGOEPressure n beta G ≤ (n : ℝ)*P+Perr)
    (D : Finset (Spin n)) :
    (∫ Z, ∑ x ∈ D, q (c • G+s • Z) x
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤
    Real.exp (L+Perr+(1-c)*|beta| *(n : ℝ)*C/2+beta^2*s^2*(n : ℝ)/4)*
      cutMass (gibbsProbability beta (GaussianProposal.goeMatrix
        (1/Real.sqrt (2*(n : ℝ))) G)) D := by
  let gamma := GaussianProposal.primitiveGaussian (Fin n × Fin n)
  let W := GaussianProposal.goeMatrix (1/Real.sqrt (2*(n : ℝ))) G
  let normCost := (1-c)*|beta| *(n : ℝ)*C/2
  let seedCost := beta^2*s^2*(n : ℝ)/4
  have hqm (x : Spin n) : Measurable (fun Z => q (c • G+s • Z) x) :=
    (hq x).comp ((continuous_const.add (continuous_id.const_smul s)).measurable)
  have hqi (x : Spin n) : Integrable (fun Z => q (c • G+s • Z) x) gamma := by
    apply (integrable_const (1 : ℝ)).mono' (hqm x).aestronglyMeasurable
    exact ae_of_all _ (fun Z => by rw [Real.norm_eq_abs,abs_of_nonneg (hq0 _ _)]; exact hq1 _ _)
  have hpoint (x : Spin n) :
      (∫ Z, q (c • G+s • Z) x ∂gamma) ≤
      Real.exp (-(n : ℝ)*P+L+normCost+seedCost)*
        Real.exp (beta*quadraticHamiltonian W x) := by
    have hi := integral_mono (hqi x)
      ((sk_seed_hamiltonian_affine_exp_integrable hn beta c s x G).const_mul
        (Real.exp (-(n : ℝ)*P+L)))
      (fun Z => by simpa only [←Real.exp_add] using hdom (c • G+s • Z) x)
    rw [integral_const_mul,sk_seed_hamiltonian_affine_exponential_moment hn] at hi
    have hnBound : |quadraticHamiltonian W x| ≤ (n : ℝ)*C/2 :=
      (quadraticHamiltonian_opNorm_bound W x).trans (by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hNorm (Nat.cast_nonneg _))
    have hcorr : beta*c*quadraticHamiltonian W x ≤
        beta*quadraticHamiltonian W x+normCost := by
      have habs : |beta*quadraticHamiltonian W x| ≤ |beta| *((n : ℝ)*C/2) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hnBound (abs_nonneg _)
      have hl := neg_le_abs (beta*quadraticHamiltonian W x)
      have hh := mul_le_mul_of_nonneg_left (hl.trans habs) (sub_nonneg.mpr hc)
      dsimp [normCost]
      nlinarith
    apply hi.trans
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -(n : ℝ)*P+L+(beta*c*quadraticHamiltonian W x+beta^2*s^2*(n : ℝ)/4) ≤ _
    dsimp [seedCost]
    linarith
  rw [integral_finsetSum D (fun x hx => hqi x)]
  have hs : (∑ x ∈ D, ∫ Z, q (c • G+s • Z) x ∂gamma) ≤
      ∑ x ∈ D, Real.exp (-(n : ℝ)*P+L+normCost+seedCost)*
        Real.exp (beta*quadraticHamiltonian W x) :=
    Finset.sum_le_sum (fun x hx => hpoint x)
  rw [←Finset.mul_sum,gibbs_weight_sum_eq_partition_mul_cutMass] at hs
  have hpart : gibbsPartition beta W ≤ Real.exp ((n : ℝ)*P+Perr) := by
    rw [←Real.exp_log (gibbsPartition_pos beta W)]
    exact Real.exp_le_exp.mpr hPressure
  apply hs.trans
  have hmass : 0 ≤ cutMass (gibbsProbability beta W) D :=
    cutMass_nonneg _ _ (fun x => (gibbsProbability_pos beta W x).le)
  calc
    _ ≤ Real.exp (-(n : ℝ)*P+L+normCost+seedCost)*
        (Real.exp ((n : ℝ)*P+Perr)*cutMass (gibbsProbability beta W) D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpart hmass) (Real.exp_pos _).le
    _ = _ := by
      rw [←mul_assoc,←Real.exp_add]
      congr 2
      dsimp [normCost,seedCost]
      ring

def pressureSelectedSparseBoundary {n : ℕ} (beta epsilon B C : ℝ)
    (r : ℕ) (A P Perr : ℝ) (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    Finset (Spin n) :=
  if primitiveGOEPressure n beta z ≤ (n : ℝ)*P+Perr then
    selectedSparseBoundary beta epsilon B C r A z else ∅

theorem measurableSet_pressureSelectedSparseBoundary_mem {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) (A P Perr : ℝ) (x : Spin n) :
    MeasurableSet {z | x ∈ pressureSelectedSparseBoundary beta epsilon B C r A P Perr z} := by
  have hp : Measurable (primitiveGOEPressure n beta) :=
    (((continuous_gibbsPartition beta).comp (continuous_goeMatrix _)).log
      (fun z => (gibbsPartition_pos beta _).ne')).measurable
  have he : {z | x ∈ pressureSelectedSparseBoundary beta epsilon B C r A P Perr z} =
      {z | primitiveGOEPressure n beta z ≤ (n : ℝ)*P+Perr} ∩
        {z | x ∈ selectedSparseBoundary beta epsilon B C r A z} := by
    ext z
    simp only [pressureSelectedSparseBoundary,Set.mem_ofPred_eq,Set.mem_inter_iff]
    split_ifs <;> simp_all
  rw [he]
  exact (measurableSet_le hp measurable_const).inter
    (measurableSet_selectedSparseBoundary_mem beta epsilon B C r A x)

theorem pressureSelectedSparseBoundary_subset {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) (A P Perr : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    pressureSelectedSparseBoundary beta epsilon B C r A P Perr z ⊆
      selectedSparseBoundary beta epsilon B C r A z := by
  unfold pressureSelectedSparseBoundary
  split_ifs <;> simp

theorem selectedSparseBoundary_eq_empty_of_norm {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) (A : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n))
    (hNorm : ¬ ‖GaussianProposal.goeMatrix (1/Real.sqrt (2*(n : ℝ))) z‖ ≤ C) :
    selectedSparseBoundary beta epsilon B C r A z = ∅ := by
  simp only [selectedSparseBoundary,selectedLowFlowCutWithinNorm,ite_eq_right hNorm,
    Option.elim_none]

theorem gaussianRegression_intrinsic_pressureSelected_boundary_mass_le {n : ℕ} (hn : 0<n)
    (beta c s P L Perr C epsilon B : ℝ) (hc : c ≤ 1) (r : ℕ) (A : ℝ)
    (q : EuclideanSpace ℝ (Fin n × Fin n) → Spin n → ℝ)
    (hq : ∀ x, Measurable (fun z => q z x))
    (hq0 : ∀ z x, 0 ≤ q z x) (hq1 : ∀ z x, q z x ≤ 1)
    (hdom : ∀ z x, q z x ≤ Real.exp (-(n : ℝ)*P+L+
      beta*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x z))
    (G : EuclideanSpace ℝ (Fin n × Fin n)) :
    (∫ Z, ∑ x ∈ pressureSelectedSparseBoundary beta epsilon B C r A P Perr G,
      q (c • G+s • Z) x ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤
    Real.exp (L+Perr+(1-c)*|beta| *(n : ℝ)*C/2+beta^2*s^2*(n : ℝ)/4)*
      cutMass (gibbsProbability beta (GaussianProposal.goeMatrix
        (1/Real.sqrt (2*(n : ℝ))) G))
        (pressureSelectedSparseBoundary beta epsilon B C r A P Perr G) := by
  by_cases hp : primitiveGOEPressure n beta G ≤ (n : ℝ)*P+Perr
  · by_cases hnrm : ‖GaussianProposal.goeMatrix (1/Real.sqrt (2*(n : ℝ))) G‖ ≤ C
    · exact gaussianRegression_intrinsic_boundary_mass_le hn beta c s P L Perr C hc
        q hq hq0 hq1 hdom G hnrm hp _
    · simp only [pressureSelectedSparseBoundary,ite_eq_left hp,
        selectedSparseBoundary_eq_empty_of_norm beta epsilon B C r A G hnrm,
        Finset.sum_empty,integral_zero,cutMass,mul_zero,le_refl]
  · simp only [pressureSelectedSparseBoundary,ite_eq_right hp,Finset.sum_empty,
      integral_zero,cutMass,Finset.sum_empty,mul_zero,le_refl]

theorem primitiveJointGibbs_pressureSelectedSparseBoundary_probability_le {n : ℕ}
    (beta epsilon B C : ℝ) (r : ℕ) (A P Perr : ℝ) :
    (primitiveJointGibbsLaw n beta (1/Real.sqrt (2*(n : ℝ)))).real
      {p | p.2 ∈ pressureSelectedSparseBoundary beta epsilon B C r A P Perr p.1} ≤
    (primitiveJointGibbsLaw n beta (1/Real.sqrt (2*(n : ℝ)))).real
      {p | p.2 ∈ selectedSparseBoundary beta epsilon B C r A p.1} := by
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro p hp
  exact pressureSelectedSparseBoundary_subset beta epsilon B C r A P Perr p.1 hp

theorem finiteSpin_sum_eq_univ_ite {n : ℕ} (D : Finset (Spin n)) (f : Spin n → ℝ) :
    (∑ x ∈ D, f x) = ∑ x : Spin n, if x ∈ D then f x else 0 := by
  rw [←Finset.sum_filter]
  congr 1
  ext x
  simp

def gaussianRegressionSetMass {n : ℕ} (c s : ℝ)
    (q : EuclideanSpace ℝ (Fin n × Fin n) → Spin n → ℝ)
    (D : EuclideanSpace ℝ (Fin n × Fin n) → Finset (Spin n))
    (G : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  ∫ Z, ∑ x ∈ D G, q (c • G+s • Z) x
    ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)

theorem measurable_gaussianRegressionSetMass {n : ℕ} (c s : ℝ)
    (q : EuclideanSpace ℝ (Fin n × Fin n) → Spin n → ℝ)
    (D : EuclideanSpace ℝ (Fin n × Fin n) → Finset (Spin n))
    (hq : ∀ x, Measurable (fun z => q z x))
    (hD : ∀ x, MeasurableSet {z | x ∈ D z}) :
    Measurable (gaussianRegressionSetMass c s q D) := by
  have hf : Measurable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) =>
      ∑ x : Spin n, if x ∈ D p.1 then q (c • p.1+s • p.2) x else 0) := by
    apply Finset.measurable_sum
    intro x hx
    apply Measurable.ite ((hD x).preimage measurable_fst)
    · exact (hq x).comp
        (((continuous_fst.const_smul c).add (continuous_snd.const_smul s)).measurable)
    · exact measurable_const
  have hm : Measurable (fun G => ∫ Z, ∑ x : Spin n,
      if x ∈ D G then q (c • G+s • Z) x else 0
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  convert hm using 1
  funext G
  apply integral_congr_ae
  exact ae_of_all _ (fun Z => finiteSpin_sum_eq_univ_ite (D G) _)

theorem gaussianRegressionSetMass_bounds {n : ℕ} (c s : ℝ)
    (q : EuclideanSpace ℝ (Fin n × Fin n) → Spin n → ℝ)
    (D : EuclideanSpace ℝ (Fin n × Fin n) → Finset (Spin n))
    (hq0 : ∀ z x, 0 ≤ q z x) (hq1 : ∀ z x, q z x ≤ 1)
    (G : EuclideanSpace ℝ (Fin n × Fin n)) :
    0 ≤ gaussianRegressionSetMass c s q D G ∧
      gaussianRegressionSetMass c s q D G ≤ Fintype.card (Spin n) := by
  have h0 : 0 ≤ gaussianRegressionSetMass c s q D G :=
    integral_nonneg (fun Z => Finset.sum_nonneg (fun x hx => hq0 _ _))
  have hnorm := norm_integral_le_of_norm_le_const (μ :=
      GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (f := fun Z => ∑ x ∈ D G, q (c • G+s • Z) x)
    (C := (Fintype.card (Spin n) : ℝ))
    (ae_of_all _ (fun Z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun x hx => hq0 _ _))]
      calc
        _ ≤ ∑ x ∈ D G, (1 : ℝ) := Finset.sum_le_sum (fun x hx => hq1 _ _)
        _ = (D G).card := by simp
        _ ≤ Fintype.card (Spin n) := by
          exact_mod_cast (Finset.card_le_card (Finset.subset_univ (D G)))))
  simp only [probReal_univ,mul_one] at hnorm
  change |gaussianRegressionSetMass c s q D G| ≤ _ at hnorm
  exact ⟨h0,(le_abs_self _).trans hnorm⟩

theorem integrable_gaussianRegressionSetMass {n : ℕ} (c s : ℝ)
    (q : EuclideanSpace ℝ (Fin n × Fin n) → Spin n → ℝ)
    (D : EuclideanSpace ℝ (Fin n × Fin n) → Finset (Spin n))
    (hq : ∀ x, Measurable (fun z => q z x))
    (hD : ∀ x, MeasurableSet {z | x ∈ D z})
    (hq0 : ∀ z x, 0 ≤ q z x) (hq1 : ∀ z x, q z x ≤ 1) :
    Integrable (gaussianRegressionSetMass c s q D)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  apply (integrable_const (Fintype.card (Spin n) : ℝ)).mono'
    (measurable_gaussianRegressionSetMass c s q D hq hD).aestronglyMeasurable
  exact ae_of_all _ (fun G => by
    rw [Real.norm_eq_abs,abs_of_nonneg (gaussianRegressionSetMass_bounds c s q D hq0 hq1 G).1]
    exact (gaussianRegressionSetMass_bounds c s q D hq0 hq1 G).2)

theorem gaussianRegression_intrinsic_annealed_boundary_mass_le {n : ℕ} (hn : 0<n)
    (beta c s P L Perr C epsilon B : ℝ) (hc : c ≤ 1) (r : ℕ) (A : ℝ)
    (q : EuclideanSpace ℝ (Fin n × Fin n) → Spin n → ℝ)
    (hq : ∀ x, Measurable (fun z => q z x))
    (hq0 : ∀ z x, 0 ≤ q z x) (hq1 : ∀ z x, q z x ≤ 1)
    (hdom : ∀ z x, q z x ≤ Real.exp (-(n : ℝ)*P+L+
      beta*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x z)) :
    (∫ G, gaussianRegressionSetMass c s q
      (pressureSelectedSparseBoundary beta epsilon B C r A P Perr) G
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤
    Real.exp (L+Perr+(1-c)*|beta| *(n : ℝ)*C/2+beta^2*s^2*(n : ℝ)/4)*
      (primitiveJointGibbsLaw n beta (1/Real.sqrt (2*(n : ℝ)))).real
        {p | p.2 ∈ pressureSelectedSparseBoundary beta epsilon B C r A P Perr p.1} := by
  let D := pressureSelectedSparseBoundary (n := n) beta epsilon B C r A P Perr
  have hD := measurableSet_pressureSelectedSparseBoundary_mem (n := n)
    beta epsilon B C r A P Perr
  have hi := integral_mono (integrable_gaussianRegressionSetMass c s q D hq hD hq0 hq1)
    ((integrable_primitive_gibbs_cutMass beta (1/Real.sqrt (2*(n : ℝ))) D hD).const_mul
      (Real.exp (L+Perr+(1-c)*|beta| *(n : ℝ)*C/2+beta^2*s^2*(n : ℝ)/4)))
    (gaussianRegression_intrinsic_pressureSelected_boundary_mass_le hn beta c s P L Perr C
      epsilon B hc r A q hq hq0 hq1 hdom)
  apply hi.trans_eq
  rw [integral_const_mul,←primitiveJointGibbs_probability_eq_integral_cutMass beta _ D hD]

end SKConstants
