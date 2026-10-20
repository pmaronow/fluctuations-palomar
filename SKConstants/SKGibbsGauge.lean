module

public import SKConstants.SKModel
public import SKConstants.GaussianProposalOrthogonalInvariant

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

@[expose] def spinGaugeAction {n : ℕ} (x y : Spin n) : Spin n :=
  fun i => if x i then y i else !(y i)

lemma spinGaugeAction_involutive {n : ℕ} (x : Spin n) :
    Function.Involutive (spinGaugeAction x) := by
  intro y
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [spinGaugeAction, hx, hy]

@[expose] def spinGaugeEquiv {n : ℕ} (x : Spin n) : Spin n ≃ Spin n :=
  ⟨spinGaugeAction x, spinGaugeAction x, spinGaugeAction_involutive x,
    spinGaugeAction_involutive x⟩

lemma signedSpin_gaugeAction {n : ℕ} (x y : Spin n) (i : Fin n) :
    signedSpin (spinGaugeAction x y) i = signedSpin x i * signedSpin y i := by
  cases hx : x i <;> cases hy : y i <;> simp [spinGaugeAction, signedSpin, hx, hy]

@[expose] def spinGaugeMatrix {n : ℕ} (x : Spin n)
    (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => signedSpin x i * W i j * signedSpin x j

lemma continuous_spinGaugeMatrix {n : ℕ} (x : Spin n) :
    Continuous (spinGaugeMatrix x) := by
  unfold spinGaugeMatrix
  fun_prop

lemma quadraticHamiltonian_gauge {n : ℕ} (x y : Spin n)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    quadraticHamiltonian (spinGaugeMatrix x W) y =
      quadraticHamiltonian W (spinGaugeAction x y) := by
  unfold quadraticHamiltonian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [signedSpin_gaugeAction, signedSpin_gaugeAction]
  unfold spinGaugeMatrix
  ring

lemma gibbsPartition_gauge {n : ℕ} (x : Spin n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    gibbsPartition beta (spinGaugeMatrix x W) = gibbsPartition beta W := by
  unfold gibbsPartition
  simp_rw [quadraticHamiltonian_gauge]
  exact (Equiv.sum_comp (spinGaugeEquiv x)
    (fun y => Real.exp (beta * quadraticHamiltonian W y)))

lemma gibbsProbability_gauge {n : ℕ} (x y : Spin n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    gibbsProbability beta (spinGaugeMatrix x W) y =
      gibbsProbability beta W (spinGaugeAction x y) := by
  unfold gibbsProbability
  rw [quadraticHamiltonian_gauge, gibbsPartition_gauge]

@[expose] def spinGaugeBasis {n : ℕ} (x : Spin n) (i j : Fin n) : ℝ :=
  signedSpin x i * GaussianProposal.canonicalBasis i j

lemma spinGaugeBasis_orthogonal {n : ℕ} (x : Spin n) (i j : Fin n) :
    GaussianProposal.dot (spinGaugeBasis x i) (spinGaugeBasis x j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [GaussianProposal.dot, spinGaugeBasis, GaussianProposal.canonicalBasis,
      ← pow_two, signedSpin_sq]
  · simp [GaussianProposal.dot, spinGaugeBasis, GaussianProposal.canonicalBasis, hij]

lemma fullBasisMatrix_spinGauge {n : ℕ} (x : Spin n) (sigma : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    GaussianProposal.fullBasisMatrix sigma (spinGaugeBasis x) z =
      spinGaugeMatrix x (GaussianProposal.goeMatrix sigma z) := by
  ext i j
  rw [GaussianProposal.fullBasisMatrix_entry, GaussianProposal.goeBilinear_eq_matrix]
  simp [spinGaugeBasis, GaussianProposal.canonicalBasis, spinGaugeMatrix]

lemma skDisorderLaw_gauge {n : ℕ} (x : Spin n) :
    (skDisorderLaw n).map (spinGaugeMatrix x) = skDisorderLaw n := by
  unfold skDisorderLaw
  rw [Measure.map_map (continuous_spinGaugeMatrix x).measurable
    (continuous_goeMatrix _).measurable]
  have h := GaussianProposal.fullBasisMatrix_law
    (1 / Real.sqrt (2 * (n : ℝ))) (spinGaugeBasis x) (spinGaugeBasis_orthogonal x)
  have he : GaussianProposal.fullBasisMatrix (1 / Real.sqrt (2 * (n : ℝ)))
      (spinGaugeBasis x) = spinGaugeMatrix x ∘
        GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) := by
    funext z
    exact fullBasisMatrix_spinGauge x _ z
  rw [he] at h
  simpa only [Nat.cast_ofNat] using h

lemma gibbsProbability_le_one {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    gibbsProbability beta W x ≤ 1 := by
  rw [← gibbsProbability_sum beta W]
  exact Finset.single_le_sum (fun y _ => (gibbsProbability_pos beta W y).le)
    (Finset.mem_univ x)

lemma integrable_gibbsProbability_sk {n : ℕ} (beta : ℝ) (x : Spin n) :
    Integrable (fun W => gibbsProbability beta W x) (skDisorderLaw n) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_gibbsProbability beta x).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun W => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gibbsProbability_pos beta W x).le]
    exact gibbsProbability_le_one beta W x

lemma spinGaugeAction_allTrue {n : ℕ} (x : Spin n) :
    spinGaugeAction x (fun _ => true) = x := by
  funext i
  cases hx : x i <;> simp [spinGaugeAction, hx]

lemma integral_gibbsProbability_sk_eq_allTrue {n : ℕ} (beta : ℝ) (x : Spin n) :
    (∫ W, gibbsProbability beta W x ∂skDisorderLaw n) =
      ∫ W, gibbsProbability beta W (fun _ => true) ∂skDisorderLaw n := by
  have hm := skDisorderLaw_gauge x
  have hi := integral_map (μ := skDisorderLaw n) (continuous_spinGaugeMatrix x).aemeasurable
    (continuous_gibbsProbability beta (fun _ => true)).aestronglyMeasurable
  rw [hm] at hi
  simpa only [gibbsProbability_gauge, spinGaugeAction_allTrue] using hi.symm

theorem integral_gibbsProbability_sk_uniform {n : ℕ} (beta : ℝ) (x : Spin n) :
    (∫ W, gibbsProbability beta W x ∂skDisorderLaw n) = 1 / (2 : ℝ) ^ n := by
  have hs : (∑ y : Spin n, ∫ W, gibbsProbability beta W y ∂skDisorderLaw n) = 1 := by
    rw [← integral_finsetSum Finset.univ (fun y _ => integrable_gibbsProbability_sk beta y)]
    simp_rw [gibbsProbability_sum]
    simp
  simp_rw [integral_gibbsProbability_sk_eq_allTrue beta] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card (Spin n) : ℝ) = (2 : ℝ) ^ n := by
    simp [Spin]
  rw [hc] at hs
  rw [integral_gibbsProbability_sk_eq_allTrue beta]
  exact (eq_div_iff (by positivity)).2 (by linarith)

theorem integral_goeGibbsWeight_sk_uniform {n : ℕ} (beta : ℝ) (x : Spin n) :
    (∫ z : EuclideanSpace ℝ (Fin n × Fin n),
      gibbsProbability beta (GaussianProposal.goeMatrix
        (1 / Real.sqrt (2 * (n : ℝ))) z) x
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) = 1 / (2 : ℝ) ^ n := by
  have hi := integral_map (μ := GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (continuous_goeMatrix (1 / Real.sqrt (2 * (n : ℝ)))).aemeasurable
    (continuous_gibbsProbability beta x).aestronglyMeasurable
  have h := integral_gibbsProbability_sk_uniform beta x
  unfold skDisorderLaw at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hi] at h
  exact h

end SKConstants
