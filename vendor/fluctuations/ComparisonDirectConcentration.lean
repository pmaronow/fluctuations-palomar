module

public import ShortComparisonError
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalPinnedWindow

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

namespace FiniteSpinCovariance

variable {S I : Type*} [Fintype S] [Fintype I]

def mean (p : S → ℝ) (z : S → I → ℝ) (i : I) : ℝ := ∑ s, p s * z s i

def second (p : S → ℝ) (z : S → I → ℝ) (i j : I) : ℝ :=
  ∑ s, p s * z s i * z s j

def cov (p : S → ℝ) (z : S → I → ℝ) (i j : I) : ℝ :=
  second p z i j - mean p z i * mean p z j

def meanSq (p : S → ℝ) (z : S → I → ℝ) : ℝ := ∑ i, (mean p z i)^2

def overlapSecond (p : S → ℝ) (z : S → I → ℝ) : ℝ :=
  ∑ s, ∑ t, p s * p t * (∑ i, z s i * z t i)^2

def observable (p : S → ℝ) (z : S → I → ℝ) (s : S) : ℝ :=
  (∑ i, z s i * mean p z i) - (1/2:ℝ) * meanSq p z

def traceCovSq (p : S → ℝ) (z : S → I → ℝ) : ℝ :=
  ∑ i, ∑ j, (cov p z i j)^2

def meanCovMean (p : S → ℝ) (z : S → I → ℝ) : ℝ :=
  ∑ i, ∑ j, mean p z i * cov p z i j * mean p z j

theorem sum_mean_dot (p : S → ℝ) (z : S → I → ℝ) :
    (∑ s, p s * ∑ i, z s i * mean p z i) = meanSq p z := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, mean, meanSq, pow_two]

theorem observable_mean (p : S → ℝ) (z : S → I → ℝ) (hp : ∑ s, p s = 1) :
    (∑ s, p s * observable p z s) = (1/2:ℝ) * meanSq p z := by
  classical
  simp only [observable, mul_sub, Finset.sum_sub_distrib]
  rw [sum_mean_dot, ← Finset.sum_mul, hp]
  ring

theorem overlapSecond_eq_second (p : S → ℝ) (z : S → I → ℝ) :
    overlapSecond p z = ∑ i, ∑ j, (second p z i j)^2 := by
  classical
  have hs (s t : S) : (∑ i, z s i * z t i)^2 =
      ∑ i, ∑ j, (z s i * z s j) * (z t i * z t j) := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [overlapSecond, hs, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he (s t : S) : p s * p t * ((z s i * z s j) * (z t i * z t j)) =
      (p s * z s i * z s j) * (p t * z t i * z t j) := by ring
  simp_rw [he, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [second, pow_two]

theorem mean_dot_second (p : S → ℝ) (z : S → I → ℝ) :
    (∑ s, p s * (∑ i, z s i * mean p z i)^2) =
      ∑ i, ∑ j, mean p z i * second p z i j * mean p z j := by
  classical
  have hs (s : S) : p s * (∑ i, z s i * mean p z i)^2 =
      ∑ i, ∑ j, mean p z i * (p s * z s i * z s j) * mean p z j := by
    rw [pow_two, Finset.mul_sum]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, second]

theorem meanCovMean_eq (p : S → ℝ) (z : S → I → ℝ) :
    meanCovMean p z =
      (∑ s, p s * (∑ i, z s i * mean p z i)^2) - (meanSq p z)^2 := by
  classical
  rw [mean_dot_second]
  unfold meanCovMean cov
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  unfold meanSq
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem meanCovMean_nonneg (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpsum : ∑ s, p s = 1) :
    0 ≤ meanCovMean p z := by
  have hv := finite_covariance_nonneg p
    (fun s => ∑ i, z s i * mean p z i) (fun s => ∑ i, z s i * mean p z i)
    hp hpsum (fun s t => by
      nlinarith [sq_nonneg ((∑ i, z s i * mean p z i) -
        (∑ i, z t i * mean p z i))])
  rw [meanCovMean_eq]
  simpa only [← mul_assoc, sum_mean_dot, pow_two] using hv

theorem overlapSecond_covariance_decomposition (p : S → ℝ) (z : S → I → ℝ) :
    overlapSecond p z = (meanSq p z)^2 + 2 * meanCovMean p z + traceCovSq p z := by
  classical
  rw [overlapSecond_eq_second]
  unfold meanCovMean traceCovSq cov meanSq
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem observable_second (p : S → ℝ) (z : S → I → ℝ) (hp : ∑ s, p s = 1) :
    (∑ s, p s * (observable p z s)^2) =
      meanCovMean p z + (1/4:ℝ) * (meanSq p z)^2 := by
  classical
  have he (s : S) : p s * (observable p z s)^2 =
      p s * (∑ i, z s i * mean p z i)^2 -
        meanSq p z * (p s * ∑ i, z s i * mean p z i) +
        p s * ((1/4:ℝ) * (meanSq p z)^2) := by
    unfold observable
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, sum_mean_dot, ← Finset.sum_mul, hp, meanCovMean_eq]
  ring

theorem overlapSecond_le_observable_second (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpsum : ∑ s, p s = 1) :
    overlapSecond p z ≤ 4 * (∑ s, p s * (observable p z s)^2) + traceCovSq p z := by
  rw [overlapSecond_covariance_decomposition, observable_second p z hpsum]
  have h := meanCovMean_nonneg p z hp hpsum
  linarith

theorem meanCovMean_le_sqrt_trace (p : S → ℝ) (z : S → I → ℝ) :
    meanCovMean p z ≤ meanSq p z * Real.sqrt (traceCovSq p z) := by
  classical
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (I × I))
    (fun ij => mean p z ij.1*mean p z ij.2) (fun ij => cov p z ij.1 ij.2)
  have hsum : (∑ ij : I × I, (mean p z ij.1*mean p z ij.2)^2) = (meanSq p z)^2 := by
    simp only [Fintype.sum_prod_type, mul_pow]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, meanSq, pow_two]
  rw [hsum, Real.sqrt_sq (show 0 ≤ meanSq p z from
    Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  simp only [Fintype.sum_prod_type] at h
  unfold meanCovMean traceCovSq
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem overlap_first (p : S → ℝ) (z : S → I → ℝ) :
    (∑ s, ∑ t, p s*p t*(∑ i, z s i*z t i)) = meanSq p z := by
  classical
  have ht (s) : (∑ t, p s*p t*(∑ i, z s i*z t i)) =
      p s*(∑ i, z s i*mean p z i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp_rw [ht]
  exact sum_mean_dot p z

theorem centered_overlap_decomposition (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∑ s, p s = 1) (c : ℝ) :
    (∑ s, ∑ t, p s*p t*((∑ i, z s i*z t i)-c)^2) =
      (meanSq p z-c)^2 +2*meanCovMean p z+traceCovSq p z := by
  classical
  have he (s t) : p s*p t*((∑ i, z s i*z t i)-c)^2 =
      p s*p t*(∑ i, z s i*z t i)^2 -
        2*c*(p s*p t*(∑ i, z s i*z t i)) +c^2*(p s*p t) := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hm : (∑ s, ∑ t, 2*c*(p s*p t*(∑ i, z s i*z t i))) =2*c*meanSq p z := by
    simp only [← Finset.mul_sum, overlap_first]
  have hc : (∑ s, ∑ t, c^2*(p s*p t)) =c^2 := by
    simp only [← Finset.mul_sum, hp, mul_one]
  rw [hm, hc]
  change overlapSecond p z-2*c*meanSq p z+c^2 = _
  rw [overlapSecond_covariance_decomposition]
  ring

theorem centered_overlap_le_norm_and_trace (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∑ s, p s = 1) (hmean : meanSq p z ≤ 1) (c : ℝ) :
    (∑ s, ∑ t, p s*p t*((∑ i, z s i*z t i)-c)^2) ≤
      (meanSq p z-c)^2+2*Real.sqrt (traceCovSq p z)+traceCovSq p z := by
  rw [centered_overlap_decomposition p z hp c]
  have h := (meanCovMean_le_sqrt_trace p z).trans
    (mul_le_mul_of_nonneg_right hmean (Real.sqrt_nonneg _))
  nlinarith

theorem observable_centered_second (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∑ s, p s = 1) (c : ℝ) :
    (∑ s, p s*(observable p z s-c/2)^2) =
      meanCovMean p z+(1/4:ℝ)*(meanSq p z-c)^2 := by
  classical
  have he (s) : p s*(observable p z s-c/2)^2 =
      p s*(observable p z s)^2-c*(p s*observable p z s)+(c^2/4)*p s := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hp, observable_mean p z hp,
    observable_second p z hp]
  ring

theorem mean_projection_centered_second (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∑ s, p s = 1) (c : ℝ) :
    (∑ s, p s*((∑ i, z s i*mean p z i)-c)^2) =
      meanCovMean p z+(meanSq p z-c)^2 := by
  classical
  have he (s) : p s*((∑ i, z s i*mean p z i)-c)^2 =
      p s*(∑ i, z s i*mean p z i)^2-
        2*c*(p s*∑ i, z s i*mean p z i)+c^2*p s := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hp, sum_mean_dot, mean_dot_second]
  rw [meanCovMean_eq]
  rw [mean_dot_second]
  ring

theorem centered_mean_sq_le_centered_overlap (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpsum : ∑ s, p s = 1) (c : ℝ) :
    (meanSq p z-c)^2 ≤ ∑ s, ∑ t, p s*p t*((∑ i, z s i*z t i)-c)^2 := by
  rw [centered_overlap_decomposition p z hpsum c]
  have hm := meanCovMean_nonneg p z hp hpsum
  have ht : 0 ≤ traceCovSq p z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem centered_mean_projection_le_centered_overlap (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpsum : ∑ s, p s = 1) (c : ℝ) :
    (∑ s, p s*((∑ i, z s i*mean p z i)-c)^2) ≤
      ∑ s, ∑ t, p s*p t*((∑ i, z s i*z t i)-c)^2 := by
  rw [mean_projection_centered_second p z hpsum c, centered_overlap_decomposition p z hpsum c]
  have hm := meanCovMean_nonneg p z hp hpsum
  have ht : 0 ≤ traceCovSq p z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem centered_overlap_le_centered_observable (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hpsum : ∑ s, p s = 1) (c : ℝ) :
    (∑ s, ∑ t, p s*p t*((∑ i, z s i*z t i)-c)^2) ≤
      4*(∑ s, p s*(observable p z s-c/2)^2)+traceCovSq p z := by
  rw [centered_overlap_decomposition p z hpsum c, observable_centered_second p z hpsum c]
  have h := meanCovMean_nonneg p z hp hpsum
  linarith

theorem centered_projection_second_eq (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∑ s, p s = 1) (v : I → ℝ) :
    (∑ s, p s*(∑ i, v i*(z s i-mean p z i))^2) =
      ∑ i, ∑ j, v i*cov p z i j*v j := by
  classical
  have hc (i j : I) : (∑ s, p s*((z s i-mean p z i)*(z s j-mean p z j))) = cov p z i j := by
    have he (s) : p s*((z s i-mean p z i)*(z s j-mean p z j)) =
        p s*z s i*z s j-mean p z j*(p s*z s i)-mean p z i*(p s*z s j)+
          p s*(mean p z i*mean p z j) := by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hp]
    unfold cov second mean
    ring
  have he (s) : p s*(∑ i, v i*(z s i-mean p z i))^2 =
      ∑ i, ∑ j, v i*(p s*((z s i-mean p z i)*(z s j-mean p z j)))*v j := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, ← Finset.mul_sum, hc]

theorem centered_projection_second_le_trace (p : S → ℝ) (z : S → I → ℝ)
    (hp : ∑ s, p s = 1) (v : I → ℝ) :
    (∑ s, p s*(∑ i, v i*(z s i-mean p z i))^2) ≤
      (∑ i, (v i)^2)*Real.sqrt (traceCovSq p z) := by
  classical
  rw [centered_projection_second_eq p z hp v]
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (I × I))
    (fun ij => v ij.1*v ij.2) (fun ij => cov p z ij.1 ij.2)
  have hv : (∑ ij : I × I, (v ij.1*v ij.2)^2) = (∑ i, (v i)^2)^2 := by
    simp only [Fintype.sum_prod_type, mul_pow]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [hv, Real.sqrt_sq (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  simp only [Fintype.sum_prod_type] at h
  unfold traceCovSq
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end FiniteSpinCovariance

section HierarchyCovariance

variable {S I J : Type*} [Fintype S] [Nonempty S] [Fintype I] [Fintype J]

def hierarchyVectorMean (w : S → ℝ) (phi : S → (J → ℝ) →L[ℝ] ℝ)
    (z : S → I → ℝ) (steps : List (GaussianStep J)) (x : J → ℝ) (i : I) : ℝ :=
  gaussianHierarchyMean w phi (fun s => z s i) steps x

def hierarchyVectorL (w : S → ℝ) (phi : S → (J → ℝ) →L[ℝ] ℝ)
    (z : S → I → ℝ) (steps : List (GaussianStep J)) (x : J → ℝ) (s : S) : ℝ :=
  (∑ i, z s i * hierarchyVectorMean w phi z steps x i) -
    (1/2:ℝ) * ∑ i, (hierarchyVectorMean w phi z steps x i)^2

def hierarchyVectorTraceCovSq (w : S → ℝ) (phi : S → (J → ℝ) →L[ℝ] ℝ)
    (z : S → I → ℝ) (steps : List (GaussianStep J)) (x : J → ℝ) : ℝ :=
  ∑ i, ∑ j, (hierarchyCovariance w phi (fun s => z s i) (fun s => z s j) steps x)^2

theorem hierarchyVectorMean_eq_atoms {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) :
    hierarchyVectorMean w phi z steps x =
      FiniteSpinCovariance.mean (fun s => hierarchyAtom w phi steps s x) z := by
  funext i
  simp only [hierarchyVectorMean, gaussianHierarchyMean_atoms hw phi steps ha,
    FiniteSpinCovariance.mean, mul_comm]

theorem hierarchyVectorL_eq_atoms {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) :
    hierarchyVectorL w phi z steps x =
      FiniteSpinCovariance.observable (fun s => hierarchyAtom w phi steps s x) z := by
  unfold hierarchyVectorL FiniteSpinCovariance.observable FiniteSpinCovariance.meanSq
  rw [hierarchyVectorMean_eq_atoms hw phi z steps ha x]

theorem hierarchyVectorTraceCovSq_eq_atoms {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) :
    hierarchyVectorTraceCovSq w phi z steps x =
      FiniteSpinCovariance.traceCovSq (fun s => hierarchyAtom w phi steps s x) z := by
  classical
  unfold hierarchyVectorTraceCovSq FiniteSpinCovariance.traceCovSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [hierarchyCovariance, gaussianHierarchyMean_atoms hw phi steps ha,
    FiniteSpinCovariance.cov, FiniteSpinCovariance.second, FiniteSpinCovariance.mean]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    ring
  · simp only [mul_comm]

theorem hierarchy_overlap_second_le_L_second {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) :
    hierarchyPairMean w phi (fun s t => (∑ i, z s i * z t i)^2) steps x ≤
      4 * gaussianHierarchyMean w phi (fun s => (hierarchyVectorL w phi z steps x s)^2)
        steps x + hierarchyVectorTraceCovSq w phi z steps x := by
  rw [hierarchyVectorTraceCovSq_eq_atoms hw phi z steps ha x,
    hierarchyVectorL_eq_atoms hw phi z steps ha x,
    gaussianHierarchyMean_atoms hw phi steps ha]
  simpa only [hierarchyPairMean, FiniteSpinCovariance.overlapSecond, mul_comm] using
    FiniteSpinCovariance.overlapSecond_le_observable_second
      (fun s => hierarchyAtom w phi steps s x) z
      (fun s => hierarchyAtom_nonneg hw phi steps ha s x)
      (hierarchyAtom_sum hw phi steps ha x)

theorem hierarchyVectorL_mean {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) :
    gaussianHierarchyMean w phi (hierarchyVectorL w phi z steps x) steps x =
      (1/2:ℝ) * ∑ i, (hierarchyVectorMean w phi z steps x i)^2 := by
  rw [hierarchyVectorL_eq_atoms hw phi z steps ha x,
    hierarchyVectorMean_eq_atoms hw phi z steps ha x,
    gaussianHierarchyMean_atoms hw phi steps ha]
  simpa only [mul_comm, FiniteSpinCovariance.meanSq] using
    FiniteSpinCovariance.observable_mean (fun s => hierarchyAtom w phi steps s x) z
      (hierarchyAtom_sum hw phi steps ha x)

theorem hierarchy_centered_overlap_le_norm_and_trace {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ)
    (hmean : (∑ i, (hierarchyVectorMean w phi z steps x i)^2) ≤ 1) (c : ℝ) :
    hierarchyPairMean w phi (fun s t => ((∑ i, z s i*z t i)-c)^2) steps x ≤
      ((∑ i, (hierarchyVectorMean w phi z steps x i)^2)-c)^2+
        2*Real.sqrt (hierarchyVectorTraceCovSq w phi z steps x)+
        hierarchyVectorTraceCovSq w phi z steps x := by
  rw [hierarchyVectorTraceCovSq_eq_atoms hw phi z steps ha x]
  rw [hierarchyVectorMean_eq_atoms hw phi z steps ha x] at hmean ⊢
  simpa only [hierarchyPairMean, FiniteSpinCovariance.meanSq, mul_comm] using
    FiniteSpinCovariance.centered_overlap_le_norm_and_trace
      (fun s => hierarchyAtom w phi steps s x) z (hierarchyAtom_sum hw phi steps ha x) hmean c

theorem hierarchy_centered_mean_sq_le_overlap {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) (c : ℝ) :
    ((∑ i, (hierarchyVectorMean w phi z steps x i)^2)-c)^2 ≤
      hierarchyPairMean w phi (fun s t => ((∑ i, z s i*z t i)-c)^2) steps x := by
  rw [hierarchyVectorMean_eq_atoms hw phi z steps ha x]
  simpa only [hierarchyPairMean, FiniteSpinCovariance.meanSq, mul_comm] using
    FiniteSpinCovariance.centered_mean_sq_le_centered_overlap
      (fun s => hierarchyAtom w phi steps s x) z
      (fun s => hierarchyAtom_nonneg hw phi steps ha s x) (hierarchyAtom_sum hw phi steps ha x) c

theorem hierarchy_centered_mean_projection_le_overlap {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) (c : ℝ) :
    gaussianHierarchyMean w phi (fun s => ((∑ i, z s i*hierarchyVectorMean w phi z steps x i)-c)^2)
      steps x ≤ hierarchyPairMean w phi (fun s t => ((∑ i, z s i*z t i)-c)^2) steps x := by
  rw [hierarchyVectorMean_eq_atoms hw phi z steps ha x, gaussianHierarchyMean_atoms hw phi steps ha]
  simpa only [hierarchyPairMean, mul_comm] using
    FiniteSpinCovariance.centered_mean_projection_le_centered_overlap
      (fun s => hierarchyAtom w phi steps s x) z
      (fun s => hierarchyAtom_nonneg hw phi steps ha s x) (hierarchyAtom_sum hw phi steps ha x) c

theorem hierarchy_centered_overlap_le_centered_L {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) (c : ℝ) :
    hierarchyPairMean w phi (fun s t => ((∑ i, z s i*z t i)-c)^2) steps x ≤
      4*gaussianHierarchyMean w phi (fun s => (hierarchyVectorL w phi z steps x s-c/2)^2)
        steps x+hierarchyVectorTraceCovSq w phi z steps x := by
  rw [hierarchyVectorTraceCovSq_eq_atoms hw phi z steps ha x,
    hierarchyVectorL_eq_atoms hw phi z steps ha x, gaussianHierarchyMean_atoms hw phi steps ha]
  simpa only [hierarchyPairMean, mul_comm] using
    FiniteSpinCovariance.centered_overlap_le_centered_observable
      (fun s => hierarchyAtom w phi steps s x) z
      (fun s => hierarchyAtom_nonneg hw phi steps ha s x) (hierarchyAtom_sum hw phi steps ha x) c

theorem hierarchy_centered_projection_second_le_trace {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps)
    (x : J → ℝ) (v : I → ℝ) :
    gaussianHierarchyMean w phi
      (fun s => (∑ i, v i*(z s i-hierarchyVectorMean w phi z steps x i))^2) steps x ≤
      (∑ i, (v i)^2)*Real.sqrt (hierarchyVectorTraceCovSq w phi z steps x) := by
  rw [hierarchyVectorTraceCovSq_eq_atoms hw phi z steps ha x,
    hierarchyVectorMean_eq_atoms hw phi z steps ha x, gaussianHierarchyMean_atoms hw phi steps ha]
  simpa only [mul_comm] using FiniteSpinCovariance.centered_projection_second_le_trace
    (fun s => hierarchyAtom w phi steps s x) z (hierarchyAtom_sum hw phi steps ha x) v

end HierarchyCovariance

def physicalSpinCovariance (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) (i j : Fin n) : ℝ :=
  hierarchyCovariance (uniformWeight n) (finiteFeature n)
    (fun sigma => normalizedSpin n sigma i) (fun sigma => normalizedSpin n sigma j) steps x

def physicalSpinTraceCovSq (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) : ℝ := ∑ i, ∑ j, (physicalSpinCovariance n steps x i j)^2

theorem physicalSpinL_eq_hierarchyVectorL (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ) :
    physicalSpinL n steps x =
      hierarchyVectorL (uniformWeight n) (finiteFeature n) (normalizedSpin n) steps x := rfl

theorem physical_overlap_second_le_L_second (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) :
    hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau)^2) steps x ≤
      4 * gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun sigma => (physicalSpinL n steps x sigma)^2) steps x +
        physicalSpinTraceCovSq n steps x := by
  simpa only [orderedOverlap_normalized, physicalSpinL_eq_hierarchyVectorL,
    physicalSpinTraceCovSq, physicalSpinCovariance, hierarchyVectorTraceCovSq] using
    hierarchy_overlap_second_le_L_second (uniformWeight_pos n) (finiteFeature n)
      (normalizedSpin n) steps ha x

theorem physicalSpinL_conditional_mean (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) :
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (physicalSpinL n steps x) steps x =
      (1/2:ℝ) * ∑ i, (actualSpinMean n steps x i)^2 := by
  exact hierarchyVectorL_mean (uniformWeight_pos n) (finiteFeature n)
    (normalizedSpin n) steps ha x

theorem physical_centered_overlap_le_norm_and_trace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (c : ℝ) :
    hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau-c)^2) steps x ≤
      ((∑ i, (actualSpinMean n steps x i)^2)-c)^2+
        2*Real.sqrt (physicalSpinTraceCovSq n steps x)+physicalSpinTraceCovSq n steps x := by
  have hmean := actualSpinMean_norm_le n steps ha x
  have hs : (∑ i, (actualSpinMean n steps x i)^2) ≤ 1 := by
    have hsum0 : 0 ≤ ∑ i, (actualSpinMean n steps x i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hh := Real.sq_sqrt hsum0
    dsimp only [projectionEuclideanNorm] at hmean
    nlinarith [Real.sqrt_nonneg (∑ i, (actualSpinMean n steps x i)^2)]
  simpa only [orderedOverlap_normalized, physicalSpinTraceCovSq, physicalSpinCovariance,
    hierarchyVectorTraceCovSq, hierarchyVectorMean, actualSpinMean] using
    hierarchy_centered_overlap_le_norm_and_trace (uniformWeight_pos n) (finiteFeature n)
      (normalizedSpin n) steps ha x hs c

theorem physical_centered_overlap_le_centered_L (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (c : ℝ) :
    hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau-c)^2) steps x ≤
      4*gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun sigma => (physicalSpinL n steps x sigma-c/2)^2) steps x+
        physicalSpinTraceCovSq n steps x := by
  simpa only [orderedOverlap_normalized, physicalSpinL_eq_hierarchyVectorL,
    physicalSpinTraceCovSq, physicalSpinCovariance, hierarchyVectorTraceCovSq] using
    hierarchy_centered_overlap_le_centered_L (uniformWeight_pos n) (finiteFeature n)
      (normalizedSpin n) steps ha x c

theorem physical_centered_mean_sq_le_overlap (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (c : ℝ) :
    ((∑ i, (actualSpinMean n steps x i)^2)-c)^2 ≤
      hierarchyPairMean (uniformWeight n) (finiteFeature n)
        (fun sigma tau => (orderedOverlap n sigma tau-c)^2) steps x := by
  simpa only [orderedOverlap_normalized, hierarchyVectorMean, actualSpinMean] using
    hierarchy_centered_mean_sq_le_overlap (uniformWeight_pos n) (finiteFeature n)
      (normalizedSpin n) steps ha x c

theorem physical_centered_mean_projection_le_overlap (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (c : ℝ) :
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun sigma => ((∑ i, normalizedSpin n sigma i*actualSpinMean n steps x i)-c)^2) steps x ≤
      hierarchyPairMean (uniformWeight n) (finiteFeature n)
        (fun sigma tau => (orderedOverlap n sigma tau-c)^2) steps x := by
  simpa only [orderedOverlap_normalized, hierarchyVectorMean, actualSpinMean] using
    hierarchy_centered_mean_projection_le_overlap (uniformWeight_pos n) (finiteFeature n)
      (normalizedSpin n) steps ha x c

theorem physical_centered_projection_second_le_trace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (v : Fin n → ℝ) :
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun sigma => (∑ i, v i*(normalizedSpin n sigma i-actualSpinMean n steps x i))^2) steps x ≤
      (∑ i, (v i)^2)*Real.sqrt (physicalSpinTraceCovSq n steps x) := by
  exact hierarchy_centered_projection_second_le_trace (uniformWeight_pos n) (finiteFeature n)
    (normalizedSpin n) steps ha x v

theorem physical_conditional_noise_second_le_trace (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail))
    (p : (FeatureIndex n → ℝ) × ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length)
    (v : Fin n → ℝ) :
    let y := actualCutField pre tail p.1 p.2
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (pre++tail) id pre.length
      (fun q => (∑ i, v i*(normalizedSpin n
        (ForwardPath.spin tail.length (continuationState pre tail q.1 q.2).2) i-
          actualSpinMean n tail y i))^2) p ≤
      (∑ i, (v i)^2)*Real.sqrt (physicalSpinTraceCovSq n tail y) := by
  dsimp only
  let y := actualCutField pre tail p.1 p.2
  let F := fun z : (FeatureIndex n → ℝ) × ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length =>
    (∑ i, v i*(normalizedSpin n (ForwardPath.spin tail.length z.2) i-actualSpinMean n tail y i))^2
  have he := conditionalPathAverage_continuation (uniformWeight n) (finiteFeature n) pre tail id F p
  change _ = ∫ q, (∑ i, v i*(normalizedSpin n (ForwardPath.spin tail.length q) i-
    actualSpinMean n tail y i))^2 ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) tail y at he
  change conditionalPathAverage (uniformWeight n) (finiteFeature n) (pre++tail) id pre.length
    (fun q => F (continuationState pre tail (id q.1) q.2)) p ≤ _
  rw [he]
  rw [integral_hierarchyPathKernel (uniformWeight_pos n) (finiteFeature n)
    (fun sigma => (∑ i, v i*(normalizedSpin n sigma i-actualSpinMean n tail y i))^2)
    tail (ha.suffix pre tail)]
  exact physical_centered_projection_second_le_trace n tail (ha.suffix pre tail) y v

theorem physicalSpinTraceCovSq_smooth (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps) :
    BddSmooth 0 (physicalSpinTraceCovSq n steps) := by
  unfold physicalSpinTraceCovSq physicalSpinCovariance hierarchyCovariance
  apply BddSmooth.sum Finset.univ
  intro i _
  apply BddSmooth.sum Finset.univ
  intro j _
  exact ((gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n) _ steps ha 0).sub
    ((gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n) _ steps ha 0).mul
      (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n) _ steps ha 0))).pow 2

namespace Hierarchy

def prefixSplice {ι S : Type} : (pre tail : List (GaussianStep ι)) → {P : Type} →
    (P × ForwardPath (ι → ℝ) S (pre++tail).length) →
    ForwardPath (ι → ℝ) S tail.length → P × ForwardPath (ι → ℝ) S (pre++tail).length
  | [], _, _, p, z => (p.1,z)
  | _::pre, tail, _, p, z =>
      let q := prefixSplice pre tail ((p.1,p.2.1),p.2.2) z
      (q.1.1,(q.1.2,q.2))

theorem prefixSplice_fst {ι S P : Type} (pre tail : List (GaussianStep ι))
    (p : P × ForwardPath (ι → ℝ) S (pre++tail).length)
    (z : ForwardPath (ι → ℝ) S tail.length) :
    (prefixSplice pre tail p z).1 = p.1 := by
  induction pre generalizing P with
  | nil => rfl
  | cons st pre ih =>
    exact congrArg (fun t : P × (ι → ℝ) => t.1) (ih ((p.1,p.2.1),p.2.2))

theorem prefixSplice_spin {ι S P : Type} (pre tail : List (GaussianStep ι))
    (p : P × ForwardPath (ι → ℝ) S (pre++tail).length)
    (z : ForwardPath (ι → ℝ) S tail.length) :
    ForwardPath.spin (pre++tail).length (prefixSplice pre tail p z).2 =
      ForwardPath.spin tail.length z := by
  induction pre generalizing P with
  | nil => rfl
  | cons st pre ih => exact ih ((p.1,p.2.1),p.2.2)

theorem hierarchyMeanPath_prefixSplice {ι S P : Type} [Fintype ι] [Fintype S]
    [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S]
    (w : S → ℝ) (phi : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (pre tail : List (GaussianStep ι)) (x : P → ι → ℝ) {i : ℕ} (hi : i ≤ pre.length)
    (p : P × ForwardPath (ι → ℝ) S (pre++tail).length)
    (z : ForwardPath (ι → ℝ) S tail.length) :
    hierarchyMeanPath w phi A (pre++tail) x i (prefixSplice pre tail p z) =
      hierarchyMeanPath w phi A (pre++tail) x i p := by
  induction pre generalizing P i with
  | nil =>
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    simp only [List.nil_append, hierarchyMeanPath_zero, prefixSplice_fst]
  | cons st pre ih =>
    cases i with
    | zero => simp only [List.cons_append, hierarchyMeanPath, prefixSplice_fst]
    | succ i =>
      exact ih (fun q : P × (ι → ℝ) => x q.1+q.2)
        (Nat.le_of_succ_le_succ hi) ((p.1,p.2.1),p.2.2)

theorem conditionalPathAverage_prefixSplice {ι S P : Type} [Fintype ι] [Fintype S]
    [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S]
    (w : S → ℝ) (phi : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre tail : List (GaussianStep ι)) (x : P → ι → ℝ)
    (F : P × ForwardPath (ι → ℝ) S (pre++tail).length → ℝ)
    (p : P × ForwardPath (ι → ℝ) S (pre++tail).length) :
    conditionalPathAverage w phi (pre++tail) x pre.length F p =
      ∫ z, F (prefixSplice pre tail p z)
        ∂hierarchyPathKernel w phi tail (actualCutField pre tail (x p.1) p.2) := by
  induction pre generalizing P with
  | nil => cases tail <;> rfl
  | cons st pre ih =>
    exact ih (fun q : P × (ι → ℝ) => x q.1+q.2)
      (fun q => F (q.1.1,(q.1.2,q.2))) ((p.1,p.2.1),p.2.2)

end Hierarchy

theorem actualSpinPath_prefixSplice (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) {i : ℕ} (hi : i ≤ pre.length)
    (p : PhysicalPathState P n (pre++tail))
    (z : ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length) :
    actualSpinPath n (pre++tail) x i (prefixSplice pre tail p z) =
      actualSpinPath n (pre++tail) x i p := by
  apply PiLp.ext
  intro j
  exact hierarchyMeanPath_prefixSplice (uniformWeight n) (finiteFeature n)
    (fun sigma => normalizedSpin n sigma j) pre tail x hi p z

theorem actualSpinPath_at_cut_eq_mean (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) :
    actualSpinPath n (pre++tail) x pre.length p =
      WithLp.toLp 2 (actualSpinMean n tail (actualCutField pre tail (x p.1) p.2)) := by
  apply PiLp.ext
  intro j
  exact hierarchyMeanPath_at_cut (uniformWeight n) (finiteFeature n)
    (fun sigma => normalizedSpin n sigma j) pre tail x p

theorem physical_norm_centered_le_conditional_pair (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++tail)) (c : ℝ) :
    (‖actualSpinPath n (pre++tail) x pre.length p‖^2-c)^2 ≤
      hierarchyPairMean (uniformWeight n) (finiteFeature n)
        (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail
        (actualCutField pre tail (x p.1) p.2) := by
  rw [actualSpinPath_at_cut_eq_mean, EuclideanSpace.real_norm_sq_eq]
  exact physical_centered_mean_sq_le_overlap n tail (ha.suffix pre tail) _ c

theorem physical_terminal_projection_conditional_le_pair (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++tail)) (c : ℝ) :
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
      (fun q => (inner ℝ (actualSpinPath n (pre++tail) x pre.length q)
        (actualSpinPath n (pre++tail) x ((pre++tail).length+1) q)-c)^2) p ≤
      hierarchyPairMean (uniformWeight n) (finiteFeature n)
        (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail
        (actualCutField pre tail (x p.1) p.2) := by
  rw [conditionalPathAverage_prefixSplice]
  simp_rw [actualSpinPath_prefixSplice n pre tail x (le_refl pre.length),
    actualSpinPath_terminal, prefixSplice_spin]
  rw [integral_hierarchyPathKernel (uniformWeight_pos n) (finiteFeature n)
    (fun sigma => (inner ℝ (actualSpinPath n (pre++tail) x pre.length p)
      (WithLp.toLp 2 (normalizedSpin n sigma))-c)^2) tail (ha.suffix pre tail)]
  rw [actualSpinPath_at_cut_eq_mean]
  simpa only [PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial, mul_comm] using
    physical_centered_mean_projection_le_overlap n tail (ha.suffix pre tail)
      (actualCutField pre tail (x p.1) p.2) c

theorem terminalScore_spin_at_cut (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) :
    terminalScore (actualSpinPath n (pre++tail) x) ((pre++tail).length+1) pre.length p =
      physicalSpinL n tail (actualCutField pre tail (x p.1) p.2)
        (ForwardPath.spin (pre++tail).length p.2) := by
  rw [terminalScore, actualSpinPath_terminal, actualSpinPath_at_cut_eq_mean]
  simp only [physicalSpinL, PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq,
    RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, actualSpinMean]

theorem physical_centered_overlap_le_conditional_score (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++tail)) (c : ℝ) :
    hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail
      (actualCutField pre tail (x p.1) p.2) ≤
      4*conditionalPathAverage (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
        (fun z => (terminalScore (actualSpinPath n (pre++tail) x)
          ((pre++tail).length+1) pre.length z-c/2)^2) p+
        physicalSpinTraceCovSq n tail (actualCutField pre tail (x p.1) p.2) := by
  rw [conditionalPathAverage_prefixSplice]
  simp_rw [terminalScore, actualSpinPath_prefixSplice n pre tail x (le_refl pre.length),
    actualSpinPath_terminal, prefixSplice_spin]
  rw [integral_hierarchyPathKernel (uniformWeight_pos n) (finiteFeature n)
    (fun sigma => (inner ℝ (actualSpinPath n (pre++tail) x pre.length p)
      (WithLp.toLp 2 (normalizedSpin n sigma))-
      (1/2:ℝ)*‖actualSpinPath n (pre++tail) x pre.length p‖^2-c/2)^2)
    tail (ha.suffix pre tail)]
  rw [actualSpinPath_at_cut_eq_mean]
  simpa only [physicalSpinL, PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq,
    RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, actualSpinMean] using
    physical_centered_overlap_le_centered_L n tail (ha.suffix pre tail)
      (actualCutField pre tail (x p.1) p.2) c

theorem physical_ordered_noise_conditional_le_trace (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) {P : Type} (x : P → FeatureIndex n → ℝ)
    {i : ℕ} (hi : i ≤ pre.length) (p : PhysicalPathState P n (pre++tail)) :
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
      (fun q => (inner ℝ
        (actualSpinPath n (pre++tail) x ((pre++tail).length+1) q-
          actualSpinPath n (pre++tail) x pre.length q)
        (actualSpinPath n (pre++tail) x pre.length q-
          actualSpinPath n (pre++tail) x i q))^2) p ≤
      ‖actualSpinPath n (pre++tail) x pre.length p-
        actualSpinPath n (pre++tail) x i p‖^2 *
      Real.sqrt (physicalSpinTraceCovSq n tail (actualCutField pre tail (x p.1) p.2)) := by
  rw [conditionalPathAverage_prefixSplice]
  have hcut (z : ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length) :=
    actualSpinPath_prefixSplice n pre tail x (le_refl pre.length) p z
  have hpast (z : ForwardPath (FeatureIndex n → ℝ) (Spin n) tail.length) :=
    actualSpinPath_prefixSplice n pre tail x hi p z
  simp_rw [hcut, hpast, actualSpinPath_terminal, prefixSplice_spin]
  let y := actualCutField pre tail (x p.1) p.2
  have hm : actualSpinPath n (pre++tail) x pre.length p =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm (actualSpinMean n tail y) := by
    apply PiLp.ext
    intro j
    exact hierarchyMeanPath_at_cut (uniformWeight n) (finiteFeature n)
      (fun sigma => normalizedSpin n sigma j) pre tail x p
  rw [integral_hierarchyPathKernel (uniformWeight_pos n) (finiteFeature n)
    (fun sigma => (inner ℝ
      (WithLp.toLp 2 (normalizedSpin n sigma)-
        actualSpinPath n (pre++tail) x pre.length p)
      (actualSpinPath n (pre++tail) x pre.length p-
        actualSpinPath n (pre++tail) x i p))^2) tail (ha.suffix pre tail)]
  have h := physical_centered_projection_second_le_trace n tail (ha.suffix pre tail) y
    (fun j => (actualSpinPath n (pre++tail) x pre.length p-
      actualSpinPath n (pre++tail) x i p) j)
  simpa only [hm, PiLp.inner_apply, PiLp.sub_apply, PiLp.continuousLinearEquiv_symm_apply,
    RCLike.inner_apply, conj_trivial, EuclideanSpace.real_norm_sq_eq, mul_comm] using h

namespace Hierarchy

section PastWindow

variable {Omega E : Type*} [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {G : Filtration ℕ ‹MeasurableSpace Omega›} {X : ℕ → Omega → E}

theorem terminalScore_sub_identity (N i j : ℕ) (omega : Omega) :
    terminalScore X N j omega-terminalScore X N i omega =
      inner ℝ (X N omega-X j omega) (X j omega-X i omega)+
        (1/2:ℝ)*‖X j omega-X i omega‖^2 := by
  simp only [terminalScore, inner_sub_left, inner_sub_right, norm_sub_sq_real]
  rw [real_inner_comm (X N omega) (X j omega), real_inner_comm (X N omega) (X i omega),
    real_inner_self_eq_norm_sq]
  ring

def orderedScoreNoise (X : ℕ → Omega → E) (N i j : ℕ) (omega : Omega) : ℝ :=
  inner ℝ (X N omega-X (max i j) omega) (X j omega-X i omega)

theorem terminalScore_sub_eq_ordered_noise (N i j : ℕ) (omega : Omega) :
    terminalScore X N j omega-terminalScore X N i omega =
      orderedScoreNoise X N i j omega+
        (if i ≤ j then (1/2:ℝ) else -(1/2:ℝ))*‖X j omega-X i omega‖^2 := by
  by_cases hij : i ≤ j
  · rw [if_pos hij, orderedScoreNoise, max_eq_right hij]
    exact terminalScore_sub_identity N i j omega
  · have hji : j ≤ i := le_of_lt (not_le.mp hij)
    rw [if_neg hij, orderedScoreNoise, max_eq_left hji]
    have h := terminalScore_sub_identity (X := X) N j i omega
    rw [show X i omega-X j omega = -(X j omega-X i omega) by abel,
      inner_neg_right, norm_neg] at h
    linarith

theorem terminalScore_upper_one_sided (N i j : ℕ) (omega : Omega) :
    terminalScore X N i omega-terminalScore X N j omega ≤
      |orderedScoreNoise X N i j omega|+
        (if j < i then (1/2:ℝ)*‖X j omega-X i omega‖^2 else 0) := by
  have h := terminalScore_sub_eq_ordered_noise (X := X) N i j omega
  by_cases hij : i ≤ j
  · rw [if_pos hij] at h
    rw [if_neg (not_lt.mpr hij)]
    linarith [neg_le_abs (orderedScoreNoise X N i j omega), sq_nonneg (‖X j omega-X i omega‖)]
  · rw [if_neg hij] at h
    rw [if_pos (not_le.mp hij)]
    linarith [neg_le_abs (orderedScoreNoise X N i j omega)]

theorem terminalScore_lower_one_sided (N i j : ℕ) (omega : Omega) :
    terminalScore X N j omega-terminalScore X N i omega ≤
      |orderedScoreNoise X N i j omega|+
        (if i < j then (1/2:ℝ)*‖X j omega-X i omega‖^2 else 0) := by
  have h := terminalScore_sub_eq_ordered_noise (X := X) N i j omega
  by_cases hij : i ≤ j
  · rw [if_pos hij] at h
    by_cases hlt : i < j
    · rw [if_pos hlt]
      linarith [le_abs_self (orderedScoreNoise X N i j omega)]
    · have heq : i = j := le_antisymm hij (not_lt.mp hlt)
      subst j
      simp only [sub_self, norm_zero, zero_pow, mul_zero, add_zero, lt_self_iff_false, ite_false]
      exact abs_nonneg _
  · rw [if_neg hij] at h
    rw [if_neg (not_lt.mpr (le_of_lt (not_le.mp hij)))]
    linarith [le_abs_self (orderedScoreNoise X N i j omega), sq_nonneg (‖X j omega-X i omega‖)]

theorem terminalWindow_upper_one_sided {I : Type*} [Fintype I]
    (N i : ℕ) (tau : I → ℕ) (alpha : I → ℝ)
    (halpha0 : ∀ j, 0 ≤ alpha j) (halpha : ∑ j, alpha j = 1) (omega : Omega) :
    terminalScore X N i omega-terminalWindow X N Finset.univ tau alpha omega ≤
      ∑ j, alpha j*(|orderedScoreNoise X N i (tau j) omega|+
        if tau j < i then (1/2:ℝ)*‖X (tau j) omega-X i omega‖^2 else 0) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset I)) fun j _ =>
    mul_le_mul_of_nonneg_left (terminalScore_upper_one_sided (X := X) N i (tau j) omega) (halpha0 j)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, halpha, one_mul] at hsum
  simpa only [terminalWindow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hsum

theorem terminalWindow_lower_one_sided {I : Type*} [Fintype I]
    (N i : ℕ) (tau : I → ℕ) (alpha : I → ℝ)
    (halpha0 : ∀ j, 0 ≤ alpha j) (halpha : ∑ j, alpha j = 1) (omega : Omega) :
    terminalWindow X N Finset.univ tau alpha omega-terminalScore X N i omega ≤
      ∑ j, alpha j*(|orderedScoreNoise X N i (tau j) omega|+
        if i < tau j then (1/2:ℝ)*‖X (tau j) omega-X i omega‖^2 else 0) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset I)) fun j _ =>
    mul_le_mul_of_nonneg_left (terminalScore_lower_one_sided (X := X) N i (tau j) omega) (halpha0 j)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, halpha, one_mul] at hsum
  simpa only [terminalWindow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hsum

theorem weighted_sum_sq_le {I : Type*} [Fintype I]
    (alpha f : I → ℝ) (halpha0 : ∀ j, 0 ≤ alpha j) (halpha : ∑ j, alpha j = 1) :
    (∑ j, alpha j*f j)^2 ≤ ∑ j, alpha j*(f j)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun j => Real.sqrt (alpha j)) (fun j => Real.sqrt (alpha j)*f j)
  have he (j : I) : Real.sqrt (alpha j)*(Real.sqrt (alpha j)*f j) = alpha j*f j := by
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (halpha0 j)]
  simp_rw [he, mul_pow, Real.sq_sqrt (halpha0 _)] at h
  rwa [halpha, one_mul] at h

def upperSideScoreError {I : Type*} [Fintype I] (X : ℕ → Omega → E)
    (N i : ℕ) (tau : I → ℕ) (alpha : I → ℝ) (omega : Omega) : ℝ :=
  ∑ j, alpha j*(|orderedScoreNoise X N i (tau j) omega|+
    if tau j < i then (1/2:ℝ)*‖X (tau j) omega-X i omega‖^2 else 0)

def lowerSideScoreError {I : Type*} [Fintype I] (X : ℕ → Omega → E)
    (N i : ℕ) (tau : I → ℕ) (alpha : I → ℝ) (omega : Omega) : ℝ :=
  ∑ j, alpha j*(|orderedScoreNoise X N i (tau j) omega|+
    if i < tau j then (1/2:ℝ)*‖X (tau j) omega-X i omega‖^2 else 0)

theorem upperSideScoreError_nonneg {I : Type*} [Fintype I]
    (N i : ℕ) (tau : I → ℕ) (alpha : I → ℝ) (halpha0 : ∀ j, 0 ≤ alpha j) (omega : Omega) :
    0 ≤ upperSideScoreError X N i tau alpha omega := by
  unfold upperSideScoreError
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (halpha0 j)
  apply add_nonneg (abs_nonneg _)
  split_ifs <;> positivity

theorem lowerSideScoreError_nonneg {I : Type*} [Fintype I]
    (N i : ℕ) (tau : I → ℕ) (alpha : I → ℝ) (halpha0 : ∀ j, 0 ≤ alpha j) (omega : Omega) :
    0 ≤ lowerSideScoreError X N i tau alpha omega := by
  unfold lowerSideScoreError
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (halpha0 j)
  apply add_nonneg (abs_nonneg _)
  split_ifs <;> positivity

theorem terminalWindow_two_sided_score_bound {I : Type*} [Fintype I]
    (N i : ℕ) (taum taup : I → ℕ) (alpham alphap : I → ℝ)
    (hm0 : ∀ j, 0 ≤ alpham j) (hp0 : ∀ j, 0 ≤ alphap j)
    (hm : ∑ j, alpham j = 1) (hp : ∑ j, alphap j = 1)
    {S cm cp eta : ℝ} (hcm : |cm-S| ≤ eta) (hcp : |cp-S| ≤ eta) (omega : Omega) :
    |terminalScore X N i omega-S| ≤
      |terminalWindow X N Finset.univ taum alpham omega-cm|+
        |terminalWindow X N Finset.univ taup alphap omega-cp|+eta+
        lowerSideScoreError X N i taum alpham omega+
        upperSideScoreError X N i taup alphap omega := by
  have hmcmp := terminalWindow_lower_one_sided (X := X) N i taum alpham hm0 hm omega
  have hpcmp := terminalWindow_upper_one_sided (X := X) N i taup alphap hp0 hp omega
  change terminalWindow X N Finset.univ taum alpham omega-terminalScore X N i omega ≤
    lowerSideScoreError X N i taum alpham omega at hmcmp
  change terminalScore X N i omega-terminalWindow X N Finset.univ taup alphap omega ≤
    upperSideScoreError X N i taup alphap omega at hpcmp
  obtain ⟨hmlo, hmhi⟩ := abs_le.mp hcm
  obtain ⟨hplo, hphi⟩ := abs_le.mp hcp
  have hnEm := lowerSideScoreError_nonneg (X := X) N i taum alpham hm0 omega
  have hnEp := upperSideScoreError_nonneg (X := X) N i taup alphap hp0 omega
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs (terminalWindow X N Finset.univ taum alpham omega-cm),
      abs_nonneg (terminalWindow X N Finset.univ taup alphap omega-cp)]
  · linarith [le_abs_self (terminalWindow X N Finset.univ taup alphap omega-cp),
      abs_nonneg (terminalWindow X N Finset.univ taum alpham omega-cm)]

theorem upperSideScoreError_sq_le {I : Type*} [Fintype I]
    (N i : ℕ) (tau : I → ℕ) (alpha : I → ℝ)
    (halpha0 : ∀ j, 0 ≤ alpha j) (halpha : ∑ j, alpha j = 1) (omega : Omega) :
    (upperSideScoreError X N i tau alpha omega)^2 ≤
      ∑ j, alpha j*(2*(orderedScoreNoise X N i (tau j) omega)^2+
        if tau j < i then (1/2:ℝ)*‖X (tau j) omega-X i omega‖^4 else 0) := by
  apply (weighted_sum_sq_le alpha _ halpha0 halpha).trans
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (halpha0 j)
  split_ifs
  · nlinarith [sq_abs (orderedScoreNoise X N i (tau j) omega),
      sq_nonneg (|orderedScoreNoise X N i (tau j) omega|-
        (1/2:ℝ)*‖X (tau j) omega-X i omega‖^2)]
  · simp only [add_zero, sq_abs]
    nlinarith [sq_nonneg (orderedScoreNoise X N i (tau j) omega)]

theorem lowerSideScoreError_sq_le {I : Type*} [Fintype I]
    (N i : ℕ) (tau : I → ℕ) (alpha : I → ℝ)
    (halpha0 : ∀ j, 0 ≤ alpha j) (halpha : ∑ j, alpha j = 1) (omega : Omega) :
    (lowerSideScoreError X N i tau alpha omega)^2 ≤
      ∑ j, alpha j*(2*(orderedScoreNoise X N i (tau j) omega)^2+
        if i < tau j then (1/2:ℝ)*‖X (tau j) omega-X i omega‖^4 else 0) := by
  apply (weighted_sum_sq_le alpha _ halpha0 halpha).trans
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (halpha0 j)
  split_ifs
  · nlinarith [sq_abs (orderedScoreNoise X N i (tau j) omega),
      sq_nonneg (|orderedScoreNoise X N i (tau j) omega|-
        (1/2:ℝ)*‖X (tau j) omega-X i omega‖^2)]
  · simp only [add_zero, sq_abs]
    nlinarith [sq_nonneg (orderedScoreNoise X N i (tau j) omega)]

theorem terminalWindow_two_sided_score_square_bound {I : Type*} [Fintype I]
    (N i : ℕ) (taum taup : I → ℕ) (alpham alphap : I → ℝ)
    (hm0 : ∀ j, 0 ≤ alpham j) (hp0 : ∀ j, 0 ≤ alphap j)
    (hm : ∑ j, alpham j = 1) (hp : ∑ j, alphap j = 1)
    {S cm cp eta : ℝ} (heta : 0 ≤ eta)
    (hcm : |cm-S| ≤ eta) (hcp : |cp-S| ≤ eta) (omega : Omega) :
    (terminalScore X N i omega-S)^2 ≤
      6*(terminalWindow X N Finset.univ taum alpham omega-cm)^2+
      6*(terminalWindow X N Finset.univ taup alphap omega-cp)^2+6*eta^2+
      4*(∑ j, alpham j*(2*(orderedScoreNoise X N i (taum j) omega)^2+
        if i < taum j then (1/2:ℝ)*‖X (taum j) omega-X i omega‖^4 else 0))+
      4*(∑ j, alphap j*(2*(orderedScoreNoise X N i (taup j) omega)^2+
        if taup j < i then (1/2:ℝ)*‖X (taup j) omega-X i omega‖^4 else 0)) := by
  let a := |terminalWindow X N Finset.univ taum alpham omega-cm|
  let b := |terminalWindow X N Finset.univ taup alphap omega-cp|
  let em := lowerSideScoreError X N i taum alpham omega
  let ep := upperSideScoreError X N i taup alphap omega
  have hnEm : 0 ≤ em := lowerSideScoreError_nonneg (X := X) N i taum alpham hm0 omega
  have hnEp : 0 ≤ ep := upperSideScoreError_nonneg (X := X) N i taup alphap hp0 omega
  have h := terminalWindow_two_sided_score_bound (X := X) N i taum taup alpham alphap
    hm0 hp0 hm hp hcm hcp omega
  have hsq := pow_le_pow_left₀ (abs_nonneg (terminalScore X N i omega-S)) h 2
  change |terminalScore X N i omega-S|^2 ≤ (a+b+eta+em+ep)^2 at hsq
  rw [sq_abs] at hsq
  have hs : (a+b+eta+em+ep)^2 ≤ 6*a^2+6*b^2+6*eta^2+4*em^2+4*ep^2 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a-eta), sq_nonneg (b-eta),
      sq_nonneg (em-ep), sq_nonneg (a+b+eta-(em+ep))]
  have hem := lowerSideScoreError_sq_le (X := X) N i taum alpham hm0 hm omega
  have hep := upperSideScoreError_sq_le (X := X) N i taup alphap hp0 hp omega
  dsimp only [a, b, em, ep] at hs hsq
  simp only [sq_abs] at hs
  linarith

def terminalMeanProjection (X : ℕ → Omega → E) (N i : ℕ) (c : ℝ) (omega : Omega) : ℝ :=
  inner ℝ (X i omega) (X N omega)-c

theorem terminalMeanProjection_memLp (hX : Martingale X G mu) {R : ℝ}
    (hR : ∀ j, ∀ᵐ omega ∂mu, ‖X j omega‖ ≤ R) (N i : ℕ) (c : ℝ) (p : ℝ≥0∞) :
    MemLp (terminalMeanProjection X N i c) p mu := by
  have hmeas (j) := (hX.stronglyAdapted j).mono (G.le j)
  apply MemLp.of_bound (((hmeas i).aestronglyMeasurable.inner
    (hmeas N).aestronglyMeasurable).sub aestronglyMeasurable_const) (R^2+|c|)
  filter_upwards [hR i, hR N] with omega hi hN
  calc
    ‖terminalMeanProjection X N i c omega‖ ≤
        ‖inner ℝ (X i omega) (X N omega)‖+|c| := norm_sub_le _ _
    _ ≤ ‖X i omega‖*‖X N omega‖+|c| := by gcongr; exact norm_inner_le_norm _ _
    _ ≤ R^2+|c| := by
      have hR0 : 0 ≤ R := (norm_nonneg _).trans hi
      have h := mul_le_mul hi hN (norm_nonneg _) hR0
      nlinarith

theorem condExp_terminalMeanProjection (hX : Martingale X G mu) {R : ℝ}
    (hR : ∀ j, ∀ᵐ omega ∂mu, ‖X j omega‖ ≤ R) {N i j : ℕ}
    (hij : i ≤ j) (hjN : j ≤ N) (c : ℝ) :
    mu[terminalMeanProjection X N i c | G j] =ᵐ[mu]
      terminalMeanProjection X j i c := by
  let A := fun omega => inner ℝ (X i omega) (X N omega)
  have hA : Integrable A mu := by
    have h := (terminalMeanProjection_memLp hX hR N i 0 1).integrable le_rfl
    change Integrable (fun omega => inner ℝ (X i omega) (X N omega)-0) mu at h
    simpa only [sub_zero] using h
  have hmeas : StronglyMeasurable[G j] (X i) := (hX.stronglyAdapted i).mono (G.mono hij)
  have hpull : mu[A | G j] =ᵐ[mu]
      fun omega => inner ℝ (X i omega) (mu[X N | G j] omega) :=
    condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hmeas hA (hX.integrable N)
  have he : terminalMeanProjection X N i c = A-(fun _ => c) := rfl
  rw [he]
  filter_upwards [condExp_sub hA (integrable_const c) (G j), hpull,
    hX.condExp_ae_eq hjN] with omega h1 h2 h3
  simp only [Pi.sub_apply] at h1
  rw [h1, condExp_const (G.le j), h2, h3]
  rfl

theorem terminalMeanProjection_moment_contract [IsProbabilityMeasure mu]
    (hX : Martingale X G mu) {R : ℝ}
    (hR : ∀ j, ∀ᵐ omega ∂mu, ‖X j omega‖ ≤ R) {N i j : ℕ}
    (hij : i ≤ j) (hjN : j ≤ N) (c : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    momentNorm mu (terminalMeanProjection X j i c) p ≤
      momentNorm mu (terminalMeanProjection X N i c) p := by
  have h := momentNorm_condExp_le (terminalMeanProjection X N i c) hp
    (terminalMeanProjection_memLp hX hR N i c (ENNReal.ofReal p)) (G j)
  have he := condExp_terminalMeanProjection hX hR hij hjN c
  unfold momentNorm at h ⊢
  rw [eLpNorm_congr_ae he] at h
  exact h

theorem condExp_terminalScore_past (hX : Martingale X G mu) {R : ℝ}
    (hR : ∀ j, ∀ᵐ omega ∂mu, ‖X j omega‖ ≤ R) {N i j : ℕ}
    (hji : j ≤ i) (hiN : i ≤ N) :
    mu[terminalScore X N j | G i] =ᵐ[mu]
      fun omega => (1/2:ℝ) * ‖X i omega‖^2 -
        (1/2:ℝ) * ‖X i omega - X j omega‖^2 := by
  let A : Omega → ℝ := fun omega => inner ℝ (X j omega) (X N omega)
  let U : Omega → ℝ := fun omega => ‖X j omega‖^2
  have hU : Integrable U mu := (boundedMartingale_sq_submartingale hX hR).integrable j
  have hA : Integrable A mu := by
    apply ((terminalScore_integrable hX hR N j).add (hU.smul (1/2:ℝ))).congr
    exact Eventually.of_forall fun omega => by dsimp [A, U, terminalScore]; ring
  have hmeas : StronglyMeasurable[G i] (X j) :=
    (hX.stronglyAdapted j).mono (G.mono hji)
  have hpull : mu[A | G i] =ᵐ[mu]
      fun omega => inner ℝ (X j omega) (mu[X N | G i] omega) :=
    condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hmeas hA (hX.integrable N)
  have hfix : mu[U | G i] = U := condExp_of_stronglyMeasurable (G.le i)
    (hmeas.norm.pow 2) hU
  have he : terminalScore X N j = A - (1/2:ℝ) • U := rfl
  rw [he]
  filter_upwards [condExp_sub hA (hU.smul (1/2:ℝ)) (G i),
    condExp_smul (μ := mu) (1/2:ℝ) U (G i), hpull,
    hX.condExp_ae_eq hiN] with omega h1 h2 h3 h4
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [h1, h2, h3, h4, hfix]
  dsimp [U]
  rw [norm_sub_sq_real, real_inner_comm]
  ring

theorem condExp_terminalWindow_past (hX : Martingale X G mu) {R : ℝ}
    (hR : ∀ j, ∀ᵐ omega ∂mu, ‖X j omega‖ ≤ R)
    {I : Type*} [Fintype I] [DecidableEq I] {N i : ℕ} {J : Finset I}
    (tau : I → ℕ) (alpha : I → ℝ) (halpha : ∑ j ∈ J, alpha j = 1)
    (hJ : ∀ j ∈ J, alpha j ≠ 0 → tau j ≤ i) (hiN : i ≤ N) :
    mu[terminalWindow X N J tau alpha | G i] =ᵐ[mu]
      fun omega => (1/2:ℝ) * ‖X i omega‖^2 -
        (1/2:ℝ) * ∑ j ∈ J, alpha j * ‖X i omega - X (tau j) omega‖^2 := by
  have hsum := condExp_finsetSum (s := J)
    (f := fun j => alpha j • terminalScore X N (tau j))
    (fun j _ => (terminalScore_integrable hX hR N (tau j)).const_mul (alpha j)) (G i)
  have hall : ∀ᵐ omega ∂mu, ∀ j ∈ J,
      mu[alpha j • terminalScore X N (tau j) | G i] omega =
        alpha j * ((1/2:ℝ) * ‖X i omega‖^2 -
          (1/2:ℝ) * ‖X i omega - X (tau j) omega‖^2) := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j ∈ J
    · by_cases hazero : alpha j = 0
      · exact Eventually.of_forall fun _ _ => by simp [hazero]
      · filter_upwards [condExp_smul (μ := mu) (alpha j) (terminalScore X N (tau j)) (G i),
          condExp_terminalScore_past hX hR (hJ j hj hazero) hiN] with omega h1 h2
        intro _
        rw [h1]
        change alpha j * mu[terminalScore X N (tau j) | G i] omega = _
        rw [h2]
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  filter_upwards [hsum, hall] with omega h1 h2
  change (mu[∑ j ∈ J, alpha j • terminalScore X N (tau j) | G i]) omega = _
  rw [h1]
  simp only [Finset.sum_apply]
  have hsum' : (∑ j ∈ J, mu[alpha j • terminalScore X N (tau j) | G i] omega) =
      ∑ j ∈ J, alpha j * ((1/2:ℝ) * ‖X i omega‖^2 -
        (1/2:ℝ) * ‖X i omega - X (tau j) omega‖^2) :=
    Finset.sum_congr rfl fun j hj => h2 j hj
  rw [hsum']
  have heq (j : I) : alpha j * ((1/2:ℝ) * ‖X i omega‖^2 -
      (1/2:ℝ) * ‖X i omega - X (tau j) omega‖^2) =
      alpha j * ((1/2:ℝ) * ‖X i omega‖^2) -
        (1/2:ℝ) * (alpha j * ‖X i omega - X (tau j) omega‖^2) := by ring
  simp_rw [heq, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, halpha]
  ring

theorem condExp_past_window_le_sqnorm (hX : Martingale X G mu) {R : ℝ}
    (hR : ∀ j, ∀ᵐ omega ∂mu, ‖X j omega‖ ≤ R)
    {I : Type*} [Fintype I] [DecidableEq I] {N i : ℕ} {J : Finset I}
    (tau : I → ℕ) (alpha : I → ℝ)
    (halpha0 : ∀ j ∈ J, 0 ≤ alpha j) (halpha : ∑ j ∈ J, alpha j = 1)
    (hJ : ∀ j ∈ J, alpha j ≠ 0 → tau j ≤ i) (hiN : i ≤ N) :
    (fun omega => 2 * mu[terminalWindow X N J tau alpha | G i] omega) ≤ᵐ[mu]
      fun omega => ‖X i omega‖^2 := by
  filter_upwards [condExp_terminalWindow_past hX hR tau alpha halpha hJ hiN]
    with omega h
  rw [h]
  have hn : 0 ≤ ∑ j ∈ J, alpha j * ‖X i omega - X (tau j) omega‖^2 :=
    Finset.sum_nonneg fun j hj => mul_nonneg (halpha0 j hj) (sq_nonneg _)
  linarith

end PastWindow

section BufferedMoments

variable {Omega : Type*} [m0 : MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]

theorem momentNorm_add_le {f g : Omega → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) mu) (hg : MemLp g (ENNReal.ofReal p) mu) :
    momentNorm mu (fun omega => f omega + g omega) p ≤
      momentNorm mu f p + momentNorm mu g p := by
  have hpc : 1 ≤ ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have h := eLpNorm_add_le (f := f) (g := g) (μ := mu) hpc
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩) h
  simpa only [momentNorm, Pi.add_def, ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using ht

theorem momentNorm_abs {f : Omega → ℝ} {p : ℝ}
    (hf : MemLp f (ENNReal.ofReal p) mu) :
    momentNorm mu (fun omega => |f omega|) p = momentNorm mu f p := by
  unfold momentNorm
  simpa only [Real.norm_eq_abs] using congrArg ENNReal.toReal
    (eLpNorm_norm f hf.aestronglyMeasurable)

theorem momentNorm_const (c : ℝ) {p : ℝ} (hp : 0 < p) :
    momentNorm mu (fun _ : Omega => c) p = |c| := by
  simp [momentNorm, eLpNorm_const c (ENNReal.ofReal_ne_zero_iff.mpr hp)
    (NeZero.ne mu), enorm_eq_nnnorm]

theorem movement_moment_le_terminal_defects {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {G : Filtration ℕ m0} {X : ℕ → Omega → E}
    (hX : Martingale X G mu) {R : ℝ}
    (hR : ∀ j, ∀ᵐ omega ∂mu, ‖X j omega‖ ≤ R)
    {N i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N)
    (Si Sj : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    momentNorm mu (fun omega => ‖X j omega-X i omega‖^2) p ≤
      |Sj-Si|+momentNorm mu (fun omega => ‖X i omega‖^2-Si) p+
        momentNorm mu (fun omega => ‖X j omega‖^2-Sj) p+
          2*momentNorm mu (terminalMeanProjection X N i Si) p := by
  have hQ (k) : MemLp (fun omega => ‖X k omega‖^2) (ENNReal.ofReal p) mu := by
    apply MemLp.of_bound (((hX.stronglyAdapted k).mono (G.le k)).norm.pow 2).aestronglyMeasurable (R^2)
    filter_upwards [hR k] with omega hk
    change ‖‖X k omega‖^2‖ ≤ R^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hk 2
  let A := fun omega => ‖X j omega‖^2-Sj
  let B := fun omega => ‖X i omega‖^2-Si
  let C := terminalMeanProjection X j i Si
  have hA : MemLp A (ENNReal.ofReal p) mu := (hQ j).sub (memLp_const Sj)
  have hB : MemLp B (ENNReal.ofReal p) mu := (hQ i).sub (memLp_const Si)
  have hC := terminalMeanProjection_memLp hX hR j i Si (ENNReal.ofReal p)
  have he : (fun omega => ‖X j omega-X i omega‖^2) =
      fun omega => (A omega+B omega)+(-2)*C omega+(Sj-Si) := by
    funext omega
    dsimp only [A, B, C, terminalMeanProjection]
    rw [norm_sub_sq_real, real_inner_comm]
    ring
  have h1 := momentNorm_add_le hp hA hB
  have h2 := momentNorm_add_le hp (hA.add hB) (hC.const_mul (-2))
  have h3 := momentNorm_add_le hp ((hA.add hB).add (hC.const_mul (-2))) (memLp_const (Sj-Si))
  have hc : momentNorm mu (fun omega => (-2)*C omega) p=2*momentNorm mu C p := by
    simpa only [Pi.smul_def, smul_eq_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<2)] using
      momentNorm_smul (μ := mu) C (-2) p
  rw [hc] at h2
  rw [momentNorm_const (Sj-Si) (by linarith)] at h3
  have hcontract := terminalMeanProjection_moment_contract hX hR hij hjN Si hp
  rw [he]
  simp only [Pi.add_def, A, B, C] at h1 h2 h3 ⊢
  linarith

theorem buffered_conditional_sandwich_moment
    (G : MeasurableSpace Omega) (hG : G ≤ m0)
    (Q Aminus Aplus : Omega → ℝ) {p S eta cminus cplus : ℝ}
    (hp : 1 ≤ p) (heta : 0 ≤ eta)
    (hAm : Integrable Aminus mu) (hAp : Integrable Aplus mu)
    (hLm : MemLp Aminus (ENNReal.ofReal p) mu)
    (hLp : MemLp Aplus (ENNReal.ofReal p) mu)
    (hlo : (fun omega => 2 * mu[Aminus | G] omega) ≤ᵐ[mu] Q)
    (hhi : Q ≤ᵐ[mu] fun omega => 2 * mu[Aplus | G] omega)
    (hcminus : |2 * cminus - S| ≤ eta) (hcplus : |2 * cplus - S| ≤ eta) :
    @momentNorm Omega m0 mu (fun omega => Q omega - S) p ≤
      2 * @momentNorm Omega m0 mu (fun omega => Aminus omega - cminus) p +
        2 * @momentNorm Omega m0 mu (fun omega => Aplus omega - cplus) p + eta := by
  letI : MeasurableSpace Omega := m0
  let fm : Omega → ℝ := fun omega => Aminus omega - cminus
  let fp : Omega → ℝ := fun omega => Aplus omega - cplus
  let Bm := mu[fm | G]
  let Bp := mu[fp | G]
  have hpc : 1 ≤ ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hfm : MemLp fm (ENNReal.ofReal p) mu := hLm.sub (memLp_const cminus)
  have hfp : MemLp fp (ENNReal.ofReal p) mu := hLp.sub (memLp_const cplus)
  have hBm : MemLp Bm (ENNReal.ofReal p) mu := hfm.condExp hpc
  have hBp : MemLp Bp (ENNReal.ofReal p) mu := hfp.condExp hpc
  have hBmabs : MemLp (fun omega => |Bm omega|) (ENNReal.ofReal p) mu := by
    simpa only [Real.norm_eq_abs] using hBm.norm
  have hBpabs : MemLp (fun omega => |Bp omega|) (ENNReal.ofReal p) mu := by
    simpa only [Real.norm_eq_abs] using hBp.norm
  have hbound : MemLp (fun omega => 2 * |Bm omega| + 2 * |Bp omega| + eta)
      (ENNReal.ofReal p) mu := ((hBmabs.const_mul 2).add
        (hBpabs.const_mul 2)).add (memLp_const eta)
  have heminus : Bm =ᵐ[mu] fun omega => mu[Aminus | G] omega - cminus := by
    simpa only [fm, Bm, condExp_const hG cminus, Pi.sub_def, Pi.sub_apply] using
      condExp_sub hAm (integrable_const cminus) G
  have heplus : Bp =ᵐ[mu] fun omega => mu[Aplus | G] omega - cplus := by
    simpa only [fp, Bp, condExp_const hG cplus, Pi.sub_def, Pi.sub_apply] using
      condExp_sub hAp (integrable_const cplus) G
  have hpoint : ∀ᵐ omega ∂mu, ‖Q omega - S‖ ≤
      ‖2 * |Bm omega| + 2 * |Bp omega| + eta‖ := by
    filter_upwards [hlo, hhi, heminus, heplus] with omega h1 h2 hm hp'
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    have ham := abs_le.mp hcminus
    have hap := abs_le.mp hcplus
    have hbm := abs_le.mp (le_refl (|Bm omega|))
    have hbp := abs_le.mp (le_refl (|Bp omega|))
    apply abs_le.mpr
    constructor <;> nlinarith [abs_nonneg (Bm omega), abs_nonneg (Bp omega)]
  have hnorm := momentNorm_le_of_norm_le hbound hpoint
  have hsum := momentNorm_add_le hp
    ((hBmabs.const_mul 2).add (hBpabs.const_mul 2)) (memLp_const eta)
  have htwo := momentNorm_add_le hp (hBmabs.const_mul 2) (hBpabs.const_mul 2)
  have hms : @momentNorm Omega m0 mu (fun omega => 2 * |Bm omega|) p = 2 * @momentNorm Omega m0 mu Bm p := by
    simpa only [Pi.smul_def, smul_eq_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      momentNorm_abs hBm] using momentNorm_smul (μ := mu) (fun omega => |Bm omega|) 2 p
  have hps : @momentNorm Omega m0 mu (fun omega => 2 * |Bp omega|) p = 2 * @momentNorm Omega m0 mu Bp p := by
    simpa only [Pi.smul_def, smul_eq_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      momentNorm_abs hBp] using momentNorm_smul (μ := mu) (fun omega => |Bp omega|) 2 p
  rw [hms, hps] at htwo
  rw [momentNorm_const eta (by linarith), abs_of_nonneg heta] at hsum
  have hcm := momentNorm_condExp_le fm hp hfm G
  have hcp := momentNorm_condExp_le fp hp hfp G
  simp only [Pi.add_def] at hsum
  dsimp only [Bm, Bp, fm, fp] at htwo hnorm hsum
  dsimp only [fm, fp] at hcm hcp
  linarith

theorem past_movement_moment_from_identity
    (G : MeasurableSpace Omega) (hG : G ≤ m0)
    (Q A M : Omega → ℝ) {p S eta c : ℝ}
    (hp : 1 ≤ p) (heta : 0 ≤ eta)
    (hQ : MemLp Q (ENNReal.ofReal p) mu)
    (hA : MemLp A (ENNReal.ofReal p) mu)
    (hM0 : ∀ᵐ z ∂mu, 0 ≤ M z)
    (hid : M =ᵐ[mu] fun z => Q z - 2 * mu[A | G] z)
    (hc : |2*c-S| ≤ eta) :
    @momentNorm Omega m0 mu M p ≤
      @momentNorm Omega m0 mu (fun z => Q z-S) p +
        2 * @momentNorm Omega m0 mu (fun z => A z-c) p + eta := by
  let : MeasurableSpace Omega := m0
  let F : Omega → ℝ := fun z => Q z-S
  let B := mu[(fun z => A z-c) | G]
  have hpc : 1 ≤ ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hF : MemLp F (ENNReal.ofReal p) mu := hQ.sub (memLp_const S)
  have hAc : MemLp (fun z => A z-c) (ENNReal.ofReal p) mu := hA.sub (memLp_const c)
  have hB : MemLp B (ENNReal.ofReal p) mu := hAc.condExp hpc
  have hFa : MemLp (fun z => |F z|) (ENNReal.ofReal p) mu := by
    simpa only [Real.norm_eq_abs] using hF.norm
  have hBa : MemLp (fun z => |B z|) (ENNReal.ofReal p) mu := by
    simpa only [Real.norm_eq_abs] using hB.norm
  have hbound := (hFa.add (hBa.const_mul 2)).add (memLp_const eta)
  have hcenter : B =ᵐ[mu] fun z => mu[A | G] z-c := by
    simpa only [B, condExp_const hG c, Pi.sub_def, Pi.sub_apply] using
      condExp_sub (hA.integrable hpc) (integrable_const c) G
  have hpoint : ∀ᵐ z ∂mu, ‖M z‖ ≤ ‖|F z|+2*|B z|+eta‖ := by
    filter_upwards [hM0, hid, hcenter] with z h0 hi hb
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
    have hf := le_abs_self (F z)
    have hbm := neg_le_abs (B z)
    have hcm := (abs_le.mp hc).1
    dsimp only [F] at hf
    rw [hi]
    nlinarith
  have hnorm := momentNorm_le_of_norm_le hbound hpoint
  have hsum := momentNorm_add_le hp (hFa.add (hBa.const_mul 2)) (memLp_const eta)
  have htwo := momentNorm_add_le hp hFa (hBa.const_mul 2)
  have hbs : @momentNorm Omega m0 mu (fun z => 2*|B z|) p =
      2 * @momentNorm Omega m0 mu B p := by
    simpa only [Pi.smul_def, smul_eq_mul, abs_of_pos (by norm_num : (0:ℝ)<2),
      momentNorm_abs hB] using momentNorm_smul (μ := mu) (fun z => |B z|) 2 p
  rw [hbs, momentNorm_abs hF] at htwo
  rw [momentNorm_const eta (by linarith), abs_of_nonneg heta] at hsum
  have hcontract := momentNorm_condExp_le (fun z => A z-c) hp hAc G
  simp only [Pi.add_def] at hsum hnorm
  dsimp only [B, F] at htwo hnorm hsum
  linarith

theorem central_movement_sq_le_buffer {E : Type*} [NormedAddCommGroup E]
    {I : Type*} [Fintype I] (alpha : I → ℝ) (halpha0 : ∀ j, 0 ≤ alpha j)
    (halpha : ∑ j, alpha j = 1) (a b : E) (Y : I → E) :
    ‖a-b‖^2 ≤ 2 * (∑ j, alpha j * ‖a-Y j‖^2) +
      2 * (∑ j, alpha j * ‖b-Y j‖^2) := by
  have hj (j : I) : ‖a-b‖^2 ≤ 2*‖a-Y j‖^2+2*‖b-Y j‖^2 := by
    have he : a-b = (a-Y j)-(b-Y j) := by abel
    have ht : ‖a-b‖ ≤ ‖a-Y j‖+‖b-Y j‖ := by rw [he]; exact norm_sub_le _ _
    nlinarith [norm_nonneg (a-b), norm_nonneg (a-Y j), norm_nonneg (b-Y j),
      sq_nonneg (‖a-Y j‖-‖b-Y j‖)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hj j) (halpha0 j))
  simp_rw [← Finset.sum_mul, halpha, one_mul] at hs
  calc
    ‖a-b‖^2 ≤ ∑ j, alpha j*(2*‖a-Y j‖^2+2*‖b-Y j‖^2) := hs
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_left_comm (alpha _) 2]
      simp only [← Finset.mul_sum]

end BufferedMoments

end Hierarchy

theorem integral_sqrt_le_sqrt_integral {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {C : Omega → ℝ}
    (hC0 : ∀ z, 0 ≤ C z)
    (hC : MemLp (fun z => Real.sqrt (C z)) 2 mu) :
    (∫ z, Real.sqrt (C z) ∂mu) ≤ Real.sqrt (∫ z, C z ∂mu) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all mu (fun z => Real.sqrt_nonneg (C z)))
    (ae_of_all mu (fun _ => (by norm_num : (0:ℝ) ≤ 1))) (by simpa using hC) (memLp_const (1:ℝ))
  simp only [mul_one, Real.rpow_two, Real.sq_sqrt (hC0 _),
    integral_const, probReal_univ, one_smul] at h
  norm_num only [one_pow, Real.one_rpow, mul_one] at h
  simpa only [Real.sqrt_eq_rpow] using h

theorem momentNorm_two_sq_integral {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {f : Omega → ℝ}
    (hf : MemLp f 2 mu) :
    (momentNorm mu f 2)^2 = ∫ z, (f z)^2 ∂mu := by
  have ha : MemLp (fun z => |f z|) 2 mu := by simpa only [Real.norm_eq_abs] using hf.norm
  rw [← momentNorm_abs (p := (2:ℝ)) (by simpa using hf)]
  have hm := momentNorm_nat_eq (μ := mu) (fun z => abs_nonneg (f z)) (by norm_num : 0 < (2:ℕ)) (by simpa using ha)
  norm_num only [Nat.cast_ofNat] at hm
  rw [hm]
  simp only [sq_abs]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun z => sq_nonneg (f z))]
  norm_num

def physicalCutPairDefectSecond (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (c : ℝ) : ℝ :=
  ∫ z, hierarchyPairMean (uniformWeight n) (finiteFeature n)
    (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail
    (actualCutField pre tail z.1 z.2)
    ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)

theorem physical_norm_centered_moment_le_pair (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) (c : ℝ) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
    let X := actualSpinPath n (pre++tail) id
    momentNorm mu (fun z => ‖X pre.length z‖^2-c) 2 ≤
      Real.sqrt (physicalCutPairDefectSecond n pre tail q0 c) := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
  let X := actualSpinPath n (pre++tail) id
  let y := fun z : PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail) =>
    actualCutField pre tail z.1 z.2
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 (pre++tail) ha
  have hF : MemLp (fun z => ‖X pre.length z‖^2-c) 2 mu :=
    (physical_sqnorm_memLp n (pre++tail) ha id measurable_id mu pre.length 2).sub (memLp_const c)
  have hFI : Integrable (fun z => (‖X pre.length z‖^2-c)^2) mu := by
    simpa [Real.norm_eq_abs] using hF.integrable_norm_rpow (by norm_num) (by norm_num)
  have hD := hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail (ha.suffix pre tail) 0
  have hDI := hD.integrable_comp_measurable (actualCutField_measurable_joint pre tail) (μ := mu)
  have hInt := integral_mono hFI hDI (fun z =>
    physical_norm_centered_le_conditional_pair n pre tail ha id z c)
  rw [← momentNorm_two_sq_integral mu hF] at hInt
  have hs := Real.sqrt_le_sqrt hInt
  rw [Real.sqrt_sq (momentNorm_nonneg (μ := mu) _ _)] at hs
  exact hs

theorem physical_terminal_projection_moment_le_pair (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) (c : ℝ) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
    let X := actualSpinPath n (pre++tail) id
    momentNorm mu (terminalMeanProjection X ((pre++tail).length+1) pre.length c) 2 ≤
      Real.sqrt (physicalCutPairDefectSecond n pre tail q0 c) := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
  let X := actualSpinPath n (pre++tail) id
  let F := terminalMeanProjection X ((pre++tail).length+1) pre.length c
  let G : ℕ → MeasurableSpace (PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail)) :=
    forwardPrefixSpace (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) (pre++tail).length
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 (pre++tail) ha
  have hX := actualSpinPath_rooted_martingale n (pre++tail) ha q0
  have hR (j : ℕ) : ∀ᵐ z ∂mu, ‖X j z‖ ≤ 1 := ae_of_all mu fun z =>
    actualSpinPath_norm_le n (pre++tail) ha id j z
  have hF : MemLp F 2 mu := terminalMeanProjection_memLp hX hR _ _ _ _
  have hFI : Integrable (fun z => (F z)^2) mu := by
    simpa [Real.norm_eq_abs] using hF.integrable_norm_rpow (by norm_num) (by norm_num)
  have hFm : Measurable (fun z => (F z)^2) :=
    (((actualSpinPath_measurable n (pre++tail) ha id measurable_id pre.length).inner
      (actualSpinPath_measurable n (pre++tail) ha id measurable_id ((pre++tail).length+1))).sub_const c).pow_const 2
  have hD := hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail (ha.suffix pre tail) 0
  have hDI := hD.integrable_comp_measurable (actualCutField_measurable_joint pre tail) (μ := mu)
  have hCE : mu[(fun z => (F z)^2) | G pre.length] =ᵐ[mu]
      conditionalPathAverage (uniformWeight n) (finiteFeature n) (pre++tail) id pre.length
        (fun z => (F z)^2) := by
    simpa only [mu, G, rootedHierarchyPathLaw, Kernel.comap_id] using
      condExp_conditionalPathAverage (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha
        (Measure.pi (fun k => gaussianReal 0 (q0 k))) id measurable_id pre.length hFm
        (by simpa only [mu, rootedHierarchyPathLaw, Kernel.comap_id] using hFI)
  have hp : mu[(fun z => (F z)^2) | G pre.length] ≤ᵐ[mu]
      fun z => hierarchyPairMean (uniformWeight n) (finiteFeature n)
        (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail
        (actualCutField pre tail z.1 z.2) := by
    filter_upwards [hCE] with z hz
    rw [hz]
    exact physical_terminal_projection_conditional_le_pair n pre tail ha id z c
  have hInt := integral_mono_ae (integrable_condExp (f := fun z => (F z)^2)) hDI hp
  rw [integral_condExp (forwardPrefixSpace_le _ _ _ _ _),
    ← momentNorm_two_sq_integral mu hF] at hInt
  have hs := Real.sqrt_le_sqrt hInt
  rw [Real.sqrt_sq (momentNorm_nonneg (μ := mu) _ _)] at hs
  exact hs

theorem physical_movement_fourth_moment_le_pair (n : ℕ)
    (pre mid tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 (pre++(mid++tail)))
    (q0 : FeatureIndex n → ℝ≥0) (Si Sj : ℝ) :
    let steps := pre++(mid++tail)
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let X := actualSpinPath n steps id
    momentNorm mu (fun z => ‖X (pre++mid).length z-X pre.length z‖^2) 2 ≤
      |Sj-Si|+3*Real.sqrt (physicalCutPairDefectSecond n pre (mid++tail) q0 Si)+
        Real.sqrt (physicalCutPairDefectSecond n (pre++mid) tail q0 Sj) := by
  dsimp only
  let steps := pre++(mid++tail)
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hX := actualSpinPath_rooted_martingale n steps ha q0
  have hR (j : ℕ) : ∀ᵐ z ∂mu, ‖X j z‖ ≤ 1 := ae_of_all mu fun z =>
    actualSpinPath_norm_le n steps ha id j z
  have hij : pre.length ≤ (pre++mid).length := by simp
  have hjN : (pre++mid).length ≤ steps.length+1 := by simp [steps]; omega
  have hm := movement_moment_le_terminal_defects hX hR hij hjN Si Sj (by norm_num : (1:ℝ)≤2)
  have hi := physical_norm_centered_moment_le_pair n pre (mid++tail) ha q0 Si
  have hp := physical_terminal_projection_moment_le_pair n pre (mid++tail) ha q0 Si
  have ha' : OrderedSteps 0 ((pre++mid)++tail) := by simpa only [List.append_assoc] using ha
  have hj := physical_norm_centered_moment_le_pair n (pre++mid) tail ha' q0 Sj
  dsimp only [steps, mu, X] at hm
  dsimp only at hi hp hj
  rw [List.append_assoc] at hj
  linarith

theorem physical_centered_overlap_integral_le_score (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) (c : ℝ) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
    let X := actualSpinPath n (pre++tail) id
    physicalCutPairDefectSecond n pre tail q0 c ≤
      4*(∫ z, (terminalScore X ((pre++tail).length+1) pre.length z-c/2)^2 ∂mu)+
        (∫ z, physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2) ∂mu) := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
  let X := actualSpinPath n (pre++tail) id
  let F := fun z => (terminalScore X ((pre++tail).length+1) pre.length z-c/2)^2
  let C := fun z : PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail) =>
    physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2)
  let G : ℕ → MeasurableSpace (PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail)) :=
    forwardPrefixSpace (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) (pre++tail).length
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 (pre++tail) ha
  have hX := actualSpinPath_rooted_martingale n (pre++tail) ha q0
  have hR (j : ℕ) : ∀ᵐ z ∂mu, ‖X j z‖ ≤ 1 := ae_of_all mu fun z =>
    actualSpinPath_norm_le n (pre++tail) ha id j z
  have hL : MemLp (fun z => terminalScore X ((pre++tail).length+1) pre.length z-c/2) 2 mu :=
    (terminalScore_memLp hX hR _ _ 2).sub (memLp_const (c/2))
  have hFI : Integrable F mu := by
    simpa [F, Real.norm_eq_abs] using hL.integrable_norm_rpow (by norm_num) (by norm_num)
  have hXm (j) := actualSpinPath_measurable n (pre++tail) ha id measurable_id j
  have hFm : Measurable F := (((hXm pre.length).inner (hXm ((pre++tail).length+1))).sub
    (((hXm pre.length).norm.pow_const 2).const_mul (1/2:ℝ))).sub_const (c/2) |>.pow_const 2
  have hCI := (physicalSpinTraceCovSq_smooth n tail (ha.suffix pre tail)).integrable_comp_measurable
    (actualCutField_measurable_joint pre tail) (μ := mu)
  have hDI := (hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail (ha.suffix pre tail) 0).integrable_comp_measurable
      (actualCutField_measurable_joint pre tail) (μ := mu)
  have hCE : mu[F | G pre.length] =ᵐ[mu]
      conditionalPathAverage (uniformWeight n) (finiteFeature n) (pre++tail) id pre.length F := by
    simpa only [mu, G, rootedHierarchyPathLaw, Kernel.comap_id] using
      condExp_conditionalPathAverage (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha
        (Measure.pi (fun k => gaussianReal 0 (q0 k))) id measurable_id pre.length hFm
        (by simpa only [mu, rootedHierarchyPathLaw, Kernel.comap_id] using hFI)
  have hp : (fun z => hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail
      (actualCutField pre tail z.1 z.2)) ≤ᵐ[mu]
        fun z => 4*mu[F | G pre.length] z+C z := by
    filter_upwards [hCE] with z hz
    rw [hz]
    exact physical_centered_overlap_le_conditional_score n pre tail ha id z c
  have hInt := integral_mono_ae hDI ((integrable_condExp (f := F)).const_mul 4 |>.add hCI) hp
  have hadd := integral_add ((integrable_condExp (f := F) (m := G pre.length)).const_mul 4) hCI
  simp only [Pi.add_apply] at hInt hadd
  rw [hadd, integral_const_mul, integral_condExp (forwardPrefixSpace_le _ _ _ _ _)] at hInt
  exact hInt

theorem physical_prefix_centered_overlap_integral (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) (c : ℝ) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
    let X := actualSpinPath n (pre++tail) id
    let C := fun z => physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2)
    (∫ z, hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail
      (actualCutField pre tail z.1 z.2) ∂mu) ≤
      (momentNorm mu (fun z => ‖X pre.length z‖^2-c) 2)^2+
        2*Real.sqrt (∫ z, C z ∂mu)+(∫ z, C z ∂mu) := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
  let X := actualSpinPath n (pre++tail) id
  let y := fun z : ((FeatureIndex n → ℝ) × ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length) =>
    actualCutField pre tail z.1 z.2
  let C := fun z => physicalSpinTraceCovSq n tail (y z)
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 (pre++tail) ha
  have htail := ha.suffix pre tail
  have hy : Measurable y := actualCutField_measurable_joint pre tail
  have hC0 (z) : 0 ≤ C z := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hCs := physicalSpinTraceCovSq_smooth n tail htail
  have hCI : Integrable C mu := hCs.integrable_comp_measurable hy
  have hCroot : MemLp (fun z => Real.sqrt (C z)) 2 mu := by
    obtain ⟨B, hB0, hB⟩ := hCs.bound
    apply MemLp.of_bound ((hCs.continuous.measurable.comp hy).sqrt).aestronglyMeasurable (Real.sqrt B)
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self (C z)).trans (by simpa only [Real.norm_eq_abs] using hB (y z)))
  have hF : MemLp (fun z => ‖X pre.length z‖^2-c) 2 mu :=
    (physical_sqnorm_memLp n (pre++tail) ha id measurable_id mu pre.length 2).sub (memLp_const c)
  have hFI : Integrable (fun z => (‖X pre.length z‖^2-c)^2) mu := by
    simpa [Real.norm_eq_abs] using hF.integrable_norm_rpow (by norm_num) (by norm_num)
  have hD := hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail htail 0
  have hDI := hD.integrable_comp_measurable hy (μ := mu)
  have hpoint (z) : hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail (y z) ≤
      (‖X pre.length z‖^2-c)^2+2*Real.sqrt (C z)+C z := by
    have h := physical_centered_overlap_le_norm_and_trace n tail htail (y z) c
    have he : (∑ i, (actualSpinMean n tail (y z) i)^2) = ‖X pre.length z‖^2 := by
      rw [actualSpinPath_norm_sq_at_cut n pre tail ha]
      rw [hierarchyPairMean_overlap_eq_norm n tail htail]
      simp only [EuclideanSpace.real_norm_sq_eq, actualSpinMean, y]
    rw [he] at h
    exact h
  have hInt := integral_mono hDI ((hFI.add (hCroot.integrable (by norm_num) |>.const_mul 2)).add hCI) hpoint
  simp only [Pi.add_apply] at hInt
  have hAdd1 := integral_add (hFI.add (hCroot.integrable (by norm_num) |>.const_mul 2)) hCI
  have hAdd2 := integral_add hFI (hCroot.integrable (by norm_num) |>.const_mul 2)
  simp only [Pi.add_apply] at hAdd1 hAdd2
  rw [hAdd1, hAdd2, integral_const_mul, ← momentNorm_two_sq_integral mu hF] at hInt
  have hroot := integral_sqrt_le_sqrt_integral mu hC0 hCroot
  dsimp only [X, C, y, mu] at hInt hroot
  linarith

theorem physical_ordered_noise_integral_le_trace (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) {i : ℕ} (hi : i ≤ pre.length) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
    let X := actualSpinPath n (pre++tail) id
    (∫ z, (inner ℝ (X ((pre++tail).length+1) z-X pre.length z)
      (X pre.length z-X i z))^2 ∂mu) ≤
      Real.sqrt (∫ z, physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2) ∂mu)*
        Real.sqrt (∫ z, ‖X pre.length z-X i z‖^4 ∂mu) := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
  let X := actualSpinPath n (pre++tail) id
  let C := fun z : PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail) =>
    physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2)
  let F := fun z => (inner ℝ (X ((pre++tail).length+1) z-X pre.length z)
    (X pre.length z-X i z))^2
  let V := fun z => ‖X pre.length z-X i z‖^2
  let G : ℕ → MeasurableSpace (PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail)) :=
    forwardPrefixSpace (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) (pre++tail).length
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 (pre++tail) ha
  have hX (j : ℕ) : Measurable (X j) := actualSpinPath_measurable n (pre++tail) ha id measurable_id j
  have hbound (j k : ℕ) (z) : ‖X j z-X k z‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have hj := actualSpinPath_norm_le n (pre++tail) ha id j z
      have hk := actualSpinPath_norm_le n (pre++tail) ha id k z
      linarith)
  have hFm : Measurable F := (((hX _).sub (hX _)).inner ((hX _).sub (hX _))).pow_const 2
  have hFI : Integrable F mu := by
    apply Integrable.of_bound hFm.aestronglyMeasurable 16
    filter_upwards [] with z
    change ‖(inner ℝ _ _)^2‖ ≤ 16
    rw [norm_pow, Real.norm_eq_abs]
    have h := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hbound ((pre++tail).length+1) pre.length z)
        (hbound pre.length i z) (norm_nonneg _) (by norm_num))
    nlinarith [abs_nonneg (inner ℝ (X ((pre++tail).length+1) z-X pre.length z)
      (X pre.length z-X i z))]
  have hV : MemLp V 2 mu := by
    apply MemLp.of_bound (((hX pre.length).sub (hX i)).norm.pow_const 2).aestronglyMeasurable 4
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    change ‖X pre.length z-X i z‖^2 ≤ 4
    nlinarith [hbound pre.length i z, norm_nonneg (X pre.length z-X i z)]
  have hC0 (z) : 0 ≤ C z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hCs := physicalSpinTraceCovSq_smooth n tail (ha.suffix pre tail)
  have hy := actualCutField_measurable_joint (S := Spin n) pre tail
  have hCr : MemLp (fun z => Real.sqrt (C z)) 2 mu := by
    obtain ⟨B, hB0, hB⟩ := hCs.bound
    apply MemLp.of_bound ((hCs.continuous.measurable.comp hy).sqrt).aestronglyMeasurable (Real.sqrt B)
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self (C z)).trans
      (by simpa only [C, Real.norm_eq_abs] using hB (actualCutField pre tail z.1 z.2)))
  have hCE : mu[F | G pre.length] =ᵐ[mu]
      conditionalPathAverage (uniformWeight n) (finiteFeature n) (pre++tail) id pre.length F := by
    simpa only [mu, G, rootedHierarchyPathLaw, Kernel.comap_id] using
      condExp_conditionalPathAverage (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha
        (Measure.pi (fun k => gaussianReal 0 (q0 k))) id measurable_id pre.length hFm
        (by simpa only [mu, rootedHierarchyPathLaw, Kernel.comap_id] using hFI)
  have hpoint : mu[F | G pre.length] ≤ᵐ[mu] fun z => V z*Real.sqrt (C z) := by
    filter_upwards [hCE] with z hz
    rw [hz]
    exact physical_ordered_noise_conditional_le_trace n pre tail ha id hi z
  have hInt := integral_mono_ae (integrable_condExp (f := F))
    (hV.integrable_mul hCr) hpoint
  rw [integral_condExp (forwardPrefixSpace_le _ _ _ _ _)] at hInt
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all mu fun z => sq_nonneg (‖X pre.length z-X i z‖))
    (ae_of_all mu fun z => Real.sqrt_nonneg (C z)) (by simpa using hV) (by simpa using hCr)
  simp only [Real.rpow_two, Real.sq_sqrt (hC0 _)] at hCS
  have hpow (z) : (‖X pre.length z-X i z‖^2)^2 = ‖X pre.length z-X i z‖^4 := by ring
  simp only [V, hpow] at hCS
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  dsimp only [F, X, mu, V, C] at hInt hCS
  exact hInt.trans (hCS.trans_eq (mul_comm _ _))

theorem physicalPinnedPair_past_identity (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : Fin (steps.length + 1) → ℝ)
    (hnorm : ∑ j, pathMassDifferences steps 0 j * k j = 1)
    {i : ℕ} (hiN : i ≤ steps.length + 1)
    (hi : ∀ j, pathMassDifferences steps 0 j * k j ≠ 0 → j.val ≤ i) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let G := forwardFiltration (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) steps.length
    let X := actualSpinPath n steps id
    mu[(fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1) | G i] =ᵐ[mu]
      fun z => (1/2:ℝ) * ‖X i z‖^2 -
        (1/2:ℝ) * ∑ j : Fin (steps.length + 1),
          (pathMassDifferences steps 0 j * k j) * ‖X i z - X j.val z‖^2 := by
  dsimp only
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have he : (fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1) =
      terminalWindow (actualSpinPath n steps id) (steps.length + 1) Finset.univ Fin.val
        (fun j => pathMassDifferences steps 0 j * k j) := by
    funext z
    exact physicalPinnedPair_fst_eq_window n steps ha k id z
  rw [he]
  exact condExp_terminalWindow_past (actualSpinPath_rooted_martingale n steps ha q0)
    (R := 1) (fun j => Eventually.of_forall fun z => actualSpinPath_norm_le n steps ha id j z)
    Fin.val (fun j => pathMassDifferences steps 0 j * k j) hnorm (fun j _ => hi j) hiN

theorem physical_buffered_norm_concentration (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (km kp : Fin (steps.length + 1) → ℝ)
    (hkm : ∀ j, 0 ≤ km j) (hkp : ∀ j, 0 ≤ kp j)
    (hnormm : ∑ j, pathMassDifferences steps 0 j * km j = 1)
    (hnormp : ∑ j, pathMassDifferences steps 0 j * kp j = 1)
    {i : ℕ} (hiN : i ≤ steps.length + 1)
    (him : ∀ j, pathMassDifferences steps 0 j * km j ≠ 0 → j.val ≤ i)
    (hip : ∀ j, pathMassDifferences steps 0 j * kp j ≠ 0 → i ≤ j.val)
    {p S eta : ℝ} (hp : 1 ≤ p) (heta : 0 ≤ eta)
    (hmeanm : |(∑ j, (pathMassDifferences steps 0 j * km j) *
        physicalPathSecondMoment n steps q0 j.val) - S| ≤ eta)
    (hmeanp : |(∑ j, (pathMassDifferences steps 0 j * kp j) *
        physicalPathSecondMoment n steps q0 j.val) - S| ≤ eta) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let Am := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 km z.1 z.2).1
    let Ap := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 kp z.1 z.2).1
    momentNorm mu (fun z => ‖actualSpinPath n steps id i z‖^2 - S) p ≤
      2 * momentNorm mu (fun z => Am z - ∫ w, Am w ∂mu) p +
        2 * momentNorm mu (fun z => Ap z - ∫ w, Ap w ∂mu) p + eta := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let G := forwardFiltration (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) steps.length
  let X := actualSpinPath n steps id
  let Am : ((FeatureIndex n → ℝ) × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) → ℝ :=
    fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
    (spinSource n) steps 0 km z.1 z.2).1
  let Ap : ((FeatureIndex n → ℝ) × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) → ℝ :=
    fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
    (spinSource n) steps 0 kp z.1 z.2).1
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hLm : MemLp Am (ENNReal.ofReal p) mu :=
    physicalPinnedPair_fst_memLp n steps ha q0 km _
  have hLp : MemLp Ap (ENNReal.ofReal p) mu :=
    physicalPinnedPair_fst_memLp n steps ha q0 kp _
  have hpc : 1 ≤ ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hlo : (fun z => 2 * mu[Am | G i] z) ≤ᵐ[mu] fun z => ‖X i z‖^2 := by
    filter_upwards [physicalPinnedPair_past_identity n steps ha q0 km hnormm hiN him]
      with z h
    rw [h]
    have hn : 0 ≤ ∑ j : Fin (steps.length + 1), (pathMassDifferences steps 0 j * km j) *
        ‖X i z - X j.val z‖^2 := by
      exact Finset.sum_nonneg fun j _ => mul_nonneg
        (mul_nonneg (pathMassDifferences_nonneg steps ha j) (hkm j)) (sq_nonneg _)
    dsimp only [X] at hn
    linarith
  have hhi : (fun z => ‖X i z‖^2) ≤ᵐ[mu] fun z => 2 * mu[Ap | G i] z :=
    physicalPinnedPair_sqnorm_le n steps ha q0 kp hkp hnormp hip
  have hcm : |2 * (∫ z, Am z ∂mu) - S| ≤ eta := by
    have hm := integral_physicalPinnedPair_fst n steps ha q0 km
    dsimp only at hm
    rw [hm]
    simpa only [physicalPathSecondMoment, ← mul_assoc, mul_one,
      show (2:ℝ) * (1/2:ℝ) = 1 by norm_num, one_mul] using hmeanm
  have hcp : |2 * (∫ z, Ap z ∂mu) - S| ≤ eta := by
    have hm := integral_physicalPinnedPair_fst n steps ha q0 kp
    dsimp only at hm
    rw [hm]
    simpa only [physicalPathSecondMoment, ← mul_assoc, mul_one,
      show (2:ℝ) * (1/2:ℝ) = 1 by norm_num, one_mul] using hmeanp
  exact buffered_conditional_sandwich_moment (G i) (G.le i)
    (fun z => ‖X i z‖^2) Am Ap hp heta (hLm.integrable hpc) (hLp.integrable hpc)
    hLm hLp hlo hhi hcm hcp

theorem physical_past_buffer_movement (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : Fin (steps.length+1) → ℝ)
    (hk : ∀ j, 0 ≤ k j)
    (hnorm : ∑ j, pathMassDifferences steps 0 j * k j = 1)
    {i : ℕ} (hiN : i ≤ steps.length+1)
    (hi : ∀ j, pathMassDifferences steps 0 j*k j ≠ 0 → j.val ≤ i)
    {p S eta : ℝ} (hp : 1 ≤ p) (heta : 0 ≤ eta)
    (hmean : |(∑ j, (pathMassDifferences steps 0 j*k j)*
      physicalPathSecondMoment n steps q0 j.val)-S| ≤ eta) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let X := actualSpinPath n steps id
    let A := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1
    momentNorm mu (fun z => ∑ j : Fin (steps.length+1),
      (pathMassDifferences steps 0 j*k j)*‖X i z-X j.val z‖^2) p ≤
      momentNorm mu (fun z => ‖X i z‖^2-S) p +
        2*momentNorm mu (fun z => A z-∫ w, A w ∂mu) p + eta := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let G := forwardFiltration (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) steps.length
  let X := actualSpinPath n steps id
  let A : ((FeatureIndex n → ℝ) × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) → ℝ :=
    fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hA : MemLp A (ENNReal.ofReal p) mu := physicalPinnedPair_fst_memLp n steps ha q0 k _
  have hM0 : ∀ᵐ z ∂mu, 0 ≤ ∑ j : Fin (steps.length+1),
      (pathMassDifferences steps 0 j*k j)*‖X i z-X j.val z‖^2 :=
    Eventually.of_forall fun z => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (pathMassDifferences_nonneg steps ha j) (hk j)) (sq_nonneg _)
  have hid : (fun z => ∑ j : Fin (steps.length+1),
      (pathMassDifferences steps 0 j*k j)*‖X i z-X j.val z‖^2) =ᵐ[mu]
      fun z => ‖X i z‖^2-2*mu[A | G i] z := by
    filter_upwards [physicalPinnedPair_past_identity n steps ha q0 k hnorm hiN hi] with z hz
    dsimp only [A, X, G, mu]
    rw [hz]
    ring
  have hc : |2*(∫ z, A z ∂mu)-S| ≤ eta := by
    have hm := integral_physicalPinnedPair_fst n steps ha q0 k
    dsimp only at hm
    rw [hm]
    simpa only [physicalPathSecondMoment, ← mul_assoc, mul_one,
      show (2:ℝ)*(1/2:ℝ)=1 by norm_num, one_mul] using hmean
  exact past_movement_moment_from_identity (G i) (G.le i) _ A _ hp heta
    (physical_sqnorm_memLp n steps ha id measurable_id mu i _) hA hM0 hid hc

theorem physical_central_movement_moment (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : Fin (steps.length+1) → ℝ)
    (hk : ∀ j, 0 ≤ k j)
    (hnorm : ∑ j, pathMassDifferences steps 0 j*k j = 1)
    {i i' : ℕ} (hiN : i ≤ steps.length+1) (hiN' : i' ≤ steps.length+1)
    (hi : ∀ j, pathMassDifferences steps 0 j*k j ≠ 0 → j.val ≤ i)
    (hi' : ∀ j, pathMassDifferences steps 0 j*k j ≠ 0 → j.val ≤ i')
    {p S eta : ℝ} (hp : 1 ≤ p) (heta : 0 ≤ eta)
    (hmean : |(∑ j, (pathMassDifferences steps 0 j*k j)*
      physicalPathSecondMoment n steps q0 j.val)-S| ≤ eta) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let X := actualSpinPath n steps id
    let A := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 k z.1 z.2).1
    momentNorm mu (fun z => ‖X i z-X i' z‖^2) p ≤
      2*momentNorm mu (fun z => ‖X i z‖^2-S) p +
        2*momentNorm mu (fun z => ‖X i' z‖^2-S) p +
        8*momentNorm mu (fun z => A z-∫ w, A w ∂mu) p +4*eta := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  let alpha := fun j => pathMassDifferences steps 0 j*k j
  let M := fun (i : ℕ) z => ∑ j : Fin (steps.length+1), alpha j*‖X i z-X j.val z‖^2
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have halpha0 (j) : 0 ≤ alpha j :=
    mul_nonneg (pathMassDifferences_nonneg steps ha j) (hk j)
  have hdiff (a b : ℕ) : MemLp (fun z => ‖X a z-X b z‖^2) (ENNReal.ofReal p) mu := by
    apply MemLp.of_bound (((actualSpinPath_measurable n steps ha id measurable_id a).sub
      (actualSpinPath_measurable n steps ha id measurable_id b)).norm.pow_const 2).aestronglyMeasurable 4
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    change ‖X a z-X b z‖^2 ≤ 4
    have ht := norm_sub_le (X a z) (X b z)
    have ha' := actualSpinPath_norm_le n steps ha id a z
    have hb' := actualSpinPath_norm_le n steps ha id b z
    have h0 := norm_nonneg (X a z-X b z)
    dsimp only [X] at ht h0 ⊢
    nlinarith
  have hM (a : ℕ) : MemLp (M a) (ENNReal.ofReal p) mu := by
    convert memLp_finsetSum' Finset.univ (fun j _ => (hdiff a j.val).const_smul (alpha j)) using 1
    ext z
    simp only [M, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hpoint : ∀ᵐ z ∂mu, ‖‖X i z-X i' z‖^2‖ ≤ ‖2*M i z+2*M i' z‖ := by
    filter_upwards [] with z
    have hMi : 0 ≤ M i z := Finset.sum_nonneg fun j _ => mul_nonneg (halpha0 j) (sq_nonneg _)
    have hMi' : 0 ≤ M i' z := Finset.sum_nonneg fun j _ => mul_nonneg (halpha0 j) (sq_nonneg _)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (by positivity)]
    exact central_movement_sq_le_buffer alpha halpha0 hnorm (X i z) (X i' z) (fun j => X j.val z)
  have hnorm' := momentNorm_le_of_norm_le ((hM i).const_mul 2 |>.add ((hM i').const_mul 2)) hpoint
  have hsum := momentNorm_add_le hp ((hM i).const_mul 2) ((hM i').const_mul 2)
  have hscale (a : ℕ) : momentNorm mu (fun z => 2*M a z) p =2*momentNorm mu (M a) p := by
    simpa only [Pi.smul_def, smul_eq_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
      momentNorm_smul (μ := mu) (M a) 2 p
  rw [hscale i, hscale i'] at hsum
  have hiB := physical_past_buffer_movement n steps ha q0 k hk hnorm hiN hi hp heta hmean
  have hiB' := physical_past_buffer_movement n steps ha q0 k hk hnorm hiN' hi' hp heta hmean
  dsimp only at hiB hiB'
  simp only [Pi.add_def] at hnorm'
  dsimp only [M, alpha, X, mu] at hsum hnorm'
  linarith

theorem physicalRawRatio_le_bounded_spins (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs : ℝ}
    (ha : OrderedSteps c steps) (hxs : 0 < xs)
    {P : Type} [MeasurableSpace P] (mu : Measure P) [IsProbabilityMeasure mu]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    physicalRawRatio n l steps c xs mu x hx ≤ max 1 (1 / Real.sqrt xs) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  let nu := physicalPathLaw mu n steps x hx
  let : IsProbabilityMeasure nu := by dsimp [nu, physicalPathLaw]; infer_instance
  unfold physicalRawRatio
  refine max_le (le_max_left _ _) ?_
  apply (Finset.sup'_le_iff (by simp) _).mpr
  intro j hj
  have hI : (∫ z, ‖actualSpinPath n steps x j z‖^(4*l) ∂nu) ≤ 1 := by
    have hh := integral_mono (physicalCutNormPower_integrable n steps ha mu x hx j _)
      (integrable_const (1:ℝ)) (fun z =>
        (pow_le_pow_left₀ (norm_nonneg _) (actualSpinPath_norm_le n steps ha x j z)
          (4*l)).trans_eq (one_pow _))
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hroot : (∫ z, ‖actualSpinPath n steps x j z‖^(4*l) ∂nu)^(((4*l:ℕ):ℝ)⁻¹) ≤ 1 :=
    Real.rpow_le_one (integral_nonneg fun z => pow_nonneg (norm_nonneg _) _) hI
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hden : Real.sqrt xs ≤ Real.sqrt (xs + physicalCutMass c steps j) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (physicalCutMass_mem steps ha j).1)
  have hs : 0 < Real.sqrt xs := Real.sqrt_pos.mpr hxs
  exact ((div_le_div_of_nonneg_right hroot (Real.sqrt_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) hs hden)).trans (le_max_right _ _)

theorem physical_window_centered_moment_energy (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length + 1)))
    (r : Fin (steps.length + 2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let A := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (physicalWindowWeight steps 0 J) z.1 z.2).1
    let v := physicalWindowMass steps 0 J
    let zeta := radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
      (physicalWindowCellMass steps 0 J)
    (momentNorm mu (fun z => A z - ∫ w, A w ∂mu) (2 * (l : ℝ)))^2 ≤
      (1 + (2 * (l : ℝ))^2 / 3) * v⁻¹^2 *
        (∫ z, (physicalSusceptibilityMassIntegral n steps id zeta (radiusGridCut r) z)^l ∂mu)^
          ((l : ℝ)⁻¹) := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  let dim := Fintype.card (Fin (steps.length + 1) × FeatureIndex n)
  let flatten : Fin dim ≃ Fin (steps.length + 1) × FeatureIndex n := (Fintype.equivFin _).symm
  have hp : 2 ≤ 2 * (l : ℝ) := by exact_mod_cast (show 2 ≤ 2*l by omega)
  have hm := physical_planted_centered_moment_le q0 steps ha flatten
    (physicalWindowWeight steps 0 J) hp
  dsimp only at hm
  simp only [Function.uncurry] at hm
  rw [show (2 * (l : ℝ)) / 2 = (l : ℝ) by ring] at hm
  have henergy := physical_radius_window_energy_moment n l hl steps ha J r hr hc id measurable_id mu
  simp only [id_eq] at henergy
  dsimp only [mu] at henergy
  rw [henergy] at hm
  simpa only [id_eq, mul_assoc] using hm

def physicalWindowVarianceScale (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    (J : Finset (Fin (steps.length+1))) (r : Fin (steps.length+2) → ℝ) : ℝ :=
  (7/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2*
    ∫ z, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) z
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps

theorem physical_window_centered_second_le_sqrt_energy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let A := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (physicalWindowWeight steps 0 J) z.1 z.2).1
    momentNorm mu (fun z => A z-∫ w, A w ∂mu) 2 ≤
      Real.sqrt (physicalWindowVarianceScale n steps q0 J r) := by
  dsimp only
  apply Real.le_sqrt_of_sq_le
  have h := physical_window_centered_moment_energy n 1 (by norm_num) steps ha q0 J r hr hc
  dsimp only at h
  norm_num only [Nat.cast_one, mul_one, pow_one, inv_one, Real.rpow_one] at h
  norm_num at h
  simpa only [physicalWindowVarianceScale, inv_pow] using h

theorem physical_buffered_overlap_second_le_energy (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0)
    (Jm Jp : Finset (Fin ((pre++tail).length+1)))
    (hvm : 0 < physicalWindowMass (pre++tail) 0 Jm)
    (hvp : 0 < physicalWindowMass (pre++tail) 0 Jp)
    (rm rp : Fin ((pre++tail).length+2) → ℝ) (hrm : Monotone rm) (hrp : Monotone rp)
    (hcm : ∀ j, physicalWindowCellMass (pre++tail) 0 Jm j ≠ 0 → rm j.castSucc < rm j.succ)
    (hcp : ∀ j, physicalWindowCellMass (pre++tail) 0 Jp j ≠ 0 → rp j.castSucc < rp j.succ)
    (him : ∀ j ∈ Jm, j.val ≤ pre.length) (hip : ∀ j ∈ Jp, pre.length ≤ j.val)
    {S eta : ℝ} (heta : 0 ≤ eta)
    (hmeanm : |(∑ j, (pathMassDifferences (pre++tail) 0 j*
      physicalWindowWeight (pre++tail) 0 Jm j)*physicalPathSecondMoment n (pre++tail) q0 j.val)-S| ≤ eta)
    (hmeanp : |(∑ j, (pathMassDifferences (pre++tail) 0 j*
      physicalWindowWeight (pre++tail) 0 Jp j)*physicalPathSecondMoment n (pre++tail) q0 j.val)-S| ≤ eta) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
    let C := fun z => physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2)
    (∫ z, hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau-S)^2) tail
      (actualCutField pre tail z.1 z.2) ∂mu) ≤
      12*physicalWindowVarianceScale n (pre++tail) q0 Jm rm+
      12*physicalWindowVarianceScale n (pre++tail) q0 Jp rp+3*eta^2+
      2*Real.sqrt (∫ z, C z ∂mu)+(∫ z, C z ∂mu) := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
  let km := physicalWindowWeight (pre++tail) 0 Jm
  let kp := physicalWindowWeight (pre++tail) 0 Jp
  have him' : ∀ j, pathMassDifferences (pre++tail) 0 j*km j ≠ 0 → j.val ≤ pre.length := by
    intro j hj
    apply him j
    by_contra hnot
    simp only [km, physicalWindowWeight, if_neg hnot, mul_zero, ne_self_iff_false] at hj
  have hip' : ∀ j, pathMassDifferences (pre++tail) 0 j*kp j ≠ 0 → pre.length ≤ j.val := by
    intro j hj
    apply hip j
    by_contra hnot
    simp only [kp, physicalWindowWeight, if_neg hnot, mul_zero, ne_self_iff_false] at hj
  have hbuf := physical_buffered_norm_concentration n (pre++tail) ha q0 km kp
    (physicalWindowWeight_nonneg _ ha Jm) (physicalWindowWeight_nonneg _ ha Jp)
    (physicalWindowWeight_normalized _ 0 Jm hvm) (physicalWindowWeight_normalized _ 0 Jp hvp)
    (by simp only [List.length_append]; omega : pre.length ≤ (pre++tail).length+1)
    him' hip' (by norm_num : 1 ≤ (2:ℝ)) heta hmeanm hmeanp
  dsimp only at hbuf
  have hm := physical_window_centered_second_le_sqrt_energy n (pre++tail) ha q0 Jm rm hrm hcm
  have hp := physical_window_centered_second_le_sqrt_energy n (pre++tail) ha q0 Jp rp hrp hcp
  dsimp only at hm hp
  have hnorm : momentNorm mu (fun z => ‖actualSpinPath n (pre++tail) id pre.length z‖^2-S) 2 ≤
      2*Real.sqrt (physicalWindowVarianceScale n (pre++tail) q0 Jm rm)+
        2*Real.sqrt (physicalWindowVarianceScale n (pre++tail) q0 Jp rp)+eta := by
    exact hbuf.trans (by dsimp only [mu, km, kp] at *; linarith)
  have hnonm : 0 ≤ physicalWindowVarianceScale n (pre++tail) q0 Jm rm := by
    have h := physical_window_centered_moment_energy n 1 (by norm_num) (pre++tail) ha q0 Jm rm hrm hcm
    dsimp only at h
    norm_num at h
    simpa only [physicalWindowVarianceScale, inv_pow] using (sq_nonneg _).trans h
  have hnonp : 0 ≤ physicalWindowVarianceScale n (pre++tail) q0 Jp rp := by
    have h := physical_window_centered_moment_energy n 1 (by norm_num) (pre++tail) ha q0 Jp rp hrp hcp
    dsimp only at h
    norm_num at h
    simpa only [physicalWindowVarianceScale, inv_pow] using (sq_nonneg _).trans h
  have hnormsq := pow_le_pow_left₀ (momentNorm_nonneg (μ := mu) _ _) hnorm 2
  have hsm := Real.sq_sqrt hnonm
  have hsp := Real.sq_sqrt hnonp
  have hsum : (2*Real.sqrt (physicalWindowVarianceScale n (pre++tail) q0 Jm rm)+
      2*Real.sqrt (physicalWindowVarianceScale n (pre++tail) q0 Jp rp)+eta)^2 ≤
      12*physicalWindowVarianceScale n (pre++tail) q0 Jm rm+
        12*physicalWindowVarianceScale n (pre++tail) q0 Jp rp+3*eta^2 := by
    nlinarith [sq_nonneg (2*Real.sqrt (physicalWindowVarianceScale n (pre++tail) q0 Jm rm)-
        2*Real.sqrt (physicalWindowVarianceScale n (pre++tail) q0 Jp rp)),
      sq_nonneg (2*Real.sqrt (physicalWindowVarianceScale n (pre++tail) q0 Jm rm)-eta),
      sq_nonneg (2*Real.sqrt (physicalWindowVarianceScale n (pre++tail) q0 Jp rp)-eta)]
  have hD := physical_prefix_centered_overlap_integral n pre tail ha q0 S
  dsimp only at hD
  exact hD.trans (by dsimp only [mu] at hnormsq; linarith [hnormsq.trans hsum])

theorem eventually_balanced_margin_polynomial {kappa D R : ℝ}
    (hkappa : 0 < kappa) (hR : 0 ≤ R) :
    ∀ᶠ n : ℕ in atTop,
      D * (Real.log (n : ℝ))^8 * Real.sqrt (R * (n : ℝ)^(-kappa)) ≤
        (n : ℝ)^(-(kappa / 4)) := by
  have ht := (tendsto_raw_log_margin 8 (show 0 < kappa / 4 by positivity)).const_mul
    (D * Real.sqrt R)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_gt_atTop (0:ℕ)] with n hsmall hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfactor :
      D * (Real.log (n : ℝ))^8 * Real.sqrt (R * (n : ℝ)^(-kappa)) =
        (D * Real.sqrt R * ((Real.log (n : ℝ))^8 * (n : ℝ)^(-(kappa / 4)))) *
          (n : ℝ)^(-(kappa / 4)) := by
    rw [Real.sqrt_mul hR]
    simp_rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hn0.le,
      show -kappa * (1/2:ℝ) = -(kappa / 4) + -(kappa / 4) by ring,
      Real.rpow_add hn0]
    ring
  rw [hfactor]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hn0.le _)

namespace PhysicalBandWindow

theorem eventually_coefficient_polynomial (k : ℕ) {kappa D R : ℝ}
    (hkappa : 0 < kappa) (hD : 0 ≤ D) (hR : 0 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ (steps : List (GaussianStep (FeatureIndex n)))
      (ha : OrderedSteps 0 steps) (xs : ℝ) (hxs : 0 < xs)
      (w : PhysicalBandWindow n steps xs) (K e L : ℝ),
      1 ≤ K → w.b ≤ K * w.a → w.mass ≤ K * w.C * w.a →
      0 < e → 0 < L → 0 < w.A →
      w.η = (1 / Real.sqrt (w.A * ((n : ℝ) * e * w.a^4))) * w.a →
      (1 / Real.sqrt (w.A * ((n : ℝ) * e * w.a^4))) * w.a * e / L ≤ w.D₀ →
      w.generalScaleFactor k K L ≤ D * (Real.log (n : ℝ))^8 →
      w.A / ((n : ℝ) * e * w.a^4) ≤ R * (n : ℝ)^(-kappa) →
      w.coefficient k ≤ (n : ℝ)^(-(kappa / 4)) * w.a^4 := by
  filter_upwards [eventually_balanced_margin_polynomial hkappa hR,
    eventually_gt_atTop (0:ℕ)] with n hmargin hn
  intro steps ha xs hxs w K e L hK hb hm he hL hA heta hclock hscale hratio
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := w.coefficient_balanced_general ha hxs k hK hb hm hn0 he hL hA heta hclock
  have hproduct := mul_le_mul hscale (Real.sqrt_le_sqrt hratio) (Real.sqrt_nonneg _)
    (show 0 ≤ D * (Real.log (n : ℝ))^8 by positivity)
  exact hc.trans (mul_le_mul_of_nonneg_right (hproduct.trans hmargin)
    (pow_nonneg (hxs.trans_le w.xa).le 4))

theorem loss_polynomial {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))} {xs : ℝ}
    (k : ℕ) (w : PhysicalBandWindow n steps xs)
    {N kappa c1 : ℝ} (hN : 0 < N) (ha : 0 < w.a)
    (hcoeff : w.coefficient k ≤ N^(-(kappa/4))*w.a^4)
    (hmass : N^(-c1)*w.a ≤ w.mass) :
    w.loss k ≤ 2*Real.sqrt (1+(2*((k+1:ℕ):ℝ))^2/3)*
      N^(-(kappa/8)+c1)*w.a := by
  have hmin : 0 < N^(-c1)*w.a := mul_pos (Real.rpow_pos_of_pos hN _) ha
  have hroot : Real.sqrt (N^(-(kappa/4))*w.a^4) = N^(-(kappa/8))*w.a^2 := by
    rw [Real.sqrt_mul (Real.rpow_nonneg hN.le _)]
    rw [show w.a^4=(w.a^2)^2 by ring, Real.sqrt_sq (sq_nonneg _)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le]
    congr 1
    ring
  have hfactor : Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*
      (N^(-(kappa/4))*w.a^4)) =
      Real.sqrt (1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹*(N^(-(kappa/8))*w.a^2) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ (1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2),
      Real.sqrt_mul (by positivity : 0 ≤ 1+(2*((k+1:ℕ):ℝ))^2/3),
      Real.sqrt_sq (show 0 ≤ w.mass⁻¹ from inv_nonneg.mpr w.mass_pos.le), hroot]
  have hinv : w.mass⁻¹ ≤ (N^(-c1)*w.a)⁻¹ :=
    (inv_le_inv₀ w.mass_pos hmin).mpr hmass
  have hpower : (N^(-c1)*w.a)⁻¹*(N^(-(kappa/8))*w.a^2) =
      N^(-(kappa/8)+c1)*w.a := by
    rw [mul_inv_rev, ← Real.rpow_neg hN.le,
      neg_neg, Real.rpow_add hN]
    field_simp
  unfold loss
  calc
    _ ≤ 2*Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*
        (N^(-(kappa/4))*w.a^4)) := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcoeff (by positivity))) (by norm_num)
    _ = 2*(Real.sqrt (1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹*
        (N^(-(kappa/8))*w.a^2)) := by rw [hfactor]
    _ ≤ 2*(Real.sqrt (1+(2*((k+1:ℕ):ℝ))^2/3)*(N^(-c1)*w.a)⁻¹*
        (N^(-(kappa/8))*w.a^2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _)) (by positivity)) (by norm_num)
    _ = _ := by rw [mul_assoc, hpower]; ring

end PhysicalBandWindow

theorem eventually_physical_band_energy_polynomial (k : ℕ) (Bclock : ℝ)
    {kappa D R : ℝ} (hkappa : 0 < kappa) (hD : 0 ≤ D) (hR : 0 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
      (xs : ℝ) (hxs : 0 < xs) (w : PhysicalBandWindow n steps xs)
      (mu : Measure P) [IsProbabilityMeasure mu]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (d : GaussianStep (FeatureIndex n) → ℝ≥0) (K e L Q : ℝ),
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st) →
      physicalFieldDuration d steps ≤ Bclock →
      (∀ s ∈ Ioc w.a w.b, w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius (s + w.η))) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) →
      (∀ r ∈ Icc (2 * w.a) ((2:ℝ)^w.depth * w.b), w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius r)) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius (3 * r / 4)))) →
      1 ≤ K → w.b ≤ K * w.a → w.mass ≤ K * w.C * w.a →
      0 < e → 0 < L → 0 < w.A →
      w.η = (1 / Real.sqrt (w.A * ((n : ℝ) * e * w.a^4))) * w.a →
      (1 / Real.sqrt (w.A * ((n : ℝ) * e * w.a^4))) * w.a * e / L ≤ w.D₀ →
      w.generalScaleFactor k K L ≤ D * (Real.log (n : ℝ))^8 →
      w.A / ((n : ℝ) * e * w.a^4) ≤ R * (n : ℝ)^(-kappa) →
      physicalRawRatio n (k + 1) steps 0 xs mu x hx ≤ Q →
      (∫ p, (physicalSusceptibilityMassIntegral n steps x w.measure
        (radiusGridCut w.radius) p)^(k + 1) ∂physicalPathLaw mu n steps x hx)^
          (((k + 1:ℕ):ℝ)⁻¹) ≤ (n : ℝ)^(-(kappa / 4)) * w.a^4 * Q^4 := by
  filter_upwards [eventually_physical_dyadic_band k Bclock,
    PhysicalBandWindow.eventually_coefficient_polynomial k hkappa hD hR] with n hband hcoeff
  intro P _ steps ha xs hxs w mu _ x hx d K e L Q hd hB hfirst hdyad
    hK hb hm he hL hA heta hclock hscale hratio hQ
  have hs := hband P steps 0 w.c₀ xs w.D₀ w.C w.R w.F ha w.c₀_pos hxs w.D₀_pos
    w.C_nonneg w.R_pos w.F_mass w.F_radius mu x hx (radiusGridCut w.radius)
    (radiusGridCut_monotone w.radius) (radiusGridCut_le w.radius)
    w.a w.b w.η w.xa w.ab w.η_pos w.η_le w.depth w.depth_pos w.last_radius
    w.measure w.A w.A_nonneg w.measure_cap d hd hB w.mass_comparable hfirst hdyad
  rw [w.measure_mass ha] at hs
  let Qactual := physicalRawRatio n (k + 1) steps 0 xs mu x hx
  have hQa : 1 ≤ Qactual := physicalRawRatio_one_le n (k + 1) steps 0 xs mu x hx
  have hQa0 : 0 ≤ Qactual := zero_le_one.trans hQa
  have ha0 : 0 ≤ w.a := (hxs.trans_le w.xa).le
  have h24 : Qactual^2 ≤ Qactual^4 := by nlinarith [sq_nonneg (Qactual^2 - 1)]
  have hfar : 0 ≤ w.mass * w.farCoefficient k :=
    mul_nonneg w.mass_pos.le (w.farCoefficient_nonneg k)
  have henergy : (∫ p, (physicalSusceptibilityMassIntegral n steps x w.measure
      (radiusGridCut w.radius) p)^(k + 1) ∂physicalPathLaw mu n steps x hx)^
        (((k + 1:ℕ):ℝ)⁻¹) ≤ w.coefficient k * Qactual^4 := by
    calc
      _ ≤ (w.depth + 3:ℕ)^3 *
          (w.nearCoefficient k * Qactual^4 + w.mass * w.farCoefficient k * Qactual^2) := by
        convert hs using 1
        dsimp [PhysicalBandWindow.nearCoefficient, PhysicalBandWindow.farCoefficient, Qactual]
        ring
      _ ≤ (w.depth + 3:ℕ)^3 *
          (w.nearCoefficient k * Qactual^4 + w.mass * w.farCoefficient k * Qactual^4) :=
        mul_le_mul_of_nonneg_left (add_le_add_right
          (mul_le_mul_of_nonneg_left h24 hfar) _) (by positivity)
      _ = _ := by unfold PhysicalBandWindow.coefficient; ring
  have hc := hcoeff steps ha xs hxs w K e L hK hb hm he hL hA heta hclock hscale hratio
  exact henergy.trans (mul_le_mul hc (pow_le_pow_left₀ hQa0 hQ 4)
    (pow_nonneg hQa0 4) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg ha0 4)))

theorem physical_buffer_centered_moment_le_loss (n k : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {xs Q : ℝ} (hxs : 0 < xs)
    (w : PhysicalBandWindow n steps xs)
    (henergy : (∫ z, (physicalSusceptibilityMassIntegral n steps id w.measure
      (radiusGridCut w.radius) z)^(k+1)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)^(((k+1:ℕ):ℝ)⁻¹) ≤
        w.coefficient k*Q^4) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let A := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (physicalWindowWeight steps 0 w.selected) z.1 z.2).1
    momentNorm mu (fun z => A z-∫ z', A z' ∂mu) (2*((k+1:ℕ):ℝ)) ≤ (w.loss k/2)*Q^2 := by
  dsimp only
  have hm := physical_window_centered_moment_energy n (k+1) (Nat.succ_pos k) steps ha q0
    w.selected w.radius w.radius_mono w.cell_pos
  dsimp only at hm
  change _ ≤ (1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*
    (∫ z, (physicalSusceptibilityMassIntegral n steps id w.measure (radiusGridCut w.radius) z)^(k+1)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)^(((k+1:ℕ):ℝ)⁻¹) at hm
  have hsmall := hm.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hs : 0 ≤ (1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*w.coefficient k :=
    mul_nonneg (by positivity) (w.coefficient_nonneg hxs k)
  have hsq := Real.sq_sqrt hs
  have hpos := mul_nonneg (Real.sqrt_nonneg ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*w.coefficient k))
    (sq_nonneg Q)
  unfold PhysicalBandWindow.loss
  have he : (2*Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*w.coefficient k)/2)*Q^2 =
      Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*w.coefficient k)*Q^2 := by ring
  rw [he]
  have hsq' : (Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*w.coefficient k)*Q^2)^2 =
      (1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*(w.coefficient k*Q^4) := by
    rw [mul_pow, hsq]
    ring
  apply le_of_sq_le_sq _ hpos
  rw [hsq']
  exact hsmall

theorem eventually_physical_band_energy_coefficient (k : ℕ) (Bclock : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
      (xs : ℝ) (hxs : 0 < xs) (w : PhysicalBandWindow n steps xs)
      (mu : Measure P) [IsProbabilityMeasure mu]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (d : GaussianStep (FeatureIndex n) → ℝ≥0) (Q : ℝ),
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st) →
      physicalFieldDuration d steps ≤ Bclock →
      (∀ s ∈ Ioc w.a w.b, w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η))) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) →
      (∀ r ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius r)) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*r/4)))) →
      physicalRawRatio n (k+1) steps 0 xs mu x hx ≤ Q →
      (∫ p, (physicalSusceptibilityMassIntegral n steps x w.measure
        (radiusGridCut w.radius) p)^(k+1) ∂physicalPathLaw mu n steps x hx)^
          (((k+1:ℕ):ℝ)⁻¹) ≤ w.coefficient k*Q^4 := by
  filter_upwards [eventually_physical_dyadic_band k Bclock] with n hband
  intro P _ steps ha xs hxs w mu _ x hx d Q hd hB hfirst hdyad hQ
  have hs := hband P steps 0 w.c₀ xs w.D₀ w.C w.R w.F ha w.c₀_pos hxs w.D₀_pos
    w.C_nonneg w.R_pos w.F_mass w.F_radius mu x hx (radiusGridCut w.radius)
    (radiusGridCut_monotone w.radius) (radiusGridCut_le w.radius)
    w.a w.b w.η w.xa w.ab w.η_pos w.η_le w.depth w.depth_pos w.last_radius
    w.measure w.A w.A_nonneg w.measure_cap d hd hB w.mass_comparable hfirst hdyad
  rw [w.measure_mass ha] at hs
  let Qactual := physicalRawRatio n (k+1) steps 0 xs mu x hx
  have hQa : 1 ≤ Qactual := physicalRawRatio_one_le n (k+1) steps 0 xs mu x hx
  have hQa0 : 0 ≤ Qactual := zero_le_one.trans hQa
  have h24 : Qactual^2 ≤ Qactual^4 := by nlinarith [sq_nonneg (Qactual^2-1)]
  have hfar : 0 ≤ w.mass*w.farCoefficient k := mul_nonneg w.mass_pos.le (w.farCoefficient_nonneg k)
  calc
    _ ≤ (w.depth+3:ℕ)^3*(w.nearCoefficient k*Qactual^4+w.mass*w.farCoefficient k*Qactual^2) := by
      convert hs using 1
      dsimp [PhysicalBandWindow.nearCoefficient, PhysicalBandWindow.farCoefficient, Qactual]
      ring
    _ ≤ (w.depth+3:ℕ)^3*(w.nearCoefficient k*Qactual^4+w.mass*w.farCoefficient k*Qactual^4) :=
      mul_le_mul_of_nonneg_left (add_le_add_right
        (mul_le_mul_of_nonneg_left h24 hfar) _) (by positivity)
    _ = w.coefficient k*Qactual^4 := by unfold PhysicalBandWindow.coefficient; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQa0 hQ 4) (w.coefficient_nonneg hxs k)

theorem eventually_physical_buffer_centered_moment (k : ℕ) (Bclock : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀
      (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
      (q0 : FeatureIndex n → ℝ≥0) (xs : ℝ) (hxs : 0 < xs)
      (w : PhysicalBandWindow n steps xs) (d : GaussianStep (FeatureIndex n) → ℝ≥0) (Q : ℝ),
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st) →
      physicalFieldDuration d steps ≤ Bclock →
      (∀ s ∈ Ioc w.a w.b, w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η))) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) →
      (∀ r ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius r)) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*r/4)))) →
      physicalRawRatio n (k+1) steps 0 xs (Measure.pi fun i => gaussianReal 0 (q0 i))
        id measurable_id ≤ Q →
      let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
      let A := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
        (spinSource n) steps 0 (physicalWindowWeight steps 0 w.selected) z.1 z.2).1
      momentNorm mu (fun z => A z-∫ z', A z' ∂mu) (2*((k+1:ℕ):ℝ)) ≤ (w.loss k/2)*Q^2 := by
  filter_upwards [eventually_physical_band_energy_coefficient k Bclock] with n hband
  intro steps ha q0 xs hxs w d Q hd hB hfirst hdyad hQ
  have hE := hband (FeatureIndex n → ℝ) steps ha xs hxs w
    (Measure.pi fun i => gaussianReal 0 (q0 i)) id measurable_id d Q hd hB hfirst hdyad hQ
  rw [← rootedHierarchyPathLaw_eq_physical] at hE
  exact physical_buffer_centered_moment_le_loss n k steps ha q0 hxs w hE

theorem exists_buffered_profile_window (S : ℕ → ℝ) (hS : Monotone S)
    {N : ℕ} (hN : 0 < N) {osc : ℝ}
    (hvariation : S (4 * N) - S 0 ≤ (N : ℝ) * osc) :
    ∃ i ∈ Finset.range N, ∀ j ∈ Icc (4 * i) (4 * (i + 1)),
      ∀ k ∈ Icc (4 * i) (4 * (i + 1)), |S j - S k| ≤ osc := by
  classical
  have hwindow : ∃ i ∈ Finset.range N, S (4 * (i + 1)) - S (4 * i) ≤ osc := by
    by_contra h
    push Not at h
    have hs := Finset.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) (fun i hi => h i hi)
    have htel : (∑ i ∈ Finset.range N, (S (4 * (i + 1)) - S (4 * i))) =
        S (4 * N) - S 0 := by
      simpa only [Nat.mul_zero] using Finset.sum_range_sub (fun i => S (4 * i)) N
    rw [htel] at hs
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    exact (not_lt_of_ge hvariation) hs
  obtain ⟨i, hi, hosc⟩ := hwindow
  refine ⟨i, hi, ?_⟩
  intro j hj k hk
  have hjlo := hS hj.1
  have hjhi := hS hj.2
  have hklo := hS hk.1
  have hkhi := hS hk.2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem whole_unit_side_energy_le {I : Type*} [Fintype I]
    (mass part energy : I → ℝ) {m tau : ℝ}
    (hmass : ∀ j, 0 < mass j) (hpart0 : ∀ j, 0 ≤ part j)
    (hpart : ∀ j, part j ≤ mass j) (htau : 0 ≤ tau)
    (henergy : ∀ j, energy j ≤ tau*mass j)
    (hm : 0 < m) (hsum : ∑ j, part j = m) :
    (∑ j, (part j/(m*mass j))^2*energy j) ≤ tau/m := by
  classical
  have hj (j) : (part j/(m*mass j))^2*energy j ≤ tau*part j/m^2 := by
    have hq : (part j)^2 ≤ part j*mass j := by
      nlinarith [mul_nonneg (hpart0 j) (sub_nonneg.mpr (hpart j))]
    calc
      _ ≤ (part j/(m*mass j))^2*(tau*mass j) :=
        mul_le_mul_of_nonneg_left (henergy j) (sq_nonneg _)
      _ ≤ _ := by
        have hm0 : m ≠ 0 := hm.ne'
        have hu0 : mass j ≠ 0 := (hmass j).ne'
        rw [div_pow, div_mul_eq_mul_div]
        apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos hm (hmass j))) (sq_pos_of_pos hm)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hq
          (mul_nonneg (mul_nonneg htau (sq_nonneg m)) (hmass j).le)]
  calc
    _ ≤ ∑ j, tau*part j/m^2 := Finset.sum_le_sum fun j _ => hj j
    _ = tau/m := by rw [← Finset.sum_div, ← Finset.mul_sum, hsum]; field_simp

def physicalSamplingUnitEnergy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    {I : Type} [Fintype I] [DecidableEq I] (unit : Fin (steps.length+1) → I) (j : I) : ℝ :=
  ∑ k, if unit k = j then pathMassDifferences steps 0 k*
    ∫ z, physicalCutSusceptibility n steps id k.val z
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps else 0

def physicalSamplingUnitMass {ι I : Type} [Fintype I] [DecidableEq I]
    (steps : List (GaussianStep ι)) (unit : Fin (steps.length+1) → I) (j : I) : ℝ :=
  ∑ k, if unit k = j then pathMassDifferences steps 0 k else 0

theorem physical_whole_unit_side_weight_normalized {ι I : Type}
    [Fintype I] [DecidableEq I] (steps : List (GaussianStep ι))
    (unit : Fin (steps.length+1) → I) (part : I → ℝ) {m : ℝ}
    (hmass : ∀ j, 0 < physicalSamplingUnitMass steps unit j)
    (hm : 0 < m) (hsum : ∑ j, part j = m) :
    (∑ k, pathMassDifferences steps 0 k*
      (part (unit k)/(m*physicalSamplingUnitMass steps unit (unit k)))) = 1 := by
  let w := fun j => part j/(m*physicalSamplingUnitMass steps unit j)
  have hgroup : (∑ k, pathMassDifferences steps 0 k*w (unit k)) =
      ∑ j, physicalSamplingUnitMass steps unit j*w j := by
    unfold physicalSamplingUnitMass
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
  change (∑ k, pathMassDifferences steps 0 k*w (unit k)) = 1
  rw [hgroup]
  calc
    _ = ∑ j, part j/m := Finset.sum_congr rfl fun j _ => by
      dsimp only [w]
      field_simp [(hmass j).ne', hm.ne']
    _ = 1 := by rw [← Finset.sum_div, hsum, div_self hm.ne']

theorem physical_whole_unit_side_variance_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {I : Type} [Fintype I] [DecidableEq I]
    (unit : Fin (steps.length+1) → I) (mass part : I → ℝ) {m tau : ℝ}
    (hmass : ∀ j, 0 < mass j) (hpart0 : ∀ j, 0 ≤ part j)
    (hpart : ∀ j, part j ≤ mass j) (htau : 0 ≤ tau)
    (henergy : ∀ j, physicalSamplingUnitEnergy n steps q0 unit j ≤ tau*mass j)
    (hm : 0 < m) (hsum : ∑ j, part j = m) :
    variance (fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (fun k => part (unit k)/(m*mass (unit k))) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤ tau/m := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let w := fun j => part j/(m*mass j)
  let d := Fintype.card (Fin (steps.length+1) × FeatureIndex n)
  let e : Fin d ≃ Fin (steps.length+1) × FeatureIndex n := (Fintype.equivFin _).symm
  have h := physical_planted_variance_le q0 steps ha e (fun k => w (unit k))
  dsimp only [Function.uncurry] at h
  change _ ≤ ∫ z, (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
    steps 0 (fun k => w (unit k)) z.1 z.2).2 ∂mu at h
  have hPairEnergy (z : PhysicalPathState (FeatureIndex n → ℝ) n steps) :
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps 0 (fun k => w (unit k)) z.1 z.2).2 =
      ∑ k, pathMassDifferences steps 0 k*(w (unit k))^2*
        physicalCutSusceptibility n steps id k.val z :=
    physicalPinnedPair_snd_eq_sum n steps ha (fun k => w (unit k)) id z
  simp_rw [hPairEnergy] at h
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hI (k : Fin (steps.length+1)) : Integrable
      (fun z => pathMassDifferences steps 0 k*(w (unit k))^2*
        physicalCutSusceptibility n steps id k.val z) mu :=
    ((physicalCutSusceptibility_memLp n steps ha id measurable_id mu k.val 1).integrable le_rfl).const_mul _
  rw [integral_finset_sum Finset.univ (fun k _ => hI k)] at h
  simp only [integral_const_mul] at h
  have heq : (∑ k, pathMassDifferences steps 0 k*(w (unit k))^2*
        ∫ z, physicalCutSusceptibility n steps id k.val z ∂mu) =
      ∑ j, (w j)^2*physicalSamplingUnitEnergy n steps q0 unit j := by
    unfold physicalSamplingUnitEnergy
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    ring
  rw [heq] at h
  exact h.trans (whole_unit_side_energy_le mass part
    (physicalSamplingUnitEnergy n steps q0 unit) hmass hpart0 hpart htau henergy hm hsum)

theorem two_sided_defect_absorption {I A B v tau : ℝ}
    (hI : 0 ≤ I) (hv : 0 ≤ v) (htau : 0 ≤ tau)
    (hbracket : I ≤ A+B*Real.sqrt (I*(v*tau))) :
    I ≤ 2*A+B^2*v*tau := by
  have hsI := Real.sq_sqrt hI
  have hsv := Real.sq_sqrt (mul_nonneg hv htau)
  rw [Real.sqrt_mul hI] at hbracket
  nlinarith [sq_nonneg (Real.sqrt I-B*Real.sqrt (v*tau))]

namespace EffectiveSideKernel

def left (i j : ℕ) : ℝ := if j ≤ i then ((i+1:ℕ):ℝ)⁻¹ else 0

theorem left_nonneg (i j : ℕ) : 0 ≤ left i j := by unfold left; split_ifs <;> positivity

theorem left_normalized (i : ℕ) : ∑ j ∈ Finset.range (i+1), left i j = 1 := by
  have hi : ((i+1:ℕ):ℝ) ≠ 0 := by positivity
  simp only [left]
  have hcond : ∀ j ∈ Finset.range (i+1), j ≤ i := fun j hj => by
    have := Finset.mem_range.mp hj
    omega
  simp only [Finset.sum_congr rfl (fun j hj => if_pos (hcond j hj)), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hi]

theorem left_column_le_log (N j : ℕ) :
    (∑ i ∈ Finset.range N, left i j) ≤ 1+Real.log (N:ℝ) := by
  have hterm (i : ℕ) : left i j ≤ ((i+1:ℕ):ℝ)⁻¹ := by
    unfold left
    split_ifs
    · exact le_rfl
    · positivity
  calc
    _ ≤ ∑ i ∈ Finset.range N, ((i+1:ℕ):ℝ)⁻¹ :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (harmonic N : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log N

theorem left_integrated_le_log (N : ℕ) (F : ℕ → ℝ)
    (hF : ∀ j ∈ Finset.range N, 0 ≤ F j) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, left i j*F j) ≤
      (1+Real.log (N:ℝ))*(∑ j ∈ Finset.range N, F j) := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  calc
    _ ≤ ∑ j ∈ Finset.range N, (1+Real.log (N:ℝ))*F j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (left_column_le_log N j) (hF j hj)
    _ = _ := by rw [Finset.mul_sum]

theorem left_ordered_integrated_le_log (N : ℕ) (F : ℕ → ℝ) (allowed : ℕ → ℕ → Prop)
    [∀ i j, Decidable (allowed i j)] (hF : ∀ j ∈ Finset.range N, 0 ≤ F j) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      if allowed i j then left i j*F j else 0) ≤
      (1+Real.log (N:ℝ))*(∑ j ∈ Finset.range N, F j) := by
  apply le_trans _ (left_integrated_le_log N F hF)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  split_ifs <;> first | exact le_rfl | exact mul_nonneg (left_nonneg i j) (hF j hj)

def right (N i j : ℕ) : ℝ := left (N-1-i) (N-1-j)

theorem right_nonneg (N i j : ℕ) : 0 ≤ right N i j := left_nonneg _ _

theorem right_column_le_log (N j : ℕ) :
    (∑ i ∈ Finset.range N, right N i j) ≤ 1+Real.log (N:ℝ) := by
  calc
    _ = ∑ i ∈ Finset.range N, left i (N-1-j) :=
      Finset.sum_range_reflect (fun i => left i (N-1-j)) N
    _ ≤ _ := left_column_le_log N (N-1-j)

theorem right_integrated_le_log (N : ℕ) (F : ℕ → ℝ)
    (hF : ∀ j ∈ Finset.range N, 0 ≤ F j) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, right N i j*F j) ≤
      (1+Real.log (N:ℝ))*(∑ j ∈ Finset.range N, F j) := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  calc
    _ ≤ ∑ j ∈ Finset.range N, (1+Real.log (N:ℝ))*F j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (right_column_le_log N j) (hF j hj)
    _ = _ := by rw [Finset.mul_sum]

end EffectiveSideKernel

end OAI.SKFluctuations
