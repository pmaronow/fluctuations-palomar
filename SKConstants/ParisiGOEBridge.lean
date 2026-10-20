module
public import SKConstants.SKModel
public import SKConstants.GaussianRotation
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Model
import Mathlib

/-!
# Actual GOE normalization bridge to OpenAI's finite-volume SK model

The unordered-edge coordinates are constructed from the genuine local standard
Gaussian endpoint. Their joint Gaussian law, identity covariance, independence
and exact standard Gaussian product law are derived. The completed local
Hamiltonian equals OpenAI's unordered-edge Hamiltonian plus its actual half
trace. This diagonal shift is integrable and centered, giving exact expected
log-partition and pressure equality, including size zero.

The spin types are definitionally identical. The finite edge-summation helper
is adapted from Apache-2.0 OpenAI Math sources at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, as identified below.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiGOEBridge

def spinEquiv (n : ℕ) : Spin n ≃ SKConstantsOAI.SK.Config n := Equiv.refl _

lemma signedSpin_eq_upstream_spin {n : ℕ} (x : Spin n) (i : Fin n) :
    signedSpin x i = SKConstantsOAI.SK.spin (x i) := rfl

def edgeDisorder (n : ℕ) (z : EuclideanSpace ℝ (Fin n × Fin n)) : SKConstantsOAI.SK.Disorder n :=
  fun e => GaussianProposal.goeMatrix (1 / Real.sqrt 2) z e.1.1 e.1.2

def edgeDisorderCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n × Fin n) →L[ℝ] SKConstantsOAI.SK.Disorder n :=
  ContinuousLinearMap.pi (fun e =>
    (1 / Real.sqrt 2) • (EuclideanSpace.proj e.1 + EuclideanSpace.proj (e.1.2,e.1.1)))

lemma edgeDisorderCLM_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    edgeDisorderCLM n z = edgeDisorder n z := by
  ext e
  simp [edgeDisorderCLM, edgeDisorder, GaussianProposal.goeMatrix]
  ring

lemma measurable_edgeDisorder (n : ℕ) : Measurable (edgeDisorder n) := by
  have he : edgeDisorder n = (fun z => edgeDisorderCLM n z) :=
    (funext (edgeDisorderCLM_apply n)).symm
  rw [he]
  exact (edgeDisorderCLM n).continuous.measurable

lemma edgeDisorder_gaussian (n : ℕ) :
    HasGaussianLaw (edgeDisorder n) (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  simpa only [id_eq, edgeDisorderCLM_apply] using
    (IsGaussian.hasGaussianLaw_id (μ := GaussianProposal.primitiveGaussian (Fin n × Fin n))).map_fun
      (edgeDisorderCLM n)

lemma edgeDisorder_mean (n : ℕ) (e : SKConstantsOAI.SK.Edge n) :
    (∫ z, edgeDisorder n z e ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) = 0 :=
  GaussianProposal.goeEntry_mean _ _ _

lemma edgeDisorder_covariance (n : ℕ) (e f : SKConstantsOAI.SK.Edge n) :
    cov[fun z => edgeDisorder n z e, fun z => edgeDisorder n z f;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] = if e = f then 1 else 0 := by
  unfold edgeDisorder
  rw [GaussianProposal.goeEntry_covariance]
  have hscale : 2 * (1 / Real.sqrt (2 : ℝ)) ^ 2 = 1 := by
    norm_num [div_pow, Real.sq_sqrt]
  rw [hscale, one_mul]
  have hs : ¬(e.1.1 = f.1.2 ∧ e.1.2 = f.1.1) := by
    have he := e.2
    have hf := f.2
    omega
  have hm : (e.1.1 = f.1.1 ∧ e.1.2 = f.1.2) ↔ e = f := by
    constructor
    · intro h
      exact Subtype.ext (Prod.ext h.1 h.2)
    · intro h
      subst f
      exact ⟨rfl,rfl⟩
  simp only [hm, hs, ↓reduceIte, add_zero]

lemma edgeDisorder_coordinate_hasLaw (n : ℕ) (e : SKConstantsOAI.SK.Edge n) :
    HasLaw (fun z => edgeDisorder n z e) (gaussianReal 0 1)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  have hG := (edgeDisorder_gaussian n).eval e
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, edgeDisorder_mean]
  have hv : Var[fun z => edgeDisorder n z e;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] = 1 := by
    rw [← covariance_self hG.aemeasurable, edgeDisorder_covariance]
    simp
  rw [hv]
  norm_num

lemma edgeDisorder_independent (n : ℕ) :
    iIndepFun (fun e z => edgeDisorder n z e)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  apply (edgeDisorder_gaussian n).iIndepFun_of_covariance_eq_zero
  intro e f hef
  rw [edgeDisorder_covariance]
  simp [hef]

/-- The actual symmetrized Gaussian endpoint supplies exactly the upstream
independent standard unordered-edge disorder. -/
lemma edgeDisorder_hasLaw (n : ℕ) :
    HasLaw (edgeDisorder n) (SKConstantsOAI.SK.disorderLaw n)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  refine ⟨(measurable_edgeDisorder n).aemeasurable, ?_⟩
  have h := (edgeDisorder_independent n).map_fun_eq_pi_map
    (fun e => (edgeDisorder_coordinate_hasLaw n e).aemeasurable)
  simp_rw [(edgeDisorder_coordinate_hasLaw n _).map_eq] at h
  exact h

/- The following finite unordered-edge summation follows the argument in
OpenAI's Apache-2.0 `SKRatio/Matrices/RandomMatrixBounded.lean`, adapted to
the actual `OAI.SK` disorder and coupling definitions. -/
lemma coupling_bilinear {n : ℕ} (x y : Fin n → ℝ) (J : SKConstantsOAI.SK.Disorder n) :
    (∑ i, ∑ j, x i * SKConstantsOAI.SK.coupling J i j * y j) =
      ∑ e : SKConstantsOAI.SK.Edge n, (x e.1.1 * y e.1.2 + x e.1.2 * y e.1.1) * J e := by
  let F : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 < p.2 then x p.1 * y p.2 * J ⟨p,h⟩ else 0
  let G : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 < p.2 then x p.2 * y p.1 * J ⟨p,h⟩ else 0
  have hid (i j : Fin n) : x i * SKConstantsOAI.SK.coupling J i j * y j = F (i,j) + G (j,i) := by
    dsimp [F,G,SKConstantsOAI.SK.coupling]
    split_ifs with h₁ h₂ h₂ <;> try omega
    all_goals ring
  simp_rw [hid]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => G (j,i)), ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  rw [← Fintype.sum_prod_type (f := fun p => F p + G p)]
  apply Finset.sum_congr_set (s := {p : Fin n × Fin n | p.1 < p.2})
  · intro p hp
    simp only [F,G,show p.1 < p.2 from hp,dite_eq_left]
    ring
  · intro p hp
    simp [F,G,show ¬p.1 < p.2 from hp]

lemma quadraticHamiltonian_upstream_coupling {n : ℕ} (J : SKConstantsOAI.SK.Disorder n) (x : Spin n) :
    quadraticHamiltonian (fun i j => SKConstantsOAI.SK.coupling J i j / Real.sqrt (n : ℝ)) x =
      SKConstantsOAI.SK.hamiltonian J x := by
  have hsum : (∑ i, ∑ j, signedSpin x i *
      (SKConstantsOAI.SK.coupling J i j / Real.sqrt (n : ℝ)) * signedSpin x j) =
      (∑ i, ∑ j, SKConstantsOAI.SK.spin (x i) * SKConstantsOAI.SK.coupling J i j * SKConstantsOAI.SK.spin (x j)) /
        Real.sqrt (n : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    simp only [signedSpin_eq_upstream_spin]
    ring
  have he : (∑ e : SKConstantsOAI.SK.Edge n,
      (SKConstantsOAI.SK.spin (x e.1.1) * SKConstantsOAI.SK.spin (x e.1.2) +
        SKConstantsOAI.SK.spin (x e.1.2) * SKConstantsOAI.SK.spin (x e.1.1)) * J e) =
      2 * ∑ e : SKConstantsOAI.SK.Edge n, J e * SKConstantsOAI.SK.spin (x e.1.1) * SKConstantsOAI.SK.spin (x e.1.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold quadraticHamiltonian SKConstantsOAI.SK.hamiltonian
  rw [hsum, coupling_bilinear, he]
  norm_num
  ring

lemma goe_entry_normalization (n : ℕ) (z : EuclideanSpace ℝ (Fin n × Fin n))
    (i j : Fin n) :
    GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i j =
      GaussianProposal.goeMatrix (1 / Real.sqrt 2) z i j / Real.sqrt (n : ℝ) := by
  unfold GaussianProposal.goeMatrix
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def matrixEdgeDisorder (n : ℕ) (W : Matrix (Fin n) (Fin n) ℝ) : SKConstantsOAI.SK.Disorder n :=
  fun e => Real.sqrt (n : ℝ) * W e.1.1 e.1.2

lemma measurable_matrixEdgeDisorder (n : ℕ) : Measurable (matrixEdgeDisorder n) := by
  unfold matrixEdgeDisorder
  fun_prop

lemma matrixEdgeDisorder_goe_eq {n : ℕ} (hn : 0 < n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    matrixEdgeDisorder n (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z) =
      edgeDisorder n z := by
  have hsq : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  ext e
  unfold matrixEdgeDisorder edgeDisorder
  rw [goe_entry_normalization]
  field_simp

/-- Extracting unordered edges from the actual completed normalized GOE,
and multiplying them by `sqrt n`, gives the literal upstream disorder law. -/
lemma matrixEdgeDisorder_hasLaw {n : ℕ} (hn : 0 < n) :
    HasLaw (matrixEdgeDisorder n) (SKConstantsOAI.SK.disorderLaw n) (skDisorderLaw n) := by
  refine ⟨(measurable_matrixEdgeDisorder n).aemeasurable, ?_⟩
  unfold skDisorderLaw
  rw [Measure.map_map (measurable_matrixEdgeDisorder n) (continuous_goeMatrix _).measurable]
  norm_num only [Nat.cast_ofNat]
  have he : matrixEdgeDisorder n ∘ GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) =
      edgeDisorder n := funext (matrixEdgeDisorder_goe_eq hn)
  rw [he]
  exact (edgeDisorder_hasLaw n).map_eq

/-- The completed local GOE differs from the normalized unordered-edge
matrix only by its actual Gaussian diagonal. -/
lemma goeMatrix_decomposition (n : ℕ) (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z =
      Matrix.of (fun i j => SKConstantsOAI.SK.coupling (edgeDisorder n z) i j / Real.sqrt (n : ℝ)) +
        Matrix.diagonal (fun i => GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [SKConstantsOAI.SK.coupling]
  · rw [Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply_ne _ hij, add_zero,
      goe_entry_normalization]
    rcases lt_or_gt_of_ne hij with h | h
    · simp [SKConstantsOAI.SK.coupling, h, edgeDisorder]
    · simp only [SKConstantsOAI.SK.coupling, not_lt_of_gt h, ↓reduceDIte, h, edgeDisorder]
      congr 1
      simp only [GaussianProposal.goeMatrix, add_comm]

/-- The local completed GOE Hamiltonian has precisely the upstream SK
normalization, plus a spin-independent half trace. -/
lemma quadraticHamiltonian_goe_eq {n : ℕ} (z : EuclideanSpace ℝ (Fin n × Fin n))
    (x : Spin n) :
    quadraticHamiltonian (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z) x =
      SKConstantsOAI.SK.hamiltonian (edgeDisorder n z) x +
        (1 / 2) * ∑ i, GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i i := by
  conv_lhs => rw [goeMatrix_decomposition, quadraticHamiltonian_add_diagonal]
  have hq : quadraticHamiltonian
      (Matrix.of fun i j => SKConstantsOAI.SK.coupling (edgeDisorder n z) i j / Real.sqrt (n : ℝ)) x =
      SKConstantsOAI.SK.hamiltonian (edgeDisorder n z) x := by
    simpa only [quadraticHamiltonian, Matrix.of_apply] using
      quadraticHamiltonian_upstream_coupling (edgeDisorder n z) x
  rw [hq]

lemma gibbsPartition_goe_eq {n : ℕ} (β : ℝ) (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    gibbsPartition β (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z) =
      Real.exp (β * ((1 / 2) * ∑ i,
        GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i i)) *
        SKConstantsOAI.SK.partition β (edgeDisorder n z) := by
  unfold gibbsPartition SKConstantsOAI.SK.partition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [quadraticHamiltonian_goe_eq, mul_add, Real.exp_add]
  ring

lemma upstream_partition_pos {n : ℕ} (β : ℝ) (J : SKConstantsOAI.SK.Disorder n) :
    0 < SKConstantsOAI.SK.partition β J := by
  unfold SKConstantsOAI.SK.partition
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨fun _ => false, Finset.mem_univ _⟩

lemma log_gibbsPartition_goe_eq {n : ℕ} (β : ℝ) (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    Real.log (gibbsPartition β (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z)) =
      β * ((1 / 2) * ∑ i, GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i i) +
        Real.log (SKConstantsOAI.SK.partition β (edgeDisorder n z)) := by
  rw [gibbsPartition_goe_eq, Real.log_mul (Real.exp_ne_zero _)
    (upstream_partition_pos β _).ne', Real.log_exp]

lemma continuous_upstream_logPartition (n : ℕ) (β : ℝ) :
    Continuous (fun J : SKConstantsOAI.SK.Disorder n => Real.log (SKConstantsOAI.SK.partition β J)) := by
  have hp : Continuous (SKConstantsOAI.SK.partition (n := n) β) := by
    unfold SKConstantsOAI.SK.partition SKConstantsOAI.SK.hamiltonian
    fun_prop
  exact hp.log (fun J => (upstream_partition_pos β J).ne')

lemma integrable_goeDiagonalShift (n : ℕ) (β : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
      β * ((1 / 2) * ∑ i, GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i i))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  exact ((integrable_finsetSum Finset.univ (fun i _ =>
    (GaussianProposal.goeEntry_gaussian (1 / Real.sqrt (2 * (n : ℝ))) i i).integrable)).const_mul
      (1 / 2 : ℝ)).const_mul β

lemma integral_goeDiagonalShift_eq_zero (n : ℕ) (β : ℝ) :
    (∫ z : EuclideanSpace ℝ (Fin n × Fin n),
      β * ((1 / 2) * ∑ i, GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i i)
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) = 0 := by
  rw [integral_const_mul, integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ =>
      (GaussianProposal.goeEntry_gaussian (1 / Real.sqrt (2 * (n : ℝ))) i i).integrable)]
  simp only [GaussianProposal.goeEntry_mean, Finset.sum_const_zero, mul_zero]

lemma integrable_upstream_logPartition_pullback (n : ℕ) (β : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
      Real.log (SKConstantsOAI.SK.partition β (edgeDisorder n z)))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  have h := (integrable_goeGibbsPressure (1 / Real.sqrt (2 * (n : ℝ))) β).sub
    (integrable_goeDiagonalShift n β)
  apply h.congr
  exact Filter.Eventually.of_forall (fun z => by
    simp only [Pi.sub_apply, log_gibbsPartition_goe_eq]
    ring)

/-- Finite-volume expected log partition equality for the actual completed
GOE law. The actual diagonal contributes a centered spin-independent shift. -/
theorem expected_logPartition_eq_upstream (n : ℕ) (β : ℝ) :
    (∫ W, Real.log (gibbsPartition β W) ∂skDisorderLaw n) =
      ∫ J : SKConstantsOAI.SK.Disorder n, Real.log (SKConstantsOAI.SK.partition β J) ∂SKConstantsOAI.SK.disorderLaw n := by
  have hm : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ => Real.log (gibbsPartition β W)) :=
    Real.measurable_log.comp (continuous_gibbsPartition β).measurable
  have hf := integrable_upstream_logPartition_pullback n β
  calc
    _ = ∫ z : EuclideanSpace ℝ (Fin n × Fin n),
        Real.log (gibbsPartition β (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z))
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
      unfold skDisorderLaw
      rw [integral_map (continuous_goeMatrix _).measurable.aemeasurable hm.aestronglyMeasurable]
      rfl
    _ = (∫ z : EuclideanSpace ℝ (Fin n × Fin n),
          β * ((1 / 2) * ∑ i, GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i i)
          ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) +
        ∫ z : EuclideanSpace ℝ (Fin n × Fin n),
          Real.log (SKConstantsOAI.SK.partition β (edgeDisorder n z))
          ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
      simp_rw [log_gibbsPartition_goe_eq]
      exact integral_add (integrable_goeDiagonalShift n β) hf
    _ = _ := by
      rw [integral_goeDiagonalShift_eq_zero, zero_add]
      exact (edgeDisorder_hasLaw n).integral_comp
        (continuous_upstream_logPartition n β).measurable.aestronglyMeasurable

theorem expected_pressure_eq_upstream_model (n : ℕ) (β : ℝ) :
    (∫ W, Real.log (gibbsPartition β W) ∂skDisorderLaw n) / (n : ℝ) =
      (∫ J : SKConstantsOAI.SK.Disorder n, Real.log (SKConstantsOAI.SK.partition β J)
        ∂SKConstantsOAI.SK.disorderLaw n) / (n : ℝ) := by
  rw [expected_logPartition_eq_upstream]

end SKConstants.ParisiGOEBridge
