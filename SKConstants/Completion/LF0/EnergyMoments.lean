module

public import SKConstants.GaussianMaximum
public import Mathlib.MeasureTheory.Function.L2Space

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace SKConstants.Completion.LF0

@[expose] def frobSq {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (W i j) ^ 2

theorem frobSq_nonneg {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobSq W := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem continuous_frobSq {n : ℕ} : Continuous (frobSq (n := n)) := by
  unfold frobSq
  fun_prop

theorem quadraticHamiltonian_sq_le_frobSq {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    (quadraticHamiltonian W x) ^ 2 ≤ (n : ℝ) ^ 2 / 4 * frobSq W := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => W p.1 p.2) (fun p => signedSpin x p.1 * signedSpin x p.2)
  have hs : (∑ p : Fin n × Fin n, W p.1 p.2 *
      (signedSpin x p.1 * signedSpin x p.2)) =
      ∑ i, ∑ j, signedSpin x i * W i j * signedSpin x j := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mul_pow, signedSpin_sq, mul_one] at h
  rw [hs, Fintype.sum_prod_type] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_mul] at h
  unfold quadraticHamiltonian frobSq
  nlinarith

theorem spinHamiltonianMaximum_sq_le_frobSq {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) :
    (spinHamiltonianMaximum W) ^ 2 ≤ (n : ℝ) ^ 2 / 4 * frobSq W := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun x : Spin n => |quadraticHamiltonian W x|)
  have hm : spinHamiltonianMaximum W = |quadraticHamiltonian W x| := by
    simpa only [spinHamiltonianMaximum, finiteMaxAbs, Finset.sup'_apply] using hx
  rw [hm, sq_abs]
  exact quadraticHamiltonian_sq_le_frobSq W x

theorem goeEntry_second_moment {n : ℕ} (sigma : ℝ) (i j : Fin n) :
    (∫ z, (GaussianProposal.goeMatrix sigma z i j) ^ 2
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) =
      2 * sigma ^ 2 * (1 + if i = j then 1 else 0) := by
  have h := (GaussianProposal.goeEntry_gaussian sigma i j).memLp_two
  have hc := GaussianProposal.goeEntry_covariance sigma i j i j
  rw [covariance_eq_sub h h] at hc
  simpa [GaussianProposal.goeEntry_mean, Pi.mul_apply, ← pow_two, eq_comm] using hc

theorem integrable_frobSq_goe {n : ℕ} (sigma : ℝ) :
    Integrable (fun z => frobSq (GaussianProposal.goeMatrix (ι := Fin n) sigma z))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (GaussianProposal.goeEntry_gaussian sigma i j).memLp_two.integrable_sq

theorem frobSq_goe_integral (n : ℕ) (sigma : ℝ) :
    (∫ z, frobSq (GaussianProposal.goeMatrix (ι := Fin n) sigma z)
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) =
      2 * sigma ^ 2 * ((n : ℝ) ^ 2 + (n : ℝ)) := by
  unfold frobSq
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (GaussianProposal.goeEntry_gaussian sigma i j).memLp_two.integrable_sq))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    (GaussianProposal.goeEntry_gaussian sigma _ j).memLp_two.integrable_sq),
    goeEntry_second_moment]
  simp [mul_add, mul_ite, Finset.sum_add_distrib]
  ring

theorem integrable_frobSq_skDisorderLaw (n : ℕ) :
    Integrable (frobSq (n := n)) (skDisorderLaw n) := by
  apply (integrable_map_measure continuous_frobSq.measurable.aestronglyMeasurable
    (continuous_goeMatrix _).measurable.aemeasurable).mpr
  exact integrable_frobSq_goe _

theorem frobSq_skDisorderLaw_integral {n : ℕ} (hn : 0 < n) :
    (∫ W, frobSq W ∂skDisorderLaw n) = (n : ℝ) + 1 := by
  unfold skDisorderLaw
  rw [integral_map (continuous_goeMatrix _).measurable.aemeasurable
    continuous_frobSq.measurable.aestronglyMeasurable]
  rw [frobSq_goe_integral, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp
  ring

theorem integrable_spinHamiltonianMaximum_sq (n : ℕ) :
    Integrable (fun W => (spinHamiltonianMaximum W) ^ 2) (skDisorderLaw n) := by
  apply ((integrable_frobSq_skDisorderLaw n).const_mul ((n : ℝ) ^ 2 / 4)).mono'
    (continuous_spinHamiltonianMaximum.pow 2).measurable.aestronglyMeasurable
  filter_upwards with W
  simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs] using
    spinHamiltonianMaximum_sq_le_frobSq W

theorem memLp_spinHamiltonianMaximum (n : ℕ) :
    MemLp (spinHamiltonianMaximum (n := n)) 2 (skDisorderLaw n) := by
  exact (memLp_two_iff_integrable_sq
    continuous_spinHamiltonianMaximum.measurable.aestronglyMeasurable).mpr
      (integrable_spinHamiltonianMaximum_sq n)

theorem sk_spinHamiltonianMaximum_second_moment {n : ℕ} (hn : 0 < n) :
    (∫ W, (spinHamiltonianMaximum W) ^ 2 ∂skDisorderLaw n) ≤
      (n : ℝ) ^ 2 * ((n : ℝ) + 1) / 4 := by
  calc
    _ ≤ ∫ W, (n : ℝ) ^ 2 / 4 * frobSq W ∂skDisorderLaw n :=
      integral_mono (integrable_spinHamiltonianMaximum_sq n)
        ((integrable_frobSq_skDisorderLaw n).const_mul _)
        spinHamiltonianMaximum_sq_le_frobSq
    _ = _ := by rw [integral_const_mul, frobSq_skDisorderLaw_integral hn]; ring

theorem measurable_coupled_energy {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (X : Ω → Spin n)
    (hW : Measurable W) (hX : Measurable X) :
    Measurable (fun ω => quadraticHamiltonian (W ω) (X ω)) := by
  have hs (i : Fin n) : Measurable (fun ω => signedSpin (X ω) i) :=
    (measurable_of_finite (fun x : Spin n => signedSpin x i)).comp hX
  unfold quadraticHamiltonian
  fun_prop

theorem gaussian_marginal_energy_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ}
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (X : Ω → Spin n)
    (hW : Measurable W) (hX : Measurable X)
    (hmarg : μ.map W = skDisorderLaw n) :
    MemLp (fun ω => quadraticHamiltonian (W ω) (X ω)) 2 μ := by
  have hlaw : HasLaw W (skDisorderLaw n) μ := ⟨hW.aemeasurable, hmarg⟩
  apply (hlaw.memLp_fun_comp (memLp_spinHamiltonianMaximum n)).mono'
    (measurable_coupled_energy W X hW hX).aestronglyMeasurable
  filter_upwards with ω
  exact abs_le_finiteMaxAbs (fun x W => quadraticHamiltonian W x) (X ω) (W ω)

theorem gaussian_marginal_energy_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (X : Ω → Spin n)
    (hW : Measurable W) (hX : Measurable X)
    (hmarg : μ.map W = skDisorderLaw n) :
    (∫ ω, (quadraticHamiltonian (W ω) (X ω)) ^ 2 ∂μ) ≤
      (n : ℝ) ^ 2 * ((n : ℝ) + 1) / 4 := by
  have hlaw : HasLaw W (skDisorderLaw n) μ := ⟨hW.aemeasurable, hmarg⟩
  calc
    _ ≤ ∫ ω, (spinHamiltonianMaximum (W ω)) ^ 2 ∂μ := by
      apply integral_mono
        (gaussian_marginal_energy_memLp μ W X hW hX hmarg).integrable_sq
        (hlaw.integrable_fun_comp (integrable_spinHamiltonianMaximum_sq n))
      intro ω
      have hb := abs_le_finiteMaxAbs (fun x W => quadraticHamiltonian W x) (X ω) (W ω)
      simpa only [spinHamiltonianMaximum, ← pow_two, sq_abs] using
        mul_self_le_mul_self (abs_nonneg _) hb
    _ = ∫ W, (spinHamiltonianMaximum W) ^ 2 ∂skDisorderLaw n :=
      hlaw.integral_comp (continuous_spinHamiltonianMaximum.pow 2).measurable.aestronglyMeasurable
    _ ≤ _ := sk_spinHamiltonianMaximum_second_moment hn

end SKConstants.Completion.LF0
