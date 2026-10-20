module

public import MatrixTraceComparison
public import Mathlib.Probability.Moments.Variance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def probabilityVectorCovariance {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : I → Ω → ℝ) : Matrix I I ℝ :=
  fun i j => covariance (X i) (X j) μ

theorem probabilityVectorCovariance_apply {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (i j : I) :
    probabilityVectorCovariance μ X i j =
      (∫ z, X i z*X j z ∂μ)-(∫ z, X i z ∂μ)*(∫ z, X j z ∂μ) := by
  simpa only [probabilityVectorCovariance, Pi.mul_apply] using covariance_eq_sub (hX i) (hX j)

theorem probabilityVectorCovariance_posSemidef {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    (probabilityVectorCovariance μ X).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [probabilityVectorCovariance, star_trivial] using (covariance_comm (μ := μ) (X i) (X j)).symm
  · intro v
    simp only [star_trivial, Matrix.mulVec, dotProduct, probabilityVectorCovariance, Finset.mul_sum]
    let Y (i : I) (z : Ω) := v i*X i z
    have hY (i : I) : MemLp (Y i) 2 μ := (hX i).const_mul _
    have hsum : MemLp (fun z => ∑ i, Y i z) 2 μ := memLp_finsetSum _ fun i _ => hY i
    have he := covariance_fun_sum_fun_sum hY hY
    rw [covariance_self hsum.aemeasurable] at he
    simp only [Y, covariance_const_mul_left, covariance_const_mul_right] at he
    have hnonneg := variance_nonneg (fun z => ∑ i, Y i z) μ
    rw [he] at hnonneg
    convert hnonneg using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem probabilityVectorCovariance_trace {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    (probabilityVectorCovariance μ X).trace =
      (∫ z, ∑ i, (X i z)^2 ∂μ) - ∑ i, (∫ z, X i z ∂μ)^2 := by
  unfold Matrix.trace Matrix.diag probabilityVectorCovariance
  simp_rw [covariance_eq_sub (hX _) (hX _)]
  simp only [Pi.mul_apply, ← pow_two, Finset.sum_sub_distrib]
  rw [integral_finsetSum]
  exact fun i _ => (hX i).integrable_sq

theorem probabilityVectorCovariance_trace_le_one {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hbound : ∀ᵐ z ∂μ, (∑ i, (X i z)^2) ≤ 1) :
    (probabilityVectorCovariance μ X).trace ≤ 1 := by
  rw [probabilityVectorCovariance_trace μ X hX]
  have hsum : Integrable (fun z => ∑ i, (X i z)^2) μ :=
    integrable_finsetSum _ fun i _ => (hX i).integrable_sq
  have hle := integral_mono_ae hsum (integrable_const (1 : ℝ)) hbound
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  have hn := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (∫ z, X i z ∂μ)
  linarith

theorem matrix_average_square_le {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → Matrix I I ℝ) (hH : ∀ i j, MemLp (fun z => H z i j) 2 μ) :
    (∑ i, ∑ j, (∫ z, H z i j ∂μ)^2) ≤
      ∫ z, ∑ i, ∑ j, (H z i j)^2 ∂μ := by
  have hentry (i j : I) : (∫ z, H z i j ∂μ)^2 ≤ ∫ z, (H z i j)^2 ∂μ := by
    have h := variance_nonneg (fun z => H z i j) μ
    rw [variance_eq_sub (hH i j)] at h
    simp only [Pi.pow_apply] at h
    linarith
  calc
    _ ≤ ∑ i, ∑ j, ∫ z, (H z i j)^2 ∂μ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = ∫ z, ∑ i, ∑ j, (H z i j)^2 ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        exact fun j _ => (hH i j).integrable_sq
      · intro i _
        exact integrable_finsetSum _ fun j _ => (hH i j).integrable_sq

theorem hessian_projection_square_le {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → Matrix I I ℝ) (hH : ∀ i j, MemLp (fun z => H z i j) 2 μ)
    {K C : Matrix I I ℝ} {m : ℝ} (hC : C.PosSemidef) (htrace : C.trace ≤ 1)
    (hprojection : ∀ i j, K i j = (∫ z, H z i j ∂μ) + m*C i j) :
    (∑ i, ∑ j, (K i j)^2) ≤
      2*(∫ z, ∑ i, ∑ j, (H z i j)^2 ∂μ) + 2*m^2*C.trace := by
  have hCov : (∑ i, ∑ j, (C i j)^2) ≤ C.trace := by
    have hh := OAI.SKFluctuations.posSemidef_entry_squares_le_trace_square hC
    have h0 := hC.trace_nonneg
    nlinarith
  have hJ := matrix_average_square_le μ H hH
  calc
    _ ≤ ∑ i, ∑ j, (2*(∫ z, H z i j ∂μ)^2 + 2*m^2*(C i j)^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [hprojection]
      nlinarith [sq_nonneg ((∫ z, H z i j ∂μ) - m*C i j)]
    _ = 2*(∑ i, ∑ j, (∫ z, H z i j ∂μ)^2) +
        2*m^2*(∑ i, ∑ j, (C i j)^2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hJ (by norm_num))
      (mul_le_mul_of_nonneg_left hCov (by positivity))

theorem hessian_spin_projection_square_le {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → Matrix I I ℝ) (hH : ∀ i j, MemLp (fun z => H z i j) 2 μ)
    (X : I → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hbound : ∀ᵐ z ∂μ, (∑ i, (X i z)^2) ≤ 1)
    {K : Matrix I I ℝ} {m : ℝ}
    (hprojection : ∀ i j, K i j = (∫ z, H z i j ∂μ) +
      m*probabilityVectorCovariance μ X i j) :
    (∑ i, ∑ j, (K i j)^2) ≤
      2*(∫ z, ∑ i, ∑ j, (H z i j)^2 ∂μ) +
        2*m^2*((∫ z, ∑ i, (X i z)^2 ∂μ)-∑ i, (∫ z, X i z ∂μ)^2) := by
  have h := hessian_projection_square_le μ H hH
    (probabilityVectorCovariance_posSemidef μ X hX)
    (probabilityVectorCovariance_trace_le_one μ X hX hbound) hprojection
  rwa [probabilityVectorCovariance_trace μ X hX] at h

theorem weighted_projection_mesh_loss {I : Type*} [Fintype I]
    (duration mass energy : I → ℝ) {mesh M : ℝ}
    (hmesh0 : 0 ≤ mesh)
    (hduration : ∀ i, 0 ≤ duration i) (hmesh : ∀ i, duration i ≤ mesh)
    (hmass : ∀ i, mass i ∈ Set.Icc (0 : ℝ) 1)
    (henergy : ∀ i, 0 ≤ energy i) (hcap : (∑ i, energy i) ≤ M) :
    (∑ i, 2*duration i*(mass i)^2*energy i) ≤ 2*mesh*M := by
  classical
  have hterm (i : I) : 2*duration i*(mass i)^2*energy i ≤ 2*mesh*energy i := by
    have hm2 : (mass i)^2 ≤ 1 := by
      nlinarith [(hmass i).1, (hmass i).2]
    have hd := mul_le_mul_of_nonneg_left hm2 (hduration i)
    have he := mul_le_mul_of_nonneg_right (hd.trans (by simpa using hmesh i)) (henergy i)
    nlinarith
  calc
    _ ≤ ∑ i, 2*mesh*energy i := Finset.sum_le_sum fun i _ => hterm i
    _ = 2*mesh*(∑ i, energy i) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcap (by positivity)

end OAI.SKFluctuations.LaplaceWindowFormalization
