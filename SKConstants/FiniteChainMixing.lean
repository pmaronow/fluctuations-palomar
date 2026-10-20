module

public import SKConstants.FiniteChainSemigroup
public import SKConstants.FiniteChainDirichlet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import SKConstants.EntropyDissipation
public import SKConstants.FiniteChainCheeger
public import Mathlib.Analysis.SpecificLimits.Basic

public section
noncomputable section

open scoped Matrix
namespace SKConstants

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Total variation between finite real vectors, in the half-L1 convention. -/
@[expose] def finiteTotalVariation (p q : Ω → ℝ) : ℝ :=
  (1 / ((2 : ℕ) : ℝ)) * ∑ x, |p x - q x|

@[expose] def finiteAveragedTV (pi : Ω → ℝ) (P : Matrix Ω Ω ℝ) : ℝ :=
  ∑ x, pi x * finiteTotalVariation (P x) pi

@[expose] def finiteChainAverageMixing (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ) (t : ℝ) : ℝ :=
  finiteAveragedTV pi (finiteChainSemigroup K t)

omit [DecidableEq Ω] in
theorem finiteTotalVariation_nonneg (p q : Ω → ℝ) : 0 ≤ finiteTotalVariation p q := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem finiteTotalVariation_contraction (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (p q : Ω → ℝ) :
    finiteTotalVariation (p ᵥ* K) (q ᵥ* K) ≤ finiteTotalVariation p q := by
  have hentry : ∀ y, |(p ᵥ* K) y - (q ᵥ* K) y| ≤ ∑ x, |p x - q x| * K x y := by
    intro y
    rw [← Pi.sub_apply, ← Matrix.sub_vecMul]
    simp only [Matrix.vecMul, dotProduct, Pi.sub_apply]
    calc
      |∑ x, (p x - q x) * K x y| ≤ ∑ x, |(p x - q x) * K x y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, |p x - q x| * K x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hK)]
  unfold finiteTotalVariation
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (∑ y, |(p ᵥ* K) y - (q ᵥ* K) y|) ≤ ∑ y, ∑ x, |p x - q x| * K x y :=
      Finset.sum_le_sum (fun y _ => hentry y)
    _ = ∑ x, |p x - q x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic hK, mul_one]

theorem finiteAveragedTV_mul_le (P K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (hstationary : pi ᵥ* K = pi) :
    finiteAveragedTV pi (P * K) ≤ finiteAveragedTV pi P := by
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hpi x)
  have hrow : (P * K) x = (P x) ᵥ* K := by
    funext y
    simp only [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rw [hrow]
  have h := finiteTotalVariation_contraction K hK (P x) pi
  rw [hstationary] at h
  exact h

theorem finiteChainAverageMixing_add_le (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (s t : ℝ) (ht : 0 ≤ t) :
    finiteChainAverageMixing K pi (s + t) ≤ finiteChainAverageMixing K pi s := by
  unfold finiteChainAverageMixing
  rw [finiteChainSemigroup_add]
  apply finiteAveragedTV_mul_le _ _ (finiteChainSemigroup_stochastic K hK t ht) pi hpi
  funext y
  exact finiteChainSemigroup_stationary K hK pi hbalance t ht y

theorem finiteChainAverageMixing_antitone (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    {s t : ℝ} (hst : s ≤ t) :
    finiteChainAverageMixing K pi t ≤ finiteChainAverageMixing K pi s := by
  have h := finiteChainAverageMixing_add_le K hK pi hpi hbalance s (t - s)
    (sub_nonneg.mpr hst)
  simpa using h

omit [DecidableEq Ω] in
theorem finiteTotalVariation_le_one (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    finiteTotalVariation p q ≤ 1 := by
  have hsum : (∑ x, |p x - q x|) ≤ 2 := by
    calc
      (∑ x, |p x - q x|) ≤ ∑ x, (p x + q x) := by
        apply Finset.sum_le_sum
        intro x _
        exact abs_sub_le_iff.mpr ⟨by linarith [hq x], by linarith [hp x]⟩
      _ = 2 := by rw [Finset.sum_add_distrib, hpsum, hqsum]; norm_num
  unfold finiteTotalVariation
  linarith

theorem finiteAveragedTV_le_one (pi : Ω → ℝ) (P : Matrix Ω Ω ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (hpisum : ∑ x, pi x = 1)
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) : finiteAveragedTV pi P ≤ 1 := by
  calc
    finiteAveragedTV pi P ≤ ∑ x, pi x * 1 := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hpi x)
      exact finiteTotalVariation_le_one (P x) pi
        (fun _ => Matrix.nonneg_of_mem_rowStochastic hP) hpi
        (Matrix.sum_row_of_mem_rowStochastic hP x) hpisum
    _ = 1 := by simpa using hpisum

omit [DecidableEq Ω] in
theorem finiteAveragedTV_nonneg (pi : Ω → ℝ) (P : Matrix Ω Ω ℝ)
    (hpi : ∀ x, 0 ≤ pi x) : 0 ≤ finiteAveragedTV pi P := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hpi x) (finiteTotalVariation_nonneg _ _))

omit [Fintype Ω] [DecidableEq Ω] in
theorem finite_weighted_cauchy_schwarz (pi u v : Ω → ℝ) (C : Finset Ω)
    (hpi : ∀ x, 0 ≤ pi x) :
    (∑ x ∈ C, pi x * |u x * v x|) ^ 2 ≤
      (∑ x ∈ C, pi x * (u x) ^ 2) * ∑ x ∈ C, pi x * (v x) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul C
    (fun x _ => mul_nonneg (hpi x) (sq_nonneg _))
    (fun x _ => mul_nonneg (hpi x) (sq_nonneg _))
  intro x _
  rw [mul_pow, sq_abs, mul_pow]
  ring_nf
  exact le_rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem finite_sqrt_mean_sq_le (pi f : Ω → ℝ) (C : Finset Ω)
    (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x, 0 ≤ f x)
    (hC : 0 < ∑ x ∈ C, pi x) :
    ((∑ x ∈ C, pi x * Real.sqrt (f x)) / (∑ x ∈ C, pi x)) ^ 2 *
      (∑ x ∈ C, pi x) ≤ ∑ x ∈ C, pi x * f x := by
  have h := finite_weighted_cauchy_schwarz pi (fun _ => 1)
    (fun x => Real.sqrt (f x)) C hpi
  simp only [one_mul, abs_of_nonneg (Real.sqrt_nonneg _), one_pow, mul_one,
    Real.sq_sqrt (hf _)] at h
  apply (le_of_mul_le_mul_right ?_ hC)
  field_simp
  exact h

omit [Fintype Ω] [DecidableEq Ω] in
theorem finite_density_core_l1_le (pi f : Ω → ℝ) (C : Finset Ω)
    (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x, 0 ≤ f x)
    (hfmass : ∑ x ∈ C, pi x * f x ≤ 1)
    (a : ℝ) (hamass : a ^ 2 * (∑ x ∈ C, pi x) ≤ 1) :
    (∑ x ∈ C, pi x * |f x - a ^ 2|) ≤
      2 * Real.sqrt (∑ x ∈ C, pi x * (Real.sqrt (f x) - a) ^ 2) := by
  let V := ∑ x ∈ C, pi x * (Real.sqrt (f x) - a) ^ 2
  let L := ∑ x ∈ C, pi x * |f x - a ^ 2|
  have hV : 0 ≤ V := Finset.sum_nonneg (fun x _ => mul_nonneg (hpi x) (sq_nonneg _))
  have hL : 0 ≤ L := Finset.sum_nonneg (fun x _ => mul_nonneg (hpi x) (abs_nonneg _))
  have hfactor : ∀ x, |(Real.sqrt (f x) - a) * (Real.sqrt (f x) + a)| =
      |f x - a ^ 2| := by
    intro x
    congr 1
    nlinarith [Real.sq_sqrt (hf x)]
  have hcs := finite_weighted_cauchy_schwarz pi
    (fun x => Real.sqrt (f x) - a) (fun x => Real.sqrt (f x) + a) C hpi
  simp only [hfactor] at hcs
  have hsecond : (∑ x ∈ C, pi x * (Real.sqrt (f x) + a) ^ 2) ≤ 4 := by
    calc
      (∑ x ∈ C, pi x * (Real.sqrt (f x) + a) ^ 2) ≤
          ∑ x ∈ C, pi x * (2 * f x + 2 * a ^ 2) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hpi x)
        nlinarith [sq_nonneg (Real.sqrt (f x) - a), Real.sq_sqrt (hf x)]
      _ = 2 * (∑ x ∈ C, pi x * f x) + 2 * a ^ 2 * (∑ x ∈ C, pi x) := by
        simp only [mul_add, Finset.sum_add_distrib]
        simp_rw [mul_comm (pi _) (2 * a ^ 2), ← Finset.mul_sum]
        rw [Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ 4 := by nlinarith
  have hsq : L ^ 2 ≤ 4 * V := by
    exact hcs.trans (by simpa only [V, mul_comm] using mul_le_mul_of_nonneg_left hsecond hV)
  have hsqrt := Real.sq_sqrt hV
  have hsnonneg := Real.sqrt_nonneg V
  change L ≤ 2 * Real.sqrt V
  nlinarith

omit [DecidableEq Ω] in
theorem finiteTotalVariation_density_eq (pi f : Ω → ℝ) (hpi : ∀ x, 0 ≤ pi x) :
    finiteTotalVariation (fun x => pi x * f x) pi =
      (1 / 2) * ∑ x, pi x * |f x - 1| := by
  unfold finiteTotalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change |pi x * f x - pi x| = _
  have heq : pi x * f x - pi x = pi x * (f x - 1) := by ring
  rw [heq, abs_mul, abs_of_nonneg (hpi x)]

theorem finite_density_retained_mass_error (pi f : Ω → ℝ) (C : Finset Ω)
    (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x, 0 ≤ f x)
    (hpisum : ∑ x, pi x = 1) (hfsum : ∑ x, pi x * f x = 1) :
    |∑ x ∈ C, pi x * (f x - 1)| ≤ ∑ x ∈ Cᶜ, pi x * (f x + 1) := by
  have hzero : (∑ x, pi x * (f x - 1)) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hpisum, hfsum, sub_self]
  have hsplit := C.sum_add_sum_compl (fun x => pi x * (f x - 1))
  rw [hzero] at hsplit
  have heq : (∑ x ∈ C, pi x * (f x - 1)) =
      -(∑ x ∈ Cᶜ, pi x * (f x - 1)) := by linarith
  rw [heq, abs_neg]
  calc
    |∑ x ∈ Cᶜ, pi x * (f x - 1)| ≤ ∑ x ∈ Cᶜ, |pi x * (f x - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Cᶜ, pi x * (f x + 1) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (hpi x)]
      apply mul_le_mul_of_nonneg_left _ (hpi x)
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith [hf x]⟩

theorem finite_density_tv_core_bound (pi f : Ω → ℝ) (C : Finset Ω)
    (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x, 0 ≤ f x)
    (hpisum : ∑ x, pi x = 1) (hfsum : ∑ x, pi x * f x = 1)
    (a : ℝ) (hamass : a ^ 2 * (∑ x ∈ C, pi x) ≤ 1) :
    finiteTotalVariation (fun x => pi x * f x) pi ≤
      2 * Real.sqrt (∑ x ∈ C, pi x * (Real.sqrt (f x) - a) ^ 2) +
        ∑ x ∈ Cᶜ, pi x * (f x + 1) := by
  let L := ∑ x ∈ C, pi x * |f x - a ^ 2|
  let E := ∑ x ∈ Cᶜ, pi x * (f x + 1)
  have hcmass : (∑ x ∈ C, pi x * f x) ≤ 1 := by
    rw [← hfsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => mul_nonneg (hpi x) (hf x))
  have hL := finite_density_core_l1_le pi f C hpi hf hcmass a hamass
  change L ≤ _ at hL
  have hE := finite_density_retained_mass_error pi f C hpi hf hpisum hfsum
  change |∑ x ∈ C, pi x * (f x - 1)| ≤ E at hE
  have hconst : (∑ x ∈ C, pi x) * |a ^ 2 - 1| ≤ L + E := by
    have heq : (∑ x ∈ C, pi x) * |a ^ 2 - 1| =
        |∑ x ∈ C, pi x * (a ^ 2 - 1)| := by
      rw [← Finset.sum_mul, abs_mul, abs_of_nonneg (Finset.sum_nonneg (fun x _ => hpi x))]
    rw [heq]
    have hdecomp : (∑ x ∈ C, pi x * (a ^ 2 - 1)) =
        (∑ x ∈ C, pi x * (a ^ 2 - f x)) + ∑ x ∈ C, pi x * (f x - 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hdecomp]
    calc
      |(∑ x ∈ C, pi x * (a ^ 2 - f x)) + ∑ x ∈ C, pi x * (f x - 1)| ≤
          |∑ x ∈ C, pi x * (a ^ 2 - f x)| + |∑ x ∈ C, pi x * (f x - 1)| :=
        abs_add_le _ _
      _ ≤ L + E := by
        apply add_le_add _ hE
        calc
          |∑ x ∈ C, pi x * (a ^ 2 - f x)| ≤ ∑ x ∈ C, |pi x * (a ^ 2 - f x)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = L := by
            apply Finset.sum_congr rfl
            intro x _
            rw [abs_mul, abs_of_nonneg (hpi x), abs_sub_comm]
  have hcore : (∑ x ∈ C, pi x * |f x - 1|) ≤ 2 * L + E := by
    calc
      (∑ x ∈ C, pi x * |f x - 1|) ≤
          ∑ x ∈ C, (pi x * |f x - a ^ 2| + pi x * |a ^ 2 - 1|) := by
        apply Finset.sum_le_sum
        intro x _
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (hpi x)
        exact abs_sub_le _ _ _
      _ = L + (∑ x ∈ C, pi x) * |a ^ 2 - 1| := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ 2 * L + E := by linarith
  have hcomp : (∑ x ∈ Cᶜ, pi x * |f x - 1|) ≤ E := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hpi x)
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith [hf x]⟩
  rw [finiteTotalVariation_density_eq pi f hpi, ← C.sum_add_sum_compl]
  change (1 / 2) * ((∑ x ∈ C, pi x * |f x - 1|) +
    (∑ x ∈ Cᶜ, pi x * |f x - 1|)) ≤ _
  linarith

@[expose] def finiteRetainedSqrtMean (pi f : Ω → ℝ) (C : Finset Ω) : ℝ :=
  (∑ y ∈ C, pi y * Real.sqrt (f y)) / (∑ y ∈ C, pi y)

@[expose] def finiteRetainedSqrtVariance (pi f : Ω → ℝ) (C : Finset Ω) : ℝ :=
  ∑ y ∈ C, pi y * (Real.sqrt (f y) - finiteRetainedSqrtMean pi f C) ^ 2

omit [DecidableEq Ω] in
theorem finite_average_sqrt_le (pi V : Ω → ℝ) (hpi : ∀ x, 0 ≤ pi x)
    (hpisum : ∑ x, pi x = 1) (hV : ∀ x, 0 ≤ V x) :
    (∑ x, pi x * Real.sqrt (V x)) ≤ Real.sqrt (∑ x, pi x * V x) := by
  have h := finite_weighted_cauchy_schwarz pi (fun x => Real.sqrt (V x))
    (fun _ => 1) Finset.univ hpi
  simp only [mul_one, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hV _),
    one_pow, hpisum] at h
  have hm : 0 ≤ ∑ x, pi x * V x :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hpi x) (hV x))
  have hs := Real.sq_sqrt hm
  have hn := Real.sqrt_nonneg (∑ x, pi x * V x)
  nlinarith

theorem finite_density_average_tv_core_bound (pi : Ω → ℝ) (f : Ω → Ω → ℝ)
    (C : Finset Ω) (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x y, 0 ≤ f x y)
    (hpisum : ∑ x, pi x = 1) (hfnorm : ∀ x, ∑ y, pi y * f x y = 1)
    (hstation : ∀ y, ∑ x, pi x * f x y = 1)
    (hC : 0 < ∑ y ∈ C, pi y) :
    (∑ x, pi x * finiteTotalVariation (fun y => pi y * f x y) pi) ≤
      2 * Real.sqrt (∑ x, pi x * finiteRetainedSqrtVariance pi (f x) C) +
        2 * (∑ y ∈ Cᶜ, pi y) := by
  have hfmass : ∀ x, (∑ y ∈ C, pi y * f x y) ≤ 1 := by
    intro x
    rw [← hfnorm x]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => mul_nonneg (hpi y) (hf x y))
  have hamass : ∀ x, (finiteRetainedSqrtMean pi (f x) C) ^ 2 * (∑ y ∈ C, pi y) ≤ 1 :=
    fun x => (finite_sqrt_mean_sq_le pi (f x) C hpi (hf x) hC).trans (hfmass x)
  have hV : ∀ x, 0 ≤ finiteRetainedSqrtVariance pi (f x) C := by
    intro x
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hpi y) (sq_nonneg _))
  have hcomp : (∑ x, pi x * (∑ y ∈ Cᶜ, pi y * (f x y + 1))) =
      2 * (∑ y ∈ Cᶜ, pi y) := by
    calc
      (∑ x, pi x * (∑ y ∈ Cᶜ, pi y * (f x y + 1))) =
          ∑ y ∈ Cᶜ, ∑ x, pi x * (pi y * (f x y + 1)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ =
          ∑ y ∈ Cᶜ, pi y * ((∑ x, pi x * f x y) + ∑ x, pi x) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 2 * (∑ y ∈ Cᶜ, pi y) := by
        simp only [hstation, hpisum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
  calc
    (∑ x, pi x * finiteTotalVariation (fun y => pi y * f x y) pi) ≤
        ∑ x, pi x * (2 * Real.sqrt (finiteRetainedSqrtVariance pi (f x) C) +
          ∑ y ∈ Cᶜ, pi y * (f x y + 1)) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (finite_density_tv_core_bound pi (f x) C hpi (hf x) hpisum (hfnorm x)
          (finiteRetainedSqrtMean pi (f x) C) (hamass x)) (hpi x)
    _ = 2 * (∑ x, pi x * Real.sqrt (finiteRetainedSqrtVariance pi (f x) C)) +
        2 * (∑ y ∈ Cᶜ, pi y) := by
      have heach : ∀ x, pi x * (2 * Real.sqrt (finiteRetainedSqrtVariance pi (f x) C) +
          ∑ y ∈ Cᶜ, pi y * (f x y + 1)) =
          pi x * (2 * Real.sqrt (finiteRetainedSqrtVariance pi (f x) C)) +
            pi x * (∑ y ∈ Cᶜ, pi y * (f x y + 1)) := fun x => mul_add _ _ _
      simp only [heach, Finset.sum_add_distrib]
      rw [hcomp]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left
        (finite_average_sqrt_le pi _ hpi hpisum hV) (show (0 : ℝ) ≤ 2 by norm_num)

omit [DecidableEq Ω] in
theorem finiteTotalVariation_stationary_mixture (p q : Ω → ℝ)
    (eta : ℝ) (heta1 : eta ≤ 1) :
    finiteTotalVariation (fun y => (1 - eta) * p y + eta * q y) q =
      (1 - eta) * finiteTotalVariation p q := by
  have heach : ∀ y, |(1 - eta) * p y + eta * q y - q y| =
      (1 - eta) * |p y - q y| := by
    intro y
    have heq : (1 - eta) * p y + eta * q y - q y =
        (1 - eta) * (p y - q y) := by ring
    rw [heq, abs_mul, abs_of_nonneg (sub_nonneg.mpr heta1)]
  unfold finiteTotalVariation
  simp only [heach, ← Finset.mul_sum]
  ring

@[expose] def finiteChainAverageRegularizedRetainedVariance (K : Matrix Ω Ω ℝ)
    (pi : Ω → ℝ) (eta : ℝ) (C : Finset Ω) (t : ℝ) : ℝ :=
  ∑ x, pi x * finiteRetainedSqrtVariance pi (finiteChainRegularizedDensity K pi eta t x) C

theorem finiteChain_regularized_tv_core_bound (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (hpisum : ∑ y, pi y = 1)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (C : Finset Ω) (hC : 0 < ∑ y ∈ C, pi y)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 - eta) * finiteChainAverageMixing K pi t ≤
      2 * Real.sqrt (finiteChainAverageRegularizedRetainedVariance K pi eta C t) +
        2 * (∑ y ∈ Cᶜ, pi y) := by
  have h := finite_density_average_tv_core_bound pi
    (finiteChainRegularizedDensity K pi eta t) C (fun y => (hpi y).le)
    (fun x y => (finiteChainRegularizedDensity_pos K hK pi hpi eta heta heta1 t ht x y).le)
    hpisum (finiteChainRegularizedDensity_sum K hK pi hpi hpisum eta t ht)
    (finiteChainRegularizedDensity_stationary_average K hK pi hpi hpisum hbalance eta t ht) hC
  have hrow : ∀ x, (fun y => pi y * finiteChainRegularizedDensity K pi eta t x y) =
      fun y => (1 - eta) * finiteChainSemigroup K t x y + eta * pi y := by
    intro x
    funext y
    simp only [finiteChainRegularizedDensity, finiteChainDensity, mul_add]
    have hp : pi y * (finiteChainSemigroup K t x y / pi y) =
        finiteChainSemigroup K t x y := mul_div_cancel₀ _ (hpi y).ne'
    calc
      pi y * ((1 - eta) * (finiteChainSemigroup K t x y / pi y)) + pi y * eta =
          (1 - eta) * (pi y * (finiteChainSemigroup K t x y / pi y)) + eta * pi y := by ring
      _ = _ := by rw [hp]
  simp only [hrow, finiteTotalVariation_stationary_mixture _ _ eta heta1] at h
  have havg : (∑ x, pi x * ((1 - eta) * finiteTotalVariation (finiteChainSemigroup K t x) pi)) =
      (1 - eta) * finiteChainAverageMixing K pi t := by
    unfold finiteChainAverageMixing finiteAveragedTV
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [havg] at h
  exact h

theorem continuous_finiteChainAverageRegularizedDirichlet (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x) (eta : ℝ) :
    Continuous (finiteChainAverageRegularizedDirichlet K pi eta) := by
  have hfc : ∀ x y, Continuous (fun t => finiteChainRegularizedDensity K pi eta t x y) :=
    fun x y => continuous_iff_continuousAt.mpr (fun t =>
      (finiteChainRegularizedDensity_hasDerivAt K hK pi hpi hbalance eta t x y).continuousAt)
  unfold finiteChainAverageRegularizedDirichlet finiteDirichletForm
  apply continuous_finsetSum
  intro x _
  apply continuous_const.mul
  apply continuous_const.mul
  apply continuous_finsetSum
  intro y _
  apply continuous_finsetSum
  intro z _
  exact continuous_const.mul (((Real.continuous_sqrt.comp (hfc x y)).sub
    (Real.continuous_sqrt.comp (hfc x z))).pow 2)

theorem finiteChain_regularized_mixing_of_retained_poincare (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (hpisum : ∑ y, pi y = 1)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (C : Finset Ω) (hC : 0 < ∑ y ∈ C, pi y)
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hcore : ∀ u : Ω → ℝ,
      (∑ y ∈ C, pi y * (u y - (∑ z ∈ C, pi z * u z) / (∑ z ∈ C, pi z)) ^ 2) ≤
        alpha * finiteDirichletForm pi K u)
    (eta T : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) (hT : 0 < T) :
    (1 - eta) * finiteChainAverageMixing K pi T ≤
      Real.sqrt (alpha * finiteShannonEntropy pi / T) + 2 * (∑ y ∈ Cᶜ, pi y) := by
  let A := (1 - eta) * finiteChainAverageMixing K pi T
  let E := 2 * (∑ y ∈ Cᶜ, pi y)
  let q := max (A - E) 0
  have hq : 0 ≤ q := le_max_right _ _
  have henergy : ∀ t,
      finiteChainAverageRegularizedRetainedVariance K pi eta C t ≤
        alpha * finiteChainAverageRegularizedDirichlet K pi eta t := by
    intro t
    unfold finiteChainAverageRegularizedRetainedVariance finiteChainAverageRegularizedDirichlet
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have h := mul_le_mul_of_nonneg_left
      (hcore (fun y => Real.sqrt (finiteChainRegularizedDensity K pi eta t x y))) (hpi x).le
    simpa only [finiteRetainedSqrtVariance, finiteRetainedSqrtMean, mul_assoc,
      mul_left_comm] using h
  have hpoint : ∀ t ∈ Set.Icc 0 T,
      q ^ 2 ≤ (4 * alpha) * finiteChainAverageRegularizedDirichlet K pi eta t := by
    intro t ht
    have hmono := mul_le_mul_of_nonneg_left
      (finiteChainAverageMixing_antitone K hK pi (fun y => (hpi y).le) hbalance ht.2)
      (sub_nonneg.mpr heta1)
    have hbound := finiteChain_regularized_tv_core_bound K hK pi hpi hpisum hbalance
      eta heta heta1 C hC t ht.1
    have hA : A ≤ 2 * Real.sqrt (finiteChainAverageRegularizedRetainedVariance K pi eta C t) + E :=
      hmono.trans hbound
    have hqle : q ≤ 2 * Real.sqrt (finiteChainAverageRegularizedRetainedVariance K pi eta C t) := by
      apply max_le
      · linarith
      · positivity
    have hV : 0 ≤ finiteChainAverageRegularizedRetainedVariance K pi eta C t := by
      apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg (hpi x).le
      exact Finset.sum_nonneg (fun y _ => mul_nonneg (hpi y).le (sq_nonneg _))
    have hsq := Real.sq_sqrt hV
    have hsr := Real.sqrt_nonneg (finiteChainAverageRegularizedRetainedVariance K pi eta C t)
    have hq2 : q ^ 2 ≤ 4 * finiteChainAverageRegularizedRetainedVariance K pi eta C t := by
      nlinarith
    nlinarith [henergy t]
  have hDc := continuous_finiteChainAverageRegularizedDirichlet K hK pi hpi hbalance eta
  have hint := intervalIntegral.integral_mono_on hT.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => q ^ 2)
      MeasureTheory.volume 0 T)
    ((hDc.const_mul (4 * alpha)).intervalIntegrable (μ := MeasureTheory.volume) 0 T) hpoint
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hint
  simp only [sub_zero, smul_eq_mul] at hint
  have hdiss := finiteChain_regularized_average_dissipation K hK pi hpi hpisum hbalance
    eta T heta heta1 hT.le
  have hH := finiteShannonEntropy_nonneg pi hpi hpisum
  have hsqbound : q ^ 2 ≤ alpha * finiteShannonEntropy pi / T := by
    apply (le_div_iff₀ hT).mpr
    have hscale := mul_le_mul_of_nonneg_left hdiss (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) halpha)
    nlinarith
  have harg : 0 ≤ alpha * finiteShannonEntropy pi / T := by positivity
  have hs := Real.sq_sqrt harg
  have hn := Real.sqrt_nonneg (alpha * finiteShannonEntropy pi / T)
  have hqbound : q ≤ Real.sqrt (alpha * finiteShannonEntropy pi / T) := by nlinarith
  have hgap : A - E ≤ q := le_max_left _ _
  change A ≤ _
  linarith

theorem finiteChain_mixing_of_retained_poincare (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (hpisum : ∑ y, pi y = 1)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (C : Finset Ω) (hC : 0 < ∑ y ∈ C, pi y)
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hcore : ∀ u : Ω → ℝ,
      (∑ y ∈ C, pi y * (u y - (∑ z ∈ C, pi z * u z) / (∑ z ∈ C, pi z)) ^ 2) ≤
        alpha * finiteDirichletForm pi K u)
    (T : ℝ) (hT : 0 < T) :
    finiteChainAverageMixing K pi T ≤
      Real.sqrt (alpha * finiteShannonEntropy pi / T) + 2 * (∑ y ∈ Cᶜ, pi y) := by
  have hlim : Filter.Tendsto
      (fun m : ℕ => (1 - (1 : ℝ) / ((m : ℝ) + 1)) * finiteChainAverageMixing K pi T)
      Filter.atTop (nhds (finiteChainAverageMixing K pi T)) := by
    have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    have h2 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h3 : Filter.Tendsto (fun _ : ℕ => finiteChainAverageMixing K pi T)
        Filter.atTop (nhds (finiteChainAverageMixing K pi T)) := tendsto_const_nhds
    simpa only [sub_zero, one_mul] using (h1.sub h2).mul h3
  apply le_of_tendsto' hlim
  intro m
  apply finiteChain_regularized_mixing_of_retained_poincare K hK pi hpi hpisum hbalance
    C hC alpha halpha hcore _ T (by positivity) _ hT
  apply (div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
  exact le_add_of_nonneg_left (Nat.cast_nonneg m)

theorem finiteChain_mixing_of_balanced_flow (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (hpisum : ∑ y, pi y = 1)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (q : Ω → Ω → ℝ) (hq : ∀ x y, 0 ≤ q x y)
    (hsym : ∀ x y, q x y = q y x)
    (R : ℝ) (hR : 0 ≤ R) (hrow : ∀ x, ∑ y, q x y ≤ R * pi x)
    (rho : ℝ) (hrho : 0 < rho)
    (henergy : ∀ u, Cheeger.dirichlet q u = rho * finiteDirichletForm pi K u)
    (epsilon B : ℝ) (hepsilon : 0 < epsilon) (hepsilon_third : epsilon < 1 / 3)
    (hB : 0 < B)
    (hbalanced : ∀ S : Finset Ω, epsilon ≤ cutMass pi S →
      cutMass pi S ≤ 1 - epsilon → B < cutFlow q S Sᶜ)
    (T : ℝ) (hT : 0 < T) :
    finiteChainAverageMixing K pi (rho * T) ≤
      Real.sqrt (2 * R * finiteShannonEntropy pi) / (B * Real.sqrt T) + 2 * epsilon := by
  obtain ⟨C, hCmass, hexpand⟩ := finite_balanced_flow_pruning pi q epsilon B
    hpi hpisum hq hepsilon hepsilon_third hB hbalanced
  have hC : 0 < cutMass pi C := by linarith
  have hcore : ∀ u : Ω → ℝ,
      (∑ y ∈ C, pi y * (u y - (∑ z ∈ C, pi z * u z) / (∑ z ∈ C, pi z)) ^ 2) ≤
        ((2 * R / B ^ 2) * rho) * finiteDirichletForm pi K u := by
    intro u
    have h := Cheeger.retained_core_cheeger_full pi q C B R
      (fun y => (hpi y).le) hC hq hsym hB hR hrow hexpand u
    rw [henergy u] at h
    simpa only [Cheeger.coreVariance, Cheeger.coreMean, cutMass, mul_assoc] using h
  have hm := finiteChain_mixing_of_retained_poincare K hK pi hpi hpisum hbalance C hC
    ((2 * R / B ^ 2) * rho) (by positivity) hcore (rho * T) (mul_pos hrho hT)
  have hrad : ((2 * R / B ^ 2) * rho) * finiteShannonEntropy pi / (rho * T) =
      (2 * R * finiteShannonEntropy pi) / (B ^ 2 * T) := by
    field_simp [hrho.ne', hB.ne', hT.ne']
  have hH := finiteShannonEntropy_nonneg pi hpi hpisum
  have hsqrt : Real.sqrt (((2 * R / B ^ 2) * rho) * finiteShannonEntropy pi / (rho * T)) =
      Real.sqrt (2 * R * finiteShannonEntropy pi) / (B * Real.sqrt T) := by
    rw [hrad, Real.sqrt_div, Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le]
    positivity
  rw [hsqrt] at hm
  have hcomp : (∑ y ∈ Cᶜ, pi y) < epsilon := by
    have h := cutMass_compl pi C hpisum
    unfold cutMass at h hCmass
    linarith
  exact hm.trans (by linarith)

end SKConstants
