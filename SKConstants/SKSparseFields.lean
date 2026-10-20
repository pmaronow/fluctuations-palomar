module

public import SKConstants.SKLocalFieldConcentration
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def sparseFieldDirections (n r : ℕ) : Finset (Spin n × Spin n) :=
  (spinHammingBall (fun _ => false) r) ×ˢ (spinHammingBall (fun _ => false) r)

def sparseFieldDirection {n : ℕ} (p : Spin n × Spin n) (i : Fin n) : ℝ :=
  (signedSpin p.1 i - signedSpin p.2 i) / 2

theorem sparseFieldDirection_norm_sq {n : ℕ} (p : Spin n × Spin n) :
    ‖toLp 2 (sparseFieldDirection p)‖^2 = (hammingDist p.1 p.2 : ℝ) := by
  have he : toLp 2 (sparseFieldDirection p) =
      (1 / 2 : ℝ) • (spinEuclidean p.1 - spinEuclidean p.2) := by
    ext i
    change (signedSpin p.1 i - signedSpin p.2 i) / 2 =
      (1 / 2) * (signedSpin p.1 i - signedSpin p.2 i)
    ring
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), spinEuclidean_distance_sq]
  ring

theorem sparseFieldDirection_abs_sum {n : ℕ} (p : Spin n × Spin n) :
    (∑ i, |sparseFieldDirection p i|) = (hammingDist p.1 p.2 : ℝ) := by
  rw [← sparseFieldDirection_norm_sq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  cases h1 : p.1 i <;> cases h2 : p.2 i <;>
    norm_num [sparseFieldDirection, signedSpin, h1, h2]

theorem sparseFieldDirection_hamming_le {n r : ℕ} {p : Spin n × Spin n}
    (hp : p ∈ sparseFieldDirections n r) : hammingDist p.1 p.2 ≤ 2 * r := by
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
  have h1' := (Finset.mem_filter.mp h1).2
  have h2' := (Finset.mem_filter.mp h2).2
  have h := hammingDist_triangle p.1 (fun _ => false) p.2
  have h1'' : hammingDist p.1 (fun _ => false) ≤ r := by
    simpa only [hammingDist_comm] using h1'
  omega

theorem sparseFieldDirections_card_le (n r : ℕ) :
    (sparseFieldDirections n r).card ≤ ((r + 1) * (n + 1)^r)^2 := by
  rw [sparseFieldDirections, Finset.card_product]
  have h := spinHammingBall_card_le_pow (n := n) (fun _ => false) r
  simpa only [pow_two] using Nat.mul_self_le_mul_self h

def sparseFieldBadSet {n : ℕ} (x : Spin n) (r : ℕ) (A : ℝ) :
    Set (EuclideanSpace ℝ (Fin n × Fin n)) :=
  ⋃ p ∈ sparseFieldDirections n r,
    {z | A ≤ goeSignedSpinField (1 / Real.sqrt (2 * (n : ℝ))) x
      (sparseFieldDirection p) z}

theorem measurableSet_sparseFieldBadSet {n : ℕ} (x : Spin n) (r : ℕ) (A : ℝ) :
    MeasurableSet (sparseFieldBadSet x r A) := by
  apply Finset.measurableSet_biUnion
  intro p hp
  rw [goeSignedSpinField_eq_linearForm]
  apply measurableSet_le measurable_const
  let a := goeSpinFieldCoefficient (1 / Real.sqrt (2 * (n : ℝ))) x (sparseFieldDirection p)
  have he : (GaussianProposal.linearFormCLM a : EuclideanSpace ℝ (Fin n × Fin n) → ℝ) =
      GaussianProposal.linearForm a := funext (GaussianProposal.linearFormCLM_apply a)
  rw [← he]
  exact (GaussianProposal.linearFormCLM a).continuous.measurable

theorem conditionalGibbs_sparseFieldBadSet_tail {n r : ℕ} (hn : 0 < n)
    (_hr : 0 < r) (beta : ℝ) (x : Spin n) (A : ℝ) (hA : 4 * |beta| * (r : ℝ) ≤ A) :
    (conditionalGibbsGaussianLaw beta (1 / Real.sqrt (2 * (n : ℝ))) x).real
      (sparseFieldBadSet x r A) ≤
      (((r + 1) * (n + 1)^r : ℕ)^2 : ℝ) *
        Real.exp (-(A - 4 * |beta| * (r : ℝ))^2 / (8 * (r : ℝ))) := by
  let ν := conditionalGibbsGaussianLaw beta (1 / Real.sqrt (2 * (n : ℝ))) x
  have hp (p) (hpm : p ∈ sparseFieldDirections n r) : ν.real
      {z | A ≤ goeSignedSpinField (1 / Real.sqrt (2 * (n : ℝ))) x
        (sparseFieldDirection p) z} ≤
      Real.exp (-(A - 4 * |beta| * (r : ℝ))^2 / (8 * (r : ℝ))) := by
    let f := goeSignedSpinField (1 / Real.sqrt (2 * (n : ℝ))) x (sparseFieldDirection p)
    have hsg := sk_signedSpinField_hasSubgaussianMGF hn beta x (sparseFieldDirection p)
    have hq : ‖toLp 2 (sparseFieldDirection p)‖₊^2 ≤ (2 * r : ℝ≥0) := by
      change ‖toLp 2 (sparseFieldDirection p)‖^2 ≤ 2 * (r : ℝ)
      rw [sparseFieldDirection_norm_sq]
      exact_mod_cast sparseFieldDirection_hamming_le hpm
    have hm : ∫ z, f z ∂ν ≤ 4 * |beta| * (r : ℝ) := by
      have h := abs_sk_signedSpinField_mean_le hn beta x (sparseFieldDirection p)
      rw [sparseFieldDirection_abs_sum] at h
      have hd : (hammingDist p.1 p.2 : ℝ) ≤ 2 * (r : ℝ) := by
        exact_mod_cast sparseFieldDirection_hamming_le hpm
      exact (le_abs_self _).trans (h.trans (by nlinarith [abs_nonneg beta]))
    have hs : HasSubgaussianMGF (fun z => f z - ∫ y, f y ∂ν) (4 * r) ν := by
      refine ⟨hsg.integrable_exp_mul, fun t => (hsg.mgf_le t).trans ?_⟩
      apply Real.exp_le_exp.mpr
      have hqR : (‖toLp 2 (sparseFieldDirection p)‖₊ : ℝ)^2 ≤ 2 * (r : ℝ) := hq
      have ht := mul_le_mul_of_nonneg_right hqR (sq_nonneg t)
      change 2 * (‖toLp 2 (sparseFieldDirection p)‖₊ : ℝ)^2 * t^2 / 2 ≤
        (4 * (r : ℝ)) * t^2 / 2
      nlinarith
    have hsub : {z | A ≤ f z} ⊆ {z | A - 4 * |beta| * (r : ℝ) ≤ f z - ∫ y, f y ∂ν} := by
      intro z hz
      change A - 4 * |beta| * (r : ℝ) ≤ f z - ∫ y, f y ∂ν
      change A ≤ f z at hz
      linarith
    exact (measureReal_mono hsub).trans (by
      simpa only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
        show 2 * (4 * (r : ℝ)) = 8 * (r : ℝ) by ring] using
        hs.measure_ge_le (sub_nonneg.mpr hA))
  calc
    ν.real (sparseFieldBadSet x r A) ≤ ∑ p ∈ sparseFieldDirections n r, ν.real
        {z | A ≤ goeSignedSpinField (1 / Real.sqrt (2 * (n : ℝ))) x
          (sparseFieldDirection p) z} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ sparseFieldDirections n r,
        Real.exp (-(A - 4 * |beta| * (r : ℝ))^2 / (8 * (r : ℝ))) :=
      Finset.sum_le_sum (fun p hp' => hp p hp')
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast sparseFieldDirections_card_le n r

end SKConstants
