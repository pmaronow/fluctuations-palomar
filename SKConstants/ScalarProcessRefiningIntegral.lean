module

public import SKConstants.ScalarObservationPredictableSums
public import SKConstants.GaussianIntegralCompletion
public import SKConstants.ScalarProcessLogCoshLimit
public import SKConstants.ScalarProcessVarianceBalance
import Mathlib

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

def scalarRefiningTime (K l i : ℕ) : ℝ≥0 :=
  (i : ℝ≥0) / ((K : ℝ≥0) * 2 ^ l)

lemma scalarRefiningTime_coe (K l i : ℕ) :
    (scalarRefiningTime K l i : ℝ) = (i : ℝ) / ((K : ℝ) * 2 ^ l) := by
  simp [scalarRefiningTime]

lemma scalarRefiningTime_monotone (K l : ℕ) : Monotone (scalarRefiningTime K l) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

lemma scalarRefiningTime_embed (K l d i : ℕ) :
    scalarRefiningTime K (l + d) (i * 2 ^ d) = scalarRefiningTime K l i := by
  unfold scalarRefiningTime
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  by_cases hK : K = 0
  · simp [hK]
  · have hKr : (K : ℝ≥0) ≠ 0 := by exact_mod_cast hK
    field_simp

lemma scalarRefiningTime_left_le (K l d i : ℕ) :
    scalarRefiningTime K l (i / 2 ^ d) ≤ scalarRefiningTime K (l + d) i := by
  rw [← scalarRefiningTime_embed K l d]
  exact scalarRefiningTime_monotone K (l + d) (Nat.div_mul_le_self i _)

lemma scalarRefiningTime_coarse_le (K l i : ℕ) :
    scalarRefiningTime K 0 (i / 2 ^ l) ≤ scalarRefiningTime K l i := by
  simpa only [zero_add] using scalarRefiningTime_left_le K 0 l i

def scalarRefiningLagSum {Ω : Type*} (g : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (K k l : ℕ) (u : Bool × Ω) : ℝ :=
  ∑ a ∈ Finset.range (k * 2 ^ l),
    g (scalarRefiningTime K l a : ℝ) *
      (Real.tanh (scalarHiddenContinuousField z B (scalarRefiningTime K l a) u) -
        Real.tanh (scalarHiddenContinuousField z B (scalarRefiningTime K 0 (a / 2 ^ l)) u)) *
      (scalarContinuousInnovation z B (scalarRefiningTime K l (a + 1)) u -
        scalarContinuousInnovation z B (scalarRefiningTime K l a) u)

def scalarRefiningLagCoefficient (g : ℝ → ℝ) (K l d : ℕ) :
    ScalarObservationPredictableCoefficient (scalarRefiningTime K (l + d)) := fun i w =>
  g (scalarRefiningTime K l (i / 2 ^ d) : ℝ) *
    (Real.tanh (w ⟨scalarRefiningTime K l (i / 2 ^ d), scalarRefiningTime_left_le K l d i⟩) -
      Real.tanh (w ⟨scalarRefiningTime K 0 (i / 2 ^ (l + d)),
        scalarRefiningTime_coarse_le K (l + d) i⟩))

lemma measurable_scalarRefiningLagCoefficient (g : ℝ → ℝ) (K l d i : ℕ) :
    Measurable (scalarRefiningLagCoefficient g K l d i) := by
  exact ((scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _)).sub
    (scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _))).const_mul _

lemma scalarRefiningLagCoefficient_abs_le (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (K l d i : ℕ)
    (w : Iic (scalarRefiningTime K (l + d) i) → ℝ) :
    |scalarRefiningLagCoefficient g K l d i w| ≤ 2 := by
  unfold scalarRefiningLagCoefficient
  rw [abs_mul]
  have ht := hg (scalarRefiningTime K l (i / 2 ^ d)) (NNReal.coe_nonneg _)
  have hdiff := norm_sub_le (Real.tanh (w ⟨_, scalarRefiningTime_left_le K l d i⟩))
    (Real.tanh (w ⟨_, scalarRefiningTime_coarse_le K (l+d) i⟩))
  simp only [Real.norm_eq_abs] at hdiff
  have h1 := scalar_tanh_abs_le_one (w ⟨_, scalarRefiningTime_left_le K l d i⟩)
  have h2 := scalar_tanh_abs_le_one (w ⟨_, scalarRefiningTime_coarse_le K (l+d) i⟩)
  have hd : |Real.tanh (w ⟨_, scalarRefiningTime_left_le K l d i⟩) -
      Real.tanh (w ⟨_, scalarRefiningTime_coarse_le K (l+d) i⟩)| ≤ 2 := by linarith
  exact (mul_le_mul ht hd (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

lemma sum_range_product_blocks (f : ℕ → ℝ) (n q : ℕ) :
    (∑ i ∈ Finset.range (n * q), f i) =
      ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range q, f (a * q + b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma sum_range_shift_increment (M : ℕ → ℝ) (a q : ℕ) :
    (∑ b ∈ Finset.range q, (M (a + b + 1) - M (a + b))) = M (a + q) - M a := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    rw [Nat.add_assoc]
    ring

lemma sum_weighted_refinement (H M : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range n, H a * (M ((a + 1) * q) - M (a * q))) =
      ∑ i ∈ Finset.range (n * q), H (i / q) * (M (i + 1) - M i) := by
  rw [sum_range_product_blocks]
  apply Finset.sum_congr rfl
  intro a ha
  have hd (b : ℕ) (hb : b ∈ Finset.range q) : (a * q + b) / q = a := by
    rw [Nat.mul_comm a q, Nat.mul_add_div hq,
      Nat.div_eq_of_lt (Finset.mem_range.mp hb), Nat.add_zero]
  have he : (∑ b ∈ Finset.range q, H ((a*q+b)/q) * (M (a*q+b+1)-M (a*q+b))) =
      ∑ b ∈ Finset.range q, H a * (M (a*q+b+1)-M (a*q+b)) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [hd b hb]
  rw [he, ← Finset.mul_sum, sum_range_shift_increment]
  simp only [Nat.add_mul, Nat.one_mul]

lemma scalarRefining_coarse_div (l d i : ℕ) :
    (i / 2 ^ d) / 2 ^ l = i / 2 ^ (l + d) := by
  rw [Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm]

lemma scalarRefiningLagSum_eq_finerPredictableSum {Ω : Type*} (g : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (K k l d : ℕ) (u : Bool × Ω) :
    scalarRefiningLagSum g z B K k l u =
      scalarObservationPredictableSum z B (scalarRefiningTime K (l + d))
        (scalarRefiningLagCoefficient g K l d) (k * 2 ^ (l + d)) u := by
  let H : ℕ → ℝ := fun a => g (scalarRefiningTime K l a : ℝ) *
    (Real.tanh (scalarHiddenContinuousField z B (scalarRefiningTime K l a) u) -
      Real.tanh (scalarHiddenContinuousField z B (scalarRefiningTime K 0 (a / 2 ^ l)) u))
  let M : ℕ → ℝ := fun i => scalarContinuousInnovation z B (scalarRefiningTime K (l+d) i) u
  calc
    scalarRefiningLagSum g z B K k l u =
        ∑ a ∈ Finset.range (k * 2 ^ l), H a * (M ((a+1)*2^d) - M (a*2^d)) := by
      simp only [scalarRefiningLagSum, H, M, scalarRefiningTime_embed]
    _ = ∑ i ∈ Finset.range ((k * 2 ^ l) * 2 ^ d), H (i / 2 ^ d) * (M (i+1)-M i) :=
      sum_weighted_refinement H M _ _ (by positivity)
    _ = scalarObservationPredictableSum z B (scalarRefiningTime K (l + d))
        (scalarRefiningLagCoefficient g K l d) (k * 2 ^ (l + d)) u := by
      rw [scalarObservationPredictableSum, predictableGaussianSum_eq_range_sum]
      simp only [pow_add, ← Nat.mul_assoc]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [H, M, scalarObservationCoefficient, scalarRefiningLagCoefficient,
        scalarActualObservationPast, brownianMeshIncrement, scalarRefining_coarse_div]

lemma memLp_scalarObservationPredictableSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ i, Measurable (H i))
    (C : ℝ) (hC : ∀ i w, ‖H i w‖ ≤ C) (n : ℕ) :
    MemLp (scalarObservationPredictableSum z B t H n) 2 (scalarHiddenBrownianLaw z P) := by
  have hHs := integrable_scalarObservationCoefficient_sq_of_bounded P z B hB t H hH C hC
  have hi := scalarObservationPredictableSum_L2_isometry P z B hB t ht H hH hHs n
  have hm : AEMeasurable (scalarObservationPredictableSum z B t H n)
      (scalarHiddenBrownianLaw z P) :=
    aemeasurable_predictableGaussianSum _ _ _
      (fun i => ((aestronglyMeasurable_scalarContinuousInnovation P z B hB _).aemeasurable.sub
        (aestronglyMeasurable_scalarContinuousInnovation P z B hB _).aemeasurable))
      (aemeasurable_scalarObservationCoefficient P z B hB t H hH) n
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hi.1

lemma memLp_scalarRefiningLagSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (K k l : ℕ) :
    MemLp (scalarRefiningLagSum g z B K k l) 2 (scalarHiddenBrownianLaw z P) := by
  have he : scalarRefiningLagSum g z B K k l =
      scalarObservationPredictableSum z B (scalarRefiningTime K l)
        (scalarRefiningLagCoefficient g K l 0) (k * 2 ^ l) := by
    funext u
    simpa only [Nat.add_zero] using scalarRefiningLagSum_eq_finerPredictableSum g z B K k l 0 u
  rw [he]
  exact memLp_scalarObservationPredictableSum P z B hB _ (scalarRefiningTime_monotone K l)
    _ (measurable_scalarRefiningLagCoefficient g K l 0) 2
    (fun i w => by simpa only [Real.norm_eq_abs] using scalarRefiningLagCoefficient_abs_le g hg K l 0 i w) _

lemma weighted_tanh_lag_difference_sq_le (a b x y c : ℝ)
    (_ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    (a * (Real.tanh x - Real.tanh c) - b * (Real.tanh y - Real.tanh c)) ^ 2 ≤
      8 * (a - b) ^ 2 + 2 * (x - y) ^ 2 := by
  have hA : |Real.tanh x - Real.tanh c| ≤ 2 := by
    have h := norm_sub_le (Real.tanh x) (Real.tanh c)
    simp only [Real.norm_eq_abs] at h
    linarith [scalar_tanh_abs_le_one x, scalar_tanh_abs_le_one c]
  have hAsq : (Real.tanh x - Real.tanh c) ^ 2 ≤ 4 := by
    have H := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mpr hA
    norm_num only [sq_abs] at H
    exact H
  have hbsq : b ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mpr hb
  have hD := scalar_tanh_abs_sub_le x y
  have hDsq : (Real.tanh x - Real.tanh y) ^ 2 ≤ (x - y) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hD
  have hx : ((a-b)*(Real.tanh x-Real.tanh c))^2 ≤ 4*(a-b)^2 := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hAsq (sq_nonneg (a-b))]
  have hy : (b*(Real.tanh x-Real.tanh y))^2 ≤ (x-y)^2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right hbsq (sq_nonneg _)).trans
      (by simpa only [one_mul] using hDsq)
  have he : a*(Real.tanh x-Real.tanh c)-b*(Real.tanh y-Real.tanh c) =
      (a-b)*(Real.tanh x-Real.tanh c)+b*(Real.tanh x-Real.tanh y) := by ring
  rw [he]
  nlinarith [sq_nonneg ((a-b)*(Real.tanh x-Real.tanh c)-b*(Real.tanh x-Real.tanh y))]

lemma integral_weighted_tanh_lag_difference_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (s t c : ℝ≥0) :
    (∫ u, (g s * (Real.tanh (scalarHiddenContinuousField z B s u) -
        Real.tanh (scalarHiddenContinuousField z B c u)) -
      g t * (Real.tanh (scalarHiddenContinuousField z B t u) -
        Real.tanh (scalarHiddenContinuousField z B c u))) ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      8 * (g s - g t) ^ 2 + 4 * |(s : ℝ) - t| + 4 * ((s : ℝ) - t) ^ 2 := by
  let X := fun u => g s * (Real.tanh (scalarHiddenContinuousField z B s u) -
      Real.tanh (scalarHiddenContinuousField z B c u)) -
    g t * (Real.tanh (scalarHiddenContinuousField z B t u) -
      Real.tanh (scalarHiddenContinuousField z B c u))
  have hX : AEStronglyMeasurable X (scalarHiddenBrownianLaw z P) :=
    ((((scalar_tanh_lipschitz.continuous.measurable.comp_aemeasurable
      (aemeasurable_scalarHiddenContinuousField P z B hB s)).sub
      (scalar_tanh_lipschitz.continuous.measurable.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB c))).const_mul _).sub
      (((scalar_tanh_lipschitz.continuous.measurable.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB t)).sub
        (scalar_tanh_lipschitz.continuous.measurable.comp_aemeasurable
          (aemeasurable_scalarHiddenContinuousField P z B hB c))).const_mul _)).aestronglyMeasurable
  have hXi : Integrable (fun u => X u ^ 2) (scalarHiddenBrownianLaw z P) := by
    apply (integrable_const (16 : ℝ)).mono' (hX.pow 2)
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hx : |X u| ≤ 4 := by
      dsimp [X]
      have hd1 := norm_sub_le (Real.tanh (scalarHiddenContinuousField z B s u))
        (Real.tanh (scalarHiddenContinuousField z B c u))
      have hd2 := norm_sub_le (Real.tanh (scalarHiddenContinuousField z B t u))
        (Real.tanh (scalarHiddenContinuousField z B c u))
      simp only [Real.norm_eq_abs] at hd1 hd2
      have hd1' : |Real.tanh (scalarHiddenContinuousField z B s u) -
          Real.tanh (scalarHiddenContinuousField z B c u)| ≤ 2 := by
        linarith [scalar_tanh_abs_le_one (scalarHiddenContinuousField z B s u),
          scalar_tanh_abs_le_one (scalarHiddenContinuousField z B c u)]
      have hd2' : |Real.tanh (scalarHiddenContinuousField z B t u) -
          Real.tanh (scalarHiddenContinuousField z B c u)| ≤ 2 := by
        linarith [scalar_tanh_abs_le_one (scalarHiddenContinuousField z B t u),
          scalar_tanh_abs_le_one (scalarHiddenContinuousField z B c u)]
      have h1 := mul_le_mul (hg s s.coe_nonneg) hd1' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      have h2 := mul_le_mul (hg t t.coe_nonneg) hd2' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      have hh := norm_sub_le (g s * (Real.tanh (scalarHiddenContinuousField z B s u) -
        Real.tanh (scalarHiddenContinuousField z B c u)))
        (g t * (Real.tanh (scalarHiddenContinuousField z B t u) -
        Real.tanh (scalarHiddenContinuousField z B c u)))
      simp only [Real.norm_eq_abs, abs_mul] at hh
      linarith
    change X u ^ 2 ≤ 16
    have H := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)).mpr hx
    norm_num only [sq_abs] at H
    exact H
  have hY := integrable_scalarHiddenContinuousField_increment_sq P z B hB s t
  have h := integral_mono hXi ((integrable_const (8*(g s-g t)^2)).add (hY.const_mul 2))
    (fun u => weighted_tanh_lag_difference_sq_le _ _ _ _ _ (hg s s.coe_nonneg) (hg t t.coe_nonneg))
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) (hY.const_mul 2), integral_const_mul,
    integral_const, probReal_univ, one_smul] at h
  simp only [integral_const_mul] at h
  have hbound := integral_scalarHiddenContinuousField_increment_sq_le P z B hB s t
  exact h.trans (by linarith)

lemma brownianMeshVariance_scalarRefiningTime (K p i : ℕ) :
    brownianMeshVariance (scalarRefiningTime K p) i = 1 / ((K : ℝ≥0) * 2 ^ p) := by
  apply NNReal.eq
  rw [brownianMeshVariance, NNReal.coe_sub (scalarRefiningTime_monotone K p (by omega))]
  simp only [scalarRefiningTime_coe, Nat.cast_add, Nat.cast_one, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_one]
  ring

lemma scalarRefiningTime_duration (K k p : ℕ) :
    scalarRefiningTime K p (k * 2 ^ p) = scalarRefiningTime K 0 k := by
  simpa only [zero_add] using scalarRefiningTime_embed K 0 p k

lemma scalarRefining_variance_sum (K k p : ℕ) :
    (∑ i ∈ Finset.range (k * 2 ^ p), (brownianMeshVariance (scalarRefiningTime K p) i : ℝ)) =
      (scalarRefiningTime K 0 k : ℝ) := by
  simp only [brownianMeshVariance_scalarRefiningTime, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rw [← scalarRefiningTime_duration K k p, scalarRefiningTime_coe]
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_ofNat]
  ring

lemma scalarRefiningTime_left_dist_le (K l d i : ℕ) :
    |(scalarRefiningTime K (l+d) i : ℝ) - scalarRefiningTime K l (i / 2 ^ d)| ≤
      (scalarRefiningTime K l 1 : ℝ) := by
  by_cases hK : K = 0
  · simp [hK, scalarRefiningTime]
  have hKr : (0:ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hden : (0:ℝ) < (K:ℝ)*2^(l+d) := by positivity
  have hid := congrArg (fun n : ℕ => (n : ℝ)) (Nat.mod_add_div i (2^d))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hid
  have he : (scalarRefiningTime K (l+d) i : ℝ) - scalarRefiningTime K l (i/2^d) =
      ((i % 2 ^ d : ℕ) : ℝ) / ((K:ℝ)*2^(l+d)) := by
    simp only [scalarRefiningTime_coe, pow_add]
    field_simp
    nlinarith
  rw [he, abs_of_nonneg (by positivity)]
  have hmod : ((i % 2 ^ d : ℕ) : ℝ) ≤ 2 ^ d := by
    exact_mod_cast (Nat.mod_lt i (by positivity : 0 < 2 ^ d)).le
  calc
    _ ≤ (2:ℝ)^d / ((K:ℝ)*2^(l+d)) := div_le_div_of_nonneg_right hmod hden.le
    _ = (scalarRefiningTime K l 1 : ℝ) := by
      rw [scalarRefiningTime_coe, pow_add]
      simp only [Nat.cast_one]
      field_simp

lemma scalarRefiningTime_le_duration {K k p i : ℕ} (hi : i ≤ k * 2 ^ p) :
    scalarRefiningTime K p i ≤ scalarRefiningTime K 0 k :=
  (scalarRefiningTime_monotone K p hi).trans_eq (scalarRefiningTime_duration K k p)

lemma scalarRefining_step_antitone (K : ℕ) :
    Antitone (fun l => (scalarRefiningTime K l 1 : ℝ)) := by
  by_cases hK : K = 0
  · simp [hK, scalarRefiningTime, antitone_const]
  have hKr : (0:ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  intro l m hlm
  simp only [scalarRefiningTime_coe, Nat.cast_one]
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hlm) (by positivity))

lemma scalarRefining_step_tendsto_zero (K : ℕ) :
    Tendsto (fun l => (scalarRefiningTime K l 1 : ℝ)) atTop (𝓝 0) := by
  by_cases hK : K = 0
  · simp [hK, scalarRefiningTime]
  have hKr : (0:ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  simpa only [scalarRefiningTime_coe, Nat.cast_one, one_div, Function.comp_def] using
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop hKr)

lemma weighted_tanh_lag_abs_le_two (a x c : ℝ) (ha : |a| ≤ 1) :
    |a * (Real.tanh x - Real.tanh c)| ≤ 2 := by
  rw [abs_mul]
  have H := norm_sub_le (Real.tanh x) (Real.tanh c)
  simp only [Real.norm_eq_abs] at H
  have hdiff : |Real.tanh x - Real.tanh c| ≤ 2 := by
    linarith [scalar_tanh_abs_le_one x, scalar_tanh_abs_le_one c]
  exact (mul_le_mul ha hdiff (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (by norm_num)

def scalarRefiningDifferenceCoefficient (g : ℝ → ℝ) (K m l : ℕ) :
    ScalarObservationPredictableCoefficient (scalarRefiningTime K (m+l)) := fun i w =>
  g (scalarRefiningTime K m (i/2^l) : ℝ) *
    (Real.tanh (w ⟨scalarRefiningTime K m (i/2^l), scalarRefiningTime_left_le K m l i⟩) -
      Real.tanh (w ⟨scalarRefiningTime K 0 (i/2^(m+l)), scalarRefiningTime_coarse_le K (m+l) i⟩)) -
  g (scalarRefiningTime K l (i/2^m) : ℝ) *
    (Real.tanh (w ⟨scalarRefiningTime K l (i/2^m), by
        simpa only [Nat.add_comm l m, mem_Iic] using scalarRefiningTime_left_le K l m i⟩) -
      Real.tanh (w ⟨scalarRefiningTime K 0 (i/2^(m+l)), scalarRefiningTime_coarse_le K (m+l) i⟩))

lemma measurable_scalarRefiningDifferenceCoefficient (g : ℝ → ℝ) (K m l i : ℕ) :
    Measurable (scalarRefiningDifferenceCoefficient g K m l i) := by
  exact (((scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _)).sub
    (scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _))).const_mul _).sub
    (((scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _)).sub
    (scalar_tanh_lipschitz.continuous.measurable.comp (measurable_pi_apply _))).const_mul _)

lemma scalarRefiningDifferenceCoefficient_abs_le (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (K m l i : ℕ) (w) :
    |scalarRefiningDifferenceCoefficient g K m l i w| ≤ 4 := by
  unfold scalarRefiningDifferenceCoefficient
  have H := norm_sub_le
    (g (scalarRefiningTime K m (i/2^l)) *
      (Real.tanh (w ⟨_,scalarRefiningTime_left_le K m l i⟩) -
        Real.tanh (w ⟨_,scalarRefiningTime_coarse_le K (m+l) i⟩)))
    (g (scalarRefiningTime K l (i/2^m)) *
      (Real.tanh (w ⟨_, by simpa only [Nat.add_comm l m, mem_Iic] using scalarRefiningTime_left_le K l m i⟩) -
        Real.tanh (w ⟨_,scalarRefiningTime_coarse_le K (m+l) i⟩)))
  simp only [Real.norm_eq_abs] at H
  linarith [weighted_tanh_lag_abs_le_two (g (scalarRefiningTime K m (i/2^l)))
      (w ⟨_,scalarRefiningTime_left_le K m l i⟩)
      (w ⟨_,scalarRefiningTime_coarse_le K (m+l) i⟩)
      (hg _ (NNReal.coe_nonneg _)),
    weighted_tanh_lag_abs_le_two (g (scalarRefiningTime K l (i/2^m)))
      (w ⟨_,by simpa only [Nat.add_comm l m, mem_Iic] using scalarRefiningTime_left_le K l m i⟩)
      (w ⟨_,scalarRefiningTime_coarse_le K (m+l) i⟩)
      (hg _ (NNReal.coe_nonneg _))]

lemma scalarRefiningLagSum_difference_eq {Ω : Type*} (g : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (K k m l : ℕ) (u : Bool × Ω) :
    scalarRefiningLagSum g z B K k m u - scalarRefiningLagSum g z B K k l u =
      scalarObservationPredictableSum z B (scalarRefiningTime K (m+l))
        (scalarRefiningDifferenceCoefficient g K m l) (k * 2^(m+l)) u := by
  have hm := scalarRefiningLagSum_eq_finerPredictableSum g z B K k m l u
  have hl := scalarRefiningLagSum_eq_finerPredictableSum g z B K k l m u
  simp only [scalarObservationPredictableSum, predictableGaussianSum_eq_range_sum,
    scalarObservationCoefficient, scalarRefiningLagCoefficient, scalarActualObservationPast,
    brownianMeshIncrement] at hm hl
  rw [Nat.add_comm l m] at hl
  rw [hm, hl, scalarObservationPredictableSum, predictableGaussianSum_eq_range_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [scalarObservationCoefficient, scalarRefiningDifferenceCoefficient,
    scalarActualObservationPast, brownianMeshIncrement]
  ring

lemma scalarRefiningDifferenceCoefficient_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (K m l i : ℕ) :
    (∫ u, scalarObservationCoefficient z B (scalarRefiningTime K (m+l))
      (scalarRefiningDifferenceCoefficient g K m l) i u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      8 * (g (scalarRefiningTime K m (i/2^l)) - g (scalarRefiningTime K l (i/2^m)))^2 +
      4 * |(scalarRefiningTime K m (i/2^l) : ℝ) - scalarRefiningTime K l (i/2^m)| +
      4 * ((scalarRefiningTime K m (i/2^l) : ℝ) - scalarRefiningTime K l (i/2^m))^2 := by
  exact integral_weighted_tanh_lag_difference_sq_le P g hg z B hB _ _ _

lemma scalarRefiningLagSum_difference_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (K k m l : ℕ) :
    (∫ u, (scalarRefiningLagSum g z B K k m u -
      scalarRefiningLagSum g z B K k l u)^2 ∂scalarHiddenBrownianLaw z P) =
    ∑ i : Fin (k * 2^(m+l)), (brownianMeshVariance (scalarRefiningTime K (m+l)) i : ℝ) *
      ∫ u, scalarObservationCoefficient z B (scalarRefiningTime K (m+l))
        (scalarRefiningDifferenceCoefficient g K m l) i u ^ 2 ∂scalarHiddenBrownianLaw z P := by
  simp_rw [scalarRefiningLagSum_difference_eq]
  exact scalarObservationPredictableSum_L2_isometry_sum P z B hB _
    (scalarRefiningTime_monotone K (m+l)) _ (measurable_scalarRefiningDifferenceCoefficient g K m l)
    (integrable_scalarObservationCoefficient_sq_of_bounded P z B hB _ _
      (measurable_scalarRefiningDifferenceCoefficient g K m l) 4
      (fun i w => by simpa only [Real.norm_eq_abs] using
        scalarRefiningDifferenceCoefficient_abs_le g hg K m l i w)) _

lemma scalarRefiningLagSum_difference_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (K k m l : ℕ) (C : ℝ)
    (hC : ∀ i < k * 2^(m+l),
      (∫ u, scalarObservationCoefficient z B (scalarRefiningTime K (m+l))
        (scalarRefiningDifferenceCoefficient g K m l) i u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤ C) :
    (∫ u, (scalarRefiningLagSum g z B K k m u -
      scalarRefiningLagSum g z B K k l u)^2 ∂scalarHiddenBrownianLaw z P) ≤
      (scalarRefiningTime K 0 k : ℝ) * C := by
  rw [scalarRefiningLagSum_difference_L2_isometry P g hg z B hB K k m l]
  calc
    _ ≤ ∑ i : Fin (k*2^(m+l)), (brownianMeshVariance (scalarRefiningTime K (m+l)) i : ℝ) * C :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hC i i.isLt) (NNReal.coe_nonneg _))
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      simpa only [brownianMeshVariance_scalarRefiningTime, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, Finset.card_range, nsmul_eq_mul]
        using scalarRefining_variance_sum K k (m+l)

lemma scalarRefiningDifferenceCoefficient_uniform_energy_small {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (hc : Continuous g) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (K k : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ l ≥ N, ∀ i < k * 2^(m+l),
      (∫ u, scalarObservationCoefficient z B (scalarRefiningTime K (m+l))
        (scalarRefiningDifferenceCoefficient g K m l) i u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤ eps := by
  let η := min (1:ℝ) (eps/32)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηeps : η ≤ eps/32 := min_le_right _ _
  have hu : UniformContinuousOn g (Icc 0 (scalarRefiningTime K 0 k : ℝ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ,hδ,hgδ⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  have hthreshold : 0 < min η δ / 2 := by positivity
  have hstep := (scalarRefining_step_tendsto_zero K).eventually
    (eventually_lt_nhds hthreshold)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hstep
  refine ⟨N, fun m hm l hl i hi => ?_⟩
  let s := scalarRefiningTime K m (i/2^l)
  let t := scalarRefiningTime K l (i/2^m)
  let v := scalarRefiningTime K (m+l) i
  have hsdist : |(v:ℝ)-s| ≤ (scalarRefiningTime K m 1 : ℝ) :=
    scalarRefiningTime_left_dist_le K m l i
  have htdist : |(v:ℝ)-t| ≤ (scalarRefiningTime K l 1 : ℝ) := by
    simpa only [Nat.add_comm l m] using scalarRefiningTime_left_dist_le K l m i
  have hsumη : (scalarRefiningTime K m 1 : ℝ) + scalarRefiningTime K l 1 < η := by
    have hh1 := hN m hm
    have hh2 := hN l hl
    have hh := min_le_left η δ
    linarith
  have hsumδ : (scalarRefiningTime K m 1 : ℝ) + scalarRefiningTime K l 1 < δ := by
    have hh1 := hN m hm
    have hh2 := hN l hl
    have hh := min_le_right η δ
    linarith
  have hdist : |(s:ℝ)-t| ≤ (scalarRefiningTime K m 1 : ℝ) + scalarRefiningTime K l 1 := by
    have hh := abs_sub_le (s:ℝ) v t
    rw [abs_sub_comm (s:ℝ) v] at hh
    linarith
  have hs : s ≤ scalarRefiningTime K 0 k :=
    (scalarRefiningTime_left_le K m l i).trans (scalarRefiningTime_le_duration hi.le)
  have ht : t ≤ scalarRefiningTime K 0 k := by
    have htv : t ≤ v := by simpa only [Nat.add_comm l m] using scalarRefiningTime_left_le K l m i
    exact htv.trans (scalarRefiningTime_le_duration hi.le)
  have hs01 : (s:ℝ) ∈ Icc 0 (scalarRefiningTime K 0 k : ℝ) :=
    ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  have ht01 : (t:ℝ) ∈ Icc 0 (scalarRefiningTime K 0 k : ℝ) :=
    ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have hgd : |g s - g t| < η := by
    simpa only [Real.dist_eq] using hgδ s hs01 t ht01 (by
      simpa only [Real.dist_eq] using hdist.trans_lt hsumδ)
  have hgdsq : (g s - g t)^2 ≤ η^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hη.le).mpr hgd.le
  have hstd : |(s:ℝ)-t| ≤ η := (hdist.trans_lt hsumη).le
  have hstdsq : ((s:ℝ)-t)^2 ≤ η^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hη.le).mpr hstd
  have hηsq : η^2 ≤ η := by nlinarith
  have hmoment := scalarRefiningDifferenceCoefficient_integral_sq_le P g hg z B hB.toIsPreBrownianReal K m l i
  change _ ≤ 8*(g s-g t)^2+4*|(s:ℝ)-t|+4*((s:ℝ)-t)^2 at hmoment
  exact hmoment.trans (by nlinarith)

lemma scalarRefiningLagSum_L2_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (hc : Continuous g) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (K k : ℕ) :
    ∀ eps > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ l ≥ N,
      (∫ u, (scalarRefiningLagSum g z B K k m u -
        scalarRefiningLagSum g z B K k l u)^2 ∂scalarHiddenBrownianLaw z P) < eps := by
  intro eps heps
  let T := (scalarRefiningTime K 0 k : ℝ)
  have hT : 0 ≤ T := NNReal.coe_nonneg _
  have hT1 : 0 < T+1 := by linarith
  obtain ⟨N,hN⟩ := scalarRefiningDifferenceCoefficient_uniform_energy_small P g hg hc z B hB K k
    (eps/(T+1)) (div_pos heps hT1)
  refine ⟨N, fun m hm l hl => ?_⟩
  have h := scalarRefiningLagSum_difference_integral_sq_le P g hg z B hB K k m l
    (eps/(T+1)) (hN m hm l hl)
  exact h.trans_lt (by
    change T*(eps/(T+1)) < eps
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hT1).mpr
    nlinarith)

theorem scalarRefiningLagSum_exists_L2_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : ℝ → ℝ)
    (hg : ∀ t ≥ 0, |g t| ≤ 1) (hc : Continuous g) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (K k : ℕ) :
    ∃ I : Bool × Ω → ℝ, MemLp I 2 (scalarHiddenBrownianLaw z P) ∧
      (∀ l, Integrable (fun u => (scalarRefiningLagSum g z B K k l u - I u)^2)
        (scalarHiddenBrownianLaw z P)) ∧
      Tendsto (fun l => ∫ u, (scalarRefiningLagSum g z B K k l u - I u)^2
        ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  let F : ℕ → Lp ℝ 2 (scalarHiddenBrownianLaw z P) := fun l =>
    (memLp_scalarRefiningLagSum P g hg z B hB K k l).toLp (scalarRefiningLagSum g z B K k l)
  have hcauchy : CauchySeq F := by
    apply Metric.cauchySeq_iff.2
    intro eps heps
    obtain ⟨N,hN⟩ := scalarRefiningLagSum_L2_cauchy P g hg hc z B hB K k (eps^2) (sq_pos_of_pos heps)
    refine ⟨N,fun m hm l hl => ?_⟩
    have he : dist (F m) (F l)^2 = ∫ u,
        (scalarRefiningLagSum g z B K k m u - scalarRefiningLagSum g z B K k l u)^2
        ∂scalarHiddenBrownianLaw z P := by
      rw [dist_eq_norm]
      exact norm_toLp_difference_sq_eq_integral
        (memLp_scalarRefiningLagSum P g hg z B hB K k m)
        (memLp_scalarRefiningLagSum P g hg z B hB K k l)
    have hh := hN m hm l hl
    rw [← he] at hh
    nlinarith [show 0 ≤ dist (F m) (F l) from dist_nonneg]
  obtain ⟨I,hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨I,Lp.memLp I,?_,?_⟩
  · intro l
    exact ((memLp_scalarRefiningLagSum P g hg z B hB K k l).sub (Lp.memLp I)).integrable_sq
  · have hn : Tendsto (fun l => ‖F l-I‖^2) atTop (𝓝 0) := by
      simpa using ((hI.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (𝓝 I))).norm).pow 2
    have he : (fun l => ∫ u, (scalarRefiningLagSum g z B K k l u - I u)^2
        ∂scalarHiddenBrownianLaw z P) = fun l => ‖F l-I‖^2 := by
      funext l
      exact (norm_toLp_sub_sq_eq_integral
        (memLp_scalarRefiningLagSum P g hg z B hB K k l) I).symm
    rw [he]
    exact hn

theorem scalarActualRefiningLagSum_exists_L2_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (K k : ℕ) :
    ∃ I : Bool × Ω → ℝ, MemLp I 2 (scalarHiddenBrownianLaw z P) ∧
      (∀ l, Integrable (fun u => (scalarRefiningLagSum
        (fun t => Real.sqrt (scalarHiddenExpectedDefectSqReal P z B t)) z B K k l u - I u)^2)
        (scalarHiddenBrownianLaw z P)) ∧
      Tendsto (fun l => ∫ u, (scalarRefiningLagSum
        (fun t => Real.sqrt (scalarHiddenExpectedDefectSqReal P z B t)) z B K k l u - I u)^2
        ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  apply scalarRefiningLagSum_exists_L2_limit P _ _
    (continuous_scalarHiddenExpectedDefectSqReal P z B hB).sqrt z B hB K k
  intro t ht
  have hr : 0 ≤ scalarHiddenExpectedDefectSqReal P z B t :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hb := scalarHiddenExpectedDefectSqReal_norm_le_one P z B t
  rw [Real.norm_eq_abs, abs_of_nonneg hr] at hb
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg (scalarHiddenExpectedDefectSqReal P z B t)]

end SKConstants
