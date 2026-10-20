module
public import SKConstants.ScalarProcessLagTailMoments

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def scalarDeterministicLagCoefficient (z : ℝ) (ρ : ℕ → ℝ) : ScalarFiniteHistoryCoefficient :=
  fun k p => ρ k * scalarLagCoefficient z k p

def scalarDeterministicLagTruncatedCoefficient (z : ℝ) (ρ : ℕ → ℝ) (b : ℝ) :
    ScalarFiniteHistoryCoefficient := fun k p => ρ k * scalarLagTruncatedCoefficient z b k p

def scalarDeterministicLagInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0) (ρ : ℕ → ℝ) (n : ℕ) :=
  scalarPredictableInnovationSum z dt (scalarDeterministicLagCoefficient z ρ) n

lemma measurable_scalarDeterministicLagCoefficient (z : ℝ) (ρ : ℕ → ℝ) (k : ℕ) :
    Measurable (scalarDeterministicLagCoefficient z ρ k) :=
  (measurable_scalarLagCoefficient z k).const_mul (ρ k)

lemma measurable_scalarDeterministicLagTruncatedCoefficient (z : ℝ) (ρ : ℕ → ℝ) (b : ℝ) (k : ℕ) :
    Measurable (scalarDeterministicLagTruncatedCoefficient z ρ b k) :=
  (measurable_scalarLagTruncatedCoefficient z b k).const_mul (ρ k)

lemma scalarDeterministicLagTruncatedCoefficient_abs_le (z : ℝ) (ρ : ℕ → ℝ)
    (hρ : ∀ k, |ρ k| ≤ 1) (b : ℝ) (hb : 0 ≤ b) (k : ℕ) (p : ScalarObservationHistory k) :
    |scalarDeterministicLagTruncatedCoefficient z ρ b k p| ≤ b := by
  change |ρ k * scalarLagTruncatedCoefficient z b k p| ≤ b
  rw [abs_mul]
  exact (mul_le_mul (hρ k) (scalarLagTruncatedCoefficient_abs_le z b hb k p)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul b)

lemma scalarDeterministicLagInnovationSum_eq_truncated (z : ℝ) (dt : ℕ → ℝ≥0)
    (ρ : ℕ → ℝ) (b : ℝ) (n : ℕ) (p : ScalarObservationHistory n)
    (hp : scalarLagRunningMax z n p ≤ b) :
    scalarDeterministicLagInnovationSum z dt ρ n p =
      scalarPredictableInnovationSum z dt (scalarDeterministicLagTruncatedCoefficient z ρ b) n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := (max_le_iff.mp hp).1
    have hcur := (max_le_iff.mp hp).2
    change scalarDeterministicLagInnovationSum z dt ρ n p.1 +
      (ρ n * scalarLagCoefficient z n p.1) * scalarInnovation (scalarLastField z n p.1) (dt n) p.2 =
      scalarPredictableInnovationSum z dt (scalarDeterministicLagTruncatedCoefficient z ρ b) n p.1 +
        (ρ n * scalarLagTruncatedCoefficient z b n p.1) *
          scalarInnovation (scalarLastField z n p.1) (dt n) p.2
    rw [ih p.1 hprev]
    simp only [scalarLagTruncatedCoefficient, ite_eq_left hcur]

lemma scalarDeterministicLagInnovationSum_two_term_tail (z : ℝ) (dt : ℕ → ℝ≥0)
    (ρ : ℕ → ℝ) (hρ : ∀ k, |ρ k| ≤ 1) (b h : ℝ) (hh : 0 < h) (hbh : h < b) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) (x : ℝ) (hx : 0 ≤ x) :
    (scalarObservationHistoryLaw z dt n).real {p | x ≤ |scalarDeterministicLagInnovationSum z dt ρ n p|} ≤
      2*Real.exp (-((b-h)^2/(4*h))) + 2*Real.exp (-(x^2/(4*b^2*h))) := by
  have hb : 0 < b := by linarith
  have hsubset : {p : ScalarObservationHistory n | x ≤ |scalarDeterministicLagInnovationSum z dt ρ n p|} ⊆
      {p | b < scalarLagRunningMax z n p} ∪
      {p | x ≤ |scalarPredictableInnovationSum z dt (scalarDeterministicLagTruncatedCoefficient z ρ b) n p|} := by
    intro p hp
    by_cases hc : b < scalarLagRunningMax z n p
    · exact Or.inl hc
    · apply Or.inr
      change x ≤ |scalarPredictableInnovationSum z dt (scalarDeterministicLagTruncatedCoefficient z ρ b) n p|
      change x ≤ |scalarDeterministicLagInnovationSum z dt ρ n p| at hp
      rwa [← scalarDeterministicLagInnovationSum_eq_truncated z dt ρ b n p (le_of_not_gt hc)]
  have hproxy (p : ScalarObservationHistory n) : scalarPredictableInnovationProxy dt
      (scalarDeterministicLagTruncatedCoefficient z ρ b) n p ≤ 2*b^2*h := by
    apply scalarPredictableInnovationProxy_le_duration dt _ n b h _ hdt hduration p
    intro k _ q
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (scalarDeterministicLagTruncatedCoefficient_abs_le z ρ hρ b hb.le k q) 2
  have ht := scalarPredictableInnovationSum_two_sided_tail z dt _
    (measurable_scalarDeterministicLagTruncatedCoefficient z ρ b) n (2*b^2*h)
    (ae_of_all _ hproxy) (by positivity) x hx
  have he : 2*(2*b^2*h) = 4*b^2*h := by ring
  rw [he] at ht
  exact (measureReal_mono hsubset).trans ((measureReal_union_le _ _).trans
    (add_le_add (scalarLagRunningMax_crossing_tail z dt b h hh hbh n hdt hduration) ht))

lemma scalarDeterministicLagInnovationSum_exponential_tail_large (z : ℝ) (dt : ℕ → ℝ≥0)
    (ρ : ℕ → ℝ) (hρ : ∀ k, |ρ k| ≤ 1) (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h)
    (x : ℝ) (hx : 4*h^2 ≤ x) :
    (scalarObservationHistoryLaw z dt n).real {p | x ≤ |scalarDeterministicLagInnovationSum z dt ρ n p|} ≤
      4 * Real.exp (-(x/(16*h))) := by
  have hxp : 0 < x := lt_of_lt_of_le (by positivity : 0 < 4*h^2) hx
  have hs0 := Real.sqrt_nonneg x
  have hss := Real.sq_sqrt hxp.le
  have hs : 2*h ≤ Real.sqrt x := by nlinarith
  have hsq : x/4 ≤ (Real.sqrt x-h)^2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt x/2)
      (by linarith : Real.sqrt x/2 ≤ Real.sqrt x-h) 2
    nlinarith
  have hcross : x/(16*h) ≤ (Real.sqrt x-h)^2/(4*h) := by
    have hc := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 4*h)
    convert hc using 1
    field_simp
    ring
  have hsecond : x/(16*h) ≤ x^2/(4*(Real.sqrt x)^2*h) := by
    rw [hss]
    have he : x^2/(4*x*h) = 4*(x/(16*h)) := by field_simp; ring
    rw [he]
    have hnonneg : 0 ≤ x/(16*h) := by positivity
    linarith
  apply (scalarDeterministicLagInnovationSum_two_term_tail z dt ρ hρ (Real.sqrt x) h hh (by linarith)
    n hdt hduration x hxp.le).trans
  have hc := Real.exp_le_exp.mpr (neg_le_neg hcross)
  have hs := Real.exp_le_exp.mpr (neg_le_neg hsecond)
  linarith

lemma scalarDeterministicLagInnovationSum_exponential_tail (z : ℝ) (dt : ℕ → ℝ≥0)
    (ρ : ℕ → ℝ) (hρ : ∀ k, |ρ k| ≤ 1) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h)
    (x : ℝ) (_hx : 0 ≤ x) :
    (scalarObservationHistoryLaw z dt n).real {p | x ≤ |scalarDeterministicLagInnovationSum z dt ρ n p|} ≤
      4 * Real.exp (1-x/(16*h)) := by
  by_cases hl : 4*h^2 ≤ x
  · apply (scalarDeterministicLagInnovationSum_exponential_tail_large z dt ρ hρ h hh n hdt hduration x hl).trans
    gcongr
    linarith
  · have hratio : x/(16*h) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 16*h)).mpr
      have hs : h^2 ≤ h := by nlinarith
      linarith
    have he : 1 ≤ Real.exp (1-x/(16*h)) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : 0 ≤ 1-x/(16*h))
    exact measureReal_le_one.trans (by linarith)

lemma scalarDeterministicLagInnovationSum_factorial_moments (z : ℝ) (dt : ℕ → ℝ≥0)
    (ρ : ℕ → ℝ) (hρ : ∀ k, |ρ k| ≤ 1) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) (p : ℕ) :
    Integrable (fun q => |scalarDeterministicLagInnovationSum z dt ρ n q|^p) (scalarObservationHistoryLaw z dt n) ∧
    (∫ q, |scalarDeterministicLagInnovationSum z dt ρ n q|^p ∂scalarObservationHistoryLaw z dt n) ≤
      (4 * Real.exp 1) * (p.factorial : ℝ) * (16*h)^p := by
  cases p with
  | zero =>
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    constructor
    · exact integrable_const 1
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      have he : 1 ≤ Real.exp 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1)
      linarith
  | succ k =>
    apply factorial_moment_le_of_exponential_tail _ _
      (measurable_scalarPredictableInnovationSum z dt (scalarDeterministicLagCoefficient z ρ)
        (measurable_scalarDeterministicLagCoefficient z ρ) n) (4*Real.exp 1) (16*h) (by positivity) (by positivity)
    intro x hx
    have htail := scalarDeterministicLagInnovationSum_exponential_tail z dt ρ hρ h hh hh1 n hdt hduration x hx
    simpa only [scalarDeterministicLagInnovationSum, sub_eq_add_neg, Real.exp_add, mul_assoc] using htail

lemma scalarDeterministicLagInnovationSum_subgaussian (z : ℝ) (dt : ℕ → ℝ≥0)
    (ρ : ℕ → ℝ) (hρ : ∀ k, |ρ k| ≤ 1) (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) :
    HasSubgaussianMGF (scalarDeterministicLagInnovationSum z dt ρ n) ⟨8*h, by positivity⟩
      (scalarObservationHistoryLaw z dt n) := by
  apply scalarPredictableInnovationSum_subgaussian z dt (scalarDeterministicLagCoefficient z ρ)
    (measurable_scalarDeterministicLagCoefficient z ρ) n
  apply ae_of_all
  intro p
  change scalarPredictableInnovationProxy dt (scalarDeterministicLagCoefficient z ρ) n p ≤ 8*h
  have hcoef (k : ℕ) (_ : k < n) (q : ScalarObservationHistory k) :
      scalarDeterministicLagCoefficient z ρ k q ^ 2 ≤ 2^2 := by
    have hb0 := scalarPosteriorIncrement_abs_le_two z (scalarLastField z k q)
    have hb : |scalarDeterministicLagCoefficient z ρ k q| ≤ 2 := by
      change |ρ k * scalarLagCoefficient z k q| ≤ 2
      rw [abs_mul]
      exact (mul_le_mul (hρ k) hb0 (abs_nonneg _) (by norm_num)).trans_eq (one_mul 2)
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) hb 2
  convert scalarPredictableInnovationProxy_le_duration dt (scalarDeterministicLagCoefficient z ρ)
    n 2 h hcoef hdt hduration p using 1
  norm_num

lemma integral_scalarDeterministicLagInnovationSum_eq_zero (z : ℝ) (dt : ℕ → ℝ≥0)
    (ρ : ℕ → ℝ) (hρ : ∀ k, |ρ k| ≤ 1) (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) :
    (∫ q, scalarDeterministicLagInnovationSum z dt ρ n q ∂scalarObservationHistoryLaw z dt n) = 0 :=
  integral_eq_zero_of_subgaussian_mgf _ _ ⟨8*h, by positivity⟩ (by change 0 < 8*h; positivity)
    (scalarDeterministicLagInnovationSum_subgaussian z dt ρ hρ h hh n hdt hduration)

lemma scalarDeterministicLagInnovationSum_local_mgf (z : ℝ) (dt : ℕ → ℝ≥0)
    (ρ : ℕ → ℝ) (hρ : ∀ k, |ρ k| ≤ 1) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) :
    Concentration.LocalQuadraticMGF (scalarDeterministicLagInnovationSum z dt ρ n)
      (scalarObservationHistoryLaw z dt n) (2048*Real.exp 1*h^2) (1/(32*h)) := by
  have hm := scalarDeterministicLagInnovationSum_factorial_moments z dt ρ hρ h hh hh1 n hdt hduration
  have hPowers (p : ℕ) : Integrable (fun q => scalarDeterministicLagInnovationSum z dt ρ n q^p)
      (scalarObservationHistoryLaw z dt n) := by
    apply (integrable_norm_iff ((measurable_scalarPredictableInnovationSum z dt (scalarDeterministicLagCoefficient z ρ)
      (measurable_scalarDeterministicLagCoefficient z ρ) n).pow_const p).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs, abs_pow, scalarDeterministicLagInnovationSum] using (hm p).1
  have hMoments (p : ℕ) (hp : 2 ≤ p) :
      (∫ q, |scalarDeterministicLagInnovationSum z dt ρ n q|^p ∂scalarObservationHistoryLaw z dt n) ≤
      (p.factorial : ℝ) * ((4*Real.exp 1)*(16*h)^2) * (16*h)^(p-2) := by
    apply (hm p).2.trans_eq
    have he : (16*h)^p = (16*h)^2 * (16*h)^(p-2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    ring
  have hmgf := Concentration.localQuadraticMGF_of_factorial_moments
    (measurable_scalarPredictableInnovationSum z dt (scalarDeterministicLagCoefficient z ρ)
      (measurable_scalarDeterministicLagCoefficient z ρ) n)
    (by positivity : 0 ≤ (4*Real.exp 1)*(16*h)^2) (by positivity : 0 < 16*h)
    hPowers (integral_scalarDeterministicLagInnovationSum_eq_zero z dt ρ hρ h hh n hdt hduration) hMoments
  have heV : 2*((4*Real.exp 1)*(16*h)^2) = 2048*Real.exp 1*h^2 := by ring
  have heR : 1/(2*(16*h)) = 1/(32*h) := by congr 1; ring
  simpa only [scalarDeterministicLagInnovationSum, heV, heR] using hmgf

end SKConstants
