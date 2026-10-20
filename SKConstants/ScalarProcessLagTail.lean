module
public import SKConstants.ScalarProcessLagMGF
public import SKConstants.ScalarProcessPosteriorIncrement
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

def scalarLagCoefficient (z : ℝ) : ScalarFiniteHistoryCoefficient :=
  fun n p => Real.tanh (scalarLastField z n p) - Real.tanh z

def scalarLagTruncatedCoefficient (z b : ℝ) : ScalarFiniteHistoryCoefficient :=
  fun n p => if |scalarLagCoefficient z n p| ≤ b then scalarLagCoefficient z n p else 0

def scalarLagRunningMax (z : ℝ) : (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n prev p => max (prev p.1) |scalarLagCoefficient z n p.1|)

def scalarLagInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) : ScalarObservationHistory n → ℝ :=
  scalarPredictableInnovationSum z dt (scalarLagCoefficient z) n

def scalarLagTruncatedSum (z : ℝ) (dt : ℕ → ℝ≥0) (b : ℝ) (n : ℕ) : ScalarObservationHistory n → ℝ :=
  scalarPredictableInnovationSum z dt (scalarLagTruncatedCoefficient z b) n

@[simp] lemma scalarLagRunningMax_zero (z : ℝ) (p : ScalarObservationHistory 0) :
    scalarLagRunningMax z 0 p = 0 := rfl
@[simp] lemma scalarLagRunningMax_succ (z : ℝ) (n : ℕ) (p : ScalarObservationHistory n) (y : ℝ) :
    scalarLagRunningMax z (n + 1) (p, y) = max (scalarLagRunningMax z n p) |scalarLagCoefficient z n p| := rfl

lemma measurable_scalarLagCoefficient (z : ℝ) (n : ℕ) : Measurable (scalarLagCoefficient z n) :=
  ((scalar_tanh_lipschitz.continuous.measurable.comp (measurable_scalarLastField z n)).sub_const _)

lemma measurable_scalarLagTruncatedCoefficient (z b : ℝ) (n : ℕ) :
    Measurable (scalarLagTruncatedCoefficient z b n) := by
  exact Measurable.ite (measurableSet_le (continuous_abs.measurable.comp (measurable_scalarLagCoefficient z n)) measurable_const)
    (measurable_scalarLagCoefficient z n) measurable_const

lemma measurable_scalarLagRunningMax (z : ℝ) (n : ℕ) : Measurable (scalarLagRunningMax z n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).max ((continuous_abs.measurable.comp (measurable_scalarLagCoefficient z n)).comp measurable_fst)

lemma scalarLagTruncatedCoefficient_abs_le (z b : ℝ) (hb : 0 ≤ b) (n : ℕ)
    (p : ScalarObservationHistory n) : |scalarLagTruncatedCoefficient z b n p| ≤ b := by
  unfold scalarLagTruncatedCoefficient
  split_ifs with h
  · exact h
  · simpa only [abs_zero] using hb

lemma scalarLagTruncatedCoefficient_sq_le (z b : ℝ) (hb : 0 ≤ b) (n : ℕ)
    (p : ScalarObservationHistory n) : scalarLagTruncatedCoefficient z b n p ^ 2 ≤ b ^ 2 := by
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
    (scalarLagTruncatedCoefficient_abs_le z b hb n p) 2

lemma scalarLagInnovationSum_eq_truncated_of_max_le (z : ℝ) (dt : ℕ → ℝ≥0)
    (b : ℝ) (n : ℕ) (p : ScalarObservationHistory n) (hp : scalarLagRunningMax z n p ≤ b) :
    scalarLagInnovationSum z dt n p = scalarLagTruncatedSum z dt b n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change scalarLagRunningMax z n p.1 ⊔ |scalarLagCoefficient z n p.1| ≤ b at hp
    have hprev := (max_le_iff.mp hp).1
    have hcur := (max_le_iff.mp hp).2
    change scalarPredictableInnovationSum z dt (scalarLagCoefficient z) n p.1 +
      scalarLagCoefficient z n p.1 * scalarInnovation (scalarLastField z n p.1) (dt n) p.2 =
      scalarPredictableInnovationSum z dt (scalarLagTruncatedCoefficient z b) n p.1 +
        scalarLagTruncatedCoefficient z b n p.1 * scalarInnovation (scalarLastField z n p.1) (dt n) p.2
    rw [show scalarPredictableInnovationSum z dt (scalarLagCoefficient z) n p.1 =
      scalarPredictableInnovationSum z dt (scalarLagTruncatedCoefficient z b) n p.1 from ih p.1 hprev]
    simp only [scalarLagTruncatedCoefficient, ite_eq_left hcur]

lemma scalarLagTruncatedProxy_le (z : ℝ) (dt : ℕ → ℝ≥0) (b h : ℝ) (hb : 0 ≤ b) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1) (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h)
    (p : ScalarObservationHistory n) :
    scalarPredictableInnovationProxy dt (scalarLagTruncatedCoefficient z b) n p ≤ 2 * b ^ 2 * h :=
  scalarPredictableInnovationProxy_le_duration dt _ n b h
    (fun k _ q => scalarLagTruncatedCoefficient_sq_le z b hb k q) hdt hduration p

lemma mgf_scalarLagTruncatedSum_le (z : ℝ) (dt : ℕ → ℝ≥0) (b h : ℝ) (hb : 0 ≤ b) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1) (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h)
    (theta : ℝ) :
    mgf (scalarLagTruncatedSum z dt b n) (scalarObservationHistoryLaw z dt n) theta ≤
      Real.exp (theta ^ 2 * (2 * b ^ 2 * h) / 2) :=
  mgf_scalarPredictableInnovationSum_le z dt _ (measurable_scalarLagTruncatedCoefficient z b)
    n _ (ae_of_all _ (scalarLagTruncatedProxy_le z dt b h hb n hdt hduration)) theta

lemma scalarLagInnovationSum_tail_of_crossing (z : ℝ) (dt : ℕ → ℝ≥0)
    (b h : ℝ) (hb : 0 < b) (hh : 0 < h) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1) (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h)
    (x : ℝ) (hx : 0 ≤ x) :
    (scalarObservationHistoryLaw z dt n).real {p | x ≤ |scalarLagInnovationSum z dt n p|} ≤
      (scalarObservationHistoryLaw z dt n).real {p | b < scalarLagRunningMax z n p} +
        2 * Real.exp (-(x ^ 2 / (4 * b ^ 2 * h))) := by
  have hsubset : {p : ScalarObservationHistory n | x ≤ |scalarLagInnovationSum z dt n p|} ⊆
      {p | b < scalarLagRunningMax z n p} ∪ {p | x ≤ |scalarLagTruncatedSum z dt b n p|} := by
    intro p hp
    by_cases hc : b < scalarLagRunningMax z n p
    · exact Or.inl hc
    · apply Or.inr
      change x ≤ |scalarLagTruncatedSum z dt b n p|
      change x ≤ |scalarLagInnovationSum z dt n p| at hp
      rwa [← scalarLagInnovationSum_eq_truncated_of_max_le z dt b n p (le_of_not_gt hc)]
  have htail := scalarPredictableInnovationSum_two_sided_tail z dt _
    (measurable_scalarLagTruncatedCoefficient z b) n (2 * b ^ 2 * h)
    (ae_of_all _ (scalarLagTruncatedProxy_le z dt b h hb.le n hdt hduration)) (by positivity) x hx
  have he : 2 * (2 * b ^ 2 * h) = 4 * b ^ 2 * h := by ring
  rw [he] at htail
  exact (measureReal_mono hsubset).trans ((measureReal_union_le _ _).trans
    (add_le_add le_rfl htail))

def scalarFiniteInnovationRunningAbsMax (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) : (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n prev p =>
    max (prev p.1) |scalarPredictableInnovationSum z dt H (n + 1) p|)

def scalarFiniteInnovationFirstExitCoefficient (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (a : ℝ) : ScalarFiniteHistoryCoefficient :=
  fun n p => if scalarFiniteInnovationRunningAbsMax z dt H n p < a then H n p else 0

lemma measurable_scalarFiniteInnovationRunningAbsMax (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (scalarFiniteInnovationRunningAbsMax z dt H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).max
      (continuous_abs.measurable.comp (measurable_scalarPredictableInnovationSum z dt H hH (n+1)))

lemma measurable_scalarFiniteInnovationFirstExitCoefficient (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k)) (a : ℝ) (n : ℕ) :
    Measurable (scalarFiniteInnovationFirstExitCoefficient z dt H a n) :=
  Measurable.ite
    (measurableSet_lt (measurable_scalarFiniteInnovationRunningAbsMax z dt H hH n) measurable_const)
    (hH n) measurable_const

lemma scalarFiniteInnovationFirstExit_sum_properties (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (a : ℝ) (ha : 0 < a)
    (n : ℕ) (p : ScalarObservationHistory n) :
    (scalarFiniteInnovationRunningAbsMax z dt H n p < a →
      scalarPredictableInnovationSum z dt (scalarFiniteInnovationFirstExitCoefficient z dt H a) n p =
        scalarPredictableInnovationSum z dt H n p) ∧
    (a ≤ scalarFiniteInnovationRunningAbsMax z dt H n p →
      a ≤ |scalarPredictableInnovationSum z dt
        (scalarFiniteInnovationFirstExitCoefficient z dt H a) n p|) := by
  induction n with
  | zero =>
    constructor
    · intro _; rfl
    · intro h; exact False.elim ((not_le_of_gt ha) h)
  | succ n ih =>
    by_cases hb : scalarFiniteInnovationRunningAbsMax z dt H n p.1 < a
    · have hs : scalarPredictableInnovationSum z dt
          (scalarFiniteInnovationFirstExitCoefficient z dt H a) (n+1) p =
          scalarPredictableInnovationSum z dt H (n+1) p := by
        change scalarPredictableInnovationSum z dt _ n p.1 + _ =
          scalarPredictableInnovationSum z dt H n p.1 + _
        rw [(ih p.1).1 hb]
        simp only [scalarFiniteInnovationFirstExitCoefficient, hb, ↓reduceIte]
      constructor
      · intro _; exact hs
      · intro h
        rw [hs]
        rcases le_max_iff.mp h with h | h
        · exact False.elim ((not_le_of_gt hb) h)
        · exact h
    · have hc : a ≤ scalarFiniteInnovationRunningAbsMax z dt H n p.1 := le_of_not_gt hb
      have hs : scalarPredictableInnovationSum z dt
          (scalarFiniteInnovationFirstExitCoefficient z dt H a) (n+1) p =
          scalarPredictableInnovationSum z dt (scalarFiniteInnovationFirstExitCoefficient z dt H a) n p.1 := by
        change _ + scalarFiniteInnovationFirstExitCoefficient z dt H a n p.1 * _ = _
        simp only [scalarFiniteInnovationFirstExitCoefficient, hb, ↓reduceIte, zero_mul, add_zero]
        rfl
      constructor
      · intro h
        have hm : scalarFiniteInnovationRunningAbsMax z dt H n p.1 ≤
            scalarFiniteInnovationRunningAbsMax z dt H (n+1) p := le_max_left _ _
        exact False.elim ((not_le_of_gt h) (hc.trans hm))
      · intro _; rw [hs]; exact (ih p.1).2 hc

lemma scalarFiniteInnovationFirstExit_proxy_le (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (a : ℝ) (n : ℕ) (p : ScalarObservationHistory n) :
    scalarPredictableInnovationProxy dt (scalarFiniteInnovationFirstExitCoefficient z dt H a) n p ≤
      scalarPredictableInnovationProxy dt H n p := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    apply add_le_add (ih p.1)
    unfold scalarFiniteInnovationFirstExitCoefficient
    split_ifs
    · exact le_rfl
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      positivity

lemma scalarFiniteInnovationSum_maximal_tail (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ p ∂scalarObservationHistoryLaw z dt n, scalarPredictableInnovationProxy dt H n p ≤ V)
    (hVp : 0 < V) (a : ℝ) (ha : 0 < a) :
    (scalarObservationHistoryLaw z dt n).real
      {p | a ≤ scalarFiniteInnovationRunningAbsMax z dt H n p} ≤
      2 * Real.exp (-(a ^ 2 / (2 * V))) := by
  have hKV : ∀ᵐ p ∂scalarObservationHistoryLaw z dt n,
      scalarPredictableInnovationProxy dt (scalarFiniteInnovationFirstExitCoefficient z dt H a) n p ≤ V := by
    filter_upwards [hV] with p hp
    exact (scalarFiniteInnovationFirstExit_proxy_le z dt H a n p).trans hp
  apply le_trans ?_ (scalarPredictableInnovationSum_two_sided_tail z dt
    (scalarFiniteInnovationFirstExitCoefficient z dt H a)
    (measurable_scalarFiniteInnovationFirstExitCoefficient z dt H hH a) n V hKV hVp a ha.le)
  exact measureReal_mono (fun p hp =>
    (scalarFiniteInnovationFirstExit_sum_properties z dt H a ha n p).2 hp)

def scalarFiniteInnovationDrift (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n prev p => prev p.1 + (dt n : ℝ) * Real.tanh (scalarLastField z n p.1))

lemma scalarLastField_sub_eq_innovation_add_drift (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (p : ScalarObservationHistory n) :
    scalarLastField z n p - z = scalarPredictableInnovationSum z dt (fun _ _ => 1) n p +
      scalarFiniteInnovationDrift z dt n p := by
  induction n with
  | zero => simp [scalarLastField, scalarPredictableInnovationSum, scalarFiniteInnovationDrift]
  | succ n ih =>
    change p.2 - z =
      (scalarPredictableInnovationSum z dt (fun _ _ => 1) n p.1 +
        1 * scalarInnovation (scalarLastField z n p.1) (dt n) p.2) +
      (scalarFiniteInnovationDrift z dt n p.1 + (dt n : ℝ) * Real.tanh (scalarLastField z n p.1))
    have hi := ih p.1
    unfold scalarInnovation
    linarith

lemma scalarFiniteInnovationDrift_abs_le_duration (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (p : ScalarObservationHistory n) :
    |scalarFiniteInnovationDrift z dt n p| ≤ ∑ k ∈ Finset.range n, (dt k : ℝ) := by
  induction n with
  | zero => simp [scalarFiniteInnovationDrift]
  | succ n ih =>
    change |scalarFiniteInnovationDrift z dt n p.1 + (dt n : ℝ) * Real.tanh (scalarLastField z n p.1)| ≤ _
    rw [Finset.sum_range_succ]
    apply (abs_add_le _ _).trans
    apply add_le_add (ih p.1)
    rw [abs_mul, abs_of_nonneg (dt n).coe_nonneg]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (scalar_tanh_abs_le_one (scalarLastField z n p.1)) (dt n).coe_nonneg

lemma scalarFiniteInnovationSum_abs_le_runningMax (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (n : ℕ) (p : ScalarObservationHistory n) :
    |scalarPredictableInnovationSum z dt H n p| ≤ scalarFiniteInnovationRunningAbsMax z dt H n p := by
  cases n with
  | zero => simp [scalarPredictableInnovationSum, scalarFiniteInnovationRunningAbsMax]
  | succ n => exact le_max_right _ _

lemma scalarLagRunningMax_le_innovationMax_add_duration (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (p : ScalarObservationHistory n) :
    scalarLagRunningMax z n p ≤ scalarFiniteInnovationRunningAbsMax z dt (fun _ _ => 1) n p +
      ∑ k ∈ Finset.range n, (dt k : ℝ) := by
  induction n with
  | zero => simp [scalarLagRunningMax, scalarFiniteInnovationRunningAbsMax]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    apply max_le
    · exact (ih p.1).trans (add_le_add
        (le_max_left _ _) (le_add_of_nonneg_right (dt n).coe_nonneg))
    · calc
        |scalarLagCoefficient z n p.1| ≤ |scalarLastField z n p.1 - z| :=
          scalar_tanh_abs_sub_le _ _
        _ ≤ |scalarPredictableInnovationSum z dt (fun _ _ => 1) n p.1| +
            |scalarFiniteInnovationDrift z dt n p.1| := by
          rw [scalarLastField_sub_eq_innovation_add_drift]
          exact abs_add_le _ _
        _ ≤ scalarFiniteInnovationRunningAbsMax z dt (fun _ _ => 1) n p.1 +
            ∑ k ∈ Finset.range n, (dt k : ℝ) := add_le_add
          (scalarFiniteInnovationSum_abs_le_runningMax z dt _ n p.1)
          (scalarFiniteInnovationDrift_abs_le_duration z dt n p.1)
        _ ≤ _ := add_le_add (le_max_left _ _) (le_add_of_nonneg_right (dt n).coe_nonneg)

lemma scalarLagRunningMax_crossing_tail (z : ℝ) (dt : ℕ → ℝ≥0)
    (b h : ℝ) (hh : 0 < h) (hbh : h < b) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) :
    (scalarObservationHistoryLaw z dt n).real {p | b < scalarLagRunningMax z n p} ≤
      2 * Real.exp (-((b - h) ^ 2 / (4 * h))) := by
  have htail := scalarFiniteInnovationSum_maximal_tail z dt (fun _ _ => 1)
    (fun _ => measurable_const) n (2*h)
    (ae_of_all _ (fun p => by
      simpa using scalarPredictableInnovationProxy_le_duration dt (fun _ _ => 1) n 1 h
        (fun _ _ _ => le_rfl) hdt hduration p)) (by positivity) (b-h) (by linarith)
  have hsubset : {p : ScalarObservationHistory n | b < scalarLagRunningMax z n p} ⊆
      {p | b-h ≤ scalarFiniteInnovationRunningAbsMax z dt (fun _ _ => 1) n p} := by
    intro p hp
    have hm := scalarLagRunningMax_le_innovationMax_add_duration z dt n p
    change b < scalarLagRunningMax z n p at hp
    change b-h ≤ scalarFiniteInnovationRunningAbsMax z dt (fun _ _ => 1) n p
    linarith
  have he : 2*(2*h) = 4*h := by ring
  rw [he] at htail
  exact (measureReal_mono hsubset).trans htail

lemma scalarLagInnovationSum_two_term_tail (z : ℝ) (dt : ℕ → ℝ≥0)
    (b h : ℝ) (hh : 0 < h) (hbh : h < b) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) (x : ℝ) (hx : 0 ≤ x) :
    (scalarObservationHistoryLaw z dt n).real {p | x ≤ |scalarLagInnovationSum z dt n p|} ≤
      2 * Real.exp (-((b-h)^2/(4*h))) + 2 * Real.exp (-(x^2/(4*b^2*h))) :=
  (scalarLagInnovationSum_tail_of_crossing z dt b h (by linarith) hh n hdt hduration x hx).trans
    (add_le_add (scalarLagRunningMax_crossing_tail z dt b h hh hbh n hdt hduration) le_rfl)

lemma scalarLagInnovationSum_exponential_tail_large (z : ℝ) (dt : ℕ → ℝ≥0)
    (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h)
    (x : ℝ) (hx : 4*h^2 ≤ x) :
    (scalarObservationHistoryLaw z dt n).real {p | x ≤ |scalarLagInnovationSum z dt n p|} ≤
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
  apply (scalarLagInnovationSum_two_term_tail z dt (Real.sqrt x) h hh (by linarith)
    n hdt hduration x hxp.le).trans
  have hc := Real.exp_le_exp.mpr (neg_le_neg hcross)
  have hs := Real.exp_le_exp.mpr (neg_le_neg hsecond)
  linarith

lemma scalarLagInnovationSum_exponential_tail (z : ℝ) (dt : ℕ → ℝ≥0)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h)
    (x : ℝ) (_hx : 0 ≤ x) :
    (scalarObservationHistoryLaw z dt n).real {p | x ≤ |scalarLagInnovationSum z dt n p|} ≤
      4 * Real.exp (1-x/(16*h)) := by
  by_cases hl : 4*h^2 ≤ x
  · apply (scalarLagInnovationSum_exponential_tail_large z dt h hh n hdt hduration x hl).trans
    gcongr
    linarith
  · have hratio : x/(16*h) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 16*h)).mpr
      have hs : h^2 ≤ h := by nlinarith
      linarith
    have he : 1 ≤ Real.exp (1-x/(16*h)) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : 0 ≤ 1-x/(16*h))
    exact measureReal_le_one.trans (by linarith)

end SKConstants
