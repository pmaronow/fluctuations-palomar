module

public import SKConstants.Completion.LM4b.ZetaAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SKConstants.Completion.LM4b
open LM4 Concentration

theorem weighted_increment_abel (w a : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, w j * (a (j+1) - a j)) =
      w k * a k - w 0 * a 0 +
        ∑ j ∈ Finset.range k, (w j - w (j+1)) * a (j+1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring

theorem antitone_weighted_increment_abs_le (v a : ℕ → ℝ) (k : ℕ)
    (hv : Antitone v) (hv0 : ∀ j, 0 ≤ v j) {M : ℝ} (_hM : 0 ≤ M)
    (ha : ∀ j, |a j| ≤ M) :
    |∑ j ∈ Finset.range k, v j * (a (j+1) - a j)| ≤ 2 * M * v 0 := by
  rw [weighted_increment_abel]
  have hdiff (j : ℕ) : 0 ≤ v j - v (j+1) := sub_nonneg.mpr (hv (Nat.le_succ j))
  have hsum : |∑ j ∈ Finset.range k, (v j - v (j+1)) * a (j+1)| ≤
      (v 0 - v k) * M := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, |(v j - v (j+1)) * a (j+1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k, (v j - v (j+1)) * M := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (hdiff j)]
        exact mul_le_mul_of_nonneg_left (ha _) (hdiff j)
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_range_sub']
  calc
    _ ≤ |v k * a k - v 0 * a 0| + |∑ j ∈ Finset.range k, (v j - v (j+1)) * a (j+1)| := abs_add_le _ _
    _ ≤ |v k * a k| + |v 0 * a 0| + (v 0 - v k) * M := add_le_add (abs_sub _ _) hsum
    _ ≤ v k * M + v 0 * M + (v 0 - v k) * M := by
      simp only [abs_mul, abs_of_nonneg (hv0 _)]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (ha k) (hv0 k))
        (mul_le_mul_of_nonneg_left (ha 0) (hv0 0))) le_rfl
    _ = _ := by ring

theorem perturbed_weighted_increment_abs_le (w v a : ℕ → ℝ) (k : ℕ)
    (hv : Antitone v) (hv0 : ∀ j, 0 ≤ v j) {M E : ℝ} (hM : 0 ≤ M)
    (ha : ∀ j, |a j| ≤ M)
    (herror : ∑ j ∈ Finset.range k, |w j - v j| ≤ E) :
    |∑ j ∈ Finset.range k, w j * (a (j+1) - a j)| ≤ 2 * M * (v 0 + E) := by
  have he : (∑ j ∈ Finset.range k, w j * (a (j+1) - a j)) =
      (∑ j ∈ Finset.range k, v j * (a (j+1) - a j)) +
        ∑ j ∈ Finset.range k, (w j - v j) * (a (j+1) - a j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have herr : |∑ j ∈ Finset.range k, (w j - v j) * (a (j+1) - a j)| ≤ 2 * M * E := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, |(w j - v j) * (a (j+1) - a j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k, |w j - v j| * (2 * M) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [ha (j+1), ha j])) (abs_nonneg _)
      _ = (∑ j ∈ Finset.range k, |w j - v j|) * (2 * M) := (Finset.sum_mul _ _ _).symm
      _ ≤ E * (2 * M) := mul_le_mul_of_nonneg_right herror (by positivity)
      _ = _ := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add
    (antitone_weighted_increment_abs_le v a k hv hv0 hM ha) herr).trans_eq (by ring))

theorem potential_weighted_increment_abs_le (w v m : ℕ → ℝ) (k : ℕ) (x β V : ℝ)
    (hx : |x| ≤ 1) (hm : ∀ j, |m j| ≤ 1) (hv : Antitone v) (hv0 : ∀ j, 0 ≤ v j)
    (hstart : v 0 ≤ β) (hβ : 0 ≤ β) (hV : 0 ≤ V)
    (herror : ∑ j ∈ Finset.range k, |w j - v j| ≤ 10 * β * V) :
    |∑ j ∈ Finset.range k, w j * (rowPotential x (m (j+1)) - rowPotential x (m j))| ≤
      33 * (1 + β) * (1 + V) := by
  have hh := perturbed_weighted_increment_abs_le w v (fun j => rowPotential x (m j)) k
    hv hv0 (by norm_num : (0:ℝ) ≤ 3/2) (fun j => rowPotential_abs_le hx (hm j)) herror
  calc
    _ ≤ 2 * (3/2) * (v 0 + 10 * β * V) := hh
    _ ≤ 3 * (β + 10 * β * V) := by linarith
    _ ≤ _ := by nlinarith [mul_nonneg hβ hV]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def zetaOfParts (A N : Ω → ℝ) (e : ℝ) (u : Ω) : ℝ := A u + N u - e / 2

theorem zetaOfParts_centered_moments [IsProbabilityMeasure μ]
    {ell A N : Ω → ℝ} (hell : Measurable ell) (hAm : Measurable A) (hNm : Measurable N)
    (hlink : ∀ᵐ u ∂μ, 0 ≤ ell u ∧ ell u ≤ 2) (hnorm : ∫ u, ell u ∂μ = 1)
    (β : ℝ) (hβ : 0 ≤ β) (V : ℝ≥0) (e : ℝ) (he : |e| ≤ 1)
    (hA : ∀ᵐ u ∂μ, |A u| ≤ 33 * (1 + β) * (1 + (V : ℝ)))
    (hN : HasSubgaussianMGF N 4 μ) :
    let ν := linkedRowLaw μ ell
    let X := centeredObservable ν (zetaOfParts A N e)
    (∀ p : ℕ, Integrable (fun u => X u ^ p) ν) ∧
    (∫ u, X u ∂ν = 0) ∧
    (∀ p : ℕ, 2 ≤ p → (∫ u, |X u| ^ p ∂ν) ≤
      (p.factorial : ℝ) * (512 * (1 + β) * (1 + (V : ℝ))) ^ p) := by
  let ν := linkedRowLaw μ ell
  let S := (1 + β) * (1 + (V : ℝ))
  have hS : 1 ≤ S := by dsimp [S]; nlinarith [V.coe_nonneg, mul_nonneg hβ V.coe_nonneg]
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have : IsProbabilityMeasure ν := linkedRowLaw_isProbability hell hlink hnorm
  have hAν := (linkedRowLaw_absolutelyContinuous (μ := μ) ell).ae_le hA
  have hD (u : Ω) : |A u - e/2| ≤ |A u| + |e|/2 := by
    simpa only [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)] using abs_sub (A u) (e/2)
  have hb : ∀ᵐ u ∂ν, |A u - e/2| ≤ 34 * S := by
    filter_upwards [hAν] with u hu
    have hh := hD u
    dsimp [S] at *
    nlinarith
  have hDI (p : ℕ) : Integrable (fun u => |A u - e/2|^p) ν :=
    Integrable.of_bound (by fun_prop) ((34*S)^p) (hb.mono (fun u hu => by
      simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using pow_le_pow_left₀ (abs_nonneg _) hu p))
  have hDM (p : ℕ) : (∫ u, |A u - e/2|^p ∂ν) ≤ (p.factorial : ℝ) * (34*S)^p := by
    calc
      _ ≤ ∫ _u, (34*S)^p ∂ν := integral_mono_ae (hDI p) (integrable_const _)
        (hb.mono (fun _ hu => pow_le_pow_left₀ (abs_nonneg _) hu p))
      _ = (34*S)^p := by simp
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.factorial_pos p)
  have hNI (p : ℕ) := linkedRowLaw_integral_moments hell hNm hlink hnorm 1 (by simpa using hN) p
  have hNM (p : ℕ) (hp : 2 ≤ p) : (∫ u, |N u|^p ∂ν) ≤ (p.factorial : ℝ) * (12*S)^p := by
    have hp5 : (5 : ℝ) ≤ (3 : ℝ)^p := (by norm_num : (5:ℝ) ≤ 3^2).trans
      (pow_le_pow_right₀ (by norm_num) hp)
    calc
      _ ≤ 5 * (p.factorial : ℝ) * 4^p := by simpa only [NNReal.coe_one, show (2:ℝ)*(1+1)=4 by norm_num] using (hNI p).2
      _ ≤ (p.factorial : ℝ) * (3^p * 4^p) := by nlinarith [mul_le_mul_of_nonneg_right hp5 (by positivity : (0:ℝ) ≤ (p.factorial : ℝ)*4^p)]
      _ = (p.factorial : ℝ) * 12^p := by rw [← mul_pow]; norm_num
      _ ≤ _ := by gcongr; nlinarith
  have hzm : Measurable (zetaOfParts A N e) := (hAm.add hNm).sub_const _
  have hzi (p : ℕ) : Integrable (fun u => |zetaOfParts A N e u|^p) ν := by
    convert integrable_abs_add_pow (hAm.sub_const (e/2)) hNm p (hDI p) (hNI p).1 using 1
    funext u
    congr 2
    unfold zetaOfParts
    ring
  have hzM (p : ℕ) (hp : 2 ≤ p) : (∫ u, |zetaOfParts A N e u|^p ∂ν) ≤
      (p.factorial : ℝ) * (46*S)^p := by
    have hh := integral_abs_add_pow_le (hAm.sub_const (e/2)) hNm
      (by positivity : 0 < 34*S) (by positivity : 0 < 12*S)
      (hDI p) (hNI p).1 (hDM p) (hNM p hp)
    convert hh.2 using 1
    · congr 1; funext u; congr 2; unfold zetaOfParts; ring
    · congr 2; ring
  have hzInt : Integrable (zetaOfParts A N e) ν :=
    (integrable_norm_iff hzm.aestronglyMeasurable).mp (by simpa only [pow_one, Real.norm_eq_abs] using hzi 1)
  refine ⟨fun p => ?_, ?_, fun p hp => ?_⟩
  · exact (integrable_abs_add_pow hzm measurable_const p (hzi p)
      (integrable_const (|-∫ u, zetaOfParts A N e u ∂ν|^p))).mono'
        ((hzm.sub_const _).pow_const p).aestronglyMeasurable
        (ae_of_all _ (fun _ => by simp [centeredObservable, Real.norm_eq_abs, sub_eq_add_neg, ν]))
  · change ∫ u, zetaOfParts A N e u - ∫ v, zetaOfParts A N e v ∂ν ∂ν = 0
    rw [integral_sub hzInt (integrable_const _)]
    simp
  · calc
      _ ≤ 2^p * (∫ u, |zetaOfParts A N e u|^p ∂ν) :=
        (integral_abs_centered_pow_le hzm hzInt (by omega : 1 ≤ p) (hzi p)).2
      _ ≤ 2^p * ((p.factorial : ℝ) * (46*S)^p) := by gcongr; exact hzM p hp
      _ = (p.factorial : ℝ) * (92*S)^p := by rw [mul_left_comm, ← mul_pow]; congr 2; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        dsimp [S]
        nlinarith [mul_nonneg hβ V.coe_nonneg, V.coe_nonneg]

end SKConstants.Completion.LM4b
