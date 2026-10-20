module

public import SKBarriers2.Analysis.WeightedJets

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2

namespace WQ

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem increment {r p : ℕ} {B : ℝ} {f : E → F}
    (hf : WQ (r + 1) B p f) (d : E) :
    WJets r (B * ‖d‖ * (1 + ‖d‖) ^ p) p (fun x => f (x + d) - f x) := by
  have hB := hf.nonneg
  have hder : ∀ j ≤ r, ∀ x,
      ‖iteratedFDeriv ℝ j f (x + d) - iteratedFDeriv ℝ j f x‖ ≤
        B * (1 + ‖x‖ + ‖d‖) ^ p * ‖d‖ := by
    intro j hj x
    have hsmooth : ContDiff ℝ 1 (iteratedFDeriv ℝ j f) :=
      hf.smooth.iteratedFDeriv_right (by exact_mod_cast (show 1 + j ≤ r + 1 by omega))
    have H := Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := iteratedFDeriv ℝ j f) (s := Metric.closedBall x ‖d‖) (x := x) (y := x + d)
      (C := B * (1 + ‖x‖ + ‖d‖) ^ p)
      (fun y _ => hsmooth.differentiable (by norm_num) y)
      (fun y hy => by
        rw [norm_fderiv_iteratedFDeriv]
        apply (hf.bound (j + 1) (by omega) (by omega) y).trans
        apply mul_le_mul_of_nonneg_left _ hf.nonneg
        apply pow_le_pow_left₀ (by positivity)
        have hdist : ‖y - x‖ ≤ ‖d‖ := by
          simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
        have hnorm : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
          simpa only [sub_add_cancel] using norm_add_le (y - x) x
        linarith)
      (convex_closedBall x ‖d‖) (Metric.mem_closedBall_self (norm_nonneg d))
      (by simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, le_refl])
    simpa only [add_sub_cancel_left] using H
  refine ⟨by positivity [hf.nonneg],
    ((hf.smooth.comp (contDiff_id.add contDiff_const)).sub hf.smooth).of_le
      (by exact_mod_cast Nat.le_succ r), ?_⟩
  intro j hj x
  have hfj : ContDiff ℝ j f := hf.smooth.of_le (by exact_mod_cast (hj.trans (Nat.le_succ r)))
  change ‖iteratedFDeriv ℝ j ((fun y => f (y + d)) - f) x‖ ≤ _
  have hft : ContDiff ℝ j (fun y : E => f (y + d)) :=
    hfj.comp (contDiff_id.add contDiff_const)
  rw [iteratedFDeriv_sub hft hfj]
  change ‖iteratedFDeriv ℝ j (fun y => f (y + d)) x - iteratedFDeriv ℝ j f x‖ ≤ _
  rw [iteratedFDeriv_comp_add_right]
  apply (hder j hj x).trans
  calc
    _ ≤ B * ((1 + ‖d‖) * (1 + ‖x‖)) ^ p * ‖d‖ := by
      gcongr
      nlinarith [mul_nonneg (norm_nonneg d) (norm_nonneg x)]
    _ = _ := by rw [mul_pow]; ring

theorem centered_wJets {r p : ℕ} {B : ℝ} {f : E → F}
    (hf : WQ r B p f) (hr : 1 ≤ r) :
    WJets r B (p + 1) (fun x => f x - f 0) := by
  refine ⟨hf.nonneg, hf.smooth.sub contDiff_const, ?_⟩
  intro j hj x
  by_cases hj0 : j = 0
  · subst j
    rw [norm_iteratedFDeriv_zero]
    have H := ((hf.of_le (by omega : 1 ≤ r)).increment (r := 0) x).norm_le 0
    simp only [zero_add, norm_zero, add_zero, one_pow, mul_one] at H
    exact H.trans (by
      rw [pow_succ]
      nlinarith [mul_nonneg hf.nonneg (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) p)])
  · change ‖iteratedFDeriv ℝ j (f - fun _ => f 0) x‖ ≤ _
    rw [iteratedFDeriv_sub (hf.smooth.of_le (by exact_mod_cast hj)) contDiff_const,
      iteratedFDeriv_const_of_ne hj0, sub_zero]
    exact (hf.bound j (by omega) hj x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)) hf.nonneg)

theorem affine_noise_centered_bound {p : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : WQ 1 B p f) (a v : E) (g : ℝ) :
    |f (a + g • v) - f a| ≤
      (B * ‖v‖ * (1 + ‖v‖) ^ p * (1 + ‖a‖) ^ p) * (1 + |g|) ^ (p + 1) := by
  have hB := hf.nonneg
  have H := (hf.increment (r := 0) (g • v)).norm_le a
  rw [Real.norm_eq_abs, norm_smul, Real.norm_eq_abs] at H
  have hw : 1 + |g| * ‖v‖ ≤ (1 + ‖v‖) * (1 + |g|) := by
    nlinarith [norm_nonneg v, abs_nonneg g]
  calc
    _ ≤ (B * (|g| * ‖v‖) * (1 + |g| * ‖v‖) ^ p) * (1 + ‖a‖) ^ p := H
    _ ≤ (B * ((1 + |g|) * ‖v‖) * ((1 + ‖v‖) * (1 + |g|)) ^ p) *
        (1 + ‖a‖) ^ p := by gcongr; linarith [abs_nonneg g]
    _ = _ := by rw [mul_pow, pow_succ]; ring

theorem mul_weighted_value {r p q : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : WQ r B p f) (hg : WQ r C q g)
    (hf₀ : ∀ x, |f x| ≤ B * (1 + ‖x‖) ^ (p + 1))
    (hg₀ : ∀ x, |g x| ≤ C * (1 + ‖x‖) ^ (q + 1)) :
    WQ r ((2 : ℝ) ^ r * B * C) (p + q + 1) (fun x => f x * g x) := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  refine ⟨by positivity, hf.smooth.mul hg.smooth, ?_⟩
  intro j hj hjr x
  have hprod (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ ≤
        B * C * (1 + ‖x‖) ^ (p + q + 1) := by
    by_cases hi0 : i = 0
    · subst i
      rw [Nat.sub_zero, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (mul_le_mul (hf₀ x) (hg.bound j hj hjr x) (norm_nonneg _) (by positivity)).trans_eq
        (by simp only [pow_add, pow_one]; ring)
    · by_cases hji0 : j - i = 0
      · rw [hji0, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact (mul_le_mul (hf.bound i (by omega) (hi.trans hjr) x) (hg₀ x)
          (abs_nonneg _) (by positivity)).trans_eq (by simp only [pow_add, pow_one]; ring)
      · calc
          _ ≤ (B * (1 + ‖x‖) ^ p) * (C * (1 + ‖x‖) ^ q) :=
            mul_le_mul (hf.bound i (by omega) (hi.trans hjr) x)
              (hg.bound (j - i) (by omega) (by omega) x) (norm_nonneg _) (by positivity)
          _ = B * C * (1 + ‖x‖) ^ (p + q) := by rw [pow_add]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)) (mul_nonneg hB hC)
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf.smooth hg.smooth x (by exact_mod_cast hjr)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (B * C * (1 + ‖x‖) ^ (p + q + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hprod i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)) (by positivity)
    _ = (2 : ℝ) ^ j * B * C * (1 + ‖x‖) ^ (p + q + 1) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjr) hB) hC) (by positivity)

end WQ

namespace StepCalculus

local notation "X" => (Fin 3 → ℝ)

private theorem wQ_anchor_density {n : ℕ} {B : ℝ} {f : X → ℝ}
    (hf : QPotential (n + 1) B f) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v : X) (hv : ‖v‖ ≤ 1) (t : ℝ) :
    QBoundedJets n (anchorJetCoefficient n B * Real.exp ((B + n) * |t|))
      (fun x => Real.exp (m * (f (x + t • v) - f x))) := by
  have hB := hf.nonneg
  have hi : QBoundedJets n (B * |t|) (fun x => m * (f (x + t • v) - f x)) := by
    apply ((hf.increment (t • v)).const_smul m).mono
    rw [abs_of_nonneg hm.1, norm_smul, Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (by positivity) hm.2).trans
    exact mul_le_mul_of_nonneg_left
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (abs_nonneg t)) hB
  apply hi.exp.mono
  have hpow : (1 + B * |t|) ^ n ≤ (1 + B) ^ n * Real.exp ((n : ℝ) * |t|) := by
    have hbase : 1 + B * |t| ≤ (1 + B) * Real.exp |t| := by
      have hE := Real.add_one_le_exp |t|
      have he : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
      nlinarith [mul_le_mul_of_nonneg_left (by linarith : |t| ≤ Real.exp |t|) hB]
    have H := pow_le_pow_left₀ (by positivity) hbase n
    simpa only [mul_pow, ← Real.exp_nat_mul] using H
  calc
    _ ≤ (n.factorial : ℝ) * Real.exp (B * |t|) *
        ((1 + B) ^ n * Real.exp ((n : ℝ) * |t|)) := by gcongr
    _ = _ := by
      dsimp only [anchorJetCoefficient]
      rw [add_mul, Real.exp_add]
      ring

theorem wJets_noiseMean_weighted {n p q : ℕ} {B C m : ℝ} {f : X → ℝ}
    {G : ℝ → X → ℝ} (hf : QPotential (n + 1) B f) (hC : 0 ≤ C)
    (hG : ContDiff ℝ n (Function.uncurry G))
    (hGj : ∀ t, WJets n (C * (1 + |t|) ^ q) p (G t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1) :
    WJets n (noiseAverageCoefficient n q B * C) p
      (fun x => noiseMean m v f x (fun t => G t x)) := by
  have hB := hf.nonneg
  let A := anchorJetCoefficient n B
  have hA : 0 ≤ A := by dsimp only [A, anchorJetCoefficient]; positivity
  let b : ℝ → ℝ := fun t => (2 : ℝ) ^ n * C * A * Real.exp ((B + n + q) * |t|)
  have hNum (t : ℝ) : WJets n (b t) p
      (fun x => G t x * Real.exp (m * (f (x + t • v) - f x))) := by
    have hpow : (1 + |t|) ^ q ≤ Real.exp ((q : ℝ) * |t|) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp |t|) q
    have hTest := (hGj t).mono (mul_le_mul_of_nonneg_left hpow hC) le_rfl
    have H := hTest.mul ((wQ_anchor_density hf hm v hv t).weighted (p := 0))
    apply H.mono _ (by simp)
    dsimp only [b, A]
    rw [show (B + (n : ℝ) + q) * |t| = (q : ℝ) * |t| + (B + n) * |t| by ring,
      Real.exp_add]
    exact le_of_eq (by ring)
  have hFam : ContDiff ℝ n (fun z : ℝ × X =>
      G z.1 z.2 * Real.exp (m * (f (z.2 + z.1 • v) - f z.2))) :=
    hG.mul (((contDiff_const.mul ((hf.smooth.comp
      (contDiff_snd.add (contDiff_fst.smul contDiff_const))).sub
        (hf.smooth.comp contDiff_snd))).exp).of_le (by exact_mod_cast Nat.le_succ n))
  have hN := WJets.integral (gaussianReal 0 1) hFam hNum
    ((integrable_exp_mul_abs_gaussian (B + n + q)).const_mul ((2 : ℝ) ^ n * C * A))
  have hP := hN.mul ((qBoundedJets_inv_anchorPartition hf hm v hv).weighted (p := 0))
  have heq : (fun x => noiseMean m v f x (fun t => G t x)) =
      fun x => (∫ t, G t x * Real.exp (m * (f (x + t • v) - f x)) ∂gaussianReal 0 1) *
        (anchorPartition m v f x)⁻¹ := by
    funext x
    rw [noiseMean_anchor, div_eq_mul_inv]
  rw [heq]
  convert hP using 1
  dsimp only [b, noiseAverageCoefficient, gaussianExpMoment, A]
  rw [integral_const_mul]
  ring

theorem wJets_noiseMean_affine_weighted {n p q : ℕ} {B C m : ℝ} {f : X → ℝ}
    {G : ℝ → X → ℝ} (hf : QPotential (n + 1) B f) (hC : 0 ≤ C)
    (hG : ContDiff ℝ n (Function.uncurry G))
    (hGj : ∀ t, WJets n (C * (1 + |t|) ^ q) p (G t))
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1)
    (A : X →L[ℝ] X) (b₀ : X) :
    WJets n (noiseAverageCoefficient n q B * C * (max 1 ‖A‖ ^ n) ^ 2) p
      (fun x => noiseMean m v f (A x + b₀) (fun t => G t x)) := by
  have hB := hf.nonneg
  let J := anchorJetCoefficient n B
  let D := max 1 ‖A‖ ^ n
  have hJ : 0 ≤ J := by dsimp only [J, anchorJetCoefficient]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let b : ℝ → ℝ := fun t => (2 : ℝ) ^ n * C * J * D *
    Real.exp ((B + n + q) * |t|)
  have hNum (t : ℝ) : WJets n (b t) p
      (fun x => G t x * Real.exp (m *
        (f (A x + b₀ + t • v) - f (A x + b₀)))) := by
    have hpow : (1 + |t|) ^ q ≤ Real.exp ((q : ℝ) * |t|) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp |t|) q
    have hTest := (hGj t).mono (mul_le_mul_of_nonneg_left hpow hC) le_rfl
    have hDensity : WJets n
        (anchorJetCoefficient n B * Real.exp ((B + n) * |t|) * D) 0
        (fun x => Real.exp (m * (f (A x + b₀ + t • v) - f (A x + b₀)))) := by
      simpa only [pow_zero, mul_one] using
        ((wQ_anchor_density hf hm v hv t).weighted (p := 0)).comp_affine A b₀
    have H := hTest.mul hDensity
    apply H.mono _ (by simp)
    dsimp only [b, J]
    rw [show (B + (n : ℝ) + q) * |t| = (q : ℝ) * |t| + (B + n) * |t| by ring,
      Real.exp_add]
    exact le_of_eq (by ring)
  have hMean : ContDiff ℝ n (fun z : ℝ × X => A z.2 + b₀) :=
    (A.contDiff.comp contDiff_snd).add contDiff_const
  have hFam : ContDiff ℝ n (fun z : ℝ × X =>
      G z.1 z.2 * Real.exp (m *
        (f (A z.2 + b₀ + z.1 • v) - f (A z.2 + b₀)))) := by
    have hfs : ContDiff ℝ n f := hf.smooth.of_le (by exact_mod_cast Nat.le_succ n)
    exact hG.mul ((contDiff_const.mul
      ((hfs.comp (hMean.add (contDiff_fst.smul contDiff_const))).sub
        (hfs.comp hMean))).exp)
  have hN := WJets.integral (gaussianReal 0 1) hFam hNum
    ((integrable_exp_mul_abs_gaussian (B + n + q)).const_mul
      ((2 : ℝ) ^ n * C * J * D))
  have hInv : WJets n (anchorInverseJetBound n B * D) 0
      (fun x => (anchorPartition m v f (A x + b₀))⁻¹) := by
    simpa only [pow_zero, mul_one] using
      ((qBoundedJets_inv_anchorPartition hf hm v hv).weighted (p := 0)).comp_affine A b₀
  have hP := hN.mul hInv
  have heq : (fun x => noiseMean m v f (A x + b₀) (fun t => G t x)) =
      fun x => (∫ t, G t x * Real.exp (m *
        (f (A x + b₀ + t • v) - f (A x + b₀))) ∂gaussianReal 0 1) *
        (anchorPartition m v f (A x + b₀))⁻¹ := by
    funext x
    rw [noiseMean_anchor, div_eq_mul_inv]
  rw [heq]
  convert hP using 1
  dsimp only [b, noiseAverageCoefficient, gaussianExpMoment, J, D]
  rw [integral_const_mul]
  ring

theorem wQ_tiltedAverage {n p : ℕ} {B C m : ℝ} {f g : X → ℝ}
    (hf : QPotential (n + 1) B f) (hg : WQ (n + 1) C p g)
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1) :
    WQ n (C + noiseAverageCoefficient n (p + 1) B * C) p (tiltedAverage m v f g) := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  let A := anchorJetCoefficient n B
  have hA : 0 ≤ A := by dsimp only [A, anchorJetCoefficient]; positivity
  let b : ℝ → ℝ := fun t => (2 : ℝ) ^ n * C * A *
    Real.exp ((B + n + (p + 1 : ℕ)) * |t|)
  let K : ℝ → X → ℝ := fun t x =>
    (g (x + t • v) - g x) * Real.exp (m * (f (x + t • v) - f x))
  have hInc (t : ℝ) : WJets n (C * Real.exp (((p + 1 : ℕ) : ℝ) * |t|)) p
      (fun x => g (x + t • v) - g x) := by
    apply (hg.increment (t • v)).mono _ le_rfl
    have hd : ‖t • v‖ ≤ |t| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg t) hv
    have ht : |t| ≤ Real.exp |t| := (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (by simpa only [add_comm] using Real.add_one_le_exp |t|)
    have hp : (1 + ‖t • v‖) ^ p ≤ Real.exp ((p : ℝ) * |t|) := by
      rw [Real.exp_nat_mul]
      apply pow_le_pow_left₀ (by positivity)
      exact (add_le_add_right hd 1).trans
        (by simpa only [add_comm] using Real.add_one_le_exp |t|)
    calc
      _ ≤ C * Real.exp |t| * Real.exp ((p : ℝ) * |t|) := by
        gcongr
        exact hd.trans ht
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
  have hNum (t : ℝ) : WJets n (b t) p (K t) := by
    have H := (hInc t).mul ((wQ_anchor_density hf hm v hv t).weighted (p := 0))
    apply H.mono _ (by simp)
    dsimp only [b, A]
    rw [show (B + (n : ℝ) + (p + 1 : ℕ)) * |t| =
      ((p + 1 : ℕ) : ℝ) * |t| + (B + n) * |t| by ring, Real.exp_add]
    exact le_of_eq (by ring)
  have hFam : ContDiff ℝ n (Function.uncurry K) := by
    exact (((hg.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const))).sub
      (hg.smooth.comp contDiff_snd)).mul
      ((contDiff_const.mul ((hf.smooth.comp
        (contDiff_snd.add (contDiff_fst.smul contDiff_const))).sub
          (hf.smooth.comp contDiff_snd))).exp)).of_le (by exact_mod_cast Nat.le_succ n)
  have hb : Integrable b (gaussianReal 0 1) :=
    (integrable_exp_mul_abs_gaussian (B + n + (p + 1 : ℕ))).const_mul
      ((2 : ℝ) ^ n * C * A)
  have hN := WJets.integral (gaussianReal 0 1) hFam hNum hb
  have hP := hN.mul ((qBoundedJets_inv_anchorPartition hf hm v hv).weighted (p := 0))
  have hCorrection : WJets n (noiseAverageCoefficient n (p + 1) B * C) p
      (fun x => (∫ t, K t x ∂gaussianReal 0 1) * (anchorPartition m v f x)⁻¹) := by
    convert hP using 1
    dsimp only [b, noiseAverageCoefficient, gaussianExpMoment, A]
    rw [integral_const_mul]
    ring
  have hEq : tiltedAverage m v f g = fun x => g x +
      (∫ t, K t x ∂gaussianReal 0 1) * (anchorPartition m v f x)⁻¹ := by
    funext x
    change noiseMean m v f x (fun t => g (x + t • v)) = _
    rw [noiseMean_anchor, div_eq_mul_inv]
    have hKI : Integrable (fun t => K t x) (gaussianReal 0 1) :=
      (hb.mul_const ((1 + ‖x‖) ^ p)).mono'
        (hFam.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
        (ae_of_all _ (fun t => (hNum t).norm_le x))
    have hZI : Integrable (fun t => Real.exp (m * (f (x + t • v) - f x)))
        (gaussianReal 0 1) := by
      apply (integrable_exp_mul_abs_gaussian B).mono'
        (Real.continuous_exp.comp
          (((hf.smooth.continuous.comp
            (continuous_const.add (continuous_id.smul continuous_const))).sub
              continuous_const).const_mul m)).aestronglyMeasurable
      filter_upwards [] with t
      change ‖Real.exp (m * (f (x + t • v) - f x))‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have H := (hf.lipschitzWith (by omega)).norm_sub_le (x + t • v) x
      change |f (x + t • v) - f x| ≤ B * ‖x + t • v - x‖ at H
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at H
      calc
        _ ≤ |m| * |f (x + t • v) - f x| := by
          rw [← abs_mul]
          exact le_abs_self _
        _ ≤ 1 * (B * (|t| * ‖v‖)) := by
          apply mul_le_mul _ H (abs_nonneg _) (by norm_num)
          simpa only [abs_of_nonneg hm.1] using hm.2
        _ ≤ 1 * (B * (|t| * 1)) := by gcongr
        _ = _ := by ring
    have hZE : anchorPartition m v f x ≠ 0 := by
      apply ne_of_gt
      exact (gaussianExpMoment_pos (-B)).trans_le (anchorPartition_lower hf (by omega) hm v hv x)
    have hsplit : (fun t => g (x + t • v) * Real.exp (m * (f (x + t • v) - f x))) =
        fun t => K t x + g x * Real.exp (m * (f (x + t • v) - f x)) := by
      funext t
      dsimp only [K]
      ring
    rw [hsplit, integral_add hKI (hZI.const_mul (g x)), integral_const_mul]
    change ((∫ t, K t x ∂gaussianReal 0 1) + g x * anchorPartition m v f x) *
      (anchorPartition m v f x)⁻¹ = _
    field_simp
    ring
  rw [hEq]
  refine ⟨add_nonneg hC hCorrection.nonneg,
    (hg.smooth.of_le (by exact_mod_cast Nat.le_succ n)).add hCorrection.smooth, ?_⟩
  intro j hj hjn x
  change ‖iteratedFDeriv ℝ j (g + (fun x =>
    (∫ t, K t x ∂gaussianReal 0 1) * (anchorPartition m v f x)⁻¹)) x‖ ≤ _
  rw [iteratedFDeriv_add (hg.smooth.of_le (by exact_mod_cast (hjn.trans (Nat.le_succ n))))
    (hCorrection.smooth.of_le (by exact_mod_cast hjn))]
  change ‖iteratedFDeriv ℝ j g x + iteratedFDeriv ℝ j
    (fun x => (∫ t, K t x ∂gaussianReal 0 1) * (anchorPartition m v f x)⁻¹) x‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add
    (hg.bound j hj (hjn.trans (Nat.le_succ n)) x) (hCorrection.bound j hjn x)).trans_eq (by ring))

end StepCalculus

end SKBarriers2

