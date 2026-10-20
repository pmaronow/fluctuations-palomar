module

public import SKBarriers2.Analysis.TiltedAffineStep
public import SKBarriers2.Analysis.ParamStep

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure WQ (r : ℕ) (B : ℝ) (p : ℕ) (f : E → F) : Prop where
  nonneg : 0 ≤ B
  smooth : ContDiff ℝ r f
  bound : ∀ j, 1 ≤ j → j ≤ r → ∀ x,
    ‖iteratedFDeriv ℝ j f x‖ ≤ B * (1 + ‖x‖) ^ p

structure WJets (r : ℕ) (B : ℝ) (p : ℕ) (f : E → F) : Prop where
  nonneg : 0 ≤ B
  smooth : ContDiff ℝ r f
  bound : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B * (1 + ‖x‖) ^ p

theorem one_add_norm_affine_le (A : E →L[ℝ] E) (b x : E) :
    1 + ‖A x + b‖ ≤ (1 + ‖A‖ + ‖b‖) * (1 + ‖x‖) := by
  have H := (norm_add_le (A x) b).trans (add_le_add (A.le_opNorm x) le_rfl)
  nlinarith [norm_nonneg A, norm_nonneg x,
    mul_nonneg (norm_nonneg b) (norm_nonneg x)]

namespace WJets

variable {r s p q : ℕ} {B C : ℝ} {f g : E → F}

theorem norm_le (hf : WJets r B p f) (x : E) : ‖f x‖ ≤ B * (1 + ‖x‖) ^ p := by
  simpa only [norm_iteratedFDeriv_zero] using hf.bound 0 (Nat.zero_le r) x

theorem potential (hf : WJets r B p f) : WQ r B p f :=
  ⟨hf.nonneg, hf.smooth, fun j _ hj x => hf.bound j hj x⟩

theorem of_le (hf : WJets r B p f) (hs : s ≤ r) : WJets s B p f := by
  exact ⟨hf.nonneg, hf.smooth.of_le (by exact_mod_cast hs),
    fun j hj x => hf.bound j (hj.trans hs) x⟩

theorem mono (hf : WJets r B p f) (hBC : B ≤ C) (hpq : p ≤ q) : WJets r C q f := by
  refine ⟨hf.nonneg.trans hBC, hf.smooth, ?_⟩
  intro j hj x
  exact (hf.bound j hj x).trans (mul_le_mul hBC
    (pow_le_pow_right₀ (by linarith [norm_nonneg x]) hpq) (by positivity)
    (hf.nonneg.trans hBC))

theorem derivativeJets (hf : WJets (r + 1) B p f) : WJets r B p (fderiv ℝ f) := by
  refine ⟨hf.nonneg, hf.smooth.fderiv_right (by simp), ?_⟩
  intro j hj x
  rw [norm_iteratedFDeriv_fderiv]
  exact hf.bound (j + 1) (by omega) x

theorem add (hf : WJets r B p f) (hg : WJets r C p g) :
    WJets r (B + C) p (fun x => f x + g x) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.add hg.smooth, ?_⟩
  intro j hj x
  change ‖iteratedFDeriv ℝ j (f + g) x‖ ≤ _
  rw [iteratedFDeriv_add (hf.smooth.of_le (by exact_mod_cast hj))
    (hg.smooth.of_le (by exact_mod_cast hj))]
  exact (norm_add_le _ _).trans ((add_le_add (hf.bound j hj x) (hg.bound j hj x)).trans_eq
    (by ring))

theorem const_smul (hf : WJets r B p f) (c : ℝ) :
    WJets r (|c| * B) p (fun x => c • f x) := by
  refine ⟨mul_nonneg (abs_nonneg c) hf.nonneg, hf.smooth.const_smul c, ?_⟩
  intro j hj x
  rw [iteratedFDeriv_const_smul_apply' ((hf.smooth.of_le (by exact_mod_cast hj)).contDiffAt),
    norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf.bound j hj x) (abs_nonneg c)).trans_eq (by ring)

theorem sub (hf : WJets r B p f) (hg : WJets r C p g) :
    WJets r (B + C) p (fun x => f x - g x) := by
  simpa only [abs_neg, abs_one, one_mul, neg_one_smul, sub_eq_add_neg] using
    hf.add (hg.const_smul (-1))

theorem translate (hf : WJets r B p f) (b : E) :
    WJets r (B * (1 + ‖b‖) ^ p) p (fun x => f (x + b)) := by
  refine ⟨by positivity [hf.nonneg], hf.smooth.comp (contDiff_id.add contDiff_const), ?_⟩
  intro j hj x
  rw [iteratedFDeriv_comp_add_right]
  calc
    _ ≤ B * (1 + ‖x + b‖) ^ p := hf.bound j hj _
    _ ≤ B * ((1 + ‖b‖) * (1 + ‖x‖)) ^ p := by
      apply mul_le_mul_of_nonneg_left _ hf.nonneg
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [norm_add_le x b, mul_nonneg (norm_nonneg b) (norm_nonneg x)]
    _ = _ := by rw [mul_pow]; ring

theorem comp_affine (hf : WJets r B p f) (A : E →L[ℝ] E) (b : E) :
    WJets r (B * (1 + ‖A‖ + ‖b‖) ^ p * max 1 ‖A‖ ^ r) p
      (fun x => f (A x + b)) := by
  have hB := hf.nonneg
  refine ⟨by positivity, hf.smooth.comp (A.contDiff.add contDiff_const), ?_⟩
  intro j hj x
  change ‖iteratedFDeriv ℝ j ((fun y => f (y + b)) ∘ A) x‖ ≤ _
  rw [A.iteratedFDeriv_comp_right (hf.translate b).smooth x (by exact_mod_cast hj)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => f (y + b)) (A x)‖ * ∏ _ : Fin j, ‖A‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j f (A x + b)‖ * ‖A‖ ^ j := by
      rw [iteratedFDeriv_comp_add_right]; simp
    _ ≤ (B * (1 + ‖A x + b‖) ^ p) * max 1 ‖A‖ ^ r := by
      apply mul_le_mul (hf.bound j hj _) _ (by positivity) (by positivity)
      exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hj)
    _ ≤ (B * ((1 + ‖A‖ + ‖b‖) * (1 + ‖x‖)) ^ p) * max 1 ‖A‖ ^ r := by
      gcongr
      exact one_add_norm_affine_le A b x
    _ = _ := by rw [mul_pow]; ring

theorem mul {f g : E → ℝ} (hf : WJets r B p f) (hg : WJets r C q g) :
    WJets r ((2 : ℝ) ^ r * B * C) (p + q) (fun x => f x * g x) := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  refine ⟨by positivity, hf.smooth.mul hg.smooth, ?_⟩
  intro j hj x
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf.smooth hg.smooth x (by exact_mod_cast hj)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (B * (1 + ‖x‖) ^ p) * (C * (1 + ‖x‖) ^ q) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      gcongr
      · exact hf.bound i (hi'.trans hj) x
      · exact hg.bound (j - i) (by omega) x
    _ = (2 : ℝ) ^ j * B * C * (1 + ‖x‖) ^ (p + q) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, pow_add]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hB) hC) (by positivity)

end WJets

theorem QBoundedJets.weighted {r p : ℕ} {B : ℝ} {f : E → F}
    (hf : QBoundedJets r B f) : WJets r B p f := by
  refine ⟨hf.nonneg, hf.smooth, ?_⟩
  intro j hj x
  exact (hf.bound j hj x).trans (le_mul_of_one_le_right hf.nonneg
    (one_le_pow₀ (by linarith [norm_nonneg x])))

namespace WQ

variable {r s p q : ℕ} {B C : ℝ} {f : E → F}

theorem of_le (hf : WQ r B p f) (hs : s ≤ r) : WQ s B p f := by
  exact ⟨hf.nonneg, hf.smooth.of_le (by exact_mod_cast hs),
    fun j hj hjs x => hf.bound j hj (hjs.trans hs) x⟩

theorem derivativeJets (hf : WQ (r + 1) B p f) : WJets r B p (fderiv ℝ f) := by
  refine ⟨hf.nonneg, hf.smooth.fderiv_right (by simp), ?_⟩
  intro j hj x
  rw [norm_iteratedFDeriv_fderiv]
  exact hf.bound (j + 1) (by omega) (by omega) x

end WQ

theorem QPotential.weighted {r p : ℕ} {B : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QPotential r B f) : WQ r B p f := by
  refine ⟨hf.nonneg, hf.smooth, ?_⟩
  intro j hj hjr x
  exact (hf.bound j hj hjr x).trans (le_mul_of_one_le_right hf.nonneg
    (one_le_pow₀ (by linarith [norm_nonneg x])))

namespace WJets

variable {n p : ℕ} {G : ℝ → E → F} {b : ℝ → ℝ}

theorem integral (μ : Measure ℝ) (hG : ContDiff ℝ n (Function.uncurry G))
    (hjets : ∀ t, WJets n (b t) p (G t)) (hb : Integrable b μ) :
    WJets n (∫ t, b t ∂μ) p (fun x => ∫ t, G t x ∂μ) := by
  have hnonneg : 0 ≤ ∫ t, b t ∂μ := integral_nonneg (fun t => (hjets t).nonneg)
  have hInt (x : E) : Integrable (fun t => G t x) μ := by
    apply (hb.mul_const ((1 + ‖x‖) ^ p)).mono'
      (hG.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    exact ae_of_all _ (fun t => (hjets t).norm_le x)
  have h0 (x : E) : ‖∫ t, G t x ∂μ‖ ≤ (∫ t, b t ∂μ) * (1 + ‖x‖) ^ p := by
    rw [← integral_mul_const]
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
        (hb.mul_const _) (ae_of_all _ (fun t => (hjets t).norm_le x)))
  have hlocal {x y : E} (hy : y ∈ Metric.ball x 1) :
      (1 + ‖y‖) ^ p ≤ (2 + ‖x‖) ^ p := by
    apply pow_le_pow_left₀ (by positivity)
    have H : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y - x) x
    have hd : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    linarith
  induction n generalizing F with
  | zero =>
    refine ⟨hnonneg, contDiff_zero.mpr ?_, ?_⟩
    · apply continuous_iff_continuousAt.mpr
      intro x
      apply continuousAt_of_dominated (bound := fun t => b t * (2 + ‖x‖) ^ p)
      · exact Eventually.of_forall (fun y => (hInt y).aestronglyMeasurable)
      · filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
        exact ae_of_all _ (fun t => ((hjets t).norm_le y).trans
          (mul_le_mul_of_nonneg_left (hlocal hy) (hjets t).nonneg))
      · exact hb.mul_const _
      · exact ae_of_all _ (fun t => (hjets t).smooth.continuous.continuousAt)
    · intro j hj x
      have hj0 : j = 0 := by omega
      subst j
      simpa only [norm_iteratedFDeriv_zero] using h0 x
  | succ n ih =>
    let D : ℝ → E → E →L[ℝ] F := fun t x => fderiv ℝ (G t) x
    have hD : ContDiff ℝ n (Function.uncurry D) := by
      have hFam : ContDiff ℝ (n + 1) (fun z : (ℝ × E) × E => G z.1.1 z.2) :=
        hG.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact hFam.fderiv contDiff_snd (by simp)
    have hdjets (t : ℝ) : WJets n (b t) p (D t) := (hjets t).derivativeJets
    have hDInt (x : E) : Integrable (fun t => D t x) μ :=
      (hb.mul_const ((1 + ‖x‖) ^ p)).mono'
        (hD.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
        (ae_of_all _ (fun t => (hdjets t).norm_le x))
    have hD0 (x : E) : ‖∫ t, D t x ∂μ‖ ≤ (∫ t, b t ∂μ) * (1 + ‖x‖) ^ p := by
      rw [← integral_mul_const]
      exact (norm_integral_le_integral_norm _).trans
        (integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
          (hb.mul_const _) (ae_of_all _ (fun t => (hdjets t).norm_le x)))
    have hAvg := ih hD hdjets hDInt hD0
    have hder (x : E) : HasFDerivAt (fun y => ∫ t, G t y ∂μ) (∫ t, D t x ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x 1)
        (bound := fun t => b t * (2 + ‖x‖) ^ p) (F' := fun y t => D t y)
      · exact Metric.ball_mem_nhds x (by norm_num)
      · exact Eventually.of_forall (fun y => (hInt y).aestronglyMeasurable)
      · exact hInt x
      · exact (hD.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      · exact ae_of_all _ (fun t y hy => ((hdjets t).norm_le y).trans
          (mul_le_mul_of_nonneg_left (hlocal hy) (hjets t).nonneg))
      · exact hb.mul_const _
      · exact ae_of_all _ (fun t y _ => ((hjets t).smooth.differentiable (by simp) y).hasFDerivAt)
    refine ⟨hnonneg, contDiff_succ_iff_hasFDerivAt.mpr ⟨_, hAvg.smooth, hder⟩, ?_⟩
    intro j hj x
    cases j with
    | zero => simpa only [norm_iteratedFDeriv_zero] using h0 x
    | succ j =>
      rw [← norm_iteratedFDeriv_fderiv,
        show fderiv ℝ (fun y => ∫ t, G t y ∂μ) = fun y => ∫ t, D t y ∂μ from
          funext (fun y => (hder y).fderiv)]
      exact hAvg.bound j (by omega) x

end WJets

theorem QPotential.centered_wJets {r : ℕ} {B : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QPotential r B f) (hr : 1 ≤ r) (c : Fin 3 → ℝ) :
    WJets r B 1 (fun x => f (x + c) - f c) := by
  refine ⟨hf.nonneg, (hf.smooth.comp (contDiff_id.add contDiff_const)).sub contDiff_const, ?_⟩
  intro j hj x
  by_cases hj0 : j = 0
  · subst j
    rw [norm_iteratedFDeriv_zero]
    have H := (hf.lipschitzWith hr).norm_sub_le (x + c) c
    change ‖f (x + c) - f c‖ ≤ B * ‖x + c - c‖ at H
    rw [add_sub_cancel_right] at H
    exact H.trans (by rw [pow_one]; nlinarith [hf.nonneg])
  · have hs : ContDiff ℝ j (fun x => f (x + c)) :=
      (hf.translate c).smooth.of_le (by exact_mod_cast hj)
    change ‖iteratedFDeriv ℝ j ((fun y => f (y + c)) - fun _ => f c) x‖ ≤ _
    rw [iteratedFDeriv_sub hs (contDiff_const : ContDiff ℝ j (fun _ : (Fin 3 → ℝ) => f c)),
      iteratedFDeriv_const_of_ne hj0, sub_zero, iteratedFDeriv_comp_add_right]
    exact (hf.bound j (by omega) hj _).trans
      (by rw [pow_one]; nlinarith [mul_nonneg hf.nonneg (norm_nonneg x)])

namespace StepCalculus

local notation "X" => (Fin 3 → ℝ)

private theorem weighted_anchor_density {n : ℕ} {B : ℝ} {f : X → ℝ}
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

theorem wJets_tiltedAverage {n p : ℕ} {B C m : ℝ} {f g : X → ℝ}
    (hf : QPotential (n + 1) B f) (hg : WJets n C p g)
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1) :
    WJets n (noiseAverageCoefficient n p B * C) p (tiltedAverage m v f g) := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  let A := anchorJetCoefficient n B
  have hA : 0 ≤ A := by dsimp only [A, anchorJetCoefficient]; positivity
  let b : ℝ → ℝ := fun t => (2 : ℝ) ^ n * C * A * Real.exp ((B + n + p) * |t|)
  have hNum (t : ℝ) : WJets n (b t) p
      (fun x => g (x + t • v) * Real.exp (m * (f (x + t • v) - f x))) := by
    have hpow : (1 + ‖t • v‖) ^ p ≤ Real.exp ((p : ℝ) * |t|) := by
      rw [norm_smul, Real.norm_eq_abs, Real.exp_nat_mul]
      apply pow_le_pow_left₀ (by positivity)
      exact (by nlinarith [abs_nonneg t] : 1 + |t| * ‖v‖ ≤ 1 + |t|).trans
        (by simpa only [add_comm] using Real.add_one_le_exp |t|)
    have hShift : WJets n (C * Real.exp ((p : ℝ) * |t|)) p (fun x => g (x + t • v)) :=
      (hg.translate (t • v)).mono (mul_le_mul_of_nonneg_left hpow hC) le_rfl
    have H := hShift.mul ((weighted_anchor_density hf hm v hv t).weighted (p := 0))
    apply H.mono _ (by simp)
    dsimp only [b, A]
    rw [show (B + (n : ℝ) + p) * |t| = (p : ℝ) * |t| + (B + n) * |t| by ring,
      Real.exp_add]
    exact le_of_eq (by ring)
  have hFam : ContDiff ℝ n (fun z : ℝ × X =>
      g (z.2 + z.1 • v) * Real.exp (m * (f (z.2 + z.1 • v) - f z.2))) :=
    (hg.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const))).mul
      (((contDiff_const.mul ((hf.smooth.comp (contDiff_snd.add
        (contDiff_fst.smul contDiff_const))).sub (hf.smooth.comp contDiff_snd))).exp).of_le
          (by exact_mod_cast Nat.le_succ n))
  have hN := WJets.integral (gaussianReal 0 1) hFam hNum
    ((integrable_exp_mul_abs_gaussian (B + n + p)).const_mul ((2 : ℝ) ^ n * C * A))
  have hP := hN.mul ((qBoundedJets_inv_anchorPartition hf hm v hv).weighted (p := 0))
  have heq : tiltedAverage m v f g = fun x =>
      (∫ t, g (x + t • v) * Real.exp (m * (f (x + t • v) - f x)) ∂gaussianReal 0 1) *
        (anchorPartition m v f x)⁻¹ := by
    funext x
    change noiseMean m v f x (fun t => g (x + t • v)) = _
    rw [noiseMean_anchor, div_eq_mul_inv]
  rw [heq]
  convert hP using 1
  dsimp only [b, noiseAverageCoefficient, gaussianExpMoment, A]
  rw [integral_const_mul]
  ring

theorem wJets_spatialCovariance {n p q : ℕ} {B C D m : ℝ} {f g a : X → ℝ}
    (hf : QPotential (n + 1) B f) (hg : WJets n C p g) (ha : WJets n D q a)
    (hm : m ∈ Icc (0 : ℝ) 1) (v : X) (hv : ‖v‖ ≤ 1) :
    WJets n (noiseAverageCoefficient n (p + q) B * ((2 : ℝ) ^ n * C * D) +
      (2 : ℝ) ^ n * (noiseAverageCoefficient n p B * C) *
        (noiseAverageCoefficient n q B * D)) (p + q) (spatialCovariance m v f g a) := by
  exact (wJets_tiltedAverage hf (hg.mul ha) hm v hv).sub
    ((wJets_tiltedAverage hf hg hm v hv).mul (wJets_tiltedAverage hf ha hm v hv))

end StepCalculus

theorem QPotential.const_mul {r : ℕ} {B : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QPotential r B f) (c : ℝ) : QPotential r (|c| * B) (fun x => c * f x) := by
  refine ⟨mul_nonneg (abs_nonneg c) hf.nonneg, hf.smooth.const_smul c, ?_⟩
  intro j hj hjr x
  change ‖iteratedFDeriv ℝ j (fun x => c • f x) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hf.smooth.of_le (by exact_mod_cast hjr)).contDiffAt),
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hf.bound j hj hjr x) (abs_nonneg c)

end SKBarriers2
