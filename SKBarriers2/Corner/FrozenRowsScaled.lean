module

public import SKBarriers2.Analysis.ScaledChain
public import SKBarriers2.Corner.FrozenRowsWeighted

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def scaledTaylorTail (f : ℝ → ℝ) (z ρ : ℝ) (y : ℝ) : ℝ :=
  (ρ ^ 3)⁻¹ * quadraticTaylorTail f z (ρ * y + z)

theorem iteratedDeriv_quadraticTaylorTail {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : ℝ) (j : ℕ) :
    iteratedDeriv j (quadraticTaylorTail f z) = quadraticResidualSpatialJet f z j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    exact (quadraticResidualSpatialJet_hasDerivAt hf z y j).deriv

theorem scaledTaylorTail_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z ρ : ℝ) :
    ContDiff ℝ ∞ (scaledTaylorTail f z ρ) := by
  exact ((hf.sub (scalarTaylorPolynomial_contDiff f 2 z)).comp
    ((contDiff_id.const_smul ρ).add contDiff_const)).const_smul ((ρ ^ 3)⁻¹)

theorem iteratedDeriv_scaledTaylorTail {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (z ρ y : ℝ) (j : ℕ) :
    iteratedDeriv j (scaledTaylorTail f z ρ) y =
      (ρ ^ 3)⁻¹ * (ρ ^ j * quadraticResidualSpatialJet f z j (ρ * y + z)) := by
  have hT : ContDiff ℝ j (fun x => quadraticTaylorTail f z (x + z)) :=
    ((hf.sub (scalarTaylorPolynomial_contDiff f 2 z)).comp
      (contDiff_id.add contDiff_const)).of_le (by simp)
  change iteratedDeriv j (fun x => (ρ ^ 3)⁻¹ * quadraticTaylorTail f z (ρ * x + z)) y = _
  rw [iteratedDeriv_const_mul_field]
  rw [show (fun x => quadraticTaylorTail f z (ρ * x + z)) =
      (fun x => (fun w => quadraticTaylorTail f z (w + z)) (ρ * x)) from rfl,
    iteratedDeriv_comp_const_mul hT ρ, iteratedDeriv_comp_add_const,
    iteratedDeriv_quadraticTaylorTail hf]

theorem quadraticResidualSpatialJet_scaled_bound {f : ℝ → ℝ} {B ρ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hρ : ρ ∈ Icc (0 : ℝ) 1)
    {r j : ℕ} (hj : j ≤ r)
    (hb : ∀ a, 3 ≤ a → a ≤ max 3 r → ∀ x, |iteratedDeriv a f x| ≤ B)
    (z y : ℝ) :
    |ρ ^ j * quadraticResidualSpatialJet f z j (ρ * y + z)| ≤
      B * ρ ^ 3 * (1 + |y|) ^ 3 := by
  have hw : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hy : |y| ≤ 1 + |y| := by linarith
  have hdy : |ρ * y + z - z| = ρ * |y| := by
    rw [add_sub_cancel_right, abs_mul, abs_of_nonneg hρ.1]
  have H := quadraticTaylorTail_bounds hf (hb 3 le_rfl (le_max_left _ _)) z (ρ * y + z)
  rw [hdy] at H
  have hBp : 0 ≤ B * ρ ^ 3 := by positivity [hρ.1]
  cases j with
  | zero =>
    change |1 * quadraticTaylorTail f z (ρ * y + z)| ≤ _
    rw [one_mul]
    calc
      _ ≤ B * (ρ * |y|) ^ 3 / 6 := H.1
      _ ≤ B * ρ ^ 3 * |y| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg y) 3]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy 3) hBp
  | succ j =>
    cases j with
    | zero =>
      change |ρ ^ 1 * quadraticTaylorTailFirst f z (ρ * y + z)| ≤ _
      rw [pow_one, abs_mul, abs_of_nonneg hρ.1]
      calc
        _ ≤ ρ * (B * (ρ * |y|) ^ 2 / 2) := mul_le_mul_of_nonneg_left H.2.1 hρ.1
        _ ≤ B * ρ ^ 3 * |y| ^ 2 := by nlinarith [sq_nonneg y]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((pow_le_pow_left₀ (abs_nonneg _) hy 2).trans (pow_le_pow_right₀ hw (by omega))) hBp
    | succ j =>
      cases j with
      | zero =>
        change |ρ ^ 2 * quadraticTaylorTailSecond f z (ρ * y + z)| ≤ _
        rw [abs_mul, abs_of_nonneg (sq_nonneg ρ)]
        calc
          _ ≤ ρ ^ 2 * (B * (ρ * |y|)) := mul_le_mul_of_nonneg_left H.2.2 (sq_nonneg ρ)
          _ = B * ρ ^ 3 * |y| := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (hy.trans (by simpa only [pow_one] using pow_le_pow_right₀ hw (show 1 ≤ 3 by omega))) hBp
      | succ j =>
        change |ρ ^ (j + 3) * iteratedDeriv (j + 3) f (ρ * y + z)| ≤ _
        rw [abs_mul, abs_of_nonneg (pow_nonneg hρ.1 _)]
        calc
          _ ≤ ρ ^ (j + 3) * B := mul_le_mul_of_nonneg_left
            (hb (j + 3) (by omega) (hj.trans (le_max_right _ _)) _) (pow_nonneg hρ.1 _)
          _ ≤ ρ ^ 3 * B := mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hρ.1 hρ.2 (by omega)) hB
          _ ≤ _ := by
            simpa only [mul_comm B (ρ ^ 3)] using
              le_mul_of_one_le_right hBp (one_le_pow₀ hw)

theorem scaledTaylorTail_wJets {f : ℝ → ℝ} {B ρ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (r : ℕ) (hb : ∀ a, 3 ≤ a → a ≤ max 3 r → ∀ x, |iteratedDeriv a f x| ≤ B)
    (z : ℝ) : WJets r B 3 (scaledTaylorTail f z ρ) := by
  refine ⟨hB, (scaledTaylorTail_contDiff hf z ρ).of_le (by simp), ?_⟩
  intro j hj y
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    iteratedDeriv_scaledTaylorTail hf, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hρ.1.le _))]
  calc
    _ ≤ (ρ ^ 3)⁻¹ * (B * ρ ^ 3 * (1 + |y|) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (quadraticResidualSpatialJet_scaled_bound hf hB ⟨hρ.1.le, hρ.2⟩ hj hb z y)
        (inv_nonneg.mpr (pow_nonneg hρ.1.le _))
    _ = B * (1 + ‖y‖) ^ 3 := by
      rw [Real.norm_eq_abs]
      field_simp [ne_of_gt hρ.1]

theorem wJets_separable_sum {r p : ℕ} {B : ℝ} {f : ℝ → ℝ}
    (hf : WJets r B p f) :
    WJets r (3 * B) p (fun y : Vec3 => ∑ i : Fin 3, f (y i)) := by
  have hs (i : Fin 3) : ContDiff ℝ r (fun y : Vec3 => f (y i)) :=
    hf.smooth.comp (tripleCoordinate i).contDiff
  refine ⟨by positivity [hf.nonneg], ContDiff.sum (fun i _ => hs i), ?_⟩
  intro j hj y
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hs i).of_le (by exact_mod_cast hj)).contDiffAt)]
  calc
    _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ j (fun y : Vec3 => f (y i)) y‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, B * (1 + ‖y‖) ^ p := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_iteratedFDeriv_coordinate_le hf.smooth hj i y).trans
      have H := hf.bound j hj (y i)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at H
      exact H.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_le_pi_norm y i) 1) p) hf.nonneg)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]; ring

def scaledTerminalResidual (β : ℝ) (α : ℝ → ℝ) (s h z ρ : ℝ) : Vec3 → ℝ :=
  fun y => (ρ ^ 3)⁻¹ * terminalResidual β α s h z (ρ • y + (fun _ => z))

theorem scaledTerminalResidual_eq_sum (β : ℝ) (α : ℝ → ℝ) (s h z ρ : ℝ) :
    scaledTerminalResidual β α s h z ρ =
      fun y => ∑ i : Fin 3, scaledTaylorTail (Phi β α (s + 4 * h)) z ρ (y i) := by
  funext y
  simp only [scaledTerminalResidual, terminalResidual_eq_quadraticTaylorTails,
    scaledTaylorTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem scalarData_scaledTerminalResidual_wJets {β s h ρ : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (r : ℕ) (z : ℝ) :
    WJets r (terminalJetBound D (max 3 r)) 3
      (scaledTerminalResidual β (cdf (D.μ : Measure ℝ)) s h z ρ) := by
  rw [scaledTerminalResidual_eq_sum]
  exact wJets_separable_sum (scaledTaylorTail_wJets (scalarData_phi_contDiff D ht)
    (scalarTerminalJetBound_nonneg D _) hρ r
    (fun a ha har x => scalarData_jet_le D (by omega) har ht x) z)

theorem completedSquare_moment_eq_tiltedAverage (P : QuadraticTerminal) (m : ℝ)
    (v x : Vec3) {R ψ : Vec3 → ℝ} {L : ℝ} (hD : 0 < P.precision m v)
    (hR : Continuous R) (hψ : Continuous ψ)
    (hLip : ∀ x y, |R x - R y| ≤ L * ‖x - y‖) :
    epsilonMoment m v (fun _ y => P.value y + R y) (fun _ => ψ) 0 x =
      StepCalculus.tiltedAverage m ((Real.sqrt (P.precision m v)⁻¹) • v) R ψ
        (quadraticMeanLinear P m v x + quadraticNoiseConstant P m v) := by
  rw [← quadraticMeanTransition_eq_affine]
  exact completedSquare_normalized_moment P m v x hD hR hψ hLip

theorem scaled_completedSquare_moment_wJets {r p : ℕ} {ρ B C K L m : ℝ}
    (P : QuadraticTerminal) (v c : Vec3) {R ψ : Vec3 → ℝ}
    (hρ : ρ ≠ 0) (hD : 0 < P.precision m v) (hR : Continuous R) (hψ : Continuous ψ)
    (hLip : ∀ x y, |R x - R y| ≤ L * ‖x - y‖)
    (hf : QPotential (r + 1) B (spatialRescale ρ c R))
    (hg : WJets r C p (spatialRescale ρ c ψ)) (hm : m ∈ Icc (0 : ℝ) 1)
    (hK : 1 ≤ K) (hv : ‖ρ⁻¹ • ((Real.sqrt (P.precision m v)⁻¹) • v)‖ ≤ K) :
    let A := quadraticMeanLinear P m v
    let b := ρ⁻¹ • (A c + quadraticNoiseConstant P m v - c)
    WJets r ((StepCalculus.noiseAverageCoefficient r p (B * K ^ (r + 1)) *
      (C * K ^ (p + r))) * (1 + ‖A‖ + ‖b‖) ^ p * max 1 ‖A‖ ^ r) p
      (spatialRescale ρ c (epsilonMoment m v (fun _ y => P.value y + R y) (fun _ => ψ) 0)) := by
  have he : epsilonMoment m v (fun _ y => P.value y + R y) (fun _ => ψ) 0 =
      fun x => StepCalculus.tiltedAverage m ((Real.sqrt (P.precision m v)⁻¹) • v) R ψ
        (quadraticMeanLinear P m v x + quadraticNoiseConstant P m v) := by
    funext x
    exact completedSquare_moment_eq_tiltedAverage P m v x hD hR hψ hLip
  rw [he, StepCalculus.spatialRescale_affine_tiltedAverage hρ]
  exact StepCalculus.wJets_affineAverage_boundedNoise hf hg hm hK _ hv _ _

def originalEpsilonKJet (l : ℝ → List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (ρ : ℝ) (c : Vec3) (y : ℝ → Vec3) (n : ℕ) (ε k : ℝ) : MomentKJet :=
  let F := fun t => epsilonSpatialJet (fun e => epsilonChain (l t) Q K e) n ε (ρ • y t + c)
  ⟨F k, iteratedDeriv 1 F k, iteratedDeriv 2 F k⟩

def normalizedEpsilonKJet (l : ℝ → List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (ρ : ℝ) (c : Vec3) (y : ℝ → Vec3) (n : ℕ) (ε k : ℝ) : MomentKJet :=
  let F := fun t => iteratedDeriv n
    (fun e => normalizedVariationChain (l t) Q.value K ρ c e (y t)) (ρ ^ 3 * ε)
  ⟨F k, iteratedDeriv 1 F k, iteratedDeriv 2 F k⟩

theorem originalEpsilonKJet_eq_scale {ρ : ℝ} (hρ : ρ ≠ 0)
    (l : ℝ → List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (c : Vec3) (y : ℝ → Vec3) (n : ℕ) (ε k : ℝ) :
    originalEpsilonKJet l Q K ρ c y n ε k =
      (normalizedEpsilonKJet l Q K ρ c y n ε k).scale ((ρ ^ 3) ^ n) := by
  have he : (fun t => epsilonSpatialJet (fun e => epsilonChain (l t) Q K e) n ε (ρ • y t + c)) =
      fun t => (ρ ^ 3) ^ n * iteratedDeriv n
        (fun e => normalizedVariationChain (l t) Q.value K ρ c e (y t)) (ρ ^ 3 * ε) := by
    funext t
    exact iteratedDeriv_spatialRescale_variationChain hρ (l t) Q.value K c (y t) n ε
  simp only [originalEpsilonKJet, he, normalizedEpsilonKJet, MomentKJet.scale,
    iteratedDeriv_const_mul_field]
  congr 1
  exact congrFun he k

theorem originalEpsilonKJet_weak_bound {h M : ℝ} (hh : 0 < h)
    (l : ℝ → List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (c : Vec3) (y : ℝ → Vec3) (n : ℕ) (ε k g : ℝ)
    (H : MomentKJet.Bound (MomentKJet.rescale (Real.sqrt h)
      (normalizedEpsilonKJet l Q K (Real.sqrt h) c y n ε k))
        ((M * (1 + g ^ 2) ^ 3) ^ n)) :
    MomentKJet.Bound (MomentKJet.rescale (Real.sqrt h)
      (originalEpsilonKJet l Q K (Real.sqrt h) c y n ε k))
        ((M * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3) ^ n) := by
  rw [originalEpsilonKJet_eq_scale (Real.sqrt_pos.mpr hh).ne', MomentKJet.rescale_scale]
  have he : (Real.sqrt h) ^ 3 = Real.sqrt h * h := by
    rw [pow_succ, Real.sq_sqrt hh.le, mul_comm]
  convert H.scale (((Real.sqrt h) ^ 3) ^ n) using 1
  rw [abs_of_nonneg (pow_nonneg (pow_nonneg (Real.sqrt_nonneg h) 3) n), he, ← mul_pow]
  congr 1
  ring

theorem frozenSchedule_scaled_direction_bound {β a h k : ℝ} (hh : 0 < h)
    (hk : |k| ≤ 1 / 2) {v : ℝ × Vec3}
    (hv : v ∈ scaleDirections (Real.sqrt h)⁻¹ (frozenSchedule β a (1 / 2) h k)) :
    ‖v.2‖ ≤ 6 * (|β| + 1) := by
  rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
  have H := (frozenSchedule_centered_direction_scale hh.le hk hw).1
  change ‖(Real.sqrt h)⁻¹ • w.2‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hh))]
  calc
    _ ≤ (Real.sqrt h)⁻¹ * (6 * (|β| + 1) * Real.sqrt h) :=
      mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := by field_simp

theorem centeredSpatialWeight_rescale {ρ : ℝ} (hρ : 0 ≤ ρ) (c y : Vec3) (p : ℕ) :
    centeredSpatialWeight c ρ p (ρ • y + c) = ρ ^ p * (1 + ‖y‖) ^ p := by
  simp only [centeredSpatialWeight, add_sub_cancel_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hρ]
  rw [show ρ + ρ * ‖y‖ = ρ * (1 + ‖y‖) by ring, mul_pow]

theorem CubicEpsilonJetBound.rescale {F : ℝ → Vec3 → ℝ} {V : Set ℝ}
    {ρ M : ℝ} {c : Vec3} (H : CubicEpsilonJetBound F V c ρ M) (hρ : 0 ≤ ρ)
    {ε : ℝ} (hε : ε ∈ V) (y : Vec3) :
    |epsilonSpatialJet F 1 ε (ρ • y + c)| ≤
        M * ρ ^ 3 * (1 + ‖y‖) ^ 3 ∧
      |epsilonSpatialJet F 2 ε (ρ • y + c)| ≤
        M ^ 2 * (ρ ^ 3) ^ 2 * (1 + ‖y‖) ^ 6 ∧
      |epsilonSpatialJet F 3 ε (ρ • y + c)| ≤
        M ^ 3 * (ρ ^ 3) ^ 3 * (1 + ‖y‖) ^ 9 := by
  have H' := H ε hε (ρ • y + c)
  simp only [centeredSpatialWeight_rescale hρ] at H'
  constructor
  · simpa only [mul_assoc] using H'.1
  constructor
  · simpa only [mul_assoc, ← pow_mul, Nat.reduceMul] using H'.2.1
  · simpa only [mul_assoc, ← pow_mul, Nat.reduceMul] using H'.2.2

theorem scalarData_frozen_scaled_epsilon_values {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ t, t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ n, 1 ≤ n → n ≤ 3 → ∀ y : Vec3,
        |epsilonSpatialJet (fun e => epsilonChain t
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e)
          n ε (Real.sqrt h • y + (fun _ => z))| ≤
          M ^ n * (Real.sqrt h * h) ^ n * (1 + ‖y‖) ^ (3 * n) := by
  rcases scalarData_frozen_cubic_epsilon_jets D hl hu with ⟨h₀, M, hh₀, hM, H⟩
  refine ⟨h₀, M, hh₀, hM, ?_⟩
  intro r hr h hh hhsmall k hk z t ht ε hε n hn hn₃ y
  have HS := (H r hr h hh hhsmall k hk z t ht).rescale (Real.sqrt_nonneg h) hε y
  have he : (Real.sqrt h) ^ 3 = Real.sqrt h * h := by
    rw [pow_succ, Real.sq_sqrt hh.le, mul_comm]
  interval_cases n
  · simpa only [pow_one, Nat.reduceMul, he] using HS.1
  · simpa only [Nat.reduceMul, he] using HS.2.1
  · simpa only [Nat.reduceMul, he] using HS.2.2

theorem scalarData_frozen_normalized_epsilon_values {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ t, t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ n, 1 ≤ n → n ≤ 3 → ∀ y : Vec3,
        |iteratedDeriv n (fun e => normalizedVariationChain t
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z).value
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (Real.sqrt h) (fun _ => z) e y) ((Real.sqrt h) ^ 3 * ε)| ≤
          M ^ n * (1 + ‖y‖) ^ (3 * n) := by
  rcases scalarData_frozen_scaled_epsilon_values D hl hu with ⟨h₀, M, hh₀, hM, H⟩
  refine ⟨h₀, M, hh₀, hM, ?_⟩
  intro r hr h hh hhsmall k hk z t ht ε hε n hn hn₃ y
  have HB := H r hr h hh hhsmall k hk z t ht ε hε n hn hn₃ y
  change |iteratedDeriv n (fun e => vectorIncrementChain t
    (fun x => (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z).value x +
      e * terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z x)
    (Real.sqrt h • y + (fun _ => z))) ε| ≤ _ at HB
  rw [iteratedDeriv_spatialRescale_variationChain (Real.sqrt_pos.mpr hh).ne',
    abs_mul, abs_of_nonneg (pow_nonneg (pow_nonneg (Real.sqrt_nonneg h) 3) n)] at HB
  have he : (Real.sqrt h) ^ 3 = Real.sqrt h * h := by
    rw [pow_succ, Real.sq_sqrt hh.le, mul_comm]
  rw [he] at HB ⊢
  apply (mul_le_mul_iff_right₀ (pow_pos (mul_pos (Real.sqrt_pos.mpr hh) hh) n)).mp
  convert HB using 1; ring

theorem scalarData_frozen_scaled_frame_qPotential {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) (R : ℕ) (hR : 2 ≤ R) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (-1 : ℝ) 2, ∀ t,
      t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      QPotential R C (spatialRescale (Real.sqrt h) (fun _ => z)
        (epsilonFrameResidual t
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
          (frozenTerminal β (cdf (D.μ : Measure ℝ)) (r - h) h) ε)) := by
  rcases scalarData_epsilonFrameResidual_spatial_qPotential D hl hu R hR with
    ⟨C, hF, hC, hhF, H⟩
  refine ⟨C, min hF 1, hC, lt_min hhF (by norm_num), ?_⟩
  intro r hr h hh hhsmall k hk z ε hε t ht
  exact (H r hr h hh (hhsmall.trans (min_le_left _ _)) k hk z ε hε t ht).spatialRescale
    (by rw [abs_of_nonneg (Real.sqrt_nonneg _)];
        exact Real.sqrt_le_one.mpr (hhsmall.trans (min_le_right _ _))) _

theorem normalized_linear_frame_mixed_jet {ρ : ℝ} (hρ : ρ ≠ 0) :
    deriv (fun y : ℝ => deriv (fun τ : ℝ => (τ / ρ ^ 3) * (ρ * y)) 0) 0 =
      (ρ⁻¹) ^ 2 := by
  have he (y : ℝ) : (fun τ : ℝ => (τ / ρ ^ 3) * (ρ * y)) =
      fun τ => τ * ((ρ⁻¹) ^ 2 * y) := by
    funext τ
    field_simp [hρ]
  have hd (y : ℝ) : deriv (fun τ : ℝ => (τ / ρ ^ 3) * (ρ * y)) 0 = (ρ⁻¹) ^ 2 * y := by
    rw [he]
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const ((ρ⁻¹) ^ 2 * y)).deriv
  simp_rw [hd]
  simpa only [mul_one, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_mul ((ρ⁻¹) ^ 2)).deriv

theorem normalized_linear_frame_mixed_jet_unbounded (B : ℝ) :
    ∃ ρ ∈ Ioc (0 : ℝ) 1,
      B < |deriv (fun y : ℝ => deriv (fun τ : ℝ => (τ / ρ ^ 3) * (ρ * y)) 0) 0| := by
  let ρ := (|B| + 2)⁻¹
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρ₁ : ρ ≤ 1 := by
    exact (inv_le_one₀ (by positivity : 0 < |B| + 2)).mpr (by linarith [abs_nonneg B])
  refine ⟨ρ, ⟨hρ, hρ₁⟩, ?_⟩
  rw [normalized_linear_frame_mixed_jet hρ.ne', abs_of_nonneg (sq_nonneg _)]
  dsimp only [ρ]
  rw [inv_inv]
  nlinarith [abs_nonneg B, le_abs_self B, sq_nonneg (|B| + 1)]

end SKBarriers2.Corner
