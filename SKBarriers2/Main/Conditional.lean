module

public import SKBarriers2.Static.Event
public import SKBarriers2.Dynamics.Assembly
public import SKOptimized.ScaleAnalysis

@[expose] public section

noncomputable section

open scoped NNReal BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set Asymptotics
open OAI.SK OAI.SK.Analytic
open SKBarriers2.Dynamics

namespace SKBarriers2

def RateCoverageCutoff (β qs : ℝ) : Prop :=
  ∀ L : ℕ → ℝ, Tendsto L atTop atTop →
    Tendsto (fun n => L n / (n : ℝ)) atTop (𝓝 0) →
    ∃ c : ℕ → ℝ, (∀ j, 0 < c j) ∧
      ∃ U : ℕ → (n : ℕ) → Set (Disorder n),
        (∀ j n, MeasurableSet (U j n)) ∧
        (∀ j, Tendsto (fun n => (disorderLaw n).real (U j n)) atTop (𝓝 1)) ∧
        ∀ j n J, J ∈ U j n → ∀ F : Config n → Prop,
          (gibbsFiniteLaw β J).prob (fun x => F x ∧
            (gibbsFiniteLaw β J).prob (fun y => F y ∧ qs ≤ |overlap x y|) <
              Real.exp (-c j * L n)) ≤ Real.exp (-(bankPrefix c j + 5) * L n)

theorem exists_rateCoverageCutoff {β : ℝ} (hβ : 1 < β) :
    ∃ qs : ℝ, 0 < qs ∧ qs < 1 ∧ RateCoverageCutoff β qs := by
  exact exists_uniform_coverage_schedule hβ

structure ConditionalScalarData (β : ℝ) (μ : ProbabilityMeasure ℝ) where
  l : ℝ
  r : ℝ
  u : ℝ
  H : ℝ
  m : ℝ
  K : ℝ≥0
  l_pos : 0 < l
  lr : l ≤ r
  ru : r < u
  u_one : u ≤ 1
  H_pos : 0 < H
  m_pos : 0 < m
  mass_one : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1
  minimizer : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β
  unique : ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
    scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ
  mass_lower : m ≤ cdf (μ : Measure ℝ) l
  lipschitz : LipschitzOnWith K (cdf (μ : Measure ℝ)) (Icc (l-H) (r+H))
  overlap_id : ∀ t ∈ Icc l u, scalarCDFOverlap β (cdf (μ : Measure ℝ)) t = t

structure ConditionalRateData (β γ : ℝ) where
  beta_pos : 0 < β
  μ : ProbabilityMeasure ℝ
  scalar : ConditionalScalarData β μ
  qs : ℝ
  qs_pos : 0 < qs
  qs_lt_one : qs < 1
  coverage : RateCoverageCutoff β qs
  cutoffs : StaticCutoffs β (cdf (μ : Measure ℝ)) qs
  l_lt_r : scalar.l < scalar.r
  l_bPrime : scalar.l < cutoffs.b'
  l_gram : scalar.l < cutoffs.b^2 / 2
  l_qs : scalar.l < qs
  θ : ℝ
  exponents : RateExponents γ θ
  Cb : ℝ
  v : ℝ
  Cv : ℝ
  mean : MeanRate β γ Cb
  variance : VarianceCap β v Cv
  variance_exponent : v < 2 - 2 * γ
  S : ℝ
  E : ℝ
  g : ℝ
  S_pos : 0 < S
  E_pos : 0 < E
  g_pos : 0 < g
  R : ℝ
  R_pos : 0 < R
  margin : 24 * Cb < g * R ^ 3
  local_gap : LocalFractionalGap β (Icc scalar.l scalar.r) (rateRho R γ) S E g

private theorem exists_rateAmplitude (Cb : ℝ) {g : ℝ} (hg : 0 < g) :
    ∃ R : ℝ, 0 < R ∧ 24 * Cb < g * R ^ 3 := by
  obtain ⟨R, hR⟩ := exists_gt (max 1 (24 * Cb / g))
  have hR1 : 1 < R := (le_max_left _ _).trans_lt hR
  have hRg : 24 * Cb / g < R := (le_max_right _ _).trans_lt hR
  have hcube : R ≤ R ^ 3 := by
    calc
      R ≤ R * R^2 := le_mul_of_one_le_right (by linarith)
        (by nlinarith [sq_nonneg (R - 1)])
      _ = R^3 := by ring
  refine ⟨R, by linarith, ?_⟩
  exact ((div_lt_iff₀ hg).mp hRg).trans_le
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcube hg.le)

theorem exists_conditionalRateData {β γ Cb v Cv : ℝ}
    (hβ : 1 < β) (hγ : 0 < γ) (hγ' : γ < 3 / 4)
    (hmean : MeanRate β γ Cb) (hvar : VarianceCap β v Cv) (hv : v < 2 - 2 * γ)
    (μ : ProbabilityMeasure ℝ)
    (hunique : ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ)
    (hscalar : ∀ qs : ℝ, 0 < qs → qs < 1 →
      ∀ cuts : StaticCutoffs β (cdf (μ : Measure ℝ)) qs,
      ∃ d : ConditionalScalarData β μ, d.l < d.r ∧ d.l < cuts.b' ∧
        d.l < cuts.b^2/2 ∧ d.l < qs ∧ ∃ S E g : ℝ,
        0 < S ∧ 0 < E ∧ 0 < g ∧ ∀ R : ℝ, 0 < R →
          LocalFractionalGap β (Icc d.l d.r) (rateRho R γ) S E g) :
    Nonempty (ConditionalRateData β γ) := by
  obtain ⟨qs, hqs, hqs1, hcov⟩ := exists_rateCoverageCutoff hβ
  obtain ⟨cuts⟩ := exists_static_cutoffs (by linarith : 0 < β) hqs hqs1.le μ hunique
  obtain ⟨d, hlr, hlb, hlg, hlq, S, E, g, hS, hE, hg, hlocal⟩ := hscalar qs hqs hqs1 cuts
  obtain ⟨R, hR, hmargin⟩ := exists_rateAmplitude Cb hg
  obtain ⟨θ, hexp⟩ := exists_rateExponents hγ hγ'
  exact ⟨⟨by linarith, μ, d, qs, hqs, hqs1, hcov, cuts, hlr, hlb, hlg, hlq,
    θ, hexp, Cb, v, Cv, hmean, hvar, hv, S, E, g, hS, hE, hg, R, hR, hmargin,
    hlocal R hR⟩⟩

namespace ConditionalRateData

def gaps {β γ : ℝ} (d : ConditionalRateData β γ) :
    StaticGapData β (cdf (d.μ : Measure ℝ)) d.scalar.l d.scalar.r d.qs
      (rateRho d.R γ) (rateEta d.θ) d.S d.E d.g :=
  Classical.choose (exists_staticGapData_with_cutoffs d.beta_pos d.scalar.l_pos d.scalar.lr
    d.scalar.ru d.scalar.u_one d.scalar.H_pos d.scalar.m_pos d.qs_pos
    d.qs_lt_one.le d.E_pos (rate_scales_tendsto_zero d.exponents d.R).1
    (Eventually.of_forall (fun n => mul_nonneg d.R_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (Eventually.of_forall (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    d.μ d.scalar.mass_one d.scalar.minimizer d.scalar.unique
    d.scalar.mass_lower d.scalar.K d.scalar.lipschitz d.scalar.overlap_id d.cutoffs d.local_gap)

theorem gaps_b {β γ : ℝ} (d : ConditionalRateData β γ) : d.gaps.b = d.cutoffs.b := by
  exact (Classical.choose_spec (exists_staticGapData_with_cutoffs d.beta_pos
    d.scalar.l_pos d.scalar.lr d.scalar.ru d.scalar.u_one d.scalar.H_pos d.scalar.m_pos
    d.qs_pos d.qs_lt_one.le d.E_pos (rate_scales_tendsto_zero d.exponents d.R).1
    (Eventually.of_forall (fun n => mul_nonneg d.R_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (Eventually.of_forall (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    d.μ d.scalar.mass_one d.scalar.minimizer d.scalar.unique d.scalar.mass_lower
    d.scalar.K d.scalar.lipschitz d.scalar.overlap_id d.cutoffs d.local_gap)).1

theorem gaps_bPrime {β γ : ℝ} (d : ConditionalRateData β γ) : d.gaps.b' = d.cutoffs.b' := by
  exact (Classical.choose_spec (exists_staticGapData_with_cutoffs d.beta_pos
    d.scalar.l_pos d.scalar.lr d.scalar.ru d.scalar.u_one d.scalar.H_pos d.scalar.m_pos
    d.qs_pos d.qs_lt_one.le d.E_pos (rate_scales_tendsto_zero d.exponents d.R).1
    (Eventually.of_forall (fun n => mul_nonneg d.R_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    (Eventually.of_forall (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    d.μ d.scalar.mass_one d.scalar.minimizer d.scalar.unique d.scalar.mass_lower
    d.scalar.K d.scalar.lipschitz d.scalar.overlap_id d.cutoffs d.local_gap)).2

end ConditionalRateData

structure CompatibleRateGeometry {β γ : ℝ} (d : ConditionalRateData β γ) where
  A : ℝ
  A_pos : 0 < A
  D : AssemblyData
  interval_eq : D.I = Icc d.scalar.l d.scalar.r
  rho_eq : D.ρ = rateRho d.R γ
  eta_eq : D.η = rateEta d.θ
  E_eq : D.E = d.E
  qs_eq : D.qStar = d.qs
  b_eq : D.b = d.gaps.b
  bPrime_eq : D.bPrime = d.gaps.b'
  length_eq : D.L = rateLength A γ
  numerics : ∀ c : ℕ → ℝ, (∀ j, 0 ≤ c j) →
    ∀ᶠ n : ℕ in atTop, AssemblyNumerics D c n

theorem geometry_requires_cutoffs {β γ : ℝ} {d : ConditionalRateData β γ}
    (G : CompatibleRateGeometry d) :
    d.scalar.l < d.gaps.b' ∧ d.scalar.l < d.gaps.b ^ 2 / 2 ∧ d.scalar.l < d.qs := by
  obtain ⟨n, hn⟩ := (G.numerics (fun _ => 0) (fun _ => le_rfl)).exists
  have hrad : 0 ≤ (G.D.scales n).centerRadius := by
    dsimp only [AnchorScales.centerRadius]
    linarith only [hn.anchor.epsilon_pos, hn.anchor.transfer_nonneg, hn.anchor.jump_nonneg]
  have hmem := hn.center_band G.D.tLo
    ⟨le_rfl, hn.anchor.threshold_order⟩ G.D.tLo (by simpa only [sub_self, abs_zero] using hrad)
  rw [G.interval_eq] at hmem
  have hV : 0 ≤ (G.D.scales n).V := by
    dsimp only [AnchorScales.V, AnchorScales.T1]
    linarith only [hn.anchor.epsilon_pos, hn.anchor.transfer_nonneg, hn.anchor.jump_nonneg]
  have hT : 0 ≤ (G.D.scales n).T1 := by
    dsimp only [AnchorScales.T1]
    linarith only [hn.anchor.epsilon_pos, hn.anchor.transfer_nonneg, hn.anchor.jump_nonneg]
  have hb' := hn.anchor.locking_margin
  have hC := hn.anchor.cell_margin
  have hq := hn.anchor.selection_margin
  change G.D.tHi + _ < G.D.bPrime at hb'
  change G.D.tHi + _ < G.D.C at hC
  change G.D.tHi + _ < G.D.qStar at hq
  rw [G.bPrime_eq] at hb'
  have hgram := hn.gram_margin
  rw [G.b_eq] at hgram
  rw [G.qs_eq] at hq
  have hord : G.D.tLo ≤ G.D.tHi := hn.anchor.threshold_order
  exact ⟨by linarith only [hmem.1, hord, hb', hV],
    by linarith only [hmem.1, hord, hC, hgram, hV],
    by linarith only [hmem.1, hord, hq, hT]⟩

private theorem shifted_polynomial_exp_decay {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)^3 * Real.exp (-c * (n : ℝ)^p))
      atTop (𝓝 0) := by
  have ht := (SKOptimized.polynomial_stretched_exponential_tendsto_zero 3 p c hp hc).const_mul 8
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n + 1)
    (by linarith : (n + 1 : ℝ) ≤ 2 * n) 3
  rw [mul_pow] at hp'
  norm_num only [show (2 : ℝ)^3 = 8 by norm_num] at hp'
  simp only [Real.rpow_ofNat] at ht ⊢
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right hp' (Real.exp_pos (-c * (n : ℝ)^p)).le

private theorem rho_cube_identity (R γ : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * rateRho R γ n^3 = R^3 * (n : ℝ)^(1-γ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [rateRho, mul_pow, ← Real.rpow_natCast ((n : ℝ)^(-γ/3)) 3,
    ← Real.rpow_mul hn'.le]
  norm_num only [Nat.cast_ofNat]
  rw [show -γ / 3 * (3 : ℝ) = -γ by ring]
  rw [Real.rpow_sub hn', Real.rpow_one, Real.rpow_neg hn'.le]
  rw [div_eq_mul_inv]
  ring

private theorem eta_square_identity (θ : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * rateEta θ n^2 = (n : ℝ)^(1-2*θ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [rateEta, ← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
  norm_num only [Nat.cast_ofNat]
  rw [show -θ * (2 : ℝ) = -(2*θ) by ring]
  rw [Real.rpow_sub hn', Real.rpow_one, Real.rpow_neg hn'.le]
  rw [div_eq_mul_inv]

private theorem weighted_tail_decay {L X : ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hX : ∀ n, 0 ≤ X n) (hsmall : L =o[atTop] X)
    (htail : Tendsto (fun n : ℕ => (n+1 : ℝ)^3 * Real.exp (-(c/2) * X n))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n+1 : ℝ)^3 * Real.exp (K * L n - c * X n))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ htail
  filter_upwards [(hsmall.const_mul_left K).bound (half_pos hc)] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hX n)] at hn
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  linarith only [(le_abs_self (K * L n)).trans hn]

private theorem rate_static_budget {γ θ R A C c K : ℝ}
    (hexp : RateExponents γ θ) (hR : 0 < R) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      C * (n+1 : ℝ)^3 *
        (Real.exp (-c*n*rateRho R γ n^3) + Real.exp (-c*n*rateEta θ n^2) +
          Real.exp (-c*n)) ≤ Real.exp (-K * rateLength A γ n) := by
  have hr : Tendsto (fun n : ℕ => (n+1 : ℝ)^3 *
      Real.exp (-(c/2) * ((n : ℝ)*rateRho R γ n^3))) atTop (𝓝 0) := by
    apply (shifted_polynomial_exp_decay (p := 1-γ) (c := c/2*R^3)
      (by linarith [hexp.gamma_lt]) (by positivity)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [rho_cube_identity R γ hn]
    ring_nf
  have he : Tendsto (fun n : ℕ => (n+1 : ℝ)^3 *
      Real.exp (-(c/2) * ((n : ℝ)*rateEta θ n^2))) atTop (𝓝 0) := by
    apply (shifted_polynomial_exp_decay (p := 1-2*θ) (c := c/2)
      (by linarith [hexp.theta_quarter]) (half_pos hc)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [eta_square_identity θ hn]
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)^3 * Real.exp (-(c/2)*(n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using shifted_polynomial_exp_decay zero_lt_one (half_pos hc)
  have hr' := weighted_tail_decay (K := K) hc (fun n => by
    exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg
      (mul_nonneg hR.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)) _))
    (rate_length_littleO_n_rho_cube hexp hR.ne' A) hr
  have he' := weighted_tail_decay (K := K) hc (fun n => by positivity)
    (rate_length_littleO_n_eta_square hexp A) he
  have hn' := weighted_tail_decay (K := K) hc (fun n => Nat.cast_nonneg n)
    (rate_length_littleO_n hexp A) hn
  have ht := ((hr'.add he').add hn').const_mul C
  simp only [add_zero, mul_zero] at ht
  have hb : ∀ᶠ n : ℕ in atTop,
      C * ((n+1 : ℝ)^3 * Real.exp (K*rateLength A γ n-c*((n : ℝ)*rateRho R γ n^3)) +
        (n+1 : ℝ)^3 * Real.exp (K*rateLength A γ n-c*((n : ℝ)*rateEta θ n^2)) +
        (n+1 : ℝ)^3 * Real.exp (K*rateLength A γ n-c*(n : ℝ))) ≤ 1 :=
    (ht.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ h => h.le)
  filter_upwards [hb] with n hb
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (K*rateLength A γ n))).mp
  rw [← Real.exp_add, show -K*rateLength A γ n + K*rateLength A γ n = 0 by ring,
    Real.exp_zero]
  have heq (x : ℝ) : Real.exp (K*rateLength A γ n-c*((n : ℝ)*x)) =
      Real.exp (-c*n*x) * Real.exp (K*rateLength A γ n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq' : Real.exp (K*rateLength A γ n-c*(n : ℝ)) =
      Real.exp (-c*n) * Real.exp (K*rateLength A γ n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, heq, heq'] at hb
  convert hb using 1
  ring

private theorem rate_crossing_error {γ θ A : ℝ} (hexp : RateExponents γ θ) (hA : 0 < A) :
    Tendsto (fun n : ℕ => ((clockAttemptCutoff n (rateLength A γ n) : ℝ)+1) *
      (3 * Real.exp (-4 * rateLength A γ n))) atTop (𝓝 0) := by
  have hpoly := (SKOptimized.polynomial_stretched_exponential_tendsto_zero 2 (γ/3)
    (3*A) (by linarith [hexp.gamma_pos]) (by positivity)).const_mul 3
  have hex := ((Real.tendsto_exp_atBot.comp
    ((rate_length_tendsto hexp hA).const_mul_atTop_of_neg
      (by norm_num : (-4 : ℝ) < 0))).const_mul 6)
  have ht := hpoly.add hex
  simp only [mul_zero, add_zero, Real.rpow_ofNat, Function.comp_apply] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht
  apply Eventually.of_forall
  intro n
  have hceil := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ (n : ℝ)^2 * Real.exp (rateLength A γ n))).le
  change (clockAttemptCutoff n (rateLength A γ n) : ℝ) ≤ _ at hceil
  have hb := mul_le_mul_of_nonneg_right (add_le_add_right hceil 1)
    (by positivity : 0 ≤ 3 * Real.exp (-4*rateLength A γ n))
  rw [add_comm (1 : ℝ)] at hb
  refine hb.trans_eq ?_
  rw [show (1 + ((n : ℝ)^2 * Real.exp (rateLength A γ n) + 1)) *
      (3 * Real.exp (-4*rateLength A γ n)) =
      3 * (n : ℝ)^2 * (Real.exp (rateLength A γ n) * Real.exp (-4*rateLength A γ n)) +
        6 * Real.exp (-4*rateLength A γ n) by ring,
    ← Real.exp_add]
  rw [show rateLength A γ n + -4*rateLength A γ n =
    -(3*A)*(n : ℝ)^(γ/3) by simp only [rateLength]; ring]
  ring

private theorem affine_le_exp_eventually {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) (a b : ℝ) :
    ∀ᶠ n : ℕ in atTop, a * L n + b ≤ Real.exp (L n) := by
  have h₁ : L =o[atTop] (fun n => Real.exp (L n)) := by
    simpa only [pow_one, Function.comp_def] using
      (Real.isLittleO_pow_exp_atTop (n := 1)).comp_tendsto hL
  have h₀ : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n => Real.exp (L n)) := by
    simpa only [pow_zero, Function.comp_def] using
      (Real.isLittleO_pow_exp_atTop (n := 0)).comp_tendsto hL
  have h := ((h₁.const_mul_left a).add (h₀.const_mul_left b)).bound zero_lt_one
  filter_upwards [h] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] at hn
  simpa only [mul_one] using (le_abs_self _).trans hn

private theorem rate_jump_small {γ θ R a : ℝ} (hexp : RateExponents γ θ)
    (hR : 0 < R) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, 2 / (n : ℝ) ≤ a * rateRho R γ n := by
  have h := SKOptimized.eventually_power_mul_le
    (p := -1) (q := -γ/3) (A := a*R) (B := 2)
    (by linarith [hexp.gamma_lt]) (mul_pos ha hR)
  simpa only [Real.rpow_neg_one, rateRho, div_eq_mul_inv, mul_assoc] using h

private def rateGrid (l r tLo tHi C b b' qs E R γ θ k A : ℝ) (H : ℕ) : AssemblyData where
  I := Icc l r
  B := H + 2
  H := H
  M := fun n => ⌈k * (n : ℝ)^(γ/3)⌉₊
  L := rateLength A γ
  ρ := rateRho R γ
  η := rateEta θ
  E := E
  tLo := tLo
  tHi := tHi
  C := C
  b := b
  bPrime := b'
  qStar := qs
  S := fun n => (16*E+2) * rateRho R γ n
  offset := fun n i => tLo + (i : ℝ) * ((24*E+4) * rateRho R γ n)
  width := fun n => (8*E+2) * rateRho R γ n

private theorem rate_grid_numerics
    {γ θ R E k l r tLo tHi C b b' qs : ℝ} {H : ℕ}
    (hexp : RateExponents γ θ) (hR : 0 < R) (hE : 0 < E) (hk : 0 < k)
    (hl : 0 < l) (hlt : l < tLo) (htt : tLo < tHi) (htr : tHi < r)
    (hC : tHi < C) (hCb : C < b) (hgram : C < b^2/2)
    (hbp : tHi < b') (hqs : tHi < qs) (hb : 0 < b)
    (hpack : ⌈2/b^2⌉₊ ≤ H)
    (hfit : ((H+2 : ℕ) : ℝ) * (24*E+4) * (k*R) < tHi-tLo) :
    let A := k * (-Real.log (1/2)) / 8
    ∀ c : ℕ → ℝ, (∀ j, 0 ≤ c j) → ∀ᶠ n : ℕ in atTop,
      AssemblyNumerics (rateGrid l r tLo tHi C b b' qs E R γ θ k A H) c n := by
  dsimp only
  let A := k * (-Real.log (1/2)) / 8
  let D := rateGrid l r tLo tHi C b b' qs E R γ θ k A H
  have hd : 0 < -Real.log (1/2) := neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  have hA : 0 < A := div_pos (mul_pos hk hd) (by norm_num)
  have hL := rate_length_tendsto hexp hA
  have hρlim := (rate_scales_tendsto_zero hexp R).1
  have hηlim := (rate_scales_tendsto_zero hexp R).2
  have hjlim : Tendsto (fun n : ℕ => 2/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
  have hVlim : Tendsto (fun n => (D.scales n).V) atTop (𝓝 0) := by
    have ht := ((hρlim.const_mul (4*E)).add (hηlim.const_mul 6)).add hjlim
    simpa only [add_zero, mul_zero, D, rateGrid, AssemblyData.scales,
      AnchorScales.V, AnchorScales.T1] using ht.congr' (Eventually.of_forall (fun n => by ring))
  have hTlim : Tendsto (fun n => (D.scales n).T1) atTop (𝓝 0) := by
    have ht := ((hρlim.const_mul (4*E)).add (hηlim.const_mul 4)).add hjlim
    simpa only [add_zero, mul_zero, D, rateGrid, AssemblyData.scales,
      AnchorScales.T1] using ht.congr' (Eventually.of_forall (fun n => by ring))
  have hradlim : Tendsto (fun n => (D.scales n).centerRadius) atTop (𝓝 0) := by
    have ht := ((hρlim.const_mul (3*E)).add (hηlim.const_mul 4)).add (hjlim.const_mul (3/2))
    simpa only [add_zero, mul_zero, D, rateGrid, AssemblyData.scales,
      AnchorScales.centerRadius] using ht.congr' (Eventually.of_forall (fun n => by ring))
  let a := min E 1 / 100
  have ha : 0 < a := div_pos (lt_min hE zero_lt_one) (by norm_num)
  have haE : a ≤ E/100 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have ha1 : a ≤ 1/100 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hηsmall : ∀ᶠ n : ℕ in atTop, rateEta θ n ≤ a * rateRho R γ n := by
    filter_upwards [(rate_eta_littleO_rho hexp hR.ne').bound ha] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
      abs_of_nonneg (mul_nonneg hR.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)), rateEta,
      rateRho] using hn
  have hVsmall := hVlim.eventually (gt_mem_nhds (lt_min
    (sub_pos.mpr hC) (sub_pos.mpr hbp)))
  have hTsmall := hTlim.eventually (gt_mem_nhds (sub_pos.mpr hqs))
  have hradsmall := hradlim.eventually (gt_mem_nhds
    (lt_min (sub_pos.mpr hlt) (sub_pos.mpr htr)))
  have hfits : ∀ᶠ n : ℕ in atTop,
      ((H+2 : ℕ) : ℝ) * (24*E+4) * (k*R + rateRho R γ n) < tHi-tLo := by
    have ht := (hρlim.const_add (k*R)).const_mul (((H+2 : ℕ) : ℝ)*(24*E+4))
    have h := ht.eventually (gt_mem_nhds (by simpa only [add_zero] using hfit))
    exact h
  have hmarker := (rate_crossing_error hexp hA).eventually (gt_mem_nhds zero_lt_one)
  intro c _hc
  have hbudget := affine_le_exp_eventually hL (bankPrefix c (H+2)+5) 0
  have hlevels := affine_le_exp_eventually hL (((H+2 : ℕ) : ℝ)*k/A) ((H+2 : ℕ) : ℝ)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hηsmall, rate_jump_small hexp hR ha,
    hVsmall, hTsmall, hradsmall, hfits, hmarker, hL.eventually (eventually_ge_atTop 5),
    hbudget, hlevels] with n hn hη hj hV hT hrad hfitn hmark hlarge hbud hlev
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hρ : 0 < rateRho R γ n := mul_pos hR (Real.rpow_pos_of_pos hn' _)
  have hη0 : 0 ≤ rateEta θ n := Real.rpow_nonneg hn'.le _
  have hj0 : 0 ≤ 2/(n : ℝ) := by positivity
  have heρ : 0 < E * rateRho R γ n := mul_pos hE hρ
  have haEρ := mul_le_mul_of_nonneg_right haE hρ.le
  have ha1ρ := mul_le_mul_of_nonneg_right ha1 hρ.le
  have hpow : (n : ℝ)^(γ/3) * rateRho R γ n = R := by
    calc
      _ = R * ((n : ℝ)^(γ/3) * (n : ℝ)^(-γ/3)) := by unfold rateRho; ring
      _ = R := by rw [← Real.rpow_add hn', show γ/3 + -γ/3 = 0 by ring,
        Real.rpow_zero, mul_one]
  have hMpos : 1 ≤ D.M n := Nat.ceil_pos.mpr
    (mul_pos hk (Real.rpow_pos_of_pos hn' _))
  have hMlo : k * (n : ℝ)^(γ/3) ≤ (D.M n : ℝ) := Nat.le_ceil _
  have hMhi : (D.M n : ℝ) ≤ k * (n : ℝ)^(γ/3) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hMrho : (D.M n : ℝ) * rateRho R γ n ≤ k*R + rateRho R γ n := by
    calc
      _ ≤ (k * (n : ℝ)^(γ/3)+1) * rateRho R γ n :=
        mul_le_mul_of_nonneg_right hMhi hρ.le
      _ = _ := by rw [add_mul, mul_assoc, hpow, one_mul]
  have hpfit : (D.p n : ℝ) * ((24*E+4)*rateRho R γ n) < tHi-tLo := by
    have ht := mul_le_mul_of_nonneg_left hMrho
      (by positivity : 0 ≤ ((H+2 : ℕ) : ℝ)*(24*E+4))
    have heq : (D.p n : ℝ) * ((24*E+4)*rateRho R γ n) =
        (((H+2 : ℕ) : ℝ)*(24*E+4)) * ((D.M n : ℝ)*rateRho R γ n) := by
      simp only [AssemblyData.p, D, rateGrid, Nat.cast_mul]
      ring
    rw [heq]
    exact ht.trans_lt hfitn
  have hwidth : 0 < D.width n := mul_pos (by positivity) hρ
  have hstep : 0 < (24*E+4)*rateRho R γ n := mul_pos (by positivity) hρ
  have hWstep : D.width n ≤ (24*E+4)*rateRho R γ n := by
    change (8*E+2)*rateRho R γ n ≤ _
    nlinarith only [heρ, hρ]
  have hratio0 : 0 ≤ 2 * (D.scales n).T0 / D.width n := by
    dsimp only [AssemblyData.scales, AnchorScales.T0]
    exact div_nonneg (by positivity) hwidth.le
  have hratio : 2 * (D.scales n).T0 / D.width n ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hwidth).mpr
    change 2 * (2*(E*rateRho R γ n)+2*rateEta θ n+2/(n : ℝ)) ≤
      (1/2)*((8*E+2)*rateRho R γ n)
    nlinarith only [hη, hj, ha1ρ, hρ]
  have hpowmark : (2*(D.scales n).T0/D.width n)^D.M n ≤
      3 * Real.exp (-4*D.L n) := by
    calc
      _ ≤ (1/2 : ℝ)^D.M n := pow_le_pow_left₀ hratio0 hratio _
      _ = Real.exp (Real.log (1/2) * (D.M n : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<1/2)]
      _ ≤ Real.exp (-4*D.L n) := by
        apply Real.exp_le_exp.mpr
        have ht := mul_le_mul_of_nonpos_left hMlo (neg_nonpos.mpr hd.le)
        change Real.log (1/2) * (D.M n : ℝ) ≤ -4*(A*(n : ℝ)^(γ/3))
        dsimp only [A]
        nlinarith only [ht, mul_pos (mul_pos hk hd) (Real.rpow_pos_of_pos hn' (γ/3))]
      _ ≤ _ := by nlinarith only [Real.exp_pos (-4*D.L n)]
  have hcount : ((clockAttemptCutoff n (D.L n) : ℝ)+1) *
      (2*(D.scales n).T0/D.width n)^D.M n < 1 := by
    exact (mul_le_mul_of_nonneg_left hpowmark (by positivity)).trans_lt hmark
  have hplev : (D.p n : ℝ) ≤ (((H+2 : ℕ) : ℝ)*k/A)*D.L n + ((H+2 : ℕ) : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hMhi (Nat.cast_nonneg (H+2) : (0 : ℝ) ≤ (H+2 : ℕ))
    change ((H+2 : ℕ) : ℝ) * (D.M n : ℝ) ≤ _ at ht
    rw [AssemblyData.p, Nat.cast_mul]
    change ((H+2 : ℕ) : ℝ) * (D.M n : ℝ) ≤ _
    convert ht using 1
    dsimp only [D, rateGrid, rateLength]
    field_simp [hA.ne']
  refine ⟨hMpos, le_rfl, ?_, hb, ?_, hgram, hpack, ?_, hwidth, ?_, ?_, hcount,
    hlarge, hplev.trans hlev, ?_⟩
  · change AnchorNumerics (D.scales n)
    have hζ : 0 ≤ 2*rateEta θ n := mul_nonneg (by norm_num) hη0
    refine ⟨hρ, heρ, hj0, hζ, ?_, ?_, ?_, htt.le, ?_, hCb, ?_, ?_, ?_, ?_⟩
    · change 2*rateEta θ n < 2*(E*rateRho R γ n)
      nlinarith only [hη, haEρ, heρ]
    · change (2/(n : ℝ))/2 ≤ E*rateRho R γ n
      nlinarith only [hj, haEρ, heρ]
    · change 0 < tLo
      linarith only [hl, hlt]
    · change tHi + (D.scales n).V < C
      linarith only [hV.trans_le (min_le_left _ _)]
    · change tHi + (D.scales n).V < b'
      linarith only [hV.trans_le (min_le_right _ _)]
    · change tHi + (D.scales n).T1 < qs
      linarith only [hT]
    · dsimp only [D, rateGrid, AssemblyData.scales, AnchorScales.V, AnchorScales.T1]
      nlinarith only [hη, hj, ha1ρ, heρ, hρ]
    · change rateRho R γ n + 5*(E*rateRho R γ n)+4*(2*rateEta θ n)+
        7*(2/(n : ℝ))/2 ≤ (16*E+2)*rateRho R γ n
      nlinarith only [hη, hj, ha1ρ, heρ, hρ]
  · change 0 ≤ C
    linarith only [hl, hlt, htt, hC]
  · intro t ht x hx
    change tLo ≤ t ∧ t ≤ tHi at ht
    change |x-t| ≤ (D.scales n).centerRadius at hx
    have hr₁ := hrad.trans_le (min_le_left _ _)
    have hr₂ := hrad.trans_le (min_le_right _ _)
    exact ⟨by linarith only [(abs_le.mp hx).1, ht.1, hr₁],
      by linarith only [(abs_le.mp hx).2, ht.2, hr₂]⟩
  · intro i hi
    have hi' : (i : ℝ)+1 ≤ D.p n := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_right hi' hstep.le
    change tLo ≤ tLo + (i : ℝ)*((24*E+4)*rateRho R γ n) ∧
      tLo + (i : ℝ)*((24*E+4)*rateRho R γ n) + D.width n ≤ tHi
    exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hstep.le),
      by nlinarith only [hm, hWstep, hpfit]⟩
  · intro i j hij _hj
    have hij' : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
    have hm := mul_le_mul_of_nonneg_right hij' hstep.le
    change (16*E+2)*rateRho R γ n ≤
      (tLo+(j : ℝ)*((24*E+4)*rateRho R γ n)) -
        ((tLo+(i : ℝ)*((24*E+4)*rateRho R γ n))+(8*E+2)*rateRho R γ n)
    nlinarith only [hm]
  · change (bankPrefix c (H+2)+5)*rateLength A γ n ≤ Real.exp (rateLength A γ n)
    simpa only [add_zero] using hbud

theorem exists_compatibleRateGeometry {β γ : ℝ} (d : ConditionalRateData β γ) :
    Nonempty (CompatibleRateGeometry d) := by
  let b := d.cutoffs.b
  let b' := d.cutoffs.b'
  let z := min d.scalar.r (min b' (min (b^2/2) d.qs))
  have hlz : d.scalar.l < z := lt_min d.l_lt_r (lt_min d.l_bPrime (lt_min d.l_gram d.l_qs))
  let δ := (z-d.scalar.l)/4
  have hδ : 0 < δ := div_pos (sub_pos.mpr hlz) (by norm_num)
  let tLo := d.scalar.l + δ
  let tHi := d.scalar.l + 2*δ
  have hlt : d.scalar.l < tLo := by dsimp only [tLo]; linarith
  have htt : tLo < tHi := by dsimp only [tLo, tHi]; linarith
  have htz : tHi < z := by dsimp only [tHi, δ]; linarith only [hlz]
  have htr : tHi < d.scalar.r := htz.trans_le (min_le_left _ _)
  have htb' : tHi < b' := htz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htg : tHi < b^2/2 := htz.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htq : tHi < d.qs := htz.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let C := (tHi+b^2/2)/2
  have htC : tHi < C := by dsimp only [C]; linarith
  have hCg : C < b^2/2 := by dsimp only [C]; linarith
  have hCb : C < b := by
    have hb := d.cutoffs.b_pos
    have hb1 := d.cutoffs.b_lt_one
    change 0 < b at hb
    change b < 1 at hb1
    have hs := mul_pos hb (sub_pos.mpr hb1)
    nlinarith only [hCg, hs, hb]
  let H := ⌈2/b^2⌉₊
  have hE := d.E_pos
  have hR := d.R_pos
  have hstep : 0 < 24*d.E+4 := by positivity
  let k := (tHi-tLo)/(4*((H+2 : ℕ) : ℝ)*(24*d.E+4)*d.R)
  have hk : 0 < k := div_pos (sub_pos.mpr htt) (by positivity)
  have hfit : ((H+2 : ℕ) : ℝ)*(24*d.E+4)*(k*d.R) < tHi-tLo := by
    have he : ((H+2 : ℕ) : ℝ)*(24*d.E+4)*(k*d.R) = (tHi-tLo)/4 := by
      dsimp only [k]
      field_simp [hR.ne', hstep.ne']
    rw [he]
    linarith only [htt]
  let A := k * (-Real.log (1/2)) / 8
  have hA : 0 < A := div_pos (mul_pos hk
    (neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num)))) (by norm_num)
  let D := rateGrid d.scalar.l d.scalar.r tLo tHi C b b' d.qs d.E d.R γ d.θ k A H
  refine ⟨⟨A, hA, D, rfl, rfl, rfl, rfl, rfl, d.gaps_b.symm, d.gaps_bPrime.symm,
    rfl, ?_⟩⟩
  exact rate_grid_numerics d.exponents d.R_pos d.E_pos hk d.scalar.l_pos hlt htt htr
    htC hCb hCg htb' htq d.cutoffs.b_pos le_rfl hfit

private theorem rate_assembly_inputs {β γ : ℝ} (d : ConditionalRateData β γ)
    (G : CompatibleRateGeometry d) :
    ∃ (c : ℕ → ℝ) (U : ℕ → (n : ℕ) → Set (Disorder n))
      (Q : (n : ℕ) → Set (Disorder n)) (qn : ℕ → ℝ),
      QuenchedStaticEvent β G.D.bad Q qn ∧ AssemblyCoverage β G.D c U ∧
      (∀ᶠ n : ℕ in atTop,
        qn n ≤ Real.exp (-(3 * bankPrefix c G.D.B + 20) * G.D.L n)) ∧
      Tendsto G.D.crossingError atTop (𝓝 0) := by
  obtain ⟨k, hk, Q, hQ⟩ := quenchedStaticEvent_of_gapData (cdf (d.μ : Measure ℝ))
    d.beta_pos.ne' d.exponents d.mean d.variance d.variance_exponent d.R_pos
    d.S_pos d.g_pos d.scalar.l_pos.le d.qs_pos.le d.margin d.gaps
  let qn (n : ℕ) := 2 * (n+1 : ℝ)^3 *
    (Real.exp (-k*n*rateRho d.R γ n^3) + Real.exp (-k*n*rateEta d.θ n^2) + Real.exp (-k*n))
  have hL : Tendsto G.D.L atTop atTop := by
    rw [G.length_eq]
    exact rate_length_tendsto d.exponents G.A_pos
  have hsub : Tendsto (fun n => G.D.L n / (n : ℝ)) atTop (𝓝 0) := by
    rw [G.length_eq]
    exact (rate_length_littleO_n d.exponents G.A).tendsto_div_nhds_zero
  obtain ⟨c, hc, U, hm, htyp, hcov⟩ := d.coverage G.D.L hL hsub
  refine ⟨c, U, Q, qn, ?_, ?_, ?_, ?_⟩
  · change QuenchedStaticEvent β (fun n => forbiddenSet n G.D.I (G.D.ρ n)
      (G.D.E * G.D.ρ n) (G.D.η n) G.D.qStar G.D.b G.D.bPrime) Q qn
    simpa only [G.interval_eq, G.rho_eq, G.eta_eq, G.E_eq,
      G.qs_eq, G.b_eq, G.bPrime_eq, qn] using hQ
  · refine ⟨fun j => (hc j).le, hm, htyp, ?_⟩
    simpa only [G.qs_eq] using hcov
  · rw [G.length_eq]
    exact rate_static_budget d.exponents d.R_pos hk
  · change Tendsto (fun n => ((clockAttemptCutoff n (G.D.L n) : ℝ)+1) *
      (3 * Real.exp (-4 * G.D.L n))) atTop (𝓝 0)
    simpa only [G.length_eq] using
      rate_crossing_error d.exponents G.A_pos

theorem barrier_of_rate_of_numerics {β γ : ℝ} (hβ : 1 < β)
    (d : ConditionalRateData β γ) (G : CompatibleRateGeometry d) :
    ∃ A : ℝ, 0 < A ∧ ∀ τ : ℝ, 0 < τ → τ < (1/2 : ℝ) →
      Tendsto (OAI.SK.Strengthened.continuousBadMass β A (γ/3) τ) atTop (𝓝 1) ∧
      Tendsto (OAI.SK.Strengthened.discreteBadMass β A (γ/3) τ) atTop (𝓝 1) := by
  obtain ⟨c, U, Q, qn, hs, hcov, hqn, herr⟩ := rate_assembly_inputs d G
  refine ⟨G.A, G.A_pos, ?_⟩
  apply bad_mass_limits_of_static_event β hβ G.D c U Q qn hs hcov
    (G.numerics c hcov.nonneg) hqn herr G.A (γ/3)
  exact Eventually.of_forall (fun n => by rw [G.length_eq]; exact le_rfl)

theorem barrier_of_rate_all_horizons_of_numerics {β γ : ℝ} (hβ : 1 < β)
    (d : ConditionalRateData β γ) (G : CompatibleRateGeometry d) :
    ∀ τ : ℝ, 0 < τ → τ < (1/2 : ℝ) → ∀ (t : ℕ → ℝ) (k : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,
        0 ≤ t n ∧ t n ≤ Real.exp (rateLength G.A γ n) ∧
          k n ≤ ⌊Real.exp (rateLength G.A γ n)⌋₊) →
      Tendsto (fun n => continuousBadMassAt β τ n (t n)) atTop (𝓝 1) ∧
      Tendsto (fun n => discreteBadMassAt β τ n (k n)) atTop (𝓝 1) := by
  obtain ⟨c, U, Q, qn, hs, hcov, hqn, herr⟩ := rate_assembly_inputs d G
  simpa only [G.length_eq] using bad_mass_limits_of_static_event_all_horizons
    β hβ G.D c U Q qn hs hcov (G.numerics c hcov.nonneg) hqn herr

theorem subcritical_of_rate_of_numerics {β γ : ℝ} (hβ : 1 < β)
    (d : ConditionalRateData β γ) (G : CompatibleRateGeometry d) :
    ∀ κ : ℝ, 0 < κ → κ < γ/3 → ∀ τ : ℝ, 0 < τ → τ < (1/2 : ℝ) →
      Tendsto (OAI.SK.Strengthened.continuousBadMass β 1 κ τ) atTop (𝓝 1) ∧
      Tendsto (OAI.SK.Strengthened.discreteBadMass β 1 κ τ) atTop (𝓝 1) := by
  intro κ _hκ hκ τ hτ hτ'
  have hpower := SKOptimized.eventually_power_mul_le hκ G.A_pos (B := 1)
  have hhorizon : ∀ᶠ n : ℕ in atTop,
      0 ≤ OAI.SK.Strengthened.timeScale 1 κ n ∧
      OAI.SK.Strengthened.timeScale 1 κ n ≤ Real.exp (rateLength G.A γ n) ∧
      ⌊OAI.SK.Strengthened.timeScale 1 κ n⌋₊ ≤ ⌊Real.exp (rateLength G.A γ n)⌋₊ := by
    filter_upwards [hpower] with n hn
    have he : OAI.SK.Strengthened.timeScale 1 κ n ≤ Real.exp (rateLength G.A γ n) :=
      Real.exp_le_exp.mpr hn
    exact ⟨(Real.exp_pos _).le, he, Nat.floor_le_floor he⟩
  exact barrier_of_rate_all_horizons_of_numerics hβ d G τ hτ hτ'
    (OAI.SK.Strengthened.timeScale 1 κ) (fun n => ⌊OAI.SK.Strengthened.timeScale 1 κ n⌋₊)
    hhorizon

theorem barrier_of_rate {β γ : ℝ} (hβ : 1 < β) (d : ConditionalRateData β γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ τ : ℝ, 0 < τ → τ < (1/2 : ℝ) →
      Tendsto (OAI.SK.Strengthened.continuousBadMass β A (γ/3) τ) atTop (𝓝 1) ∧
      Tendsto (OAI.SK.Strengthened.discreteBadMass β A (γ/3) τ) atTop (𝓝 1) := by
  obtain ⟨G⟩ := exists_compatibleRateGeometry d
  exact barrier_of_rate_of_numerics hβ d G

theorem barrier_of_rate_all_horizons {β γ : ℝ} (hβ : 1 < β) (d : ConditionalRateData β γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ τ : ℝ, 0 < τ → τ < (1/2 : ℝ) →
      ∀ (t : ℕ → ℝ) (k : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,
        0 ≤ t n ∧ t n ≤ Real.exp (rateLength A γ n) ∧
          k n ≤ ⌊Real.exp (rateLength A γ n)⌋₊) →
      Tendsto (fun n => continuousBadMassAt β τ n (t n)) atTop (𝓝 1) ∧
      Tendsto (fun n => discreteBadMassAt β τ n (k n)) atTop (𝓝 1) := by
  obtain ⟨G⟩ := exists_compatibleRateGeometry d
  exact ⟨G.A, G.A_pos, barrier_of_rate_all_horizons_of_numerics hβ d G⟩

theorem subcritical_of_rate {β γ : ℝ} (hβ : 1 < β) (d : ConditionalRateData β γ) :
    ∀ κ : ℝ, 0 < κ → κ < γ/3 → ∀ τ : ℝ, 0 < τ → τ < (1/2 : ℝ) →
      Tendsto (OAI.SK.Strengthened.continuousBadMass β 1 κ τ) atTop (𝓝 1) ∧
      Tendsto (OAI.SK.Strengthened.discreteBadMass β 1 κ τ) atTop (𝓝 1) := by
  obtain ⟨G⟩ := exists_compatibleRateGeometry d
  exact subcritical_of_rate_of_numerics hβ d G

theorem mainStatement_of_rate_data
    (h : ∀ β : ℝ, 1 < β → Nonempty (ConditionalRateData β (2/3))) :
    OAI.SK.Strengthened.MainStatement := by
  intro β hβ
  obtain ⟨d⟩ := h β hβ
  simpa only [show ((2 : ℝ)/3)/3 = (2 : ℝ)/9 by norm_num] using barrier_of_rate hβ d

theorem subcriticalStatement_of_rate_data
    (h : ∀ β : ℝ, 1 < β → Nonempty (ConditionalRateData β (2/3))) :
    OAI.SK.Strengthened.SubcriticalStatement := by
  intro β κ hβ hκ hκ' τ hτ hτ'
  obtain ⟨d⟩ := h β hβ
  have hexp : κ < ((2 : ℝ)/3)/3 := by linarith only [hκ']
  exact subcritical_of_rate hβ d κ hκ hexp τ hτ hτ'

theorem mainStatement_of_compatible_rate_data
    (h : ∀ β : ℝ, 1 < β → ∃ d : ConditionalRateData β (2/3),
      Nonempty (CompatibleRateGeometry d)) : OAI.SK.Strengthened.MainStatement := by
  apply mainStatement_of_rate_data
  intro β hβ
  obtain ⟨d, _⟩ := h β hβ
  exact ⟨d⟩

theorem subcriticalStatement_of_compatible_rate_data
    (h : ∀ β : ℝ, 1 < β → ∃ d : ConditionalRateData β (2/3),
      Nonempty (CompatibleRateGeometry d)) : OAI.SK.Strengthened.SubcriticalStatement := by
  apply subcriticalStatement_of_rate_data
  intro β hβ
  obtain ⟨d, _⟩ := h β hβ
  exact ⟨d⟩

end SKBarriers2
