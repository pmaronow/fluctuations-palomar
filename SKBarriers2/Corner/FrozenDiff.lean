module

public import SKBarriers2.Corner.FrozenRemainder
public import SKBarriers2.Corner.TimeShift

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem exponentialMoment_integralDerivativeControl
    {μ ν : Measure ℝ} {W X : ℝ → ℝ} (hW : Continuous W) (hX : Continuous X)
    (hW₀ : ∀ t, 0 ≤ W t)
    (hweight : ∀ g : ℝ → ℝ, Integrable g ν ↔ Integrable (fun t => W t * g t) μ)
    {ε : ℝ} (hε : ε ∈ interior (integrableExpSet X ν)) (n : ℕ) :
    IntegralDerivativeControl μ
      (fun e t => W t * (X t ^ n * Real.exp (e * X t)))
      (fun e t => W t * (X t ^ (n + 1) * Real.exp (e * X t))) ε := by
  obtain ⟨l, u, hlu, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp hε)
  let ρ : ℝ := min (ε - l) (u - ε) / 2
  have hρ : 0 < ρ := half_pos (lt_min (sub_pos.mpr hlu.1) (sub_pos.mpr hlu.2))
  have hip : Integrable (fun t => Real.exp ((ε + ρ) * X t)) ν :=
    hsub (add_half_inf_sub_mem_Ioo hlu)
  have him : Integrable (fun t => Real.exp ((ε - ρ) * X t)) ν :=
    hsub (sub_half_inf_sub_mem_Ioo hlu)
  have hb : Integrable
      (fun t => |X t| ^ (n + 1) * Real.exp (ε * X t + ρ / 2 * |X t|)) ν :=
    integrable_pow_abs_mul_exp_add_of_integrable_exp_mul hip him
      (by positivity : 0 ≤ ρ / 2) (by rw [abs_of_pos hρ]; linarith) (n + 1)
  refine ⟨Metric.ball ε (ρ / 2), Metric.ball_mem_nhds ε (half_pos hρ),
    (fun t => W t * (|X t| ^ (n + 1) * Real.exp (ε * X t + ρ / 2 * |X t|))),
    Filter.Eventually.of_forall (fun e => ?_), ?_, ?_, (hweight _).mp hb, ?_, ?_⟩
  · exact (hW.mul ((hX.pow n).mul
      (Real.continuous_exp.comp (continuous_const.mul hX)))).aestronglyMeasurable
  · exact (hweight _).mp (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hε n)
  · exact (hW.mul ((hX.pow (n + 1)).mul
      (Real.continuous_exp.comp (continuous_const.mul hX)))).aestronglyMeasurable
  · refine ae_of_all μ (fun t e he => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (hW₀ t),
      abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (hW₀ t)
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) _)
    apply Real.exp_le_exp.mpr
    have he' : |e - ε| < ρ / 2 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using he
    calc
      e * X t = ε * X t + (e - ε) * X t := by ring
      _ ≤ ε * X t + |(e - ε) * X t| := add_le_add (le_refl _) (le_abs_self _)
      _ = ε * X t + |e - ε| * |X t| := by rw [abs_mul]
      _ ≤ _ := add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right he'.le (abs_nonneg _))
  · refine ae_of_all μ (fun t e _ => ?_)
    have hd : HasDerivAt (fun a : ℝ => Real.exp (a * X t))
        (Real.exp (e * X t) * X t) e :=
      by simpa only [id_eq, one_mul] using ((hasDerivAt_id e).mul_const (X t)).exp
    convert (hd.const_mul (X t ^ n)).const_mul (W t) using 1
    ring

namespace QuadraticTerminal

theorem integrable_weighted_iff (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (hD : 0 < Q.precision m v) (g : ℝ → ℝ) :
    Integrable g (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) ↔
      Integrable (fun t => Real.exp (m * Q.value (x + t • v)) * g t)
        (gaussianReal 0 1) := by
  rw [integrable_quadraticGaussian_iff hD]
  have he (t : ℝ) :
      Real.exp (m * Q.value (x + t • v)) * g t =
        Real.exp (m * Q.value x) *
          (Real.exp ((1 - Q.precision m v) * t ^ 2 / 2 +
            (m * Q.slope v x) * t) * g t) := by
    rw [Q.value_shift, ← mul_assoc, ← Real.exp_add]
    congr 2
    unfold precision
    ring
  simp_rw [he]
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)) _).symm

theorem exponential_integrand_control (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    {K : Vec3 → ℝ} (hK : Continuous K) (hD : 0 < Q.precision m v)
    {ε : ℝ} (hε : ε ∈ interior (integrableExpSet (fun t => m * K (x + t • v))
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)))) (n : ℕ) :
    IntegralDerivativeControl (gaussianReal 0 1)
      (fun e t => Real.exp (m * Q.value (x + t • v)) *
        ((m * K (x + t • v)) ^ n * Real.exp (e * (m * K (x + t • v)))))
      (fun e t => Real.exp (m * Q.value (x + t • v)) *
        ((m * K (x + t • v)) ^ (n + 1) * Real.exp (e * (m * K (x + t • v))))) ε := by
  apply exponentialMoment_integralDerivativeControl (by unfold value; fun_prop)
    (by fun_prop) (fun t => (Real.exp_pos _).le)
    (fun g => Q.integrable_weighted_iff m v x hD g) hε n

end QuadraticTerminal

private theorem epsilonChain_nil_deriv (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (x : Vec3) : deriv (fun e => epsilonChain [] Q K e x) = fun _ => K x := by
  funext ε
  simpa only [epsilonChain, vectorIncrementChain, id_eq, one_mul] using
    (((hasDerivAt_id ε).mul_const (K x)).const_add (Q.value x)).deriv

private theorem epsilonChain_nil_second (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (x : Vec3) (ε : ℝ) : iteratedDeriv 2 (fun e => epsilonChain [] Q K e x) ε = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, epsilonChain_nil_deriv]
  exact deriv_const ε (K x)

theorem epsilonChainControl_singleton (Q : QuadraticTerminal) (u : ℝ × Vec3)
    {K : Vec3 → ℝ} (hK : Continuous K) (hD : 0 < Q.precision u.1 u.2)
    (hX : ∀ x : Vec3, 0 ∈ interior (integrableExpSet
      (fun t => u.1 * K (x + t • u.2))
      (quadraticGaussian (Q.precision u.1 u.2) (u.1 * Q.slope u.2 x)))) :
    EpsilonChainControl [u] Q K := by
  refine ⟨True.intro, ?_⟩
  intro x
  let F : ℕ → ℝ → ℝ → ℝ := fun n e t =>
    Real.exp (u.1 * Q.value (x + t • u.2)) *
      ((u.1 * K (x + t • u.2)) ^ n * Real.exp (e * (u.1 * K (x + t • u.2))))
  have he₀ : epsilonWeight [] Q K u x = F 0 := by
    funext e t
    simp only [epsilonWeight, epsilonChain, vectorIncrementChain, F, pow_zero, one_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  have he₁ : epsilonWeightFirst [] Q K u x = F 1 := by
    funext e t
    simp only [epsilonWeightFirst, epsilonChain_nil_deriv, he₀, F, pow_zero, pow_one, one_mul]
    ring
  have he₂ : epsilonWeightSecond [] Q K u x = F 2 := by
    funext e t
    simp only [epsilonWeightSecond, epsilonChain_nil_second, epsilonChain_nil_deriv,
      he₀, F, zero_add, pow_zero, one_mul]
    ring
  have hnear : ∀ᶠ e in 𝓝 (0 : ℝ), e ∈ interior (integrableExpSet
      (fun t => u.1 * K (x + t • u.2))
      (quadraticGaussian (Q.precision u.1 u.2) (u.1 * Q.slope u.2 x))) :=
    isOpen_interior.mem_nhds (hX x)
  constructor
  · filter_upwards [hnear] with e he
    rw [he₀, he₁]
    exact Q.exponential_integrand_control u.1 u.2 x hK hD he 0
  · rw [he₁, he₂]
    exact Q.exponential_integrand_control u.1 u.2 x hK hD (hX x) 1

theorem quadraticGrowth_mem_interior_at {D C ε : ℝ} (hD : 0 < D) (hC : 0 ≤ C)
    (L A : ℝ) {K : ℝ → ℝ} (hK : Continuous K)
    (hgrowth : ∀ t, |K t| ≤ A + C * t ^ 2) (hε : 2 * |ε| * C < D) :
    ε ∈ interior (integrableExpSet K (quadraticGaussian D L)) := by
  have hc : Continuous (fun e : ℝ => 2 * |e| * C) := by fun_prop
  have hn : ∀ᶠ e in 𝓝 ε, 2 * |e| * C < D := hc.continuousAt.eventually_lt_const hε
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hn] with e he
  exact integrable_exp_quadraticGrowth hD hC L A e hK hgrowth he

theorem terminalResidual_singleton_chainControl
    (β : ℝ) (α : ℝ → ℝ) (s h z B : ℝ) (u : ℝ × Vec3)
    (hB : 0 ≤ B) (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B)
    (hD : 0 < (terminalTaylorQuadratic β α s h z).precision u.1 u.2) :
    EpsilonChainControl [u] (terminalTaylorQuadratic β α s h z)
      (terminalResidual β α s h z) := by
  apply epsilonChainControl_singleton _ u (terminalResidual_continuous β α s h z hΦ) hD
  intro x
  apply quadraticGrowth_mem_interior
    (K := fun t => u.1 * terminalResidual β α s h z (x + t • u.2))
    (C := |u.1| * (4 * B * squaredLength u.2)) hD
    (mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (squaredLength_nonneg _)))
    (u.1 * (terminalTaylorQuadratic β α s h z).slope u.2 x)
    (|u.1| * (6 * B + 4 * B * ∑ i, (x i - z) ^ 2))
    (continuous_const.mul ((terminalResidual_continuous β α s h z hΦ).comp (by fun_prop)))
  intro t
  rw [abs_mul]
  have H := mul_le_mul_of_nonneg_left
    (terminalResidual_growth β α s h z B hB hΦ h₁ h₂ x u.2 t) (abs_nonneg u.1)
  calc
    _ ≤ |u.1| * ((6 * B + 4 * B * ∑ i, (x i - z) ^ 2) +
        (4 * B * squaredLength u.2) * t ^ 2) := H
    _ = _ := by ring

theorem scalarData_terminalResidual_singleton_chainControl
    {β : ℝ} (D : ScalarData β) (s h z : ℝ) (u : ℝ × Vec3)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1)
    (hD : 0 < (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z).precision u.1 u.2) :
    EpsilonChainControl [u] (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
      (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) := by
  exact terminalResidual_singleton_chainControl β _ s h z (scalarTerminalJetBound D 2) u
    (scalarTerminalJetBound_nonneg D 2) (scalarData_phi_regular D ht)
    (scalarData_jet_le D (by norm_num) (by norm_num) ht)
    (scalarData_jet_le D (by norm_num) (by norm_num) ht z) hD

theorem quadraticPerturbation_analyticAt {m H ε : ℝ} (hm : m ≠ 0)
    (hD : 0 < 1 - m * H) (C L : ℝ) (K : ℝ → ℝ)
    (hK : m * ε ∈ interior (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L)))) :
    AnalyticAt ℝ (quadraticPerturbation m C L H K) ε := by
  have ha : AnalyticAt ℝ
      (fun t => C - Real.log (1 - m * H) / (2 * m) + m * L ^ 2 / (2 * (1 - m * H)) +
        cgf K (quadraticGaussian (1 - m * H) (m * L)) (m * t) / m) ε :=
    analyticAt_const.add (((analyticAt_cgf hK).comp
      (analyticAt_const.mul analyticAt_id)).div_const)
  exact ha.congr (quadraticPerturbation_eventuallyEq_cgf hm hD C L K hK).symm

theorem quadraticPerturbation_epsilon_regular {m H ε : ℝ} (hm : m ≠ 0)
    (hD : 0 < 1 - m * H) (C L : ℝ) (K : ℝ → ℝ)
    (hK : m * ε ∈ interior (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L)))) :
    HasDerivAt (quadraticPerturbation m C L H K)
        (deriv (quadraticPerturbation m C L H K) ε) ε ∧
      HasDerivAt (deriv (quadraticPerturbation m C L H K))
        (iteratedDeriv 2 (quadraticPerturbation m C L H K) ε) ε ∧
      HasDerivAt (iteratedDeriv 2 (quadraticPerturbation m C L H K))
        (iteratedDeriv 3 (quadraticPerturbation m C L H K) ε) ε := by
  have ha := quadraticPerturbation_analyticAt hm hD C L K hK
  refine ⟨ha.differentiableAt.hasDerivAt, ?_, ?_⟩
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      ha.deriv.differentiableAt.hasDerivAt
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      ha.deriv.deriv.differentiableAt.hasDerivAt

theorem terminalResidual_interior_at (β : ℝ) (α : ℝ → ℝ) (s h z B m : ℝ)
    (v x : Vec3) (hB : 0 ≤ B) (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B)
    (hm : |m| ≤ 1) (hsmall : 32 * B * squaredLength v ≤ 1)
    (hD : 1 / 2 ≤ (terminalTaylorQuadratic β α s h z).precision m v)
    {ε : ℝ} (hε : |ε| ≤ 1) :
    m * ε ∈ interior (integrableExpSet (fun t => terminalResidual β α s h z (x + t • v))
      (quadraticGaussian ((terminalTaylorQuadratic β α s h z).precision m v)
        (m * (terminalTaylorQuadratic β α s h z).slope v x))) := by
  have hC : 0 ≤ 4 * B * squaredLength v :=
    mul_nonneg (by positivity) (squaredLength_nonneg _)
  have hmε : |m * ε| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hm hε (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  apply quadraticGrowth_mem_interior_at (by linarith) hC _
    (6 * B + 4 * B * ∑ i, (x i - z) ^ 2)
    ((terminalResidual_continuous β α s h z hΦ).comp (by fun_prop))
    (terminalResidual_growth β α s h z B hB hΦ h₁ h₂ x v)
  have H := mul_le_mul_of_nonneg_right hmε hC
  nlinarith

theorem terminalResidual_singleton_epsilon_regular
    (β : ℝ) (α : ℝ → ℝ) (s h z B m : ℝ) (v x : Vec3)
    (hB : 0 ≤ B) (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B)
    (hm₀ : m ≠ 0) (hm : |m| ≤ 1) (hsmall : 32 * B * squaredLength v ≤ 1)
    (hD : 1 / 2 ≤ (terminalTaylorQuadratic β α s h z).precision m v)
    {ε : ℝ} (hε : |ε| ≤ 1) :
    let θ := fun e => epsilonChain [(m, v)] (terminalTaylorQuadratic β α s h z)
      (terminalResidual β α s h z) e x
    HasDerivAt θ (deriv θ ε) ε ∧
      HasDerivAt (deriv θ) (iteratedDeriv 2 θ ε) ε ∧
      HasDerivAt (iteratedDeriv 2 θ) (iteratedDeriv 3 θ ε) ε := by
  have hmoment := terminalResidual_interior_at β α s h z B m v x hB hΦ h₁ h₂ hm hsmall hD hε
  have he : (fun e => epsilonChain [(m, v)] (terminalTaylorQuadratic β α s h z)
      (terminalResidual β α s h z) e x) =
      quadraticPerturbation m ((terminalTaylorQuadratic β α s h z).value x)
        ((terminalTaylorQuadratic β α s h z).slope v x)
        ((terminalTaylorQuadratic β α s h z).curvature v)
        (fun t => terminalResidual β α s h z (x + t • v)) := by
    funext e
    exact (terminalTaylorQuadratic β α s h z).vectorStep_perturbation m v x _ e
  dsimp only
  rw [he]
  exact quadraticPerturbation_epsilon_regular hm₀ (by linarith :
    0 < (terminalTaylorQuadratic β α s h z).precision m v) _ _ _ hmoment

theorem iteratedDeriv_three_cgf_zero {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {X : ℝ → ℝ} (hX : 0 ∈ interior (integrableExpSet X ν)) :
    iteratedDeriv 3 (cgf X ν) 0 = (∫ t, X t ^ 3 ∂ν) -
      3 * (∫ t, X t ^ 2 ∂ν) * (∫ t, X t ∂ν) + 2 * (∫ t, X t ∂ν) ^ 3 := by
  have hn : ∀ᶠ e in 𝓝 (0 : ℝ), e ∈ interior (integrableExpSet X ν) :=
    isOpen_interior.mem_nhds hX
  have he : iteratedDeriv 2 (cgf X ν) =ᶠ[𝓝 (0 : ℝ)]
      (fun e => (∫ t, X t ^ 2 * Real.exp (e * X t) ∂ν) / mgf X ν e -
        deriv (cgf X ν) e ^ 2) := by
    filter_upwards [hn] with e he
    exact iteratedDeriv_two_cgf he
  have hd₀ : deriv (cgf X ν) 0 = ∫ t, X t ∂ν := by
    simpa only [probReal_univ, div_one] using deriv_cgf_zero hX
  have hd₁ : deriv (deriv (cgf X ν)) 0 =
      (∫ t, X t ^ 2 ∂ν) - (∫ t, X t ∂ν) ^ 2 := by
    have H := iteratedDeriv_two_cgf hX
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero,
      zero_mul, Real.exp_zero, mul_one, mgf_zero, probReal_univ, div_one, hd₀] using H
  have hd := ((hasDerivAt_integral_pow_mul_exp_real hX 2).div (hasDerivAt_mgf hX)
    (by simp : mgf X ν 0 ≠ 0)).sub
      (((analyticAt_cgf hX).deriv.differentiableAt.hasDerivAt).pow 2)
  have H := (hd.congr_of_eventuallyEq he).deriv
  rw [← iteratedDeriv_succ] at H
  simp only [zero_mul, Real.exp_zero, mul_one, mgf_zero, Nat.cast_ofNat, hd₀, hd₁] at H
  rw [H]
  ring

theorem quadraticPerturbation_third_zero {m H : ℝ} (hm : m ≠ 0)
    (hD : 0 < 1 - m * H) (C L : ℝ) (K : ℝ → ℝ)
    (hK : 0 ∈ interior (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L)))) :
    iteratedDeriv 3 (quadraticPerturbation m C L H K) 0 =
      m ^ 2 * ((∫ t, K t ^ 3 ∂quadraticGaussian (1 - m * H) (m * L)) -
        3 * (∫ t, K t ^ 2 ∂quadraticGaussian (1 - m * H) (m * L)) *
          (∫ t, K t ∂quadraticGaussian (1 - m * H) (m * L)) +
        2 * (∫ t, K t ∂quadraticGaussian (1 - m * H) (m * L)) ^ 3) := by
  let ν := quadraticGaussian (1 - m * H) (m * L)
  let : IsProbabilityMeasure ν := by unfold ν quadraticGaussian; infer_instance
  let Y : ℝ → ℝ := fun t => m * K t
  have hnear : ∀ᶠ e in 𝓝 (0 : ℝ), m * e ∈ interior (integrableExpSet K ν) := by
    have hzero : m * 0 ∈ interior (integrableExpSet K ν) := by simpa only [mul_zero] using hK
    exact (continuous_const.mul continuous_id).continuousAt.eventually
      (isOpen_interior.mem_nhds hzero)
  have hY : 0 ∈ interior (integrableExpSet Y ν) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hnear] with e he
    have hi := interior_subset he
    change Integrable (fun t => Real.exp ((m * e) * K t)) ν at hi
    change Integrable (fun t => Real.exp (e * (m * K t))) ν
    convert hi using 1
    ext t
    congr 1
    ring
  have he : quadraticPerturbation m C L H K =ᶠ[𝓝 (0 : ℝ)]
      (fun e => C - Real.log (1 - m * H) / (2 * m) + m * L ^ 2 / (2 * (1 - m * H)) +
        cgf Y ν e / m) := by
    filter_upwards [hnear] with e he
    rw [quadraticPerturbation_eq_cgf hm hD C L e K (interior_subset he)]
    congr 2
    exact (congrArg Real.log (mgf_const_mul (X := K) (μ := ν) (t := e) m)).symm
  have hderiv := (he.iteratedDeriv 3).self_of_nhds
  rw [hderiv, iteratedDeriv_const_add (by norm_num : 0 < 3)]
  have hdiv : (fun e => cgf Y ν e / m) = fun e => m⁻¹ * cgf Y ν e := by
    funext e
    ring
  rw [hdiv, iteratedDeriv_const_mul_field, iteratedDeriv_three_cgf_zero hY]
  simp only [Y, mul_pow, integral_const_mul]
  field_simp
  ring

theorem QuadraticTerminal.vectorStep_perturbation_third
    (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) (K : Vec3 → ℝ)
    (hm : m ≠ 0) (hD : 0 < Q.precision m v)
    (hK : 0 ∈ interior (integrableExpSet (fun t => K (x + t • v))
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)))) :
    iteratedDeriv 3 (fun ε => vectorStep m v (fun y => Q.value y + ε * K y) x) 0 =
      m ^ 2 * ((∫ t, K (x + t • v) ^ 3 ∂quadraticGaussian (Q.precision m v) (m * Q.slope v x)) -
        3 * (∫ t, K (x + t • v) ^ 2 ∂quadraticGaussian (Q.precision m v) (m * Q.slope v x)) *
          (∫ t, K (x + t • v) ∂quadraticGaussian (Q.precision m v) (m * Q.slope v x)) +
        2 * (∫ t, K (x + t • v) ∂quadraticGaussian (Q.precision m v) (m * Q.slope v x)) ^ 3) := by
  simpa only [Q.vectorStep_perturbation, QuadraticTerminal.precision] using
    quadraticPerturbation_third_zero hm hD (Q.value x) (Q.slope v x)
      (fun t => K (x + t • v)) hK

theorem scalarData_cdf_pos_of_pos {β : ℝ} (D : ScalarData β) {s : ℝ} (hs : 0 < s) :
    0 < cdf (D.μ : Measure ℝ) s := by
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  have ht : 0 < min s T := lt_min hs hT
  exact (mul_pos hc ht).trans_le ((hlin _ ⟨ht.le, min_le_right _ _⟩).trans
    (monotone_cdf (D.μ : Measure ℝ) (min_le_left _ _)))

theorem scalarData_frozen_singleton_controls {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ w ∈ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k,
        EpsilonChainControl [w]
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
          (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) ∧
        ∀ (x : Vec3) (ε : ℝ), |ε| ≤ 1 →
          let θ := fun e => epsilonChain [w]
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e x
          HasDerivAt θ (deriv θ ε) ε ∧
            HasDerivAt (deriv θ) (iteratedDeriv 2 θ ε) ε ∧
            HasDerivAt (iteratedDeriv 2 θ) (iteratedDeriv 3 θ ε) ε := by
  let B : ℝ := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  let R : ℝ := 72 * (2 ^ 12 * B) * (β ^ 2 + 1)
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨min (l / 2) (min ((D.q - u) / 6) R⁻¹),
    lt_min (by positivity) (lt_min (by positivity) (inv_pos.mpr hR)), ?_⟩
  intro r hr h hh hh₀ k hk z w hw
  have hhl : h ≤ l / 2 := hh₀.trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhR : h ≤ R⁻¹ := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  have hm := frozenSchedule_masses β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩ w hw
  have hsmall : 72 * (2 ^ 12 * B) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ R * h := by dsimp only [R]; nlinarith
      _ ≤ R * R⁻¹ := mul_le_mul_of_nonneg_left hhR hR.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hR)
  have hnoise : squaredLength w.2 ≤ 12 * β ^ 2 * h := by
    calc
      _ ≤ chainEnergy (frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k) :=
        squaredLength_le_chainEnergy hw
      _ = _ := frozenSchedule_chainEnergy _ _ _ _ hh.le hk
  have hnoiseB := mul_le_mul_of_nonneg_left hnoise hB.le
  have hsmall₁ : 32 * B * squaredLength w.2 ≤ 1 := by
    norm_num at hsmall
    nlinarith [mul_nonneg hB.le (squaredLength_nonneg w.2)]
  have hsmall₂ : 2 * B * directionEnergy w.2 ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (directionEnergy_le_squaredLength w.2)
      (show 0 ≤ 2 * B by positivity)
    nlinarith [mul_nonneg hB.le (squaredLength_nonneg w.2)]
  have h₁ : ∀ y, |jet β (cdf (D.μ : Measure ℝ)) 1 ((r - h) + 4 * h) y| ≤ B := by
    intro y
    exact (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) ht y).trans
      (by dsimp only [B]; linarith)
  have h₂ : |jet β (cdf (D.μ : Measure ℝ)) 2 ((r - h) + 4 * h) z| ≤ B :=
    (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) ht z).trans
      (by dsimp only [B]; linarith)
  have hD := (QuadraticTerminal.update_small hB
    (terminalTaylorQuadratic_hessian_bound β _ (r - h) h z B hB.le h₂)
    ⟨hm.1.le, hm.2⟩ w.2 hsmall₂).1
  refine ⟨scalarData_terminalResidual_singleton_chainControl D (r - h) h z w ht
    (by linarith), ?_⟩
  intro x ε hε
  exact terminalResidual_singleton_epsilon_regular β _ (r - h) h z B w.1 w.2 x hB.le
    (scalarData_phi_regular D ht) h₁ h₂ (ne_of_gt hm.1)
    (by rw [abs_of_pos hm.1]; exact hm.2) hsmall₁ hD hε

end SKBarriers2.Corner
