module

public import SKBarriers2.Corner.FrozenRowsAssembly

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

private theorem wJets_apply_const
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {r p : ℕ} {B : ℝ} {f : E → F →L[ℝ] G}
    (hf : WJets r B p f) (w : F) :
    WJets r (B * ‖w‖) p (fun x => f x w) := by
  refine ⟨mul_nonneg hf.nonneg (norm_nonneg w), hf.smooth.clm_apply contDiff_const, ?_⟩
  intro j hj x
  calc
    _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ j f x‖ :=
      norm_iteratedFDeriv_clm_apply_const hf.smooth.contDiffAt (by exact_mod_cast hj)
    _ ≤ ‖w‖ * (B * (1 + ‖x‖) ^ p) :=
      mul_le_mul_of_nonneg_left (hf.bound j hj x) (norm_nonneg w)
    _ = _ := by ring

private theorem wJets_zero {r p : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    WJets r B p (fun _ : Vec3 => (0 : ℝ)) := by
  refine ⟨hB, contDiff_const, ?_⟩
  intro j hj x
  by_cases hj0 : j = 0
  · subst j
    simp only [norm_iteratedFDeriv_zero, norm_zero]
    positivity
  · rw [iteratedFDeriv_const_of_ne hj0]
    simp only [Pi.zero_apply, norm_zero]
    positivity

private theorem translated_derivatives {f : Vec3 → ℝ}
    (hf : ContDiff ℝ 2 f) {b b₁ b₂ : ℝ → Vec3} {U : Set ℝ}
    (hU : IsOpen U)
    (hb : ∀ k ∈ U, HasDerivAt b (b₁ k) k)
    (hb₁ : ∀ k ∈ U, HasDerivAt b₁ (b₂ k) k)
    {k : ℝ} (hk : k ∈ U) (y : Vec3) :
    deriv (fun t => f (y + b t)) k = fderiv ℝ f (y + b k) (b₁ k) ∧
      deriv (deriv (fun t => f (y + b t))) k =
        fderiv ℝ (fderiv ℝ f) (y + b k) (b₁ k) (b₁ k) +
          fderiv ℝ f (y + b k) (b₂ k) := by
  have hfirst (t : ℝ) (ht : t ∈ U) :
      HasDerivAt (fun q => f (y + b q)) (fderiv ℝ f (y + b t) (b₁ t)) t :=
    (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
      (by convert (hasDerivAt_const t y).add (hb t ht) using 1; simp only [zero_add])
  refine ⟨(hfirst k hk).deriv, ?_⟩
  have hc : HasDerivAt (fun t => y + b t) (b₁ k) k := by
    convert (hasDerivAt_const k y).add (hb k hk) using 1; simp only [zero_add]
  have hd : HasDerivAt (fun t => fderiv ℝ f (y + b t))
      (fderiv ℝ (fderiv ℝ f) (y + b k) (b₁ k)) k :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (y + b k)).hasFDerivAt.comp_hasDerivAt k hc
  have HD := hd.clm_apply (hb₁ k hk)
  have he : (fun t => fderiv ℝ f (y + b t) (b₁ t)) =ᶠ[𝓝 k]
      deriv (fun t => f (y + b t)) := by
    filter_upwards [hU.mem_nhds hk] with t ht
    exact (hfirst t ht).deriv.symm
  exact (HD.congr_of_eventuallyEq he.symm).deriv

theorem translated_mixed_wJets {r p : ℕ} {B ρ K : ℝ} {f : Vec3 → ℝ}
    (hf : WJets (r + 2) B p f) (hρ : |ρ| ≤ 1) (hK : 1 ≤ K)
    {b b₁ b₂ : ℝ → Vec3} {U : Set ℝ} (hU : IsOpen U)
    (hb : ∀ k ∈ U, HasDerivAt b (b₁ k) k)
    (hb₁ : ∀ k ∈ U, HasDerivAt b₁ (b₂ k) k)
    {k : ℝ} (hk : k ∈ U)
    (h₁ : ‖b₁ k‖ ≤ K) (h₂ : ‖b₂ k‖ ≤ K) :
    let C := 2 * B * K ^ 2 * (1 + ‖b k‖) ^ p
    WJets r C p (fun y => f (y + b k)) ∧
      WJets r C p (fun y => ρ * deriv (fun t => f (y + b t)) k) ∧
      WJets r C p (fun y => ρ ^ 2 * deriv (deriv (fun t => f (y + b t))) k) := by
  have hB := hf.nonneg
  have hK₀ : 0 ≤ K := by linarith
  have hweight : 0 ≤ (1 + ‖b k‖) ^ p := by positivity
  have HD := hf.derivativeJets
  have HD₂ := HD.derivativeJets
  have H₀ := (hf.of_le (by omega : r ≤ r + 2)).translate (b k)
  have H₁ := (wJets_apply_const (HD.of_le (by omega : r ≤ r + 1)) (b₁ k)).translate (b k)
  have H₂ := ((wJets_apply_const (wJets_apply_const HD₂ (b₁ k)) (b₁ k)).add
    (wJets_apply_const (HD.of_le (by omega : r ≤ r + 1)) (b₂ k))).translate (b k)
  have he₁ : (fun y => deriv (fun t => f (y + b t)) k) =
      fun y => fderiv ℝ f (y + b k) (b₁ k) :=
    funext (fun y => (translated_derivatives (hf.smooth.of_le (by simp)) hU hb hb₁ hk y).1)
  have he₂ : (fun y => deriv (deriv (fun t => f (y + b t))) k) =
      fun y => fderiv ℝ (fderiv ℝ f) (y + b k) (b₁ k) (b₁ k) +
        fderiv ℝ f (y + b k) (b₂ k) :=
    funext (fun y => (translated_derivatives (hf.smooth.of_le (by simp)) hU hb hb₁ hk y).2)
  dsimp only
  refine ⟨H₀.mono ?_ le_rfl, ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hweight
    calc
      B ≤ B * (2 * K ^ 2) := le_mul_of_one_le_right hB (by nlinarith)
      _ = _ := by ring
  · change WJets r _ p (fun y => ρ • ((fun y => deriv (fun t => f (y + b t)) k) y))
    rw [he₁]
    apply (H₁.const_smul ρ).mono _ le_rfl
    change |ρ| * (B * ‖b₁ k‖ * (1 + ‖b k‖) ^ p) ≤ _
    calc
      _ ≤ 1 * (B * K * (1 + ‖b k‖) ^ p) := by gcongr
      _ = (B * (1 + ‖b k‖) ^ p) * K := by ring
      _ ≤ (B * (1 + ‖b k‖) ^ p) * (2 * K ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith : K ≤ 2 * K ^ 2) (mul_nonneg hB hweight)
      _ = _ := by ring
  · change WJets r _ p (fun y => ρ ^ 2 • ((fun y => deriv (deriv (fun t => f (y + b t))) k) y))
    rw [he₂]
    apply (H₂.const_smul (ρ ^ 2)).mono _ le_rfl
    change |ρ ^ 2| * ((B * ‖b₁ k‖ * ‖b₁ k‖ + B * ‖b₂ k‖) * (1 + ‖b k‖) ^ p) ≤ _
    have hρ₂ : |ρ ^ 2| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hρ
    calc
      _ ≤ 1 * ((B * K * K + B * K) * (1 + ‖b k‖) ^ p) := by gcongr
      _ = (B * (1 + ‖b k‖) ^ p) * (K ^ 2 + K) := by ring
      _ ≤ (B * (1 + ‖b k‖) ^ p) * (2 * K ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith : K ^ 2 + K ≤ 2 * K ^ 2)
          (mul_nonneg hB hweight)
      _ = _ := by ring

private def terminalHeadDirection (β k : ℝ) : Vec3 :=
  (β * Real.sqrt (2 - OW.repairLength (1 / 2) k)) • Pi.single 2 1

private theorem terminalHeadDirection_contDiffOn (β : ℝ) :
    ContDiffOn ℝ ∞ (terminalHeadDirection β) (Ioo (-(1 / 2) : ℝ) (1 / 2)) := by
  intro k hk
  have hsq : k ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    have H : |k| < 1 / 2 := abs_lt.mpr hk
    nlinarith [sq_abs k, mul_pos (sub_pos.mpr H) (by positivity : 0 < 1 / 2 + |k|)]
  have hr : 0 < 2 - OW.repairLength (1 / 2) k := by
    norm_num [OW.repairLength, varianceCoefficient, tentWeight, rampWeight]
    nlinarith
  have hpoly : ContDiffAt ℝ ∞ (fun k => 2 - OW.repairLength (1 / 2) k) k := by
    unfold OW.repairLength
    fun_prop
  exact ((contDiffAt_const.mul (hpoly.sqrt hr.ne')).smul contDiffAt_const).contDiffWithinAt

private theorem terminalHeadDirection_uniform (β : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k ∈ frozenRowsKDomain,
      ‖terminalHeadDirection β k‖ ≤ K ∧
        ‖deriv (terminalHeadDirection β) k‖ ≤ K ∧
        ‖deriv (deriv (terminalHeadDirection β)) k‖ ≤ K := by
  let U : Set ℝ := Ioo (-(1 / 2) : ℝ) (1 / 2)
  let S : Set ℝ := Icc (-(1 / 3) : ℝ) (1 / 3)
  have hSU : S ⊆ U := fun k hk => ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hv := terminalHeadDirection_contDiffOn β
  have hv₁ := hv.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)
  have hv₂ := hv₁.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
    (hv.continuousOn.mono hSU)
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
    (hv₁.continuousOn.mono hSU)
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
    (hv₂.continuousOn.mono hSU)
  refine ⟨1 + |B₀| + |B₁| + |B₂|,
    by linarith [abs_nonneg B₀, abs_nonneg B₁, abs_nonneg B₂], ?_⟩
  intro k hk
  have hkS : k ∈ S := ⟨hk.1.le, hk.2.le⟩
  exact ⟨(hB₀ k hkS).trans (by linarith [le_abs_self B₀, abs_nonneg B₁, abs_nonneg B₂]),
    (hB₁ k hkS).trans (by linarith [le_abs_self B₁, abs_nonneg B₀, abs_nonneg B₂]),
    (hB₂ k hkS).trans (by linarith [le_abs_self B₂, abs_nonneg B₀, abs_nonneg B₁])⟩

private theorem frozenRows_terminal_head (β a h k g : ℝ) (hh : 0 < h) :
    (Real.sqrt h)⁻¹ • (g • (frozenRowsHead β a h 11 k).2) =
      g • terminalHeadDirection β k := by
  have hρ : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  simp only [frozenRowsHead, frozenSchedule, frozenCommon, frozenShared, frozenInner,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    terminalHeadDirection, Real.sqrt_mul hh.le, smul_smul]
  congr 1
  field_simp

private theorem normalizedVariationChain_nil_jet
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) (ρ ε : ℝ) (c y : Vec3) (i : Fin 3) :
    iteratedDeriv (i.val + 1)
      (fun e => normalizedVariationChain [] Q.value K ρ c e y) ε =
        if i = 0 then (ρ ^ 3)⁻¹ * K (ρ • y + c) else 0 := by
  let A := Q.value (ρ • y + c)
  let B := (ρ ^ 3)⁻¹ * K (ρ • y + c)
  have he : (fun e => normalizedVariationChain [] Q.value K ρ c e y) =
      fun e => A + e * B := rfl
  have hd : deriv (fun e => A + e * B) = fun _ => B := by
    funext e
    convert ((hasDerivAt_const e A).add ((hasDerivAt_id e).mul_const B)).deriv using 1 <;> simp
  have hdB : deriv (fun _ : ℝ => B) = fun _ => 0 := funext (fun e => deriv_const e B)
  have hd0 : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := funext (fun e => deriv_const e 0)
  rw [he]
  fin_cases i <;>
    norm_num [iteratedDeriv_succ, iteratedDeriv_zero, hd, hdB, hd0, B]

private theorem frozenRowsNormalizedJet_terminal
    (β a s h z ε k g : ℝ) (α : ℝ → ℝ) (hh : 0 < h) (i : Fin 3) (y : Vec3) :
    frozenRowsNormalizedJet β α a s h z ε 11 i y k g =
      if i = 0 then
        let f := fun t => scaledTerminalResidual β α s h z (Real.sqrt h)
          (y + g • terminalHeadDirection β t)
        ⟨f k, deriv f k, deriv (deriv f) k⟩
      else MomentKJet.const 0 := by
  have hd (t : ℝ) : (frozenSchedule β a (1 / 2) h t).drop (11 + 1) = [] := by
    rw [show 11 + 1 = 12 from rfl, ← frozenSchedule_length β a (1 / 2) h t,
      List.drop_length]
  unfold frozenRowsNormalizedJet normalizedEpsilonKJet
  simp only [hd]
  simp_rw [normalizedVariationChain_nil_jet, frozenRows_terminal_head β a h _ g hh]
  by_cases hi : i = 0
  · simp only [ite_eq_left hi, scaledTerminalResidual, iteratedDeriv_succ, iteratedDeriv_zero]
  · simp only [ite_eq_right hi, iteratedDeriv_fun_const_zero, MomentKJet.const]

theorem scalarData_frozenRowsMixed_seed {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ M₀ : ℝ, 0 < h₀ ∧ 1 ≤ M₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
        ∀ k ∈ frozenRowsKDomain,
          FrozenRowsMixedEnvelope β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε 11 M₀ k := by
  obtain ⟨K, hK, HK⟩ := terminalHeadDirection_uniform β
  let B := terminalJetBound D 24
  let M₀ := 1 + 16 * B * K ^ 5
  let h₀ := min 1 ((D.q - u) / 6)
  have hB : 0 ≤ B := terminalJetBound_nonneg D 24
  have hK₀ : 0 ≤ K := by linarith
  have hM₀ : 1 ≤ M₀ := by
    dsimp only [M₀]
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hB) (pow_nonneg hK₀ 5)]
  refine ⟨h₀, M₀, lt_min (by norm_num) (by positivity), hM₀, ?_⟩
  intro r hr h hh hhsmall z ε _hε k hk g i
  have hh₁ : h ≤ 1 := hhsmall.trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 := hhsmall.trans (min_le_right _ _)
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hr.1], by linarith [hr.2, D.q_mem.2]⟩
  let ρ := Real.sqrt h
  let R := K * (1 + |g|)
  have hρ : ρ ∈ Ioc (0 : ℝ) 1 := ⟨Real.sqrt_pos.mpr hh, Real.sqrt_le_one.mpr hh₁⟩
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le hK (by linarith [abs_nonneg g])
  have hR₀ : 0 ≤ R := by linarith
  let b := fun t => g • terminalHeadDirection β t
  let b₁ := fun t => g • deriv (terminalHeadDirection β) t
  let b₂ := fun t => g • deriv (deriv (terminalHeadDirection β)) t
  have hv := terminalHeadDirection_contDiffOn β
  have hv₁ := hv.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)
  have hb (t : ℝ) (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) : HasDerivAt b (b₁ t) t :=
    ((hv.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt.const_smul g
  have hb₁ (t : ℝ) (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) : HasDerivAt b₁ (b₂ t) t :=
    ((hv₁.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt.const_smul g
  have hk' : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) :=
    ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hnorm {v : Vec3} (hv : ‖v‖ ≤ K) : ‖g • v‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |g| * K := mul_le_mul_of_nonneg_left hv (abs_nonneg g)
      _ ≤ R := by dsimp only [R]; nlinarith
  have hshift : 1 + ‖b k‖ ≤ R := by
    dsimp only [b]
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ 1 + |g| * K := add_le_add_right
        (mul_le_mul_of_nonneg_left (HK k hk).1 (abs_nonneg g)) 1
      _ ≤ R := by dsimp only [R]; nlinarith
  have H := translated_mixed_wJets
    (scalarData_scaledTerminalResidual_wJets D ht hρ 24 z)
    (by rw [abs_of_pos hρ.1]; exact hρ.2) hR isOpen_Ioo hb hb₁ hk'
    (hnorm (HK k hk).2.1) (hnorm (HK k hk).2.2) (r := 22)
  have hbudget : 2 * B * R ^ 2 * (1 + ‖b k‖) ^ 3 ≤ M₀ * (1 + g ^ 2) ^ 3 := by
    have hg : 1 ≤ 1 + |g| := by linarith [abs_nonneg g]
    have hsq : (1 + |g|) ^ 2 ≤ 2 * (1 + g ^ 2) := by
      nlinarith [sq_nonneg (|g| - 1), sq_abs g]
    have hnoise : (1 + |g|) ^ 5 ≤ 8 * (1 + g ^ 2) ^ 3 := by
      calc
        _ ≤ (1 + |g|) ^ 6 := pow_le_pow_right₀ hg (by omega)
        _ = ((1 + |g|) ^ 2) ^ 3 := by ring
        _ ≤ (2 * (1 + g ^ 2)) ^ 3 := pow_le_pow_left₀ (by positivity) hsq 3
        _ = _ := by ring
    calc
      _ ≤ 2 * B * R ^ 2 * R ^ 3 := by gcongr
      _ = 2 * B * K ^ 5 * (1 + |g|) ^ 5 := by dsimp only [R]; ring
      _ ≤ 2 * B * K ^ 5 * (8 * (1 + g ^ 2) ^ 3) := by gcongr
      _ = (16 * B * K ^ 5) * (1 + g ^ 2) ^ 3 := by ring
      _ ≤ M₀ * (1 + g ^ 2) ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp only [M₀]
        linarith
  have H' := And.intro (H.1.mono hbudget le_rfl)
    (And.intro (H.2.1.mono hbudget le_rfl) (H.2.2.mono hbudget le_rfl))
  by_cases hi : i = 0
  · subst i
    simpa only [frozenRowsNormalizedJet_terminal β _ _ h z ε k g _ hh,
      ite_eq_left rfl, ite_true, MomentKJet.rescale, Fin.val_zero, zero_add, pow_one, mul_one,
      b, ρ, B] using H'
  · simp only [frozenRowsNormalizedJet_terminal β _ _ h z ε k g _ hh,
      ite_eq_right hi, MomentKJet.rescale, MomentKJet.const, mul_zero]
    exact ⟨wJets_zero (by positivity), wJets_zero (by positivity), wJets_zero (by positivity)⟩

section CenteredTransport

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem secondAverageTransport_centered
    {f a b s t : Ω → ℝ}
    (hf : MemLp f 2 μ) (ha : MemLp a 2 μ)
    (hs : MemLp s 2 μ) (ht : MemLp t 2 μ)
    (hsq : MemLp (fun x => s x ^ 2) 2 μ) (f₀ a₀ s₀ t₀ : ℝ) :
    StepCalculus.secondAverageTransport μ f a b s t =
      (∫ x, b x ∂μ) +
        2 * covariance (fun x => a x - a₀) (fun x => s x - s₀) μ +
        covariance (fun x => f x - f₀) (fun x => t x - t₀) μ +
        covariance (fun x => f x - f₀) (fun x => (s x - s₀) ^ 2) μ -
          2 * (∫ x, s x - s₀ ∂μ) *
            covariance (fun x => f x - f₀) (fun x => s x - s₀) μ := by
  have he : StepCalculus.secondAverageTransport μ f a b
      (fun x => s x - s₀) (fun x => t x - t₀) =
        StepCalculus.secondAverageTransport μ f a b s t := by
    simpa only [sub_eq_add_neg] using
      StepCalculus.secondAverageTransport_add_constants hf ha hs ht hsq (-s₀) (-t₀)
  rw [← he]
  unfold StepCalculus.secondAverageTransport
  rw [covariance_sub_const_left (ha.integrable (by norm_num)),
    covariance_sub_const_left (hf.integrable (by norm_num)),
    covariance_sub_const_left (hf.integrable (by norm_num)),
    covariance_sub_const_left (hf.integrable (by norm_num))]

theorem averageTransportKJet_centered
    {f a b s t : Ω → ℝ}
    (hf : MemLp f 2 μ) (ha : MemLp a 2 μ)
    (hs : MemLp s 2 μ) (ht : MemLp t 2 μ)
    (hsq : MemLp (fun x => s x ^ 2) 2 μ) (f₀ a₀ s₀ t₀ : ℝ) :
    averageTransportKJet μ f a b s t =
      (averageTransportKJet μ (fun x => f x - f₀) (fun x => a x - a₀) b
        (fun x => s x - s₀) (fun x => t x - t₀)).add ⟨f₀, a₀, 0⟩ := by
  have hiF : Integrable f μ := hf.integrable (by norm_num)
  have hiA : Integrable a μ := ha.integrable (by norm_num)
  have he₂ := secondAverageTransport_centered (b := b) hf ha hs ht hsq f₀ a₀ s₀ t₀
  unfold averageTransportKJet MomentKJet.add
  congr 1
  · change (∫ x, f x ∂μ) = (∫ x, f x - f₀ ∂μ) + f₀
    rw [integral_sub hiF (integrable_const f₀), integral_const, probReal_univ, one_smul]
    ring
  · change (∫ x, a x ∂μ) + covariance f s μ =
      (∫ x, a x - a₀ ∂μ) + covariance (fun x => f x - f₀) (fun x => s x - s₀) μ + a₀
    rw [integral_sub hiA (integrable_const a₀), integral_const, probReal_univ, one_smul,
      covariance_sub_const_left hiF, covariance_sub_const_right (hs.integrable (by norm_num))]
    ring
  · simpa only [StepCalculus.secondAverageTransport, add_zero] using he₂

theorem covariance_centered_weight_bound {f s w : Ω → ℝ} {C L T f₀ s₀ : ℝ} {p q : ℕ}
    (hf : MemLp f 2 μ) (hs : MemLp s 2 μ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hfB : ∀ x, |f x - f₀| ≤ C * w x ^ p)
    (hsB : ∀ x, |s x - s₀| ≤ L * w x ^ q)
    (hi₁ : Integrable (fun x => w x ^ p) μ)
    (hi₂ : Integrable (fun x => w x ^ q) μ)
    (hi₃ : Integrable (fun x => w x ^ (p + q)) μ)
    (hT₁ : (∫ x, w x ^ p ∂μ) ≤ T) (hT₂ : (∫ x, w x ^ q ∂μ) ≤ T)
    (hT₃ : (∫ x, w x ^ (p + q) ∂μ) ≤ T) (hT : 0 ≤ T) :
    |covariance f s μ| ≤ C * L * (T + T ^ 2) := by
  have H := covariance_weight_bound (hf.sub (memLp_const f₀)) (hs.sub (memLp_const s₀))
    hC hL hfB hsB hi₁ hi₂ hi₃ hT₁ hT₂ hT₃ hT
  change |covariance (fun x => f x - f₀) (fun x => s x - s₀) μ| ≤ _ at H
  rwa [covariance_sub_const_left (hf.integrable (by norm_num)),
    covariance_sub_const_right (hs.integrable (by norm_num))] at H

theorem scoreCumulant_centered {f s : Ω → ℝ}
    (hf : MemLp f 2 μ) (hs : MemLp s 2 μ)
    (hsq : MemLp (fun x => s x ^ 2) 2 μ) (f₀ s₀ : ℝ) :
    covariance f (fun x => s x ^ 2) μ -
        2 * (∫ x, s x ∂μ) * covariance f s μ =
      covariance (fun x => f x - f₀) (fun x => (s x - s₀) ^ 2) μ -
        2 * (∫ x, s x - s₀ ∂μ) *
          covariance (fun x => f x - f₀) (fun x => s x - s₀) μ := by
  have H := secondAverageTransport_centered (a := fun _ => 0) (b := fun _ => 0)
    (t := fun _ => 0) hf (memLp_const 0) hs (memLp_const 0) hsq f₀ 0 s₀ 0
  simpa only [StepCalculus.secondAverageTransport, integral_zero,
    covariance_const_left, covariance_const_right, sub_zero, mul_zero, zero_add] using H

theorem scoreCumulant_centered_weight_bound {f s w : Ω → ℝ}
    {C L T f₀ s₀ : ℝ} {p q : ℕ}
    (hf : MemLp f 2 μ) (hs : MemLp s 2 μ)
    (hsq : MemLp (fun x => s x ^ 2) 2 μ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hfB : ∀ x, |f x - f₀| ≤ C * w x ^ p)
    (hsB : ∀ x, |s x - s₀| ≤ L * w x ^ q)
    (hi : ∀ n ≤ p + 2 * q, Integrable (fun x => w x ^ n) μ)
    (hMom : ∀ n ≤ p + 2 * q, (∫ x, w x ^ n ∂μ) ≤ T) :
    |covariance f (fun x => s x ^ 2) μ -
        2 * (∫ x, s x ∂μ) * covariance f s μ| ≤
      C * L ^ 2 * ((T + T ^ 2) + 2 * T * (T + T ^ 2)) := by
  have hfC := hf.sub (memLp_const f₀)
  have hsC := hs.sub (memLp_const s₀)
  have hsqC : MemLp (fun x => (s x - s₀) ^ 2) 2 μ := by
    convert (hsq.sub (hs.const_mul (2 * s₀))).add (memLp_const (s₀ ^ 2)) using 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hsqB (x : Ω) : |(s x - s₀) ^ 2| ≤ L ^ 2 * w x ^ (2 * q) := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hsB x) 2).trans_eq (by rw [mul_pow, ← pow_mul]; ring)
  have Hsq := covariance_weight_bound hfC hsqC hC (sq_nonneg L) hfB hsqB
    (hi p (by omega)) (hi (2 * q) (by omega)) (hi (p + 2 * q) le_rfl)
    (hMom p (by omega)) (hMom (2 * q) (by omega)) (hMom (p + 2 * q) le_rfl) hT
  have Hfirst := covariance_weight_bound hfC hsC hC hL hfB hsB
    (hi p (by omega)) (hi q (by omega)) (hi (p + q) (by omega))
    (hMom p (by omega)) (hMom q (by omega)) (hMom (p + q) (by omega)) hT
  have Hmean : |∫ x, s x - s₀ ∂μ| ≤ L * T := by
    calc
      _ ≤ ∫ x, |s x - s₀| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, L * w x ^ q ∂μ := integral_mono_of_nonneg
        (ae_of_all _ (fun _ => abs_nonneg _)) ((hi q (by omega)).const_mul L) (ae_of_all _ hsB)
      _ = L * (∫ x, w x ^ q ∂μ) := integral_const_mul _ _
      _ ≤ L * T := mul_le_mul_of_nonneg_left (hMom q (by omega)) hL
  rw [scoreCumulant_centered hf hs hsq f₀ s₀]
  have Hlast : |2 * (∫ x, s x - s₀ ∂μ) *
      covariance (fun x => f x - f₀) (fun x => s x - s₀) μ| ≤
        2 * (L * T) * (C * L * (T + T ^ 2)) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left Hmean (by norm_num)) Hfirst
      (abs_nonneg _) (by positivity)
  exact (abs_sub _ _).trans ((add_le_add Hsq Hlast).trans_eq (by ring))

end CenteredTransport

end SKBarriers2.Corner
