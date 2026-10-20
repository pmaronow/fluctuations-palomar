module

public import SKBarriers2.Corner.FrozenRiccati
public import SKBarriers2.Corner.FJ

@[expose] public section

noncomputable section
open OAI.SK.Analytic SKOptimized.Overshoot
open Set Filter
open scoped Topology

namespace SKBarriers2.Corner

def frozenJetPolynomial (β : ℝ) (α : ℝ → ℝ) (a t h k z : ℝ) : ℝ :=
  h * (frozenCoefficient₁ k a (β ^ 2) (jet β α 1 t z) (jet β α 2 t z) -
    frozenCoefficient₁ 0 a (β ^ 2) (jet β α 1 t z) (jet β α 2 t z)) +
  h ^ 2 * (frozenCoefficient₂ k a (β ^ 2) (jet β α 2 t z) -
    frozenCoefficient₂ 0 a (β ^ 2) (jet β α 2 t z)) +
  h ^ 3 * (frozenCoefficient₃ k a (β ^ 2) (jet β α 1 t z) (jet β α 2 t z)
    (jet β α 3 t z) (jet β α 4 t z) -
    frozenCoefficient₃ 0 a (β ^ 2) (jet β α 1 t z) (jet β α 2 t z)
      (jet β α 3 t z) (jet β α 4 t z))

def frozenJetShift (β : ℝ) (α : ℝ → ℝ) (a s k z : ℝ) : ℝ :=
  (a * (β ^ 2) ^ 2 / 4) *
    (-4 * (β ^ 2) * jet β α 2 s z *
      (jet β α 4 s z + 2 * a * jet β α 2 s z ^ 2 +
        2 * a * jet β α 1 s z * jet β α 3 s z)) * penaltyPolynomial (1 / 2) k

def transportedFrozenPolynomial (β : ℝ) (α : ℝ → ℝ) (s h k z : ℝ) : ℝ :=
  frozenJetPolynomial β α (α s) s h k z + h ^ 3 * frozenJetShift β α (α s) s k z

def frozenError (h k : ℝ) : ℝ := Real.sqrt h * h ^ 3 * k ^ 2 + h ^ 3 * |k| ^ 3

def FrozenRemainderBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧ κ ≤ 1 / 2 ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ → ∀ z : ℝ,
      |frozenDifference β α (α (r - h)) (r - h) h k z -
        transportedFrozenPolynomial β α (r - h) h k z| ≤ C * frozenError h k

def TerminalFrozenRemainderBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧ κ ≤ 1 / 2 ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ → ∀ z : ℝ,
      |frozenDifference β α (α (r - h)) (r - h) h k z -
        frozenJetPolynomial β α (α (r - h)) ((r - h) + 4 * h) h k z| ≤ C * frozenError h k

def FrozenJetTransportBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧ κ ≤ 1 / 2 ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ → ∀ z : ℝ,
      |frozenJetPolynomial β α (α (r - h)) ((r - h) + 4 * h) h k z -
        transportedFrozenPolynomial β α (r - h) h k z| ≤ C * h ^ 4 * k ^ 2

theorem frozenError_nonneg {h : ℝ} (hh : 0 ≤ h) (k : ℝ) : 0 ≤ frozenError h k := by
  unfold frozenError
  positivity

theorem fourth_order_le_frozenError {h : ℝ} (hh : 0 ≤ h) (h₁ : h ≤ 1) (k : ℝ) :
    h ^ 4 * k ^ 2 ≤ frozenError h k := by
  have hs : h ≤ Real.sqrt h := by
    have hs₀ := Real.sqrt_nonneg h
    have hs₂ := Real.sq_sqrt hh
    nlinarith [mul_nonneg hh (sub_nonneg.mpr h₁)]
  have H := mul_le_mul_of_nonneg_right hs (mul_nonneg (pow_nonneg hh 3) (sq_nonneg k))
  unfold frozenError
  nlinarith [mul_nonneg (pow_nonneg hh 3) (pow_nonneg (abs_nonneg k) 3)]

theorem frozenRemainderBound_of_terminal_and_transport {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hflow : TerminalFrozenRemainderBound β α I) (htime : FrozenJetTransportBound β α I) :
    FrozenRemainderBound β α I := by
  rcases hflow with ⟨C, h₀, κ, hC, hh₀, hκ, hκ₂, hflow⟩
  rcases htime with ⟨D, h₁, κ₁, hD, hh₁, hκ₁, hκ₁₂, htime⟩
  refine ⟨C + D, min (min h₀ h₁) 1, min κ κ₁, add_pos hC hD,
    lt_min (lt_min hh₀ hh₁) zero_lt_one, lt_min hκ hκ₁, (min_le_left _ _).trans hκ₂, ?_⟩
  intro r hr h hh hhsmall k hk z
  have hh₀' : h ≤ h₀ := (hhsmall.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hh₁' : h ≤ h₁ := (hhsmall.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hh1 : h ≤ 1 := hhsmall.trans (min_le_right _ _)
  have hf := hflow r hr h hh hh₀' k (hk.trans (min_le_left _ _)) z
  have ht := htime r hr h hh hh₁' k (hk.trans (min_le_right _ _)) z
  have he := fourth_order_le_frozenError hh.le hh1 k
  calc
    _ ≤ |frozenDifference β α (α (r - h)) (r - h) h k z -
          frozenJetPolynomial β α (α (r - h)) ((r - h) + 4 * h) h k z| +
        |frozenJetPolynomial β α (α (r - h)) ((r - h) + 4 * h) h k z -
          transportedFrozenPolynomial β α (r - h) h k z| := abs_sub_le _ _ _
    _ ≤ C * frozenError h k + D * (h ^ 4 * k ^ 2) := by nlinarith [hf, ht]
    _ ≤ (C + D) * frozenError h k := by nlinarith [mul_le_mul_of_nonneg_left he hD.le]

private theorem interval_increment_le {f f₁ : ℝ → ℝ} {M : ℝ}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |f₁ t| ≤ M) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |f t - f 0| ≤ M * t := by
  simpa only [Real.norm_eq_abs, sub_zero] using norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hd t ht).hasDerivWithinAt) (fun t ht => by
      simpa only [Real.norm_eq_abs] using hb t (Ico_subset_Icc_self ht)) t ht

theorem epsilon_taylor_remainder {θ θ₁ θ₂ θ₃ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hd₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt θ (θ₁ t) t)
    (hd₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt θ₁ (θ₂ t) t)
    (hd₃ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt θ₂ (θ₃ t) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |θ₃ t| ≤ M) :
    |θ 1 - θ 0 - θ₁ 0 - θ₂ 0 / 2| ≤ M := by
  have h₂ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |θ₂ t - θ₂ 0| ≤ M := by
    exact (interval_increment_le hd₃ hb t ht).trans (mul_le_of_le_one_right hM ht.2)
  let R₁ : ℝ → ℝ := fun t => θ₁ t - θ₁ 0 - t * θ₂ 0
  have hR₁ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt R₁ (θ₂ t - θ₂ 0) t := by
    simpa only [R₁, one_mul, sub_zero, Pi.sub_def, id_eq] using
      ((hd₂ t ht).sub_const (θ₁ 0)).sub ((hasDerivAt_id t).mul_const (θ₂ 0))
  have h₁ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |R₁ t| ≤ M := by
    have H := interval_increment_le hR₁ h₂ t ht
    have hz : R₁ 0 = 0 := by simp [R₁]
    rw [hz, sub_zero] at H
    exact H.trans (mul_le_of_le_one_right hM ht.2)
  let R : ℝ → ℝ := fun t => θ t - θ 0 - t * θ₁ 0 - t ^ 2 * θ₂ 0 / 2
  have hR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt R (R₁ t) t := by
    have hd := (((hd₁ t ht).sub_const (θ 0)).sub ((hasDerivAt_id t).mul_const (θ₁ 0))).sub
      ((((hasDerivAt_id t).pow 2).mul_const (θ₂ 0)).div_const 2)
    simp only [Pi.pow_apply, id_eq, one_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
    convert hd using 1
    dsimp only [R₁]
    ring
  have H := interval_increment_le hR h₁ 1 (by norm_num)
  simpa [R] using H

theorem locally_even_derivative_zero {f : ℝ → ℝ} {κ d : ℝ} (hκ : 0 < κ)
    (heven : ∀ k ∈ Icc (-κ) κ, f (-k) = f k) (hd : HasDerivAt f d 0) : d = 0 := by
  have hn : Icc (-κ) κ ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) hκ
  have he : (fun t => f (-t)) =ᶠ[𝓝 (0 : ℝ)] f := by
    filter_upwards [hn] with t ht
    exact heven t ht
  have hneg : HasDerivAt (fun t => f (-t)) (-d) 0 := by
    have hd' : HasDerivAt f d (-(0 : ℝ)) := by simpa only [neg_zero] using hd
    simpa only [Function.comp_def, mul_neg, mul_one] using hd'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hz : HasDerivAt f (-d) 0 := hneg.congr_of_eventuallyEq he.symm
  have hh := hd.unique hz
  linarith

theorem even_second_difference_bound {f f₁ f₂ : ℝ → ℝ} {κ M : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (heven : ∀ k ∈ Icc (-κ) κ, f (-k) = f k)
    (hd₁ : ∀ k ∈ Icc (-κ) κ, HasDerivAt f (f₁ k) k)
    (hd₂ : ∀ k ∈ Icc (-κ) κ, HasDerivAt f₁ (f₂ k) k)
    (hb : ∀ k ∈ Icc (-κ) κ, |f₂ k| ≤ M)
    {k : ℝ} (hk : |k| ≤ κ) : |f k - f 0| ≤ M * k ^ 2 := by
  have hz : f₁ 0 = 0 := locally_even_derivative_zero hκ heven (hd₁ 0 (by constructor <;> linarith))
  have ht (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t * k ∈ Icc (-κ) κ := by
    have ha : |t * k| ≤ κ := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg k) ht.2).trans hk
    exact abs_le.mp ha
  have hfirst (t : ℝ) (htt : t ∈ Icc (0 : ℝ) 1) : |f₁ (t * k)| ≤ M * |k| := by
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun u => f₁ (u * k)) (f₂ (s * k) * k) s :=
      (hd₂ _ (ht s hs)).comp s (by simpa only [id_eq, one_mul] using (hasDerivAt_id s).mul_const k)
    have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : |f₂ (s * k) * k| ≤ M * |k| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb _ (ht s hs)) (abs_nonneg _)
    have H := interval_increment_le hd hbound t htt
    simp only [zero_mul, hz, sub_zero] at H
    exact H.trans (mul_le_of_le_one_right (mul_nonneg hM (abs_nonneg _)) htt.2)
  have hd (t : ℝ) (htt : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun u => f (u * k)) (f₁ (t * k) * k) t :=
    (hd₁ _ (ht t htt)).comp t (by simpa only [id_eq, one_mul] using (hasDerivAt_id t).mul_const k)
  have hb' (t : ℝ) (htt : t ∈ Icc (0 : ℝ) 1) : |f₁ (t * k) * k| ≤ M * k ^ 2 := by
    rw [abs_mul]
    have H := mul_le_mul_of_nonneg_right (hfirst t htt) (abs_nonneg k)
    nlinarith [sq_abs k]
  simpa only [one_mul, zero_mul, mul_one] using interval_increment_le hd hb' 1 (by norm_num)

theorem even_second_difference_envelope {f f₁ f₂ : ℝ → ℝ} {κ A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (heven : ∀ k ∈ Icc (-κ) κ, f (-k) = f k)
    (hd₁ : ∀ k ∈ Icc (-κ) κ, HasDerivAt f (f₁ k) k)
    (hd₂ : ∀ k ∈ Icc (-κ) κ, HasDerivAt f₁ (f₂ k) k)
    (hb : ∀ k ∈ Icc (-κ) κ, |f₂ k| ≤ A + B * |k|)
    {k : ℝ} (hk : |k| ≤ κ) : |f k - f 0| ≤ A * k ^ 2 + B * |k| ^ 3 := by
  by_cases hz : k = 0
  · simp [hz]
  have hsub : Icc (-|k|) |k| ⊆ Icc (-κ) κ :=
    fun _ hu => ⟨(neg_le_neg hk).trans hu.1, hu.2.trans hk⟩
  have hb' (u : ℝ) (hu : u ∈ Icc (-|k|) |k|) : |f₂ u| ≤ A + B * |k| := by
    exact (hb u (hsub hu)).trans
      (add_le_add (le_refl A) (mul_le_mul_of_nonneg_left (abs_le.mpr hu) hB))
  have H := even_second_difference_bound (abs_pos.mpr hz) (by positivity : 0 ≤ A + B * |k|)
    (fun u hu => heven u (hsub hu)) (fun u hu => hd₁ u (hsub hu))
    (fun u hu => hd₂ u (hsub hu)) hb' (le_refl |k|)
  have hc : |k| ^ 3 = |k| * k ^ 2 := by rw [pow_succ, sq_abs]; ring
  calc
    _ ≤ (A + B * |k|) * k ^ 2 := H
    _ = _ := by rw [hc]; ring

def EvenSecondControl (f : ℝ → ℝ) (κ A B : ℝ) : Prop :=
  ∃ f₁ f₂ : ℝ → ℝ,
    (∀ k ∈ Icc (-κ) κ, HasDerivAt f (f₁ k) k ∧ HasDerivAt f₁ (f₂ k) k) ∧
    (∀ k ∈ Icc (-κ) κ, |f₂ k| ≤ A + B * |k|) ∧
    (∀ k ∈ Icc (-κ) κ, f (-k) = f k)

theorem EvenSecondControl.bound {f : ℝ → ℝ} {κ A B k : ℝ} (H : EvenSecondControl f κ A B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : |k| ≤ κ) :
    |f k - f 0| ≤ A * k ^ 2 + B * |k| ^ 3 := by
  rcases H with ⟨f₁, f₂, hd, hb, heven⟩
  exact even_second_difference_envelope hA hB heven (fun t ht => (hd t ht).1)
    (fun t ht => (hd t ht).2) hb hk

def frozenThetaDifference (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ) : ℝ → ℝ :=
  fun ε => frozenTerminalTheta β α a s h k z ε - frozenTerminalTheta β α a s h 0 z ε

def frozenRiccatiValue (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ) : ℝ :=
  (riccatiRecursion (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)).value (fun _ => z)

def frozenGaussianCoefficient (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ) : ℝ :=
  frozenRiccatiValue β α a s h k z + frozenFirstMoment β α a s h k z + frozenSecondMoment β α a s h k z / 2

theorem frozenThetaDifference_one (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ) :
    frozenThetaDifference β α a s h k z 1 = frozenDifference β α a s h k z := by
  unfold frozenThetaDifference frozenTerminalTheta
  rw [frozenTheta_one, frozenTheta_one]
  rfl

theorem frozenThetaDifference_taylor_coefficient (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (hQk : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hQ₀ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z))
    (hDk : EpsilonChainControl (frozenSchedule β a (1 / 2) h k)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z))
    (hD₀ : EpsilonChainControl (frozenSchedule β a (1 / 2) h 0)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)) :
    frozenThetaDifference β α a s h k z 0 + deriv (frozenThetaDifference β α a s h k z) 0 +
        iteratedDeriv 2 (frozenThetaDifference β α a s h k z) 0 / 2 =
      frozenGaussianCoefficient β α a s h k z - frozenGaussianCoefficient β α a s h 0 z := by
  have hk' := frozenTerminalTheta_first_second β α a s h k z hQk hDk
  have h₀' := frozenTerminalTheta_first_second β α a s h 0 z hQ₀ hD₀
  have h₁ : deriv (frozenThetaDifference β α a s h k z) 0 =
      frozenFirstMoment β α a s h k z - frozenFirstMoment β α a s h 0 z := (hk'.1.sub h₀'.1).deriv
  have hnearK := frozenTerminalTheta_eventually_differentiable β α a s h k z hQk hDk
  have hnear₀ := frozenTerminalTheta_eventually_differentiable β α a s h 0 z hQ₀ hD₀
  have he : deriv (frozenThetaDifference β α a s h k z) =ᶠ[𝓝 (0 : ℝ)]
      fun ε => deriv (frozenTerminalTheta β α a s h k z) ε - deriv (frozenTerminalTheta β α a s h 0 z) ε := by
    filter_upwards [hnearK, hnear₀] with ε hεK hε₀
    exact (hεK.hasDerivAt.sub hε₀.hasDerivAt).deriv
  have hd₂ := (hk'.2.sub h₀'.2).congr_of_eventuallyEq he
  have h₂ : iteratedDeriv 2 (frozenThetaDifference β α a s h k z) 0 =
      frozenSecondMoment β α a s h k z - frozenSecondMoment β α a s h 0 z := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hd₂.deriv
  rw [h₁, h₂]
  unfold frozenThetaDifference
  rw [frozenTerminalTheta_zero β α a s h k z hQk, frozenTerminalTheta_zero β α a s h 0 z hQ₀]
  unfold frozenGaussianCoefficient frozenRiccatiValue
  ring

def TerminalChainDifferentiation (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) (h₀ κ : ℝ) : Prop :=
  ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ → ∀ z : ℝ,
    EpsilonChainControl (frozenSchedule β (α (r - h)) (1 / 2) h k)
      (terminalTaylorQuadratic β α (r - h) h z) (terminalResidual β α (r - h) h z)

def TerminalCoefficientControl (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) (C h₀ κ : ℝ) : Prop :=
  ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ → ∀ z : ℝ,
    |(frozenGaussianCoefficient β α (α (r - h)) (r - h) h k z -
        frozenGaussianCoefficient β α (α (r - h)) (r - h) h 0 z) -
      frozenJetPolynomial β α (α (r - h)) ((r - h) + 4 * h) h k z| ≤ C * frozenError h k

def riccatiRow (k h a b χ : ℝ) : ℝ :=
  h ^ 2 * (a * b ^ 2 / 4 * χ ^ 2 * penaltyPolynomial (1 / 2) k) +
    h ^ 3 * (a ^ 2 * b ^ 3 * χ ^ 3 *
      (riccatiJet (1 / 2) k - riccatiJet (1 / 2) 0 + 2 * penaltyPolynomial (1 / 2) k))

def firstMomentRow (k h a b u χ w g₄ : ℝ) : ℝ :=
  h ^ 3 * (a * b ^ 3 * χ * (g₄ + 2 * a * u * w) * penaltyPolynomial (1 / 2) k)

def wickRow (k h a b w : ℝ) : ℝ :=
  h ^ 3 * (a * b ^ 3 * w ^ 2 * (wickJet (1 / 2) k - wickJet (1 / 2) 0))

theorem frozenJetPolynomial_split (β : ℝ) (α : ℝ → ℝ) (a t h k z : ℝ) :
    frozenJetPolynomial β α a t h k z =
      riccatiRow k h a (β ^ 2) (jet β α 2 t z) +
      firstMomentRow k h a (β ^ 2) (jet β α 1 t z) (jet β α 2 t z) (jet β α 3 t z) (jet β α 4 t z) +
      wickRow k h a (β ^ 2) (jet β α 3 t z) := by
  unfold frozenJetPolynomial
  rw [FJ_coefficient₁, FJ_coefficient₂, FJ_coefficient₃]
  unfold riccatiRow firstMomentRow wickRow
  ring

structure SplitCoefficientEstimate (β : ℝ) (α : ℝ → ℝ) (a s h k z C : ℝ) : Prop where
  riccati : |(frozenRiccatiValue β α a s h k z - frozenRiccatiValue β α a s h 0 z) -
    riccatiRow k h a (β ^ 2) (jet β α 2 (s + 4 * h) z)| ≤ C * frozenError h k
  first : |(frozenFirstMoment β α a s h k z - frozenFirstMoment β α a s h 0 z) -
    firstMomentRow k h a (β ^ 2) (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z)
      (jet β α 3 (s + 4 * h) z) (jet β α 4 (s + 4 * h) z)| ≤ C * frozenError h k
  wick : |(frozenSecondMoment β α a s h k z - frozenSecondMoment β α a s h 0 z) / 2 -
    wickRow k h a (β ^ 2) (jet β α 3 (s + 4 * h) z)| ≤ C * frozenError h k

def TerminalSplitEstimates (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) (C h₀ κ : ℝ) : Prop :=
  ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ → ∀ z : ℝ,
    SplitCoefficientEstimate β α (α (r - h)) (r - h) h k z C

theorem coefficient_error_of_split (β : ℝ) (α : ℝ → ℝ) (a s h k z C : ℝ)
    (H : SplitCoefficientEstimate β α a s h k z C) :
    |(frozenGaussianCoefficient β α a s h k z - frozenGaussianCoefficient β α a s h 0 z) -
      frozenJetPolynomial β α a (s + 4 * h) h k z| ≤ (3 * C) * frozenError h k := by
  have he : (frozenGaussianCoefficient β α a s h k z - frozenGaussianCoefficient β α a s h 0 z) -
      frozenJetPolynomial β α a (s + 4 * h) h k z =
    ((frozenRiccatiValue β α a s h k z - frozenRiccatiValue β α a s h 0 z) -
      riccatiRow k h a (β ^ 2) (jet β α 2 (s + 4 * h) z)) +
    ((frozenFirstMoment β α a s h k z - frozenFirstMoment β α a s h 0 z) -
      firstMomentRow k h a (β ^ 2) (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z)
        (jet β α 3 (s + 4 * h) z) (jet β α 4 (s + 4 * h) z)) +
    ((frozenSecondMoment β α a s h k z - frozenSecondMoment β α a s h 0 z) / 2 -
      wickRow k h a (β ^ 2) (jet β α 3 (s + 4 * h) z)) := by
    rw [frozenJetPolynomial_split]
    unfold frozenGaussianCoefficient
    ring
  rw [he]
  calc
    _ ≤ |(frozenRiccatiValue β α a s h k z - frozenRiccatiValue β α a s h 0 z) -
        riccatiRow k h a (β ^ 2) (jet β α 2 (s + 4 * h) z)| +
      |(frozenFirstMoment β α a s h k z - frozenFirstMoment β α a s h 0 z) -
        firstMomentRow k h a (β ^ 2) (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z)
          (jet β α 3 (s + 4 * h) z) (jet β α 4 (s + 4 * h) z)| +
      |(frozenSecondMoment β α a s h k z - frozenSecondMoment β α a s h 0 z) / 2 -
        wickRow k h a (β ^ 2) (jet β α 3 (s + 4 * h) z)| := by
      exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ _ := by linarith [H.riccati, H.first, H.wick]

theorem terminalCoefficientControl_of_split {β C h₀ κ : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (H : TerminalSplitEstimates β α I C h₀ κ) : TerminalCoefficientControl β α I (3 * C) h₀ κ := by
  intro r hr h hh hh₀ k hk z
  exact coefficient_error_of_split _ _ _ _ _ _ _ _ (H r hr h hh hh₀ k hk z)

def riccatiCoefficientError (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  (frozenRiccatiValue β α a s h k z - frozenRiccatiValue β α a s h 0 z) -
    riccatiRow k h a (β ^ 2) (jet β α 2 (s + 4 * h) z)

def firstCoefficientError (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  (frozenFirstMoment β α a s h k z - frozenFirstMoment β α a s h 0 z) -
    firstMomentRow k h a (β ^ 2) (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z)
      (jet β α 3 (s + 4 * h) z) (jet β α 4 (s + 4 * h) z)

def wickCoefficientError (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  (frozenSecondMoment β α a s h k z - frozenSecondMoment β α a s h 0 z) / 2 -
    wickRow k h a (β ^ 2) (jet β α 3 (s + 4 * h) z)

def TerminalSplitDerivativeControl (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) (C h₀ κ : ℝ) : Prop :=
  ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
    EvenSecondControl (riccatiCoefficientError β α (α (r - h)) (r - h) h z)
      κ (C * Real.sqrt h * h ^ 3) (C * h ^ 3) ∧
    EvenSecondControl (firstCoefficientError β α (α (r - h)) (r - h) h z)
      κ (C * Real.sqrt h * h ^ 3) (C * h ^ 3) ∧
    EvenSecondControl (wickCoefficientError β α (α (r - h)) (r - h) h z)
      κ (C * Real.sqrt h * h ^ 3) (C * h ^ 3)

theorem terminalSplitEstimates_of_derivative_control {β C h₀ κ : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hC : 0 ≤ C) (H : TerminalSplitDerivativeControl β α I C h₀ κ) :
    TerminalSplitEstimates β α I C h₀ κ := by
  intro r hr h hh hh₀ k hk z
  rcases H r hr h hh hh₀ z with ⟨hR, h₁, hW⟩
  have hbound (f : ℝ → ℝ) (hf : f 0 = 0)
      (hf₂ : EvenSecondControl f κ (C * Real.sqrt h * h ^ 3) (C * h ^ 3)) :
      |f k| ≤ C * frozenError h k := by
    have hb := hf₂.bound (by positivity) (by positivity) hk
    rw [hf, sub_zero] at hb
    calc
      _ ≤ C * Real.sqrt h * h ^ 3 * k ^ 2 + C * h ^ 3 * |k| ^ 3 := hb
      _ = _ := by unfold frozenError; ring
  refine ⟨?_, ?_, ?_⟩
  · change |riccatiCoefficientError β α (α (r - h)) (r - h) h z k| ≤ _
    apply hbound _ _ hR
    simp [riccatiCoefficientError, riccatiRow, penaltyPolynomial]
  · change |firstCoefficientError β α (α (r - h)) (r - h) h z k| ≤ _
    apply hbound _ _ h₁
    simp [firstCoefficientError, firstMomentRow, penaltyPolynomial]
  · change |wickCoefficientError β α (α (r - h)) (r - h) h z k| ≤ _
    apply hbound _ _ hW
    simp [wickCoefficientError, wickRow]

def thetaThirdInTilt (β : ℝ) (α : ℝ → ℝ) (a s h z ε k : ℝ) : ℝ :=
  iteratedDeriv 3 (frozenThetaDifference β α a s h k z) ε

def TerminalMixedThirdControl (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) (C h₀ κ : ℝ) : Prop :=
  ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
    (∀ k : ℝ, |k| ≤ κ → ∀ ε ∈ Icc (0 : ℝ) 1,
      HasDerivAt (frozenThetaDifference β α (α (r - h)) (r - h) h k z)
        (deriv (frozenThetaDifference β α (α (r - h)) (r - h) h k z) ε) ε ∧
      HasDerivAt (deriv (frozenThetaDifference β α (α (r - h)) (r - h) h k z))
        (iteratedDeriv 2 (frozenThetaDifference β α (α (r - h)) (r - h) h k z) ε) ε ∧
      HasDerivAt (iteratedDeriv 2 (frozenThetaDifference β α (α (r - h)) (r - h) h k z))
        (iteratedDeriv 3 (frozenThetaDifference β α (α (r - h)) (r - h) h k z) ε) ε) ∧
    ∀ ε ∈ Icc (0 : ℝ) 1, ∃ g₁ g₂ : ℝ → ℝ,
      (∀ k ∈ Icc (-κ) κ, HasDerivAt (thetaThirdInTilt β α (α (r - h)) (r - h) h z ε) (g₁ k) k ∧
        HasDerivAt g₁ (g₂ k) k) ∧
      (∀ k ∈ Icc (-κ) κ, |g₂ k| ≤ C * Real.sqrt h * h ^ 3) ∧
      (∀ k ∈ Icc (-κ) κ, thetaThirdInTilt β α (α (r - h)) (r - h) h z ε (-k) =
        thetaThirdInTilt β α (α (r - h)) (r - h) h z ε k)

theorem terminal_epsilon_taylor_bound {β C h₀ κ : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ) (H : TerminalMixedThirdControl β α I C h₀ κ)
    {r h k z : ℝ} (hr : r ∈ I) (hh : 0 < h) (hh₀ : h ≤ h₀) (hk : |k| ≤ κ) :
    |frozenThetaDifference β α (α (r - h)) (r - h) h k z 1 -
      frozenThetaDifference β α (α (r - h)) (r - h) h k z 0 -
      deriv (frozenThetaDifference β α (α (r - h)) (r - h) h k z) 0 -
      iteratedDeriv 2 (frozenThetaDifference β α (α (r - h)) (r - h) h k z) 0 / 2| ≤
        C * Real.sqrt h * h ^ 3 * k ^ 2 := by
  rcases H r hr h hh hh₀ z with ⟨heps, hmix⟩
  have hb (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) :
      |iteratedDeriv 3 (frozenThetaDifference β α (α (r - h)) (r - h) h k z) ε| ≤
        C * Real.sqrt h * h ^ 3 * k ^ 2 := by
    rcases hmix ε hε with ⟨g₁, g₂, hd, hbound, heven⟩
    have Hk := even_second_difference_bound hκ (by positivity : 0 ≤ C * Real.sqrt h * h ^ 3)
      heven (fun k hk => (hd k hk).1) (fun k hk => (hd k hk).2) hbound hk
    have hz : thetaThirdInTilt β α (α (r - h)) (r - h) h z ε 0 = 0 := by
      have hf : frozenThetaDifference β α (α (r - h)) (r - h) h 0 z = fun _ => 0 := by
        funext e
        exact sub_self _
      unfold thetaThirdInTilt
      rw [hf]
      simp
    rw [hz, sub_zero] at Hk
    simpa only [thetaThirdInTilt] using Hk
  exact epsilon_taylor_remainder (by positivity) (fun ε hε => (heps k hk ε hε).1)
    (fun ε hε => (heps k hk ε hε).2.1) (fun ε hε => (heps k hk ε hε).2.2) hb

theorem terminalFrozenRemainderBound_of_controls {β a₀ B C D h₀ κ δ : ℝ}
    {α : ℝ → ℝ} {I J : Set ℝ} (HJ : FrozenJetHypotheses β α J a₀ B)
    (hC : 0 < C) (hD : 0 < D) (hh₀ : 0 < h₀) (hκ : 0 < κ) (hκ₂ : κ ≤ 1 / 2) (hδ : 0 < δ)
    (hcover : ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ δ → r - h ∈ J ∧ (r - h) + 4 * h ∈ J)
    (hdiff : TerminalChainDifferentiation β α I h₀ κ)
    (hcoef : TerminalCoefficientControl β α I C h₀ κ)
    (hthird : TerminalMixedThirdControl β α I D h₀ κ) :
    TerminalFrozenRemainderBound β α I := by
  rcases HJ.uniform_startup with ⟨hA, hhA, hstart⟩
  refine ⟨C + D, min h₀ (min δ hA), κ, add_pos hC hD,
    lt_min hh₀ (lt_min hδ hhA), hκ, hκ₂, ?_⟩
  intro r hr h hh hhsmall k hk z
  have hh₀' : h ≤ h₀ := hhsmall.trans (min_le_left _ _)
  have hhδ : h ≤ δ := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhA' : h ≤ hA := (hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hpoints := hcover r hr h hh hhδ
  have hQk := (hstart (r - h) h k z hpoints.1 hpoints.2 hh.le hhA' (hk.trans hκ₂)).1
  have hQ₀ := (hstart (r - h) h 0 z hpoints.1 hpoints.2 hh.le hhA' (by norm_num)).1
  have hdk := hdiff r hr h hh hh₀' k hk z
  have hd₀ := hdiff r hr h hh hh₀' 0 (by simpa using hκ.le) z
  have hc := frozenThetaDifference_taylor_coefficient β α (α (r - h)) (r - h) h k z hQk hQ₀ hdk hd₀
  have ht := terminal_epsilon_taylor_bound hD.le hκ hthird hr hh hh₀' hk (z := z)
  have he : frozenThetaDifference β α (α (r - h)) (r - h) h k z 1 -
      frozenThetaDifference β α (α (r - h)) (r - h) h k z 0 -
      deriv (frozenThetaDifference β α (α (r - h)) (r - h) h k z) 0 -
      iteratedDeriv 2 (frozenThetaDifference β α (α (r - h)) (r - h) h k z) 0 / 2 =
      frozenDifference β α (α (r - h)) (r - h) h k z -
        (frozenGaussianCoefficient β α (α (r - h)) (r - h) h k z -
          frozenGaussianCoefficient β α (α (r - h)) (r - h) h 0 z) := by
    rw [frozenThetaDifference_one]
    linear_combination -hc
  rw [he] at ht
  have hp := hcoef r hr h hh hh₀' k hk z
  have herror : Real.sqrt h * h ^ 3 * k ^ 2 ≤ frozenError h k := by
    unfold frozenError
    exact le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ |frozenDifference β α (α (r - h)) (r - h) h k z -
        (frozenGaussianCoefficient β α (α (r - h)) (r - h) h k z -
          frozenGaussianCoefficient β α (α (r - h)) (r - h) h 0 z)| +
      |(frozenGaussianCoefficient β α (α (r - h)) (r - h) h k z -
          frozenGaussianCoefficient β α (α (r - h)) (r - h) h 0 z) -
        frozenJetPolynomial β α (α (r - h)) ((r - h) + 4 * h) h k z| := abs_sub_le _ _ _
    _ ≤ D * (Real.sqrt h * h ^ 3 * k ^ 2) + C * frozenError h k := by nlinarith [ht, hp]
    _ ≤ (C + D) * frozenError h k := by nlinarith [mul_le_mul_of_nonneg_left herror hD.le]

theorem terminalFrozenRemainderBound_of_split_estimates {β a₀ B C D h₀ κ δ : ℝ}
    {α : ℝ → ℝ} {I J : Set ℝ} (HJ : FrozenJetHypotheses β α J a₀ B)
    (hC : 0 < C) (hD : 0 < D) (hh₀ : 0 < h₀) (hκ : 0 < κ) (hκ₂ : κ ≤ 1 / 2) (hδ : 0 < δ)
    (hcover : ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ δ → r - h ∈ J ∧ (r - h) + 4 * h ∈ J)
    (hdiff : TerminalChainDifferentiation β α I h₀ κ)
    (hcoef : TerminalSplitEstimates β α I C h₀ κ)
    (hthird : TerminalMixedThirdControl β α I D h₀ κ) :
    TerminalFrozenRemainderBound β α I := by
  exact terminalFrozenRemainderBound_of_controls HJ (by positivity) hD hh₀ hκ hκ₂ hδ hcover hdiff
    (terminalCoefficientControl_of_split hcoef) hthird

theorem terminalFrozenRemainderBound_of_derivative_controls {β a₀ B C D h₀ κ δ : ℝ}
    {α : ℝ → ℝ} {I J : Set ℝ} (HJ : FrozenJetHypotheses β α J a₀ B)
    (hC : 0 < C) (hD : 0 < D) (hh₀ : 0 < h₀) (hκ : 0 < κ) (hκ₂ : κ ≤ 1 / 2) (hδ : 0 < δ)
    (hcover : ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ δ → r - h ∈ J ∧ (r - h) + 4 * h ∈ J)
    (hdiff : TerminalChainDifferentiation β α I h₀ κ)
    (hcoef : TerminalSplitDerivativeControl β α I C h₀ κ)
    (hthird : TerminalMixedThirdControl β α I D h₀ κ) :
    TerminalFrozenRemainderBound β α I := by
  exact terminalFrozenRemainderBound_of_split_estimates HJ hC hD hh₀ hκ hκ₂ hδ hcover hdiff
    (terminalSplitEstimates_of_derivative_control hC.le hcoef) hthird

end SKBarriers2.Corner
