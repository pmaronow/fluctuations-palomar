module

public import SKBarriers2.Corner.FrozenRowsMoments6
public import SKBarriers2.Corner.FrozenRowsInductionK

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def frozenRowsKDomain : Set ℝ := Ioo (-(1 / 3) : ℝ) (1 / 3)

def frozenRowsHead (β a h : ℝ) (j : ℕ) (k : ℝ) : ℝ × Vec3 :=
  (frozenSchedule β a (1 / 2) h k).getD j (0, 0)

def frozenRowsNoise (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (i : Fin 4) (k g : ℝ) : ℝ :=
  epsilonSuffixNoiseJet ((frozenSchedule β a (1 / 2) h k).drop (j + 1))
    (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
    (frozenRowsHead β a h j k) (fun _ => z) i.val ε g

def frozenRowsNoiseKJet (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (i : Fin 4) (k g : ℝ) : MomentKJet :=
  let f := fun k => frozenRowsNoise β α a s h z ε j i k g
  ⟨f k, deriv f k, deriv (deriv f) k⟩

def frozenRowsNormalizedJet (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (i : Fin 3) (y : Vec3) (k g : ℝ) : MomentKJet :=
  normalizedEpsilonKJet (fun k => (frozenSchedule β a (1 / 2) h k).drop (j + 1))
    (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
    (Real.sqrt h) (fun _ => z)
    (fun k => y + (Real.sqrt h)⁻¹ • (g • (frozenRowsHead β a h j k).2))
    (i.val + 1) ε k

def FrozenRowsMixedEnvelope (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (M : ℝ) (k : ℝ) : Prop :=
  ∀ g : ℝ, ∀ i : Fin 3,
    let J := fun y => MomentKJet.rescale (Real.sqrt h)
      (frozenRowsNormalizedJet β α a s h z ε j i y k g)
    let C := (M * (1 + g ^ 2) ^ 3) ^ (i.val + 1)
    WJets (2 * j) C (3 * (i.val + 1)) (fun y => (J y).value) ∧
      WJets (2 * j) C (3 * (i.val + 1)) (fun y => (J y).first) ∧
      WJets (2 * j) C (3 * (i.val + 1)) (fun y => (J y).second)

def FrozenRowsMixedStep {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  ∃ h₀ M₀ T : ℝ, 0 < h₀ ∧ 1 ≤ M₀ ∧ 1 ≤ T ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      let α := cdf (D.μ : Measure ℝ)
      let H := fun j M k => FrozenRowsMixedEnvelope β α (α (r - h)) (r - h) h z ε j M k
      (∀ k ∈ frozenRowsKDomain, H 11 M₀ k) ∧
        ∀ j : ℕ, j < 11 → ∀ M : ℝ, 1 ≤ M →
          (∀ k ∈ frozenRowsKDomain, H (j + 1) M k) →
            ∀ k ∈ frozenRowsKDomain, H j (T * M) k

def FrozenRowsNoiseRegularity {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 11 →
      let J := frozenRowsNoiseKJet β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j
      (∀ k ∈ frozenRowsKDomain, ∀ i,
        Continuous (fun g => (J i k g).value) ∧
          Continuous (fun g => (J i k g).first) ∧
          Continuous (fun g => (J i k g).second)) ∧
        ∀ g k, k ∈ frozenRowsKDomain → ∀ i,
          MomentKJet.Differentiates (fun k => J i k g) k

def FrozenRowsPotentialKBounds {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  ∃ h₀ L : ℝ, 0 < h₀ ∧ 0 ≤ L ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 11 → ∀ k ∈ frozenRowsKDomain, ∀ g : ℝ,
      let J := frozenRowsNoiseKJet β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j 0 k g
      |J.first| ≤ L * (1 + g ^ 2) ∧ |J.second| ≤ L * (1 + g ^ 2)

private theorem frozenRows_drop (β a h k : ℝ) (j : ℕ) (hj : j < 12) :
    (frozenSchedule β a (1 / 2) h k).drop j =
      frozenRowsHead β a h j k :: (frozenSchedule β a (1 / 2) h k).drop (j + 1) := by
  interval_cases j <;> rfl

private theorem frozenRows_head_mass (β a h k : ℝ) (j : ℕ) (hj : j < 12) :
    (frozenRowsHead β a h j k).1 = frozenPartitionMass a j := by
  interval_cases j <;> norm_num [frozenRowsHead, frozenPartitionMass, frozenSchedule,
    frozenCommon, frozenShared, frozenInner, List.getD]

private theorem frozenRows_mem_domain {k : ℝ} (hk : k ∈ frozenRowsKDomain) :
    |k| ≤ 1 / 2 := by
  exact abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩

private theorem frozenRows_compact_sub : Icc (-(1 / 4) : ℝ) (1 / 4) ⊆ frozenRowsKDomain := by
  intro k hk
  exact ⟨by linarith [hk.1], by linarith [hk.2]⟩

theorem FrozenRowsMixedEnvelope.mono {β a s h z ε M N k : ℝ} {α : ℝ → ℝ} {j : ℕ}
    (H : FrozenRowsMixedEnvelope β α a s h z ε j M k) (hM : 0 ≤ M) (hMN : M ≤ N) :
    FrozenRowsMixedEnvelope β α a s h z ε j N k := by
  intro g i
  have hb := pow_le_pow_left₀ (mul_nonneg hM (by positivity : 0 ≤ (1 + g ^ 2) ^ 3))
    (mul_le_mul_of_nonneg_right hMN (by positivity : 0 ≤ (1 + g ^ 2) ^ 3)) (i.val + 1)
  exact ⟨(H g i).1.mono hb le_rfl, (H g i).2.1.mono hb le_rfl,
    (H g i).2.2.mono hb le_rfl⟩

theorem FrozenRowsMixedStep.envelopes {β : ℝ} {D : ScalarData β} {I : Set ℝ}
    (H : FrozenRowsMixedStep D I) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
        ∀ j : ℕ, j < 12 → ∀ k ∈ frozenRowsKDomain,
          FrozenRowsMixedEnvelope β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j M k := by
  obtain ⟨h₀, M₀, T, hh₀, hM₀, hT, H⟩ := H
  refine ⟨h₀, T ^ 11 * M₀, hh₀, one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) hM₀, ?_⟩
  intro r hr h hh hhsmall z ε hε j hj k hk
  have HP := H r hr h hh hhsmall z ε hε
  have Hind : ∀ n : ℕ, n ≤ 11 → ∀ k ∈ frozenRowsKDomain,
      FrozenRowsMixedEnvelope β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε (11 - n) (T ^ n * M₀) k := by
    intro n
    induction n with
    | zero => simpa only [Nat.sub_zero, pow_zero, one_mul] using fun _ => HP.1
    | succ n ih =>
      intro hn
      have hn' : n ≤ 11 := by omega
      have hj' : 11 - (n + 1) < 11 := by omega
      have he : 11 - (n + 1) + 1 = 11 - n := by omega
      have Hstep := HP.2 (11 - (n + 1)) hj' (T ^ n * M₀)
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) hM₀)
        (by simpa only [he] using ih hn')
      have hbudget : T ^ (n + 1) * M₀ = T * (T ^ n * M₀) := by
        rw [pow_succ]
        ring1
      rw [hbudget]
      exact Hstep
  have hn : 11 - j ≤ 11 := Nat.sub_le _ _
  have he : 11 - (11 - j) = j := by omega
  have HJ := Hind (11 - j) hn k hk
  rw [he] at HJ
  exact HJ.mono (by positivity : 0 ≤ T ^ (11 - j) * M₀)
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT hn) (by linarith))

private theorem frozenRows_original_noise {β a s h z ε : ℝ} {α : ℝ → ℝ}
    (hh : 0 < h) (j : ℕ) (i : Fin 3) (k g : ℝ) :
    originalEpsilonKJet (fun k => (frozenSchedule β a (1 / 2) h k).drop (j + 1))
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
      (Real.sqrt h) (fun _ => z)
      (fun k => (0 : Vec3) + (Real.sqrt h)⁻¹ • (g • (frozenRowsHead β a h j k).2))
      (i.val + 1) ε k = frozenRowsNoiseKJet β α a s h z ε j i.succ k g := by
  have hp : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have he (k : ℝ) : Real.sqrt h • ((0 : Vec3) +
      (Real.sqrt h)⁻¹ • (g • (frozenRowsHead β a h j k).2)) + (fun _ => z) =
      (fun _ => z) + g • (frozenRowsHead β a h j k).2 := by
    rw [zero_add, smul_smul, mul_inv_cancel₀ hp, one_smul, add_comm]
  simp only [originalEpsilonKJet, he, frozenRowsNoiseKJet, frozenRowsNoise,
    epsilonSpatialJet, epsilonSuffixNoiseJet, Fin.val_succ,
    iteratedDeriv_succ, iteratedDeriv_zero]

theorem FrozenRowsMixedEnvelope.weak_noise {β a s h z ε M k : ℝ}
    {α : ℝ → ℝ} {j : ℕ} (hh : 0 < h)
    (H : FrozenRowsMixedEnvelope β α a s h z ε j M k) (g : ℝ) (i : Fin 3) :
    MomentKJet.Bound (MomentKJet.rescale (Real.sqrt h)
      (frozenRowsNoiseKJet β α a s h z ε j i.succ k g))
      ((M * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3) ^ (i.val + 1)) := by
  have HB : MomentKJet.Bound (MomentKJet.rescale (Real.sqrt h)
      (frozenRowsNormalizedJet β α a s h z ε j i 0 k g))
        ((M * (1 + g ^ 2) ^ 3) ^ (i.val + 1)) := by
    have H₀ := (H g i).1.norm_le 0
    have H₁ := (H g i).2.1.norm_le 0
    have H₂ := (H g i).2.2.norm_le 0
    simpa only [MomentKJet.Bound, norm_zero, add_zero, one_pow, mul_one, Real.norm_eq_abs] using
      And.intro H₀ (And.intro H₁ H₂)
  have HT := originalEpsilonKJet_weak_bound hh
    (fun k => (frozenSchedule β a (1 / 2) h k).drop (j + 1))
    (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
    (fun _ => z) (fun k => (0 : Vec3) +
      (Real.sqrt h)⁻¹ • (g • (frozenRowsHead β a h j k).2)) (i.val + 1) ε k g HB
  rw [frozenRows_original_noise hh] at HT
  exact HT

def FrozenRowsExponentialBounds {β : ℝ} (D : ScalarData β) (I : Set ℝ) : Prop :=
  ∃ h₀ A S T : ℝ, 0 < h₀ ∧ 0 ≤ A ∧ 0 ≤ S ∧ 0 ≤ T ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 11 → ∀ k ∈ frozenRowsKDomain, ∀ g : ℝ,
      let F := frozenRowsNoise β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j 0 k g -
          3 * Phi β (cdf (D.μ : Measure ℝ)) ((r - h) + 4 * h) z + A
      let m := frozenPartitionMass (cdf (D.μ : Measure ℝ) (r - h)) j
      Real.exp (-S * |g| - T * g ^ 2) ≤ Real.exp (m * F) ∧
        Real.exp (m * F) ≤ Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)

theorem scalarData_frozenRowsExponentialBounds {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    FrozenRowsExponentialBounds D (Icc l u) := by
  obtain ⟨h₀, A, S, T, hh₀, hA, hS, hT, H⟩ :=
    scalarData_frozen_suffix_centered_exponential_envelopes D hl hu
  refine ⟨h₀, A, S, T, hh₀, hA, hS, hT, ?_⟩
  intro r hr h hh hhsmall z ε hε j hj k hk g
  have hj' : j < 12 := by omega
  have ht : frozenRowsHead β (cdf (D.μ : Measure ℝ) (r - h)) h j k ::
      (frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k).drop (j + 1) <:+
        frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k := by
    rw [← frozenRows_drop _ _ _ _ j hj']
    exact List.drop_suffix _ _
  have HE := H r hr h hh hhsmall k (frozenRows_mem_domain hk) z ε hε _ _ ht g
  rw [frozenRows_head_mass _ _ _ _ j hj'] at HE
  exact HE

theorem PartitionIntegralKWeakControl.const_mul
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {U : Set ℝ} {B h : ℝ}
    (H : PartitionIntegralKWeakControl W W₁ W₂ U B h) {c : ℝ} (hc : c ≠ 0) :
    PartitionIntegralKWeakControl (fun n k g => c * W n k g)
      (fun n k g => c * W₁ n k g) (fun n k g => c * W₂ n k g) U B h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    simpa only [partitionIntegral, integral_const_mul] using mul_ne_zero hc (H.nonzero k hk)
  · intro k hk n
    exact ⟨(H.domination k hk n).1.const_mul c, (H.domination k hk n).2.const_mul c⟩
  · intro k hk n
    simpa only [partitionIntegral, integral_const_mul, mul_div_mul_left _ _ hc] using H.bounds k hk n
  · intro k hk
    simpa only [partitionIntegral, integral_const_mul, mul_div_mul_left _ _ hc] using H.normalizer k hk

private theorem nonlinearPartitionKJet_value_shift (m C : ℝ) (R : Fin 4 → MomentKJet)
    (n : Fin 4) :
    (nonlinearPartitionKJet m (fun i => (R i).add (MomentKJet.const (if i = 0 then C else 0))) n).value =
      Real.exp (m * C) * (nonlinearPartitionKJet m R n).value := by
  simp only [nonlinearPartitionKJet_value]
  fin_cases n <;>
    norm_num [MomentKJet.add, MomentKJet.const, mul_add, Real.exp_add] <;> ring1

private theorem frozenRows_weight_eq (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (hj : j < 12) (n : Fin 4) (k g : ℝ) :
    frozenPartitionWeight β α a s h z ε j n k g =
      (nonlinearPartitionKJet (frozenPartitionMass a j)
        (fun i => frozenRowsNoiseKJet β α a s h z ε j i k g) n).value := by
  rw [frozenPartitionWeight, frozenRows_drop _ _ _ _ j hj,
    ← frozenRows_head_mass β a h k j hj]
  exact epsilonPartitionWeight_eq_nonlinearPartitionKJet _ _ _ _ _ _ _ _ (fun _ => rfl) n

theorem scalarData_frozenPartitionKDerivativeWeak_of_parts {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (h₁ : FrozenRowsMixedStep D (Icc l u))
    (h₂ : FrozenRowsNoiseRegularity D (Icc l u))
    (h₃ : FrozenRowsPotentialKBounds D (Icc l u)) :
    FrozenPartitionKDerivativeWeak β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨hJ, M, hhJ, hM, HJ⟩ := h₁.envelopes
  obtain ⟨hR, hhR, HR⟩ := h₂
  obtain ⟨hP, L, hhP, hL, HP⟩ := h₃
  obtain ⟨hE, A, S, T, hhE, _, hS, hT, HE⟩ :=
    scalarData_frozenRowsExponentialBounds D hl hu
  let B := 1 + ∑ n : Fin 4, (232 * (L + 1) ^ 2 * M ^ n.val) *
    gaussianQuadraticMoment S (3 * n.val + 2) / gaussianQuadraticLower S T
  have hB : 1 ≤ B := by
    have H := Finset.sum_nonneg (s := Finset.univ) (f := fun n : Fin 4 =>
      (232 * (L + 1) ^ 2 * M ^ n.val) * gaussianQuadraticMoment S (3 * n.val + 2) /
        gaussianQuadraticLower S T) (fun n _ =>
      div_nonneg (mul_nonneg (by positivity) (gaussianQuadraticMoment_nonneg _ _))
        (gaussianQuadraticLower_pos hS hT).le)
    dsimp only [B]
    linarith
  let η := min hJ (min hR (min hP (min hE (min 1 (l / 2)))))
  have hη : 0 < η := lt_min hhJ (lt_min hhR (lt_min hhP
    (lt_min hhE (lt_min (by norm_num) (by positivity)))))
  refine ⟨B, η, 1 / 4, hB, hη, by norm_num, ?_⟩
  intro r hr h hh hhη z ε hε j hj
  have hhJ' : h ≤ hJ := hhη.trans (min_le_left _ _)
  have hrest := hhη.trans (min_le_right _ _)
  have hhR' : h ≤ hR := hrest.trans (min_le_left _ _)
  have hrest' := hrest.trans (min_le_right _ _)
  have hhP' : h ≤ hP := hrest'.trans (min_le_left _ _)
  have hrest'' := hrest'.trans (min_le_right _ _)
  have hhE' : h ≤ hE := hrest''.trans (min_le_left _ _)
  have hlast := hrest''.trans (min_le_right _ _)
  have hh₁ : h ≤ 1 := hlast.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := hlast.trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let m := frozenPartitionMass a j
  let C := 3 * Phi β α ((r - h) + 4 * h) z - A
  let R := frozenRowsNoiseKJet β α a (r - h) h z ε j
  let F := fun i k g => (R i k g).add (MomentKJet.const (if i = 0 then -C else 0))
  let J := fun n k g => nonlinearPartitionKJet m (fun i => F i k g) n
  have hFzero (k g : ℝ) : (F 0 k g).value =
      frozenRowsNoise β α a (r - h) h z ε j 0 k g -
        3 * Phi β α ((r - h) + 4 * h) z + A := by
    change frozenRowsNoise β α a (r - h) h z ε j 0 k g +
      (if (0 : Fin 4) = 0 then -C else 0) = _
    rw [ite_eq_left rfl]
    dsimp only [C]
    ring1
  have hmass := frozenSchedule_masses β a (1 / 2) h (0 : ℝ)
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hmem : frozenRowsHead β a h j 0 ∈ frozenSchedule β a (1 / 2) h 0 := by
    apply (List.drop_suffix j (frozenSchedule β a (1 / 2) h 0)).subset
    rw [frozenRows_drop _ _ _ _ j (by omega)]
    exact List.mem_cons_self
  have hm : m ∈ Icc (0 : ℝ) 1 := by
    have H := hmass _ hmem
    rw [frozenRows_head_mass β a h 0 j (by omega)] at H
    exact ⟨H.1.le, H.2⟩
  have Hreg := HR r hr h hh hhR' z ε hε j hj
  have Hgate := nonlinearPartitionKJet_integral_weak_control
    (F := F) (U := Icc (-(1 / 4) : ℝ) (1 / 4)) (V := frozenRowsKDomain)
    (m := m) (S := S) (T := T) (L := L) (M := M)
    isOpen_Ioo frozenRows_compact_sub hm hS hT hL (by linarith) hh hh₁
    (by
      intro k hk i
      exact ⟨(Hreg.1 k hk i).1.add continuous_const,
        by simpa only [F, MomentKJet.add, MomentKJet.const, add_zero] using (Hreg.1 k hk i).2.1,
        by simpa only [F, MomentKJet.add, MomentKJet.const, add_zero] using (Hreg.1 k hk i).2.2⟩)
    (by
      intro g k hk i
      exact (Hreg.2 g k hk i).add (MomentKJet.differentiates_const _ k))
    (by
      intro k hk g
      rw [hFzero]
      exact (HE r hr h hh hhE' z ε hε j hj k hk g).2)
    (by
      intro k hk g
      simpa only [F, R, MomentKJet.add, MomentKJet.const, add_zero] using
        (HP r hr h hh hhP' z ε hε j hj k hk g).1)
    (by
      intro k hk g
      simpa only [F, R, MomentKJet.add, MomentKJet.const, add_zero] using
        (HP r hr h hh hhP' z ε hε j hj k hk g).2)
    (by
      intro k hk g i
      have H := (HJ r hr h hh hhJ' z ε hε j (by omega) k hk).weak_noise hh g i
      simpa only [F, R, Fin.succ_ne_zero, ite_false, MomentKJet.add,
        MomentKJet.const, add_zero] using H)
    (by
      intro k hk g
      rw [hFzero]
      exact (HE r hr h hh hhE' z ε hε j hj k (frozenRows_compact_sub hk) g).1)
  have HC : PartitionIntegralKWeakControl (fun n k g => (J n k g).value)
      (fun n k g => (J n k g).first) (fun n k g => (J n k g).second)
      (Icc (-(1 / 4) : ℝ) (1 / 4)) B h := Hgate.2
  let c := Real.exp (m * C)
  have Hrestore := HC.const_mul (Real.exp_ne_zero (m * C))
  have heq : (fun n k g => c * (J n k g).value) =
      frozenPartitionWeight β α a (r - h) h z ε j := by
    funext n k g
    rw [frozenRows_weight_eq β α a (r - h) h z ε j (by omega) n k g]
    change Real.exp (m * C) * (nonlinearPartitionKJet m
      (fun i => (R i k g).add (MomentKJet.const (if i = 0 then -C else 0))) n).value = _
    rw [nonlinearPartitionKJet_value_shift, mul_neg, Real.exp_neg, ← mul_assoc,
      mul_inv_cancel₀ (Real.exp_ne_zero (m * C)), one_mul]
  rw [heq] at Hrestore
  exact ⟨_, _, Hrestore.domination, Hrestore.normalizer,
    fun k hk n => (Hrestore.bounds k hk n).2⟩

end SKBarriers2.Corner
