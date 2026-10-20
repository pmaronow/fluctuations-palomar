module

public import SKBarriers2.Corner.PathEnergyProof2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

section CenteredTransport

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

def secondAverageTransport (μ : Measure Ω) (g a b s t : Ω → ℝ) : ℝ :=
  (∫ x, b x ∂μ) + 2 * covariance a s μ + covariance g t μ +
    covariance g (fun x => s x ^ 2) μ -
      2 * (∫ x, s x ∂μ) * covariance g s μ

theorem secondAverageTransport_eq_moments {g a b s t : Ω → ℝ}
    (hg : MemLp g 2 μ) (ha : MemLp a 2 μ) (hb : Integrable b μ)
    (hs : MemLp s 2 μ) (ht : MemLp t 2 μ)
    (hsq : MemLp (fun x => s x ^ 2) 2 μ) :
    secondAverageTransport μ g a b s t =
      (∫ x, b x + 2 * a x * s x + g x * (t x + s x ^ 2) ∂μ) -
        2 * (∫ x, a x + g x * s x ∂μ) * (∫ x, s x ∂μ) +
        (2 * (∫ x, s x ∂μ) ^ 2 - (∫ x, t x + s x ^ 2 ∂μ)) *
          (∫ x, g x ∂μ) := by
  have ias : Integrable (fun x => a x * s x) μ := ha.integrable_mul hs
  have igs : Integrable (fun x => g x * s x) μ := hg.integrable_mul hs
  have igt : Integrable (fun x => g x * t x) μ := hg.integrable_mul ht
  have igsq : Integrable (fun x => g x * s x ^ 2) μ := hg.integrable_mul hsq
  have he (x : Ω) : g x * (t x + s x ^ 2) =
      g x * t x + g x * s x ^ 2 := by ring
  have he2 (x : Ω) : 2 * a x * s x = 2 * (a x * s x) := by ring
  simp_rw [he, he2]
  rw [
    integral_add (f := fun x => b x + 2 * (a x * s x))
      (g := fun x => g x * t x + g x * s x ^ 2)
      (hb.add (ias.const_mul 2)) (igt.add igsq),
    integral_add (f := b) (g := fun x => 2 * (a x * s x)) hb (ias.const_mul 2),
    integral_const_mul,
    integral_add igt igsq, integral_add (ha.integrable (by norm_num)) igs,
    integral_add (ht.integrable (by norm_num)) (hsq.integrable (by norm_num))]
  unfold secondAverageTransport
  rw [covariance_eq_sub ha hs, covariance_eq_sub hg ht,
    covariance_eq_sub hg hsq, covariance_eq_sub hg hs]
  simp only [Pi.mul_apply]
  ring

theorem secondAverageTransport_add_constants {g a b s t : Ω → ℝ}
    (hg : MemLp g 2 μ) (_ha : MemLp a 2 μ) (hs : MemLp s 2 μ)
    (ht : MemLp t 2 μ) (hsq : MemLp (fun x => s x ^ 2) 2 μ)
    (c d : ℝ) :
    secondAverageTransport μ g a b (fun x => s x + c) (fun x => t x + d) =
      secondAverageTransport μ g a b s t := by
  have hi : Integrable s μ := hs.integrable (by norm_num)
  have hsqeq : (fun x => (s x + c) ^ 2) =
      fun x => (s x ^ 2 + (2 * c) * s x) + c ^ 2 := by funext x; ring
  have hcov : covariance g (fun x => (s x + c) ^ 2) μ =
      covariance g (fun x => s x ^ 2) μ + (2 * c) * covariance g s μ := by
    rw [hsqeq, covariance_add_const_right (Y := fun x => s x ^ 2 + (2 * c) * s x)
      ((hsq.integrable (by norm_num)).add (hi.const_mul (2 * c)))]
    change covariance g ((fun x => s x ^ 2) + (fun x => (2 * c) * s x)) μ = _
    rw [covariance_add_right hg hsq (hs.const_mul (2 * c)), covariance_const_mul_right]
  unfold secondAverageTransport
  rw [covariance_add_const_right hi,
    covariance_add_const_right (ht.integrable (by norm_num)), hcov,
    integral_add hi (integrable_const c), integral_const]
  simp only [probReal_univ]
  rw [covariance_add_const_right hi]
  ring

end CenteredTransport

section NoiseEnvelopes

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem abs_integral_le_noise_moment {f : ℝ → ℝ} {A M : ℝ} {p : ℕ}
    (hi : Integrable (fun x : ℝ => |x| ^ p) μ) (hA : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A * |x| ^ p)
    (hM : (∫ x : ℝ, |x| ^ p ∂μ) ≤ M) :
    |∫ x, f x ∂μ| ≤ A * M := by
  calc
    _ ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, A * |x| ^ p ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun x => abs_nonneg _))
        (hi.const_mul A) (ae_of_all _ hf)
    _ = A * (∫ x : ℝ, |x| ^ p ∂μ) := integral_const_mul _ _
    _ ≤ A * M := mul_le_mul_of_nonneg_left hM hA

theorem abs_covariance_le_noise_moments {f g : ℝ → ℝ}
    {A B Mp Mq Mpq : ℝ} {p q : ℕ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpf : ∀ x, |f x| ≤ A * |x| ^ p)
    (hqg : ∀ x, |g x| ≤ B * |x| ^ q)
    (hip : Integrable (fun x : ℝ => |x| ^ p) μ)
    (hiq : Integrable (fun x : ℝ => |x| ^ q) μ)
    (hipq : Integrable (fun x : ℝ => |x| ^ (p + q)) μ)
    (hMp : (∫ x : ℝ, |x| ^ p ∂μ) ≤ Mp)
    (hMq : (∫ x : ℝ, |x| ^ q ∂μ) ≤ Mq)
    (hMpq : (∫ x : ℝ, |x| ^ (p + q) ∂μ) ≤ Mpq) :
    |covariance f g μ| ≤ A * B * (Mpq + Mp * Mq) := by
  have hp0 : 0 ≤ Mp := (integral_nonneg (fun _ => by positivity)).trans hMp
  have hq0 : 0 ≤ Mq := (integral_nonneg (fun _ => by positivity)).trans hMq
  have hprod : ∀ x, |f x * g x| ≤ (A * B) * |x| ^ (p + q) := by
    intro x
    rw [abs_mul, pow_add]
    exact (mul_le_mul (hpf x) (hqg x) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have h0 := abs_integral_le_noise_moment hip hA hpf hMp
  have h1 := abs_integral_le_noise_moment hiq hB hqg hMq
  have h2 := abs_integral_le_noise_moment hipq (mul_nonneg hA hB) hprod hMpq
  rw [covariance_eq_sub hf hg]
  simp only [Pi.mul_apply]
  calc
    _ ≤ |∫ x, f x * g x ∂μ| + |(∫ x, f x ∂μ) * (∫ x, g x ∂μ)| := abs_sub _ _
    _ ≤ (A * B) * Mpq + (A * Mp) * (B * Mq) := by
      apply add_le_add h2
      rw [abs_mul]
      exact mul_le_mul h0 h1 (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem abs_secondAverageTransport_le {g a b s t₁ t₂ : ℝ → ℝ}
    {C G A S T U H M₁ M₂ M₃ : ℝ} {g₀ a₀ : ℝ}
    (hg : MemLp g 2 μ) (ha : MemLp a 2 μ) (hs : MemLp s 2 μ)
    (ht₁ : MemLp t₁ 2 μ) (ht₂ : MemLp t₂ 2 μ)
    (hsq : MemLp (fun x => s x ^ 2) 2 μ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hg0 : ∀ x, |g x| ≤ C) (hgc : ∀ x, |g x - g₀| ≤ G * |x|)
    (hac : ∀ x, |a x - a₀| ≤ A * |x|) (hsc : ∀ x, |s x| ≤ S * |x|)
    (ht1 : ∀ x, |t₁ x| ≤ T * |x|) (ht2 : ∀ x, |t₂ x| ≤ U * |x| ^ 2)
    (hi₁ : Integrable (fun x : ℝ => |x|) μ)
    (hi₂ : Integrable (fun x : ℝ => |x| ^ 2) μ)
    (hi₃ : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hm₁ : (∫ x : ℝ, |x| ∂μ) ≤ M₁)
    (hm₂ : (∫ x : ℝ, |x| ^ 2 ∂μ) ≤ M₂)
    (hm₃ : (∫ x : ℝ, |x| ^ 3 ∂μ) ≤ M₃)
    (hb : |∫ x, b x ∂μ| ≤ H) :
    |secondAverageTransport μ g a b s (fun x => t₁ x + t₂ x)| ≤
      H + 2 * A * S * (M₂ + M₁ ^ 2) + G * T * (M₂ + M₁ ^ 2) +
        G * U * (M₃ + M₁ * M₂) + 2 * C * S ^ 2 * M₂ +
          4 * C * S ^ 2 * M₁ ^ 2 := by
  have hM₁ : 0 ≤ M₁ := (integral_nonneg (fun _ => abs_nonneg _)).trans hm₁
  have hM₂ : 0 ≤ M₂ := (integral_nonneg (fun _ => sq_nonneg _)).trans hm₂
  have hi0 : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hm0 : (∫ _ : ℝ, (1 : ℝ) ∂μ) ≤ 1 := by simp
  have hca := abs_covariance_le_noise_moments (p := 1) (q := 1)
    (ha.sub (memLp_const a₀)) hs hA hS
    (by simpa only [pow_one, Pi.sub_apply] using hac) (by simpa only [pow_one] using hsc)
    (by simpa only [pow_one] using hi₁) (by simpa only [pow_one] using hi₁)
    hi₂ (by simpa only [pow_one] using hm₁) (by simpa only [pow_one] using hm₁) hm₂
  rw [covariance_sub_left ha (memLp_const a₀) hs, covariance_const_left, sub_zero] at hca
  have hct₁ := abs_covariance_le_noise_moments (p := 1) (q := 1)
    (hg.sub (memLp_const g₀)) ht₁ hG hT
    (by simpa only [pow_one, Pi.sub_apply] using hgc) (by simpa only [pow_one] using ht1)
    (by simpa only [pow_one] using hi₁) (by simpa only [pow_one] using hi₁)
    hi₂ (by simpa only [pow_one] using hm₁) (by simpa only [pow_one] using hm₁) hm₂
  rw [covariance_sub_left hg (memLp_const g₀) ht₁, covariance_const_left, sub_zero] at hct₁
  have hct₂ := abs_covariance_le_noise_moments (p := 1) (q := 2)
    (hg.sub (memLp_const g₀)) ht₂ hG hU
    (by simpa only [pow_one, Pi.sub_apply] using hgc) ht2
    (by simpa only [pow_one] using hi₁) hi₂ hi₃
    (by simpa only [pow_one] using hm₁) hm₂ hm₃
  rw [covariance_sub_left hg (memLp_const g₀) ht₂, covariance_const_left, sub_zero] at hct₂
  have hsqbound (x : ℝ) : |s x ^ 2| ≤ S ^ 2 * |x| ^ 2 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hsc x) 2).trans_eq (by ring)
  have hcq := abs_covariance_le_noise_moments hg hsq hC (sq_nonneg S)
    (p := 0) (q := 2) (by simpa only [pow_zero, mul_one] using hg0) hsqbound
    (by simpa only [pow_zero] using hi0) hi₂ hi₂
    (by simpa only [pow_zero] using hm0) hm₂ hm₂
  have hcs := abs_covariance_le_noise_moments hg hs hC hS
    (p := 0) (q := 1) (by simpa only [pow_zero, mul_one] using hg0)
    (by simpa only [pow_one] using hsc)
    (by simpa only [pow_zero] using hi0) (by simpa only [pow_one] using hi₁)
    (by simpa only [Nat.zero_add, pow_one] using hi₁)
    (by simpa only [pow_zero] using hm0) (by simpa only [pow_one] using hm₁)
    (by simpa only [Nat.zero_add, pow_one] using hm₁)
  have hmean := abs_integral_le_noise_moment (p := 1)
    (by simpa only [pow_one] using hi₁) hS
    (by simpa only [pow_one] using hsc) (by simpa only [pow_one] using hm₁)
  have hlast : |2 * (∫ x, s x ∂μ) * covariance g s μ| ≤
      4 * C * S ^ 2 * M₁ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hmean (by norm_num)) hcs
      (abs_nonneg _) (by positivity)).trans_eq (by ring)
  unfold secondAverageTransport
  rw [show (fun x => t₁ x + t₂ x) = t₁ + t₂ from rfl,
    covariance_add_right hg ht₁ ht₂]
  simp only [← add_assoc]
  have htri (u v w x y z : ℝ) :
      |u + v + w + x + y - z| ≤ |u| + |v| + |w| + |x| + |y| + |z| := by
    exact (abs_sub _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)
  have htwo : |2 * covariance a s μ| ≤ 2 * (A * S * (M₂ + M₁ * M₁)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hca (by norm_num)
  exact (htri _ _ _ _ _ _).trans ((add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add hb htwo) hct₁) hct₂) hcq)
    hlast).trans_eq (by ring))

end NoiseEnvelopes

def secondAverageTransportCoefficient (R M₁ M₂ M₃ : ℝ) : ℝ :=
  R + 3 * R * (M₂ + M₁ ^ 2) + R * (M₃ + M₁ * M₂) +
    2 * R ^ 2 * M₂ + 4 * R ^ 2 * M₁ ^ 2

theorem secondAverageTransport_budget_le {C D G A S T U R d H M₁ M₂ M₃ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (_hG : 0 ≤ G) (_hA : 0 ≤ A)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hU : 0 ≤ U) (hR : 0 ≤ R)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hGb : G ≤ C * d) (hAb : A ≤ (C + D) * d)
    (hSb : S ≤ R * d) (hTb : T ≤ R * d) (hUb : U ≤ R * d ^ 2) :
    (H + R * (C + D) * d ^ 2) + 2 * A * S * (M₂ + M₁ ^ 2) +
        G * T * (M₂ + M₁ ^ 2) + G * U * (M₃ + M₁ * M₂) +
        2 * C * S ^ 2 * M₂ + 4 * C * S ^ 2 * M₁ ^ 2 ≤
      H + secondAverageTransportCoefficient R M₁ M₂ M₃ * (C + D) * d ^ 2 := by
  have hCD : C ≤ C + D := le_add_of_nonneg_right hD
  have hGb' : G ≤ (C + D) * d :=
    hGb.trans (mul_le_mul_of_nonneg_right hCD hd)
  have h0 : 2 * A * S * (M₂ + M₁ ^ 2) ≤
      2 * ((C + D) * d) * (R * d) * (M₂ + M₁ ^ 2) := by gcongr
  have h1 : G * T * (M₂ + M₁ ^ 2) ≤
      ((C + D) * d) * (R * d) * (M₂ + M₁ ^ 2) := by gcongr
  have h2 : G * U * (M₃ + M₁ * M₂) ≤
      (C + D) * R * d ^ 2 * (M₃ + M₁ * M₂) := by
    calc
      _ ≤ ((C + D) * d) * (R * d ^ 2) * (M₃ + M₁ * M₂) := by gcongr
      _ = ((C + D) * R * d ^ 2 * (M₃ + M₁ * M₂)) * d := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hd1
  have h3 : 2 * C * S ^ 2 * M₂ ≤ 2 * (C + D) * (R * d) ^ 2 * M₂ := by gcongr
  have h4 : 4 * C * S ^ 2 * M₁ ^ 2 ≤ 4 * (C + D) * (R * d) ^ 2 * M₁ ^ 2 := by gcongr
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl h0) h1) h2) h3)
    h4).trans_eq (by unfold secondAverageTransportCoefficient; ring)

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

section ThreeLevelGronwall

variable {ι : Type}

private theorem pathEnergy_variationEnergy_tail_le {e : ι → ℝ} {l front tail : List ι}
    (he : ∀ p ∈ l, 0 ≤ e p) (hsplit : l = front ++ tail) :
    variationEnergy e tail ≤ variationEnergy e l := by
  have hf := variationEnergy_nonneg
    (fun p hp => he p (hsplit.symm ▸ List.mem_append_left tail hp))
  rw [hsplit, variationEnergy_append]
  linarith only [hf]

theorem pathEnergy_three_level_recursion_le {e : ι → ℝ} {K D : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (a b c : List ι → ℝ) (l : List ι)
    (he : ∀ p ∈ l, 0 ≤ e p)
    (ha0 : a [] ≤ 0) (hb0 : b [] ≤ 0) (hc0 : c [] ≤ 0)
    (hvalue : ∀ front p tail, l = front ++ p :: tail →
      a (p :: tail) ≤ (1 + K * e p) * a tail + D * e p)
    (hfirst : ∀ front p tail, l = front ++ p :: tail →
      b (p :: tail) ≤ (1 + K * e p) * b tail + K * e p * a tail + D * e p)
    (hsecond : ∀ front p tail, l = front ++ p :: tail →
      c (p :: tail) ≤ (1 + K * e p) * c tail +
        K * e p * (a tail + b tail) + D * e p)
    (hsmall : 2 * K * variationEnergy e l ≤ 1) :
    a l ≤ 2 * D * variationEnergy e l ∧
      b l ≤ 4 * D * variationEnergy e l ∧
        c l ≤ 8 * D * variationEnergy e l := by
  have htail (front : List ι) (p : ι) (tail : List ι)
      (hsplit : l = front ++ p :: tail) : l = (front ++ [p]) ++ tail := by
    simpa only [List.append_assoc, List.singleton_append] using hsplit
  have ha (front tail : List ι) (hsplit : l = front ++ tail) :
      K * a tail ≤ D := by
    have ha := variation_recursion_tail_le hK hD a l he ha0 hvalue hsmall front tail hsplit
    have hE := pathEnergy_variationEnergy_tail_le he hsplit
    have hshort : 2 * K * variationEnergy e tail ≤ 1 :=
      (mul_le_mul_of_nonneg_left hE (by positivity)).trans hsmall
    calc
      K * a tail ≤ K * (2 * D * variationEnergy e tail) :=
        mul_le_mul_of_nonneg_left ha hK
      _ = D * (2 * K * variationEnergy e tail) := by ring
      _ ≤ D := mul_le_of_le_one_right hD hshort
  have hfirst' : ∀ front p tail, l = front ++ p :: tail →
      b (p :: tail) ≤ (1 + K * e p) * b tail + (2 * D) * e p := by
    intro front p tail hsplit
    have hp := he p (hsplit.symm ▸ List.mem_append_right front (List.mem_cons_self ..))
    have H := mul_le_mul_of_nonneg_right (ha (front ++ [p]) tail (htail front p tail hsplit)) hp
    exact (hfirst front p tail hsplit).trans (by nlinarith only [H])
  have hb (front tail : List ι) (hsplit : l = front ++ tail) :
      K * b tail ≤ 2 * D := by
    have hb := variation_recursion_tail_le hK (show 0 ≤ 2 * D by positivity)
      b l he hb0 hfirst' hsmall front tail hsplit
    have hE := pathEnergy_variationEnergy_tail_le he hsplit
    have hshort : 2 * K * variationEnergy e tail ≤ 1 :=
      (mul_le_mul_of_nonneg_left hE (by positivity)).trans hsmall
    calc
      K * b tail ≤ K * (2 * (2 * D) * variationEnergy e tail) :=
        mul_le_mul_of_nonneg_left hb hK
      _ = (2 * D) * (2 * K * variationEnergy e tail) := by ring
      _ ≤ 2 * D := mul_le_of_le_one_right (by positivity) hshort
  have hsecond' : ∀ front p tail, l = front ++ p :: tail →
      c (p :: tail) ≤ (1 + K * e p) * c tail + (4 * D) * e p := by
    intro front p tail hsplit
    have hp := he p (hsplit.symm ▸ List.mem_append_right front (List.mem_cons_self ..))
    have hsplit' := htail front p tail hsplit
    have H := mul_le_mul_of_nonneg_right
      (add_le_add (ha (front ++ [p]) tail hsplit') (hb (front ++ [p]) tail hsplit')) hp
    exact (hsecond front p tail hsplit).trans (by nlinarith only [H])
  refine ⟨variation_recursion_le hK hD a l he ha0 hvalue hsmall, ?_, ?_⟩
  · have H := variation_recursion_le hK (show 0 ≤ 2 * D by positivity)
      b l he hb0 hfirst' hsmall
    convert H using 1; ring
  · have H := variation_recursion_le hK (show 0 ≤ 4 * D by positivity)
      c l he hc0 hsecond' hsmall
    convert H using 1; ring

end ThreeLevelGronwall

theorem scalarData_window_three_level_transport {β : ℝ} (D : ScalarData β)
    {l u K : ℝ} (hl : 0 < l) (hu : u < D.q) (hK : 0 ≤ K) :
    ∃ A h0 : ℝ, 0 < A ∧ 0 < h0 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ k : ℝ, |k| ≤ 1 / 2 →
      let α := cdf (D.μ : Measure ℝ)
      let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
      let e := windowVariationEnergy k
      ∀ B : ℝ, 0 ≤ B → ∀ a b c : List (ℝ → ℝ × (Fin 3 → ℝ)) → ℝ,
      a [] ≤ 0 → b [] ≤ 0 → c [] ≤ 0 →
      (∀ front p tail, ps = front ++ p :: tail →
        a (p :: tail) ≤ (1 + K * e p) * a tail + B * e p) →
      (∀ front p tail, ps = front ++ p :: tail →
        b (p :: tail) ≤ (1 + K * e p) * b tail + K * e p * a tail + B * e p) →
      (∀ front p tail, ps = front ++ p :: tail →
        c (p :: tail) ≤ (1 + K * e p) * c tail +
          K * e p * (a tail + b tail) + B * e p) →
      a ps ≤ 2 * A * B * h ∧ b ps ≤ 4 * A * B * h ∧ c ps ≤ 8 * A * B * h := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,hA,_,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    have hden : 0 < 2 * K * A + 1 := by positivity
    refine ⟨A, min hV (1 / (2 * K * A + 1)), hA, lt_min hhV (by positivity), ?_⟩
    intro r hr h hh hh0 N hN lam hlam k hk
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let e := windowVariationEnergy k
    have hE : variationEnergy e ps ≤ A * h :=
      (hvar r hr h hh (hh0.trans (min_le_left _ _)) N hN lam hlam k hk).1
    have hshort : 2 * K * variationEnergy e ps ≤ 1 := by
      have H := (le_div_iff₀ hden).mp (hh0.trans (min_le_right _ _))
      have HE := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2 * K by positivity)
      nlinarith only [H, HE, hh.le]
    intro B hB a b c ha0 hb0 hc0 hvalue hfirst hsecond
    obtain ⟨ha,hb,hc⟩ := pathEnergy_three_level_recursion_le hK hB a b c ps
      (fun p _ => windowVariationEnergy_nonneg k p) ha0 hb0 hc0 hvalue hfirst hsecond hshort
    refine ⟨ha.trans ?_, hb.trans ?_, hc.trans ?_⟩
    · exact (mul_le_mul_of_nonneg_left hE (show 0 ≤ 2 * B by positivity)).trans_eq (by ring)
    · exact (mul_le_mul_of_nonneg_left hE (show 0 ≤ 4 * B by positivity)).trans_eq (by ring)
    · exact (mul_le_mul_of_nonneg_left hE (show 0 ≤ 8 * B by positivity)).trans_eq (by ring)
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner

namespace SKBarriers2.ParamChain

section CenteredAverageFormula

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

local instance : NormedAddCommGroup (P × (X × ℝ) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × (X × ℝ) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup
    (P × (X × ℝ) →L[ℝ] P × (X × ℝ) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ
    (P × (X × ℝ) →L[ℝ] P × (X × ℝ) →L[ℝ] ℝ) := inferInstance

private theorem transport_memLp_two {H W : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hW : ParamExpGrowth W) (hc : Continuous W)
    (q : P) (x : X) :
    MemLp (fun t => W (q,(x,t))) 2
      (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))) (q,x)) := by
  rw [memLp_two_iff_integrable_sq]
  · simpa only [pow_two] using
      (hW.mul hW).integrable_paramStepLaw hH (hc.mul hc) 1 (q,x)
  · exact (hc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).aestronglyMeasurable

private theorem transport_first_growth {W : P × (X × ℝ) → ℝ}
    (hW : ParamSmooth W) (u : P) :
    ParamExpGrowth (fun z => fderiv ℝ W z (u,0)) ∧
      Continuous (fun z => fderiv ℝ W z (u,0)) := by
  exact ⟨hW.2.2.1.clm (ContinuousLinearMap.apply ℝ ℝ (u,0)),
    (hW.1.fderiv_right (m := 1) (by norm_num)).continuous.clm_apply continuous_const⟩

private theorem transport_second_growth {W : P × (X × ℝ) → ℝ}
    (hW : ParamSmooth W) (u b : P) :
    ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ W) z (u,0) (u,0) +
        fderiv ℝ W z (b,0)) ∧
      Continuous (fun z => fderiv ℝ (fderiv ℝ W) z (u,0) (u,0) +
        fderiv ℝ W z (b,0)) := by
  have hg := (hW.2.2.2.clm
    (ContinuousLinearMap.apply ℝ (P × (X × ℝ) →L[ℝ] ℝ) (u,0))).clm
      (ContinuousLinearMap.apply ℝ ℝ (u,0))
  have hc : Continuous (fun z : P × (X × ℝ) =>
      fderiv ℝ (fderiv ℝ W) z (u,0) (u,0)) :=
    ((hW.1.fderiv_right (m := 1) (by norm_num) |>.fderiv_right
      (m := 0) (by norm_num)).continuous.clm_apply continuous_const).clm_apply continuous_const
  exact ⟨hg.add (transport_first_growth hW b).1,
    hc.add (transport_first_growth hW b).2⟩

theorem gaussianAverage_curve_second_covariance {H G : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) :
    let U : (P × X) × ℝ → ℝ := fun z => H (z.1.1,(z.1.2,z.2))
    let J : (P × X) × ℝ → ℝ := fun z => G (z.1.1,(z.1.2,z.2))
    let μ := gaussianStepLaw 1 U (p k,x)
    let g := fun t => G (p k,(x,t))
    let a := fun t => deriv (fun q => G (p q,(x,t))) k
    let b := fun t => deriv (deriv (fun q => G (p q,(x,t)))) k
    let s := fun t => deriv (fun q => H (p q,(x,t))) k
    let t := fun t => deriv (deriv (fun q => H (p q,(x,t)))) k
    ContDiffAt ℝ 2 (fun q => OAI.SK.Analytic.gaussianAverage 1 U J (p q,x)) k ∧
      deriv (deriv (fun q => OAI.SK.Analytic.gaussianAverage 1 U J (p q,x))) k =
        StepCalculus.secondAverageTransport μ g a b s t := by
  dsimp only
  let μ := gaussianStepLaw 1
    (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))) (p k,x)
  have hexp := (hH.2.1.exp_mul 1).weakLocallyDominated.integrable_section
    (Real.continuous_exp.comp (continuous_const.mul (hH.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))))) (p k,x)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hexp
  have hfirst {W : P × (X × ℝ) → ℝ} (hW : ParamSmooth W) (t : ℝ) :
      deriv (fun q => W (p q,(x,t))) k =
        fderiv ℝ W (p k,(x,t)) (deriv p k,0) :=
    ((hW.1.differentiable (by norm_num) (p k,(x,t))).hasFDerivAt.comp_hasDerivAt k
      ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k (x,t)))).deriv
  have hsecond {W : P × (X × ℝ) → ℝ} (hW : ParamSmooth W) (t : ℝ) :
      deriv (deriv (fun q => W (p q,(x,t)))) k =
        fderiv ℝ (fderiv ℝ W) (p k,(x,t)) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ W (p k,(x,t)) (deriv (deriv p) k,0) :=
    second_parameter_curve hW.1 hp (x,t)
  have hH' := hH.toSmooth
  obtain ⟨hg1,hc1⟩ := transport_first_growth hG (deriv p k)
  obtain ⟨hg2,hc2⟩ := transport_second_growth hG (deriv p k) (deriv (deriv p) k)
  obtain ⟨hs1,hsc1⟩ := transport_first_growth hH' (deriv p k)
  obtain ⟨hs2,hsc2⟩ := transport_second_growth hH' (deriv p k) (deriv (deriv p) k)
  have hgm := transport_memLp_two hH hG.2.1 hG.1.continuous (p k) x
  have ham := transport_memLp_two hH hg1 hc1 (p k) x
  have hbm := transport_memLp_two hH hg2 hc2 (p k) x
  have hsm := transport_memLp_two hH hs1 hsc1 (p k) x
  have htm := transport_memLp_two hH hs2 hsc2 (p k) x
  have hssm := transport_memLp_two hH (hs1.mul hs1) (hsc1.mul hsc1) (p k) x
  have hnorm := gaussianAverage_curve_second hH hG hp x
  dsimp only at hnorm
  refine ⟨hnorm.1, ?_⟩
  rw [hnorm.2]
  simp_rw [hfirst hG, hfirst hH', hsecond hG, hsecond hH']
  symm
  apply StepCalculus.secondAverageTransport_eq_moments hgm ham
    (hbm.integrable (by norm_num)) hsm htm
  simpa only [pow_two] using hssm

end CenteredAverageFormula

end SKBarriers2.ParamChain

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def firstAverageScore (m dm : ℝ) (v w : E) (f f₁ : E → ℝ) (x : E) (t : ℝ) : ℝ :=
  dm * (f (x+t • v)-f x) +
    m * (f₁ (x+t • v)-f₁ x+t*fderiv ℝ f (x+t • v) w)

def secondAverageScoreLinear (m dm ddm : ℝ) (v w b : E)
    (f f₁ f₂ : E → ℝ) (x : E) (t : ℝ) : ℝ :=
  ddm * (f (x+t • v)-f x) +
    2 * dm * (f₁ (x+t • v)-f₁ x+t*fderiv ℝ f (x+t • v) w) +
    m * (f₂ (x+t • v)-f₂ x+2*(t*fderiv ℝ f₁ (x+t • v) w)+
      t*fderiv ℝ f (x+t • v) b)

def secondAverageScoreQuadratic (m : ℝ) (v w : E) (f : E → ℝ) (x : E) (t : ℝ) : ℝ :=
  m * t^2 * fderiv ℝ (fderiv ℝ f) (x+t • v) w w

private theorem transport_increment_le {r : ℕ} {B d : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 1 ≤ r) {v : E} (hv : ‖v‖ ≤ d) (x : E) (t : ℝ) :
    |f (x+t • v)-f x| ≤ B*d*|t| := by
  have H := (hf.lipschitzWith hr).dist_le_mul (x+t • v) x
  change dist (f (x+t • v)) (f x) ≤ B*dist (x+t • v) x at H
  have H' : |f (x+t • v)-f x| ≤ B*‖v‖*|t| := by
    simpa only [dist_eq_norm,Real.norm_eq_abs,add_sub_cancel_left,norm_smul,
      mul_comm,mul_left_comm,mul_assoc] using H
  exact H'.trans (by have hB := hf.nonneg; gcongr)

private theorem transport_direction_le {r : ℕ} {B d : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 1 ≤ r) {w : E} (hw : ‖w‖ ≤ d) (y : E) (t : ℝ) :
    |t*fderiv ℝ f y w| ≤ B*d*|t| := by
  rw [abs_mul]
  have hB := hf.nonneg
  calc
    _ ≤ |t| * (B*‖w‖) := mul_le_mul_of_nonneg_left (hf.directional_le hr y w) (abs_nonneg t)
    _ = B*‖w‖*|t| := by ring
    _ ≤ B*d*|t| := by gcongr

private theorem transport_weight_le {a x X : ℝ} (ha : |a| ≤ 1) (hx : |x| ≤ X) :
    |a*x| ≤ X := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right ha (abs_nonneg x)).trans (by simpa using hx)

theorem averageScore_envelopes {B A H d m dm ddm : ℝ} {f f₁ f₂ : E → ℝ}
    (hf : QPotential 3 B f) (hf₁ : QBoundedJets 1 A f₁) (hf₂ : QBoundedJets 1 H f₂)
    (hm : m ∈ Icc (0 : ℝ) 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (hd : 0 ≤ d) (v w b : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d)
    (x : E) (t : ℝ) :
    |firstAverageScore m dm v w f f₁ x t| ≤ (2*B+A)*d*|t| ∧
      |secondAverageScoreLinear m dm ddm v w b f f₁ f₂ x t| ≤ (4*B+4*A+H)*d*|t| ∧
        |secondAverageScoreQuadratic m v w f x t| ≤ B*d^2*|t|^2 := by
  have hB := hf.nonneg
  have hA := hf₁.nonneg
  have hH := hf₂.nonneg
  have hmabs : |m| ≤ 1 := by rw [abs_of_nonneg hm.1]; exact hm.2
  have hdf := transport_increment_le hf (by norm_num) hv x t
  have hdf₁ := transport_increment_le (qBoundedJets_iff_qBddSmooth.mp hf₁).potential
    le_rfl hv x t
  have hdf₂ := transport_increment_le (qBoundedJets_iff_qBddSmooth.mp hf₂).potential
    le_rfl hv x t
  have hdw := transport_direction_le hf (by norm_num) hw (x+t • v) t
  have hdb := transport_direction_le hf (by norm_num) hb (x+t • v) t
  have hgw := transport_direction_le (qBoundedJets_iff_qBddSmooth.mp hf₁).potential
    le_rfl hw (x+t • v) t
  have hsum : |f₁ (x+t • v)-f₁ x+t*fderiv ℝ f (x+t • v) w| ≤ (A+B)*d*|t| :=
    (abs_add_le _ _).trans ((add_le_add hdf₁ hdw).trans_eq (by ring))
  have hsum₂ : |f₂ (x+t • v)-f₂ x+2*(t*fderiv ℝ f₁ (x+t • v) w)+
      t*fderiv ℝ f (x+t • v) b| ≤ (H+2*A+B)*d*|t| := by
    have htwo : |2*(t*fderiv ℝ f₁ (x+t • v) w)| ≤ 2*(A*d*|t|) := by
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left hgw (by norm_num)
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      ((add_le_add (add_le_add hdf₂ htwo) hdb).trans_eq (by ring))
  refine ⟨?_, ?_, ?_⟩
  · unfold firstAverageScore
    exact (abs_add_le _ _).trans ((add_le_add (transport_weight_le hdm hdf)
      (transport_weight_le hmabs hsum)).trans_eq (by ring))
  · unfold secondAverageScoreLinear
    have htwo : |2*dm*(f₁ (x+t • v)-f₁ x+t*fderiv ℝ f (x+t • v) w)| ≤
        2*((A+B)*d*|t|) := by
      rw [mul_assoc,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left (transport_weight_le hdm hsum) (by norm_num)
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      ((add_le_add (add_le_add (transport_weight_le hddm hdf) htwo)
        (transport_weight_le hmabs hsum₂)).trans_eq (by ring))
  · have hhess := (hf.derivativeJets.derivativeJets.apply_const w).apply_const w
    have hbound : |fderiv ℝ (fderiv ℝ f) (x+t • v) w w| ≤ B*d^2 := by
      have H := hhess.norm_le (x+t • v)
      simp only [Real.norm_eq_abs] at H
      calc
        _ ≤ B*‖w‖*‖w‖ := H
        _ ≤ B*d*d := by gcongr
        _ = B*d^2 := by ring
    unfold secondAverageScoreQuadratic
    rw [mul_assoc]
    apply transport_weight_le hmabs
    rw [abs_mul,abs_pow]
    exact (mul_le_mul_of_nonneg_left hbound (sq_nonneg _)).trans_eq (by ring)

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem pathEnergy_window_direction_bound (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
        ‖(p k).2‖ ≤ L*Real.sqrt (h/(N:ℝ)) ∧
        ‖deriv (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N:ℝ)) ∧
        ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ L*Real.sqrt (h/(N:ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (hbound β h hh N i k hk).2

theorem scalarData_window_averageScore_envelopes {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ K h0 kap : ℝ, 0 ≤ K ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      ∀ x : E, ∀ t : ℝ,
      let α := cdf (D.μ : Measure ℝ)
      let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
      let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
      let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
      let dm := deriv (fun q => (p q).1) k
      let ddm := deriv (deriv (fun q => (p q).1)) k
      let w := deriv (fun q => (p q).2) k
      let b := deriv (deriv (fun q => (p q).2)) k
      |firstAverageScore (p k).1 dm (p k).2 w F (G 1) x t| ≤
          K*Real.sqrt (h/(N:ℝ))*|t| ∧
        |secondAverageScoreLinear (p k).1 dm ddm (p k).2 w b F (G 1) (G 2) x t| ≤
          K*Real.sqrt (h/(N:ℝ))*|t| ∧
        |secondAverageScoreQuadratic (p k).1 (p k).2 w F x t| ≤
          K*(h/(N:ℝ))*|t|^2 := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,_,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨R,hJ,hR,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    obtain ⟨L,hL,hdir⟩ := pathEnergy_window_direction_bound β
    let K := (4*B+5*R)*L+B*L^2
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hcoef : (4*B+5*R)*L ≤ K := by
      dsimp only [K]
      exact le_add_of_nonneg_right (by positivity)
    have hcoef₁ : (2*B+R)*L ≤ K := by
      exact (mul_le_mul_of_nonneg_right (by linarith : 2*B+R ≤ 4*B+5*R) hL).trans hcoef
    have hcoef₂ : B*L^2 ≤ K := by
      dsimp only [K]
      exact le_add_of_nonneg_left (by positivity)
    refine ⟨K,min hV (min hJ (min hE 1)),min kapE (1/2),hK,
      lt_min hhV (lt_min hhJ (lt_min hhE (by norm_num))),lt_min hkapE (by norm_num),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk x t
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
    let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
    have hhV' := hh0.trans (min_le_left _ _)
    have hhJ' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhE' := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hkhalf := hk.trans (min_le_right _ _)
    have hp : p ∈ windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N :=
      orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hinputs := (hvar r hr h hh hhV' N hN lam hlam k hkhalf).2 p hp
    have hds := hdir _ _ _ hh.le N p hp k hkhalf
    obtain ⟨hG1,hG2⟩ := hjets r hr h hh hhJ' N hN lam hlam j k hkhalf
    have hRG : R*h ≤ R := mul_le_of_le_one_right hR.le hh1
    have hg : QBoundedJets 1 R (G 1) := (hG1.of_le (by norm_num : 1 ≤ 6)).mono hRG
    have hq : QBoundedJets 1 R (G 2) := (hG2.of_le (by norm_num : 1 ≤ 4)).mono hRG
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k (hk.trans (min_le_left _ _)) N hN
    obtain ⟨hinner,_⟩ := hEN lam hlam
    have hf : QPotential 3 B F := by
      simpa only [F,orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner j.val (by rw [windowMassPath_length]; exact j.isLt)).of_le (by norm_num : 3 ≤ 10)
    have H := averageScore_envelopes hf hg hq
      ⟨ha0.le.trans hinputs.2.1.1,hinputs.2.1.2⟩ hinputs.2.2.1 hinputs.2.2.2
      (show 0 ≤ L*Real.sqrt (h/(N:ℝ)) by positivity)
      (p k).2 (deriv (fun q => (p q).2) k) (deriv (deriv (fun q => (p q).2)) k)
      hds.1 hds.2.1 hds.2.2 x t
    refine ⟨H.1.trans ?_,H.2.1.trans ?_,H.2.2.trans ?_⟩
    · have HC := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef₁ (Real.sqrt_nonneg (h/(N:ℝ)))) (abs_nonneg t)
      convert HC using 1; ring
    · have HC := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (h/(N:ℝ)))) (abs_nonneg t)
      convert HC using 1; ring
    · rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))]
      have HC := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef₂ (div_nonneg hh.le (Nat.cast_nonneg N))) (sq_nonneg |t|)
      convert HC using 1; ring
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner

namespace SKBarriers2.StepCalculus

section MovingScoreIdentification

local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem movingLogInput_centered_scores {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) (q u a : P) (x : E) (t : ℝ) :
    let I := ParamChain.movingLogInput F M V
    let f := fun y => F (q,y)
    let f₁ := fun y => fderiv ℝ F (q,y) (u,0)
    let f₂ := fun y => fderiv ℝ (fderiv ℝ F) (q,y) (u,0) (u,0) +
      fderiv ℝ F (q,y) (a,0)
    let m := Real.exp (M q)
    let dm := m * M u
    let ddm := m * ((M u)^2 + M a)
    fderiv ℝ I (q,(x,t)) (u,0) - fderiv ℝ I (q,(x,0)) (u,0) =
        firstAverageScore m dm (V q) (V u) f f₁ x t ∧
      (fderiv ℝ (fderiv ℝ I) (q,(x,t)) (u,0) (u,0) +
        fderiv ℝ I (q,(x,t)) (a,0)) -
      (fderiv ℝ (fderiv ℝ I) (q,(x,0)) (u,0) (u,0) +
        fderiv ℝ I (q,(x,0)) (a,0)) =
        secondAverageScoreLinear m dm ddm (V q) (V u) (V a) f f₁ f₂ x t +
          secondAverageScoreQuadratic m (V q) (V u) f x t := by
  dsimp only
  have hfirst := ParamChain.movingLogInput_first_source hF M V q u x t
  have hzero := ParamChain.movingLogInput_first_source hF M V q u x 0
  have hsecond := ParamChain.movingLogInput_second_source hF M V q u a x t
  have hsecondzero := ParamChain.movingLogInput_second_source hF M V q u a x 0
  simp only [zero_smul,add_zero,zero_mul,mul_zero,zero_pow (by norm_num : 2 ≠ 0)] at hzero hsecondzero
  constructor
  · rw [hfirst,hzero]
    unfold firstAverageScore
    ring
  · rw [hfirst] at hsecond
    rw [hzero] at hsecondzero
    unfold secondAverageScoreLinear secondAverageScoreQuadratic
    linear_combination hsecond - hsecondzero

end MovingScoreIdentification

end SKBarriers2.StepCalculus
