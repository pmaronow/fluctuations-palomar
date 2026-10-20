module

public import SKBarriers2.Corner.FrozenRowsWeak

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner
namespace MomentKJet

def rescale (ρ : ℝ) (J : MomentKJet) : MomentKJet :=
  ⟨J.value, ρ * J.first, ρ ^ 2 * J.second⟩

theorem rescale_const (ρ c : ℝ) : rescale ρ (const c) = const c := by
  simp only [rescale, const, mul_zero]

theorem rescale_add (ρ : ℝ) (A B : MomentKJet) :
    rescale ρ (A.add B) = (rescale ρ A).add (rescale ρ B) := by
  simp only [rescale, add, mul_add]

theorem rescale_scale (ρ c : ℝ) (A : MomentKJet) :
    rescale ρ (A.scale c) = (rescale ρ A).scale c := by
  simp only [rescale, scale, mul_left_comm ρ c, mul_left_comm (ρ ^ 2) c]

theorem rescale_mul (ρ : ℝ) (A B : MomentKJet) :
    rescale ρ (A.mul B) = (rescale ρ A).mul (rescale ρ B) := by
  unfold rescale mul
  congr 1 <;> ring

theorem rescale_exp (ρ : ℝ) (A : MomentKJet) :
    rescale ρ A.exp = (rescale ρ A).exp := by
  unfold rescale exp
  congr 1 <;> ring

end MomentKJet

theorem nonlinearBellKJet_rescale (ρ : ℝ) (R : Fin 3 → MomentKJet) (n : Fin 4) :
    MomentKJet.rescale ρ (nonlinearBellKJet R n) =
      nonlinearBellKJet (fun i => MomentKJet.rescale ρ (R i)) n := by
  fin_cases n <;> norm_num [nonlinearBellKJet,
    MomentKJet.rescale_const, MomentKJet.rescale_add, MomentKJet.rescale_mul,
    MomentKJet.rescale_scale]

theorem nonlinearPartitionKJet_rescale (ρ m : ℝ) (F : Fin 4 → MomentKJet) (n : Fin 4) :
    MomentKJet.rescale ρ (nonlinearPartitionKJet m F n) =
      nonlinearPartitionKJet m (fun i => MomentKJet.rescale ρ (F i)) n := by
  simp only [nonlinearPartitionKJet, MomentKJet.rescale_mul,
    MomentKJet.rescale_exp, MomentKJet.rescale_scale, nonlinearBellKJet_rescale]

theorem epsilonCumulantKJet_rescale (ρ m : ℝ) (A : Fin 4 → MomentKJet) (i : Fin 3) :
    MomentKJet.rescale ρ (epsilonCumulantKJet m A i) =
      epsilonCumulantKJet m (fun n => MomentKJet.rescale ρ (A n)) i := by
  fin_cases i <;> norm_num [epsilonCumulantKJet, MomentKJet.rescale_scale,
    MomentKJet.rescale_add, MomentKJet.rescale_mul]

theorem PartitionIntegralKWeakControl.epsilonCumulants
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {V : Set ℝ} {B h m : ℝ}
    (H : PartitionIntegralKWeakControl W W₁ W₂ V B h)
    (hB : 1 ≤ B) (hh : 0 ≤ h) (hm : 0 < m) :
    let A := normalizedMomentKJet (partitionIntegral W) (partitionIntegral W₁) (partitionIntegral W₂)
    let J := fun i k => epsilonCumulantKJet m (fun n => A n k) i
    (∀ k ∈ V, ∀ i, MomentKJet.Differentiates (J i) k) ∧
      (∀ k ∈ V, ∀ i, MomentKJet.Bound (MomentKJet.rescale (Real.sqrt h) (J i k))
        (((6 * B ^ 3) + 12 * (6 * B ^ 3) ^ 2 + 32 * (6 * B ^ 3) ^ 3) / m *
          (Real.sqrt h * h) ^ (i.val + 1))) := by
  constructor
  · intro k hk i
    exact epsilonCumulantKJet_differentiates (fun n => normalizedMomentKJet_differentiates
      (fun n => (H.domination k hk n).1.hasDerivAt)
      (fun n => (H.domination k hk n).2.hasDerivAt) (H.nonzero k hk) n) m i
  · intro k hk i
    rw [epsilonCumulantKJet_rescale]
    apply epsilonCumulantKJet_bound hm (by positivity) (by positivity)
    intro n
    exact normalizedPartition_weak_bounds (P₁ := partitionIntegral W₁) (P₂ := partitionIntegral W₂)
      (ρ := Real.sqrt h) (t := Real.sqrt h * h) hB (by positivity)
      (by simpa only [Real.sq_sqrt hh] using H.bounds k hk) n

private theorem weak_gaussian_normalized_bound
    {F Z : ℝ → ℝ} {S T C t : ℝ} {p n : ℕ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hF : AEStronglyMeasurable F (gaussianReal 0 1))
    (hiZ : Integrable Z (gaussianReal 0 1))
    (hZ : ∀ g, Real.exp (-S * |g| - T * g ^ 2) ≤ Z g)
    (hb : ∀ g, |F g| ≤ C * t ^ n *
      ((1 + g ^ 2) ^ p * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))) :
    |(∫ g, F g ∂gaussianReal 0 1) / (∫ g, Z g ∂gaussianReal 0 1)| ≤
      (C * gaussianQuadraticMoment S p / gaussianQuadraticLower S T) * t ^ n := by
  have hscale : 0 ≤ C * t ^ n := mul_nonneg hC (pow_nonneg ht _)
  have henv := (gaussianQuadraticMoment_integrable S p).const_mul (C * t ^ n)
  have hiF : Integrable F (gaussianReal 0 1) := henv.mono' hF
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g))
  have hD := gaussianQuadraticLower_pos hS hT
  have hDZ : gaussianQuadraticLower S T ≤ ∫ g, Z g ∂gaussianReal 0 1 :=
    integral_mono (gaussianQuadraticLower_integrable hS hT) hiZ hZ
  have H : |∫ g, F g ∂gaussianReal 0 1| ≤ (C * t ^ n) * gaussianQuadraticMoment S p :=
    abs_integral_le_integral_abs.trans
      ((integral_mono hiF.abs henv hb).trans_eq (integral_const_mul _ _))
  rw [abs_div, abs_of_pos (hD.trans_le hDZ)]
  calc
    _ ≤ ((C * t ^ n) * gaussianQuadraticMoment S p) / (∫ g, Z g ∂gaussianReal 0 1) :=
      div_le_div_of_nonneg_right H (hD.trans_le hDZ).le
    _ ≤ ((C * t ^ n) * gaussianQuadraticMoment S p) / gaussianQuadraticLower S T :=
      div_le_div_of_nonneg_left (mul_nonneg hscale (gaussianQuadraticMoment_nonneg _ _)) hD hDZ
    _ = _ := by ring

private theorem unscale_abs_bound {a x C : ℝ} (ha : 0 < a) (hx : |a * x| ≤ C) :
    |x| ≤ a⁻¹ * C := by
  rw [abs_mul, abs_of_pos ha] at hx
  calc
    _ = a⁻¹ * (a * |x|) := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr ha.le)

theorem partitionIntegralKWeakControl_of_gaussian_envelopes
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {U V : Set ℝ} {S T h : ℝ}
    {C : Fin 4 → ℝ} {p : Fin 4 → ℕ}
    (hV : IsOpen V) (hUV : U ⊆ V) (hS : 0 ≤ S) (hT : 0 ≤ T) (hh : 0 < h)
    (hC : ∀ n, 0 ≤ C n)
    (hc : ∀ k ∈ V, ∀ n,
      AEStronglyMeasurable (W n k) (gaussianReal 0 1) ∧
      AEStronglyMeasurable (W₁ n k) (gaussianReal 0 1) ∧
      AEStronglyMeasurable (W₂ n k) (gaussianReal 0 1))
    (hd : ∀ g k, k ∈ V → ∀ n,
      HasDerivAt (fun x => W n x g) (W₁ n k g) k ∧
      HasDerivAt (fun x => W₁ n x g) (W₂ n k g) k)
    (hb : ∀ k ∈ V, ∀ g n,
      |W n k g| ≤ C n * (Real.sqrt h * h) ^ n.val *
        ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)) ∧
      |Real.sqrt h * W₁ n k g| ≤ C n * (Real.sqrt h * h) ^ n.val *
        ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)) ∧
      |h * W₂ n k g| ≤ C n * (Real.sqrt h * h) ^ n.val *
        ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)))
    (hn : ∀ k ∈ U, ∀ g,
      |W₁ 0 k g| ≤ C 0 * ((1 + g ^ 2) ^ p 0 * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)) ∧
      |W₂ 0 k g| ≤ C 0 * ((1 + g ^ 2) ^ p 0 * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)))
    (hlower : ∀ k ∈ U, ∀ g, Real.exp (-S * |g| - T * g ^ 2) ≤ W 0 k g) :
    let B := 1 + ∑ n : Fin 4,
      C n * gaussianQuadraticMoment S (p n) / gaussianQuadraticLower S T
    1 ≤ B ∧ PartitionIntegralKWeakControl W W₁ W₂ U B h := by
  let A : Fin 4 → ℝ := fun n =>
    C n * gaussianQuadraticMoment S (p n) / gaussianQuadraticLower S T
  let B := 1 + ∑ n : Fin 4, A n
  let R := 1 + (Real.sqrt h)⁻¹ + h⁻¹
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsInv : 0 ≤ (Real.sqrt h)⁻¹ := inv_nonneg.mpr hs.le
  have hhInv : 0 ≤ h⁻¹ := inv_nonneg.mpr hh.le
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hR₀ : 1 ≤ R := by dsimp only [R]; linarith
  have hR₁ : (Real.sqrt h)⁻¹ ≤ R := by dsimp only [R]; linarith
  have hR₂ : h⁻¹ ≤ R := by dsimp only [R]; linarith
  have Hstrong := partitionIntegralKControl_of_gaussian_envelopes
    (C := fun n => R * C n) (p := p) hV hUV hS hT (by positivity : 0 ≤ Real.sqrt h * h)
    (fun n => mul_nonneg hR (hC n)) hc hd (by
      intro k hk g n
      let X := C n * (Real.sqrt h * h) ^ n.val *
        ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))
      have hX : 0 ≤ X := by have hCn := hC n; dsimp only [X]; positivity
      have h₀ := (hb k hk g n).1
      have h₁ := unscale_abs_bound hs (hb k hk g n).2.1
      have h₂ := unscale_abs_bound hh (hb k hk g n).2.2
      refine ⟨h₀.trans ?_, h₁.trans ?_, h₂.trans ?_⟩
      · calc
          _ = 1 * X := by ring
          _ ≤ R * X := mul_le_mul_of_nonneg_right hR₀ hX
          _ = _ := by dsimp only [X]; ring
      · exact (mul_le_mul_of_nonneg_right hR₁ hX).trans_eq (by dsimp only [X]; ring)
      · exact (mul_le_mul_of_nonneg_right hR₂ hX).trans_eq (by dsimp only [X]; ring)) hlower
  have hA (n : Fin 4) : 0 ≤ A n :=
    div_nonneg (mul_nonneg (hC n) (gaussianQuadraticMoment_nonneg _ _))
      (gaussianQuadraticLower_pos hS hT).le
  have hB : 1 ≤ B := by
    have H := Finset.sum_nonneg (fun n (_ : n ∈ (Finset.univ : Finset (Fin 4))) => hA n)
    dsimp only [B]
    linarith
  have hAB (n : Fin 4) : A n ≤ B := by
    have H := Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hA i) (Finset.mem_univ n)
    dsimp only [B]
    linarith
  have Hbound (k : ℝ) (hk : k ∈ U) (n : Fin 4) (F : ℝ → ℝ)
      (hF : AEStronglyMeasurable F (gaussianReal 0 1))
      (hbF : ∀ g, |F g| ≤ C n * (Real.sqrt h * h) ^ n.val *
        ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))) :
      |(∫ g, F g ∂gaussianReal 0 1) / partitionIntegral W 0 k| ≤
        B * (Real.sqrt h * h) ^ n.val :=
    (weak_gaussian_normalized_bound (t := Real.sqrt h * h) hS hT (hC n) (by positivity) hF
      (Hstrong.2.domination k hk 0).1.integrable (hlower k hk) hbF).trans
      (mul_le_mul_of_nonneg_right (hAB n) (by positivity))
  refine ⟨hB, Hstrong.2.nonzero, Hstrong.2.domination, ?_, ?_⟩
  · intro k hk n
    refine ⟨Hbound k hk n _ (hc k (hUV hk) n).1 (fun g => (hb k (hUV hk) g n).1), ?_, ?_⟩
    · simpa only [integral_const_mul, mul_div_assoc, partitionIntegral, B, A] using
        Hbound k hk n _ ((hc k (hUV hk) n).2.1.const_mul (Real.sqrt h))
          (fun g => (hb k (hUV hk) g n).2.1)
    · simpa only [integral_const_mul, mul_div_assoc, partitionIntegral, B, A] using
        Hbound k hk n _ ((hc k (hUV hk) n).2.2.const_mul h)
          (fun g => (hb k (hUV hk) g n).2.2)
  · intro k hk
    have h₁ := Hbound k hk 0 _ (hc k (hUV hk) 0).2.1
      (by simpa only [Fin.val_zero, pow_zero, mul_one] using fun g => (hn k hk g).1)
    have h₂ := Hbound k hk 0 _ (hc k (hUV hk) 0).2.2
      (by simpa only [Fin.val_zero, pow_zero, mul_one] using fun g => (hn k hk g).2)
    simpa only [Fin.val_zero, pow_zero, mul_one, partitionIntegral, B, A] using And.intro h₁ h₂

theorem nonlinearPartitionKJet_zero_bound {F : Fin 4 → MomentKJet} {m E L q : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hL : 0 ≤ L) (hq : 1 ≤ q) (hE₀ : 0 ≤ E)
    (hE : Real.exp (m * (F 0).value) ≤ E)
    (h₁ : |(F 0).first| ≤ L * q) (h₂ : |(F 0).second| ≤ L * q) :
    MomentKJet.Bound (nonlinearPartitionKJet m F 0)
      (232 * (L + 1) ^ 2 * q ^ 2 * E) := by
  have ha₁ : |((F 0).scale m).first| ≤ L * q := by
    rw [MomentKJet.scale, abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left h₁ hm.1).trans
      (mul_le_of_le_one_left (by positivity) hm.2)
  have ha₂ : |((F 0).scale m).second| ≤ L * q := by
    rw [MomentKJet.scale, abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left h₂ hm.1).trans
      (mul_le_of_le_one_left (by positivity) hm.2)
  have HE := MomentKJet.bound_exp (A := (F 0).scale m) hE hL hq ha₁ ha₂
  have H := HE.mul (MomentKJet.bound_const (by norm_num : 0 ≤ (1 : ℝ)))
  exact H.mono (by
    calc
      _ = 8 * ((L + 1) ^ 2 * q ^ 2 * E) := by ring
      _ ≤ 232 * ((L + 1) ^ 2 * q ^ 2 * E) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by ring)

theorem nonlinearPartitionKJet_integral_weak_control
    {F : Fin 4 → ℝ → ℝ → MomentKJet} {U V : Set ℝ} {m S T L M h : ℝ}
    (hV : IsOpen V) (hUV : U ⊆ V) (hm : m ∈ Icc (0 : ℝ) 1)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (hc : ∀ k ∈ V, ∀ i, Continuous (fun g => (F i k g).value) ∧
      Continuous (fun g => (F i k g).first) ∧ Continuous (fun g => (F i k g).second))
    (hd : ∀ g k, k ∈ V → ∀ i, MomentKJet.Differentiates (fun x => F i x g) k)
    (hE : ∀ k ∈ V, ∀ g,
      Real.exp (m * (F 0 k g).value) ≤ Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))
    (h₁ : ∀ k ∈ V, ∀ g, |(F 0 k g).first| ≤ L * (1 + g ^ 2))
    (h₂ : ∀ k ∈ V, ∀ g, |(F 0 k g).second| ≤ L * (1 + g ^ 2))
    (hjets : ∀ k ∈ V, ∀ g, ∀ i : Fin 3,
      MomentKJet.Bound (MomentKJet.rescale (Real.sqrt h) (F i.succ k g))
        ((M * (Real.sqrt h * h) * (1 + g ^ 2) ^ 3) ^ (i.val + 1)))
    (hlower : ∀ k ∈ U, ∀ g,
      Real.exp (-S * |g| - T * g ^ 2) ≤ Real.exp (m * (F 0 k g).value)) :
    let J := fun n k g => nonlinearPartitionKJet m (fun i => F i k g) n
    let B := 1 + ∑ n : Fin 4, (232 * (L + 1) ^ 2 * M ^ n.val) *
      gaussianQuadraticMoment S (3 * n.val + 2) / gaussianQuadraticLower S T
    1 ≤ B ∧ PartitionIntegralKWeakControl
      (fun n k g => (J n k g).value) (fun n k g => (J n k g).first)
      (fun n k g => (J n k g).second) U B h := by
  apply partitionIntegralKWeakControl_of_gaussian_envelopes
    (C := fun n => 232 * (L + 1) ^ 2 * M ^ n.val) (p := fun n => 3 * n.val + 2)
    hV hUV hS hT hh (fun n => by positivity)
  · intro k hk n
    have H := nonlinearPartitionKJet_noise_continuous (hc k hk) m n
    exact ⟨H.1.aestronglyMeasurable, H.2.1.aestronglyMeasurable, H.2.2.aestronglyMeasurable⟩
  · intro g k hk n
    exact nonlinearPartitionKJet_differentiates (hd g k hk) m n
  · intro k hk g n
    have hs : Real.sqrt h ≤ 1 := Real.sqrt_le_one.mpr hh₁
    have hfirst : |(MomentKJet.rescale (Real.sqrt h) (F 0 k g)).first| ≤ L * (1 + g ^ 2) := by
      rw [MomentKJet.rescale, abs_mul, abs_of_nonneg (Real.sqrt_nonneg h)]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (h₁ k hk g)
    have hsecond : |(MomentKJet.rescale (Real.sqrt h) (F 0 k g)).second| ≤ L * (1 + g ^ 2) := by
      rw [MomentKJet.rescale, Real.sq_sqrt hh.le, abs_mul, abs_of_pos hh]
      exact (mul_le_of_le_one_left (abs_nonneg _) hh₁).trans (h₂ k hk g)
    have H := nonlinearPartitionKJet_gaussian_envelope
      (F := fun i => MomentKJet.rescale (Real.sqrt h) (F i k g)) hm hL hM
      (by positivity : 0 ≤ Real.sqrt h * h) (hE k hk g) hfirst hsecond (hjets k hk g) n
    rw [← nonlinearPartitionKJet_rescale] at H
    simpa only [MomentKJet.Bound, MomentKJet.rescale, Real.sq_sqrt hh.le] using H
  · intro k hk g
    have H := nonlinearPartitionKJet_zero_bound (F := fun i => F i k g)
      (q := 1 + g ^ 2) hm hL (by nlinarith [sq_nonneg g])
      (Real.exp_pos _).le (hE k (hUV hk) g) (h₁ k (hUV hk) g) (h₂ k (hUV hk) g)
    have H' : MomentKJet.Bound (nonlinearPartitionKJet m (fun i => F i k g) 0)
        ((232 * (L + 1) ^ 2 * M ^ (0 : Fin 4).val) *
          ((1 + g ^ 2) ^ (3 * (0 : Fin 4).val + 2) *
            Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))) :=
      H.mono (le_of_eq (by norm_num only [Fin.val_zero, pow_zero, mul_one, mul_zero, zero_add]; ring))
    exact ⟨H'.2.1, H'.2.2⟩
  · intro k hk g
    change Real.exp (-S * |g| - T * g ^ 2) ≤ Real.exp (m * (F 0 k g).value) * 1
    simpa only [mul_one] using hlower k hk g

theorem movingEpsilonChain_k_jets_of_partition_weak_control
    {m B h ε : ℝ} {v x : ℝ → Vec3} {l : ℝ → List (ℝ × Vec3)}
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hε : ε ∈ U)
    (hm : 0 < m) (hB : 1 ≤ B) (hh : 0 ≤ h)
    {W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ}
    (H : PartitionIntegralKWeakControl
      (fun n k g => epsilonPartitionWeight ((m, v k) :: l k) Q K (x k) ε n g)
      W₁ W₂ V B h)
    (Hε : ∀ k ∈ V, EpsilonChainDominationOn ((m, v k) :: l k) Q K U) :
    let C := ((6 * B ^ 3) + 12 * (6 * B ^ 3) ^ 2 + 32 * (6 * B ^ 3) ^ 3) / m
    let f := fun (i : Fin 3) (k : ℝ) => iteratedDeriv (i.val + 1)
      (fun e => epsilonChain ((m, v k) :: l k) Q K e (x k)) ε
    ∃ d₁ d₂ : Fin 3 → ℝ → ℝ,
      (∀ k ∈ V, ∀ i : Fin 3, HasDerivAt (f i) (d₁ i k) k ∧ HasDerivAt (d₁ i) (d₂ i k) k) ∧
      (∀ k ∈ V, ∀ i : Fin 3,
        |f i k| ≤ C * (Real.sqrt h * h) ^ (i.val + 1) ∧
        |Real.sqrt h * d₁ i k| ≤ C * (Real.sqrt h * h) ^ (i.val + 1) ∧
        |h * d₂ i k| ≤ C * (Real.sqrt h * h) ^ (i.val + 1)) := by
  let W := fun n k g => epsilonPartitionWeight ((m, v k) :: l k) Q K (x k) ε n g
  let A := normalizedMomentKJet (partitionIntegral W) (partitionIntegral W₁) (partitionIntegral W₂)
  let J := fun i k => epsilonCumulantKJet m (fun n => A n k) i
  have HC := H.epsilonCumulants hB hh hm
  have heq (k : ℝ) (hk : k ∈ V) (i : Fin 3) :
      iteratedDeriv (i.val + 1) (fun e => epsilonChain ((m, v k) :: l k) Q K e (x k)) ε =
        (J i k).value := by
    rw [epsilonChain_epsilonJet_eq_cumulant (m, v k) (l k) Q K (x k) hU hm.ne' (Hε k hk) hε i,
      epsilonCumulantKJet_value, epsilonCumulantKJet_value]
    rfl
  refine ⟨(fun i k => (J i k).first), (fun i k => (J i k).second), ?_, ?_⟩
  · intro k hk i
    refine ⟨(HC.1 k hk i).1.congr_of_eventuallyEq ?_, (HC.1 k hk i).2⟩
    filter_upwards [hV.mem_nhds hk] with a ha
    exact heq a ha i
  · intro k hk i
    dsimp only
    rw [heq k hk i]
    simpa only [MomentKJet.Bound, MomentKJet.rescale, Real.sq_sqrt hh] using HC.2 k hk i

theorem quadraticResidualSpatialKJet_rescale (f : ℝ → ℝ) (z : ℝ) (j : ℕ)
    (ρ y y₁ y₂ : ℝ) :
    MomentKJet.rescale ρ (quadraticResidualSpatialKJet f z j y y₁ y₂) =
      quadraticResidualSpatialKJet f z j y (ρ * y₁) (ρ ^ 2 * y₂) := by
  unfold MomentKJet.rescale quadraticResidualSpatialKJet
  congr 1 <;> ring

theorem scalarData_quadraticResidualSpatialKJet_weak_bound {β s h R z y y₁ y₂ : ℝ}
    (D : ScalarData β) (ht : s + 4 * h ∈ Icc (0 : ℝ) 1)
    (hh : 0 ≤ h) (hh₁ : h ≤ 1) (hR : 0 ≤ R)
    (hy : |y - z| ≤ Real.sqrt h * R) (hy₁ : |y₁| ≤ R) (hy₂ : |y₂| ≤ R) (j : Fin 4) :
    MomentKJet.Bound
      (MomentKJet.rescale (Real.sqrt h)
        (quadraticResidualSpatialKJet (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h))
          z j.val y y₁ y₂))
      (4 * scalarTerminalJetBound D 5 * (1 + Real.sqrt h * R) ^ 2 *
        (Real.sqrt h * R) ^ (3 - j.val)) := by
  rw [quadraticResidualSpatialKJet_rescale, Real.sq_sqrt hh]
  apply scalarData_quadraticResidualSpatialKJet_bound D ht (by positivity) hy
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg h)]
    exact mul_le_mul_of_nonneg_left hy₁ (Real.sqrt_nonneg h)
  · rw [abs_mul, abs_of_nonneg hh]
    exact (mul_le_mul_of_nonneg_left hy₂ hh).trans
      (mul_le_mul_of_nonneg_right (Real.le_sqrt_self_iff.mpr hh₁) hR)

end SKBarriers2.Corner
