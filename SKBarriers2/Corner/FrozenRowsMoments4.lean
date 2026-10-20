module

public import SKBarriers2.Corner.FrozenRowsMoments3

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

structure MomentKJet where
  value : ℝ
  first : ℝ
  second : ℝ

namespace MomentKJet

def const (a : ℝ) : MomentKJet := ⟨a, 0, 0⟩

def add (A B : MomentKJet) : MomentKJet :=
  ⟨A.value + B.value, A.first + B.first, A.second + B.second⟩

def scale (c : ℝ) (A : MomentKJet) : MomentKJet :=
  ⟨c * A.value, c * A.first, c * A.second⟩

def mul (A B : MomentKJet) : MomentKJet :=
  ⟨A.value * B.value, A.first * B.value + A.value * B.first,
    A.second * B.value + 2 * A.first * B.first + A.value * B.second⟩

def exp (A : MomentKJet) : MomentKJet :=
  ⟨Real.exp A.value, Real.exp A.value * A.first,
    Real.exp A.value * (A.second + A.first ^ 2)⟩

def Differentiates (J : ℝ → MomentKJet) (k : ℝ) : Prop :=
  HasDerivAt (fun x => (J x).value) (J k).first k ∧
    HasDerivAt (fun x => (J x).first) (J k).second k

def Bound (J : MomentKJet) (C : ℝ) : Prop :=
  |J.value| ≤ C ∧ |J.first| ≤ C ∧ |J.second| ≤ C

theorem differentiates_const (c k : ℝ) : Differentiates (fun _ => const c) k :=
  ⟨hasDerivAt_const k c, hasDerivAt_const k 0⟩

theorem Differentiates.add {A B : ℝ → MomentKJet} {k : ℝ}
    (hA : Differentiates A k) (hB : Differentiates B k) :
    Differentiates (fun x => (A x).add (B x)) k :=
  ⟨hA.1.add hB.1, hA.2.add hB.2⟩

theorem Differentiates.scale {A : ℝ → MomentKJet} {k : ℝ}
    (hA : Differentiates A k) (c : ℝ) :
    Differentiates (fun x => (A x).scale c) k :=
  ⟨hA.1.const_mul c, hA.2.const_mul c⟩

theorem Differentiates.mul {A B : ℝ → MomentKJet} {k : ℝ}
    (hA : Differentiates A k) (hB : Differentiates B k) :
    Differentiates (fun x => (A x).mul (B x)) k := by
  refine ⟨hA.1.mul hB.1, ?_⟩
  convert ((hA.2.mul hB.1).add (hA.1.mul hB.2)) using 1 <;>
    dsimp only [MomentKJet.mul, Pi.mul_apply, Pi.add_apply] <;> first | rfl | ring

theorem Differentiates.exp {A : ℝ → MomentKJet} {k : ℝ}
    (hA : Differentiates A k) : Differentiates (fun x => (A x).exp) k := by
  refine ⟨hA.1.exp, ?_⟩
  convert hA.1.exp.mul hA.2 using 1 <;>
    dsimp only [MomentKJet.exp, Pi.mul_apply] <;> first | rfl | ring

theorem Bound.mono {J : MomentKJet} {C D : ℝ} (H : Bound J C) (hCD : C ≤ D) :
    Bound J D := ⟨H.1.trans hCD, H.2.1.trans hCD, H.2.2.trans hCD⟩

theorem bound_const {C : ℝ} (hC : 0 ≤ C) : Bound (const C) C := by
  exact ⟨(abs_of_nonneg hC).le, by simpa [const] using hC, by simpa [const] using hC⟩

theorem Bound.add {A B : MomentKJet} {C D : ℝ} (hA : Bound A C) (hB : Bound B D) :
    Bound (A.add B) (C + D) := by
  exact ⟨(abs_add_le _ _).trans (add_le_add hA.1 hB.1),
    (abs_add_le _ _).trans (add_le_add hA.2.1 hB.2.1),
    (abs_add_le _ _).trans (add_le_add hA.2.2 hB.2.2)⟩

theorem Bound.scale {A : MomentKJet} {C : ℝ} (hA : Bound A C) (c : ℝ) :
    Bound (A.scale c) (|c| * C) := by
  exact ⟨(abs_mul c A.value).trans_le (mul_le_mul_of_nonneg_left hA.1 (abs_nonneg c)),
    (abs_mul c A.first).trans_le (mul_le_mul_of_nonneg_left hA.2.1 (abs_nonneg c)),
    (abs_mul c A.second).trans_le (mul_le_mul_of_nonneg_left hA.2.2 (abs_nonneg c))⟩

private theorem mul_abs_bound {a b C D : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ D) :
    |a * b| ≤ C * D := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg a).trans ha)

theorem Bound.mul {A B : MomentKJet} {C D : ℝ} (hA : Bound A C) (hB : Bound B D) :
    Bound (A.mul B) (4 * C * D) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hA.1
  have hD : 0 ≤ D := (abs_nonneg _).trans hB.1
  have hCD : 0 ≤ C * D := mul_nonneg hC hD
  refine ⟨(mul_abs_bound hA.1 hB.1).trans (by nlinarith), ?_, ?_⟩
  · exact ((abs_add_le _ _).trans (add_le_add (mul_abs_bound hA.2.1 hB.1)
      (mul_abs_bound hA.1 hB.2.1))).trans (by nlinarith)
  · have hm : |2 * A.first * B.first| ≤ 2 * (C * D) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
      exact mul_le_mul_of_nonneg_left (mul_abs_bound hA.2.1 hB.2.1) (by norm_num)
    exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (mul_abs_bound hA.2.2 hB.1) hm)) (mul_abs_bound hA.1 hB.2.2))).trans_eq (by ring)

theorem bound_exp {A : MomentKJet} {E L q : ℝ}
    (hE : Real.exp A.value ≤ E) (hL : 0 ≤ L) (hq : 1 ≤ q)
    (h₁ : |A.first| ≤ L * q) (h₂ : |A.second| ≤ L * q) :
    Bound A.exp (2 * (L + 1) ^ 2 * q ^ 2 * E) := by
  have hq₀ : 0 ≤ q := by linarith
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le.trans hE
  have hEv : |Real.exp A.value| ≤ E := by simpa only [abs_of_pos (Real.exp_pos _)] using hE
  have hq₂ : q ≤ q ^ 2 := by nlinarith [mul_nonneg hq₀ (sub_nonneg.mpr hq)]
  have hc₀ : 1 ≤ 2 * (L + 1) ^ 2 * q ^ 2 := by
    have H := mul_le_mul_of_nonneg_left (hq.trans hq₂) (sq_nonneg (L + 1))
    nlinarith
  have hc₁ : L * q ≤ 2 * (L + 1) ^ 2 * q ^ 2 := by
    have H := mul_le_mul_of_nonneg_left hq₂ hL
    have H' := mul_le_mul_of_nonneg_right (show L ≤ 2 * (L + 1) ^ 2 by nlinarith) (sq_nonneg q)
    linarith
  have hc₂ : L * q + (L * q) ^ 2 ≤ 2 * (L + 1) ^ 2 * q ^ 2 := by
    have H := mul_le_mul_of_nonneg_left hq₂ hL
    have H' := mul_le_mul_of_nonneg_right (show L + L ^ 2 ≤ 2 * (L + 1) ^ 2 by nlinarith) (sq_nonneg q)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · exact hEv.trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc₀ hE₀])
  · exact (mul_abs_bound hEv h₁).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc₁ hE₀])
  · have H : |A.second + A.first ^ 2| ≤ L * q + (L * q) ^ 2 := by
      exact (abs_add_le _ _).trans (add_le_add h₂ (by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) h₁ 2))
    exact (mul_abs_bound hEv H).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hc₂ hE₀])

end MomentKJet

def nonlinearBellKJet (R : Fin 3 → MomentKJet) (n : Fin 4) : MomentKJet :=
  ![MomentKJet.const 1, R 0,
    (R 1).add ((R 0).mul (R 0)),
    ((R 2).add (((R 0).mul (R 1)).scale 3)).add (((R 0).mul (R 0)).mul (R 0))] n

theorem nonlinearBellKJet_differentiates {R : Fin 3 → ℝ → MomentKJet} {k : ℝ}
    (H : ∀ i, MomentKJet.Differentiates (R i) k) (n : Fin 4) :
    MomentKJet.Differentiates (fun x => nonlinearBellKJet (fun i => R i x) n) k := by
  fin_cases n
  · exact MomentKJet.differentiates_const 1 k
  · exact H 0
  · exact (H 1).add ((H 0).mul (H 0))
  · exact ((H 2).add (((H 0).mul (H 1)).scale 3)).add (((H 0).mul (H 0)).mul (H 0))

theorem nonlinearBellKJet_bound {R : Fin 3 → MomentKJet} {t : ℝ} (ht : 0 ≤ t)
    (H : ∀ i : Fin 3, MomentKJet.Bound (R i) (t ^ (i.val + 1))) (n : Fin 4) :
    MomentKJet.Bound (nonlinearBellKJet R n) (29 * t ^ n.val) := by
  have H₀ : MomentKJet.Bound (R 0) t := by simpa using H 0
  have H₁ : MomentKJet.Bound (R 1) (t ^ 2) := H 1
  have H₂ : MomentKJet.Bound (R 2) (t ^ 3) := H 2
  fin_cases n
  · exact (MomentKJet.bound_const (by norm_num : 0 ≤ (1 : ℝ))).mono (by norm_num)
  · exact H₀.mono (by dsimp; nlinarith)
  · exact (H₁.add (H₀.mul H₀)).mono (by dsimp; nlinarith [sq_nonneg t])
  · exact ((H₂.add ((H₀.mul H₁).scale 3)).add ((H₀.mul H₀).mul H₀)).mono (by
      norm_num
      ring_nf
      exact le_refl _)

def nonlinearPartitionKJet (m : ℝ) (F : Fin 4 → MomentKJet) (n : Fin 4) : MomentKJet :=
  ((F 0).scale m).exp.mul
    (nonlinearBellKJet (fun i => (F i.succ).scale m) n)

theorem nonlinearPartitionKJet_differentiates {F : Fin 4 → ℝ → MomentKJet} {k : ℝ}
    (H : ∀ i, MomentKJet.Differentiates (F i) k) (m : ℝ) (n : Fin 4) :
    MomentKJet.Differentiates (fun x => nonlinearPartitionKJet m (fun i => F i x) n) k :=
  ((H 0).scale m).exp.mul
    (nonlinearBellKJet_differentiates (fun i => (H i.succ).scale m) n)

theorem nonlinearPartitionKJet_value (m : ℝ) (F : Fin 4 → MomentKJet) (n : Fin 4) :
    (nonlinearPartitionKJet m F n).value =
      ![Real.exp (m * (F 0).value),
        Real.exp (m * (F 0).value) * (m * (F 1).value),
        Real.exp (m * (F 0).value) * (m * (F 2).value + m ^ 2 * (F 1).value ^ 2),
        Real.exp (m * (F 0).value) *
          (m * (F 3).value + 3 * m ^ 2 * (F 1).value * (F 2).value + m ^ 3 * (F 1).value ^ 3)] n := by
  fin_cases n <;>
    simp only [nonlinearPartitionKJet, nonlinearBellKJet, MomentKJet.mul,
      MomentKJet.scale, MomentKJet.exp, MomentKJet.const,
      MomentKJet.add, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceSucc] <;>
    ring

theorem nonlinearPartitionKJet_bound {F : Fin 4 → MomentKJet} {m E L q t : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) (hL : 0 ≤ L) (hq : 1 ≤ q)
    (hE : Real.exp (m * (F 0).value) ≤ E)
    (h₁ : |(F 0).first| ≤ L * q) (h₂ : |(F 0).second| ≤ L * q)
    (H : ∀ i : Fin 3, MomentKJet.Bound (F i.succ) (t ^ (i.val + 1))) (n : Fin 4) :
    MomentKJet.Bound (nonlinearPartitionKJet m F n)
      (232 * (L + 1) ^ 2 * q ^ 2 * t ^ n.val * E) := by
  have hscale {A : MomentKJet} {C : ℝ} (H : MomentKJet.Bound A C) :
      MomentKJet.Bound (A.scale m) C := by
    have hC : 0 ≤ C := (abs_nonneg _).trans H.1
    exact (H.scale m).mono (by rw [abs_of_nonneg hm.1]; exact mul_le_of_le_one_left hC hm.2)
  have ha₁ : |((F 0).scale m).first| ≤ L * q := by
    rw [MomentKJet.scale, abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left h₁ hm.1).trans (mul_le_of_le_one_left (by positivity) hm.2)
  have ha₂ : |((F 0).scale m).second| ≤ L * q := by
    rw [MomentKJet.scale, abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left h₂ hm.1).trans (mul_le_of_le_one_left (by positivity) hm.2)
  have HE := MomentKJet.bound_exp (A := (F 0).scale m) hE hL hq ha₁ ha₂
  have HB := nonlinearBellKJet_bound ht (fun i => hscale (H i)) n
  exact (HE.mul HB).mono (le_of_eq (by ring))

theorem nonlinearPartitionKJet_noise_continuous {F : Fin 4 → ℝ → MomentKJet}
    (H : ∀ i, Continuous (fun g => (F i g).value) ∧
      Continuous (fun g => (F i g).first) ∧ Continuous (fun g => (F i g).second))
    (m : ℝ) (n : Fin 4) :
    Continuous (fun g => (nonlinearPartitionKJet m (fun i => F i g) n).value) ∧
      Continuous (fun g => (nonlinearPartitionKJet m (fun i => F i g) n).first) ∧
      Continuous (fun g => (nonlinearPartitionKJet m (fun i => F i g) n).second) := by
  have hv (i : Fin 4) := (H i).1
  have h₁ (i : Fin 4) := (H i).2.1
  have h₂ (i : Fin 4) := (H i).2.2
  fin_cases n <;>
    dsimp only [nonlinearPartitionKJet, nonlinearBellKJet, MomentKJet.mul,
      MomentKJet.scale, MomentKJet.exp, MomentKJet.const, MomentKJet.add,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceSucc] <;>
    exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

theorem nonlinearPartitionKJet_gaussian_envelope
    {F : Fin 4 → MomentKJet} {m S L M t g : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hL : 0 ≤ L) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hE : Real.exp (m * (F 0).value) ≤ Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))
    (h₁ : |(F 0).first| ≤ L * (1 + g ^ 2))
    (h₂ : |(F 0).second| ≤ L * (1 + g ^ 2))
    (H : ∀ i : Fin 3, MomentKJet.Bound (F i.succ)
      ((M * t * (1 + g ^ 2) ^ 3) ^ (i.val + 1))) (n : Fin 4) :
    MomentKJet.Bound (nonlinearPartitionKJet m F n)
      ((232 * (L + 1) ^ 2 * M ^ n.val) * t ^ n.val *
        ((1 + g ^ 2) ^ (3 * n.val + 2) * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))) := by
  have Hbound := nonlinearPartitionKJet_bound hm (by positivity : 0 ≤ M * t * (1 + g ^ 2) ^ 3)
    hL (by nlinarith [sq_nonneg g] : 1 ≤ 1 + g ^ 2) hE h₁ h₂ H n
  convert Hbound using 1
  rw [mul_pow, mul_pow, ← pow_mul, pow_add]
  ring

theorem partitionIntegralKControl_of_gaussian_envelopes
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {U V : Set ℝ} {S T t : ℝ}
    {C : Fin 4 → ℝ} {p : Fin 4 → ℕ}
    (hV : IsOpen V) (hUV : U ⊆ V) (hS : 0 ≤ S) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (hC : ∀ n, 0 ≤ C n)
    (hc : ∀ k ∈ V, ∀ n,
      AEStronglyMeasurable (W n k) (gaussianReal 0 1) ∧
      AEStronglyMeasurable (W₁ n k) (gaussianReal 0 1) ∧
      AEStronglyMeasurable (W₂ n k) (gaussianReal 0 1))
    (hd : ∀ g k, k ∈ V → ∀ n,
      HasDerivAt (fun x => W n x g) (W₁ n k g) k ∧
      HasDerivAt (fun x => W₁ n x g) (W₂ n k g) k)
    (hb : ∀ k ∈ V, ∀ g n,
      |W n k g| ≤ C n * t ^ n.val * ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)) ∧
      |W₁ n k g| ≤ C n * t ^ n.val * ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)) ∧
      |W₂ n k g| ≤ C n * t ^ n.val * ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)))
    (hlower : ∀ k ∈ U, ∀ g, Real.exp (-S * |g| - T * g ^ 2) ≤ W 0 k g) :
    let B := 1 + ∑ n : Fin 4,
      C n * gaussianQuadraticMoment S (p n) / gaussianQuadraticLower S T
    1 ≤ B ∧ PartitionIntegralKControl W W₁ W₂ U B t := by
  let A : Fin 4 → ℝ := fun n =>
    C n * gaussianQuadraticMoment S (p n) / gaussianQuadraticLower S T
  let B := 1 + ∑ n : Fin 4, A n
  have hD : 0 < gaussianQuadraticLower S T := gaussianQuadraticLower_pos hS hT
  have hA (n : Fin 4) : 0 ≤ A n :=
    div_nonneg (mul_nonneg (hC n) (gaussianQuadraticMoment_nonneg _ _)) hD.le
  have hB : 1 ≤ B := by
    have H := Finset.sum_nonneg (fun n (_ : n ∈ (Finset.univ : Finset (Fin 4))) => hA n)
    dsimp only [B]
    linarith
  have hAB (n : Fin 4) : A n ≤ B := by
    have H := Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hA i) (Finset.mem_univ n)
    dsimp only [B]
    linarith
  have controls (k : ℝ) (hk : k ∈ V) (n : Fin 4) :=
    quadratic_gaussian_integral_k_controls (F := W n) (F₁ := W₁ n) (F₂ := W₂ n)
      (hV.mem_nhds hk) (by norm_num : 0 ≤ (1 / 4 : ℝ)) (by norm_num : 2 * (1 / 4 : ℝ) < 1)
      (fun x hx => hc x hx n) (fun g x hx => hd g x hx n)
      (fun x hx g => hb x hx g n)
  have hiZ (k : ℝ) (hk : k ∈ U) : Integrable (W 0 k) (gaussianReal 0 1) :=
    (controls k (hUV hk) 0).1.integrable
  have hDZ (k : ℝ) (hk : k ∈ U) : gaussianQuadraticLower S T ≤ partitionIntegral W 0 k :=
    integral_mono (gaussianQuadraticLower_integrable hS hT) (hiZ k hk) (hlower k hk)
  refine ⟨hB, ?_, (fun k hk n => controls k (hUV hk) n), ?_⟩
  · intro k hk
    exact ne_of_gt (hD.trans_le (hDZ k hk))
  · intro k hk n
    have Hbound (F : ℝ → ℝ) (hF : AEStronglyMeasurable F (gaussianReal 0 1))
        (hFb : ∀ g, |F g| ≤ C n * t ^ n.val *
          ((1 + g ^ 2) ^ p n * Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))) :
        |(∫ g, F g ∂gaussianReal 0 1) / partitionIntegral W 0 k| ≤ B * t ^ n.val := by
      have hscale : 0 ≤ C n * t ^ n.val := mul_nonneg (hC n) (pow_nonneg ht _)
      have henv := (gaussianQuadraticMoment_integrable S (p n)).const_mul (C n * t ^ n.val)
      have hiF : Integrable F (gaussianReal 0 1) :=
        henv.mono' hF (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hFb g))
      have hnum : |∫ g, F g ∂gaussianReal 0 1| ≤
          (C n * t ^ n.val) * gaussianQuadraticMoment S (p n) := by
        exact abs_integral_le_integral_abs.trans
          ((integral_mono hiF.abs henv hFb).trans_eq (integral_const_mul _ _))
      rw [abs_div, abs_of_pos (hD.trans_le (hDZ k hk))]
      calc
        _ ≤ ((C n * t ^ n.val) * gaussianQuadraticMoment S (p n)) / partitionIntegral W 0 k :=
          div_le_div_of_nonneg_right hnum (hD.trans_le (hDZ k hk)).le
        _ ≤ ((C n * t ^ n.val) * gaussianQuadraticMoment S (p n)) / gaussianQuadraticLower S T :=
          div_le_div_of_nonneg_left (mul_nonneg hscale (gaussianQuadraticMoment_nonneg _ _)) hD (hDZ k hk)
        _ = A n * t ^ n.val := by dsimp only [A]; ring
        _ ≤ B * t ^ n.val := mul_le_mul_of_nonneg_right (hAB n) (pow_nonneg ht _)
    exact ⟨Hbound _ (hc k (hUV hk) n).1 (fun g => (hb k (hUV hk) g n).1),
      Hbound _ (hc k (hUV hk) n).2.1 (fun g => (hb k (hUV hk) g n).2.1),
      Hbound _ (hc k (hUV hk) n).2.2 (fun g => (hb k (hUV hk) g n).2.2)⟩

theorem nonlinearPartitionKJet_integral_control
    {F : Fin 4 → ℝ → ℝ → MomentKJet} {U V : Set ℝ} {m S T L M t : ℝ}
    (hV : IsOpen V) (hUV : U ⊆ V) (hm : m ∈ Icc (0 : ℝ) 1)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hL : 0 ≤ L) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hc : ∀ k ∈ V, ∀ i, Continuous (fun g => (F i k g).value) ∧
      Continuous (fun g => (F i k g).first) ∧ Continuous (fun g => (F i k g).second))
    (hd : ∀ g k, k ∈ V → ∀ i, MomentKJet.Differentiates (fun x => F i x g) k)
    (hE : ∀ k ∈ V, ∀ g,
      Real.exp (m * (F 0 k g).value) ≤ Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2))
    (h₁ : ∀ k ∈ V, ∀ g, |(F 0 k g).first| ≤ L * (1 + g ^ 2))
    (h₂ : ∀ k ∈ V, ∀ g, |(F 0 k g).second| ≤ L * (1 + g ^ 2))
    (hjets : ∀ k ∈ V, ∀ g, ∀ i : Fin 3,
      MomentKJet.Bound (F i.succ k g) ((M * t * (1 + g ^ 2) ^ 3) ^ (i.val + 1)))
    (hlower : ∀ k ∈ U, ∀ g,
      Real.exp (-S * |g| - T * g ^ 2) ≤ Real.exp (m * (F 0 k g).value)) :
    let J := fun n k g => nonlinearPartitionKJet m (fun i => F i k g) n
    let B := 1 + ∑ n : Fin 4, (232 * (L + 1) ^ 2 * M ^ n.val) *
      gaussianQuadraticMoment S (3 * n.val + 2) / gaussianQuadraticLower S T
    1 ≤ B ∧ PartitionIntegralKControl
      (fun n k g => (J n k g).value) (fun n k g => (J n k g).first)
      (fun n k g => (J n k g).second) U B t := by
  apply partitionIntegralKControl_of_gaussian_envelopes
    (C := fun n => 232 * (L + 1) ^ 2 * M ^ n.val) (p := fun n => 3 * n.val + 2)
    hV hUV hS hT ht (fun n => by positivity)
  · intro k hk n
    have H := nonlinearPartitionKJet_noise_continuous (hc k hk) m n
    exact ⟨H.1.aestronglyMeasurable, H.2.1.aestronglyMeasurable, H.2.2.aestronglyMeasurable⟩
  · intro g k hk n
    exact nonlinearPartitionKJet_differentiates (hd g k hk) m n
  · intro k hk g n
    exact nonlinearPartitionKJet_gaussian_envelope hm hL hM ht
      (hE k hk g) (h₁ k hk g) (h₂ k hk g) (hjets k hk g) n
  · intro k hk g
    change Real.exp (-S * |g| - T * g ^ 2) ≤ Real.exp (m * (F 0 k g).value) * 1
    simpa only [mul_one] using hlower k hk g

theorem PartitionIntegralKControl.const_mul
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {U : Set ℝ} {B t : ℝ}
    (H : PartitionIntegralKControl W W₁ W₂ U B t) {c : ℝ} (hc : c ≠ 0) :
    PartitionIntegralKControl (fun n k g => c * W n k g)
      (fun n k g => c * W₁ n k g) (fun n k g => c * W₂ n k g) U B t := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simpa only [partitionIntegral, integral_const_mul] using mul_ne_zero hc (H.nonzero k hk)
  · intro k hk n
    exact ⟨(H.domination k hk n).1.const_mul c, (H.domination k hk n).2.const_mul c⟩
  · intro k hk n
    simpa only [partitionIntegral, integral_const_mul, mul_div_mul_left _ _ hc] using H.bounds k hk n

theorem epsilonPartitionWeight_eq_nonlinearPartitionKJet
    (w : ℝ × Vec3) (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (x : Vec3) (ε g : ℝ) (F : Fin 4 → MomentKJet)
    (hF : ∀ i, (F i).value = epsilonSuffixNoiseJet l Q K w x i ε g) (n : Fin 4) :
    epsilonPartitionWeight (w :: l) Q K x ε n g = (nonlinearPartitionKJet w.1 F n).value := by
  rw [nonlinearPartitionKJet_value]
  simp_rw [hF]
  fin_cases n <;>
    simp only [epsilonPartitionWeight, NonlinearEpsilonStep.weight,
      NonlinearEpsilonStep.weightFirst, NonlinearEpsilonStep.weightSecond,
      NonlinearEpsilonStep.weightThird, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    norm_num <;> ring

def momentKJetAlongCurve (F : ℝ × Vec3 → ℝ) (y y₁ y₂ : ℝ → Vec3) (k : ℝ) : MomentKJet :=
  ⟨F (k, y k), fderiv ℝ F (k, y k) (1, y₁ k),
    fderiv ℝ (fderiv ℝ F) (k, y k) (1, y₁ k) (1, y₁ k) +
      fderiv ℝ F (k, y k) (0, y₂ k)⟩

theorem momentKJetAlongCurve_differentiates {F : ℝ × Vec3 → ℝ}
    (hF : ContDiff ℝ 2 F) {y y₁ y₂ : ℝ → Vec3} {k : ℝ}
    (hy : HasDerivAt y (y₁ k) k) (hy₁ : HasDerivAt y₁ (y₂ k) k) :
    MomentKJet.Differentiates (momentKJetAlongCurve F y y₁ y₂) k := by
  have hcurve : HasDerivAt (fun x => (x, y x)) (1, y₁ k) k :=
    (hasDerivAt_id k).prodMk hy
  have hvelocity : HasDerivAt (fun x => ((1 : ℝ), y₁ x)) (0, y₂ k) k :=
    (hasDerivAt_const k 1).prodMk hy₁
  have hD := ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (k, y k)).hasFDerivAt.comp_hasDerivAt k hcurve
  exact ⟨(hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt k hcurve,
    hD.clm_apply hvelocity⟩

def quadraticResidualSpatialJet (f : ℝ → ℝ) (z : ℝ) : ℕ → ℝ → ℝ
  | 0 => quadraticTaylorTail f z
  | 1 => quadraticTaylorTailFirst f z
  | 2 => quadraticTaylorTailSecond f z
  | j + 3 => iteratedDeriv (j + 3) f

theorem quadraticResidualSpatialJet_hasDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (z y : ℝ) (j : ℕ) :
    HasDerivAt (quadraticResidualSpatialJet f z j)
      (quadraticResidualSpatialJet f z (j + 1) y) y := by
  cases j with
  | zero => exact (quadraticTaylorTail_derivatives hf z y).1
  | succ j =>
    cases j with
    | zero => exact (quadraticTaylorTail_derivatives hf z y).2
    | succ j =>
      cases j with
      | zero =>
        have heq : quadraticTaylorTailSecond f z =
            fun x => iteratedDeriv 2 f x - iteratedDeriv 2 f z := by
          funext x
          simp only [quadraticTaylorTailSecond, scalarTaylorPolynomial,
            Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
            iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, div_one,
            iteratedDeriv_succ]
        change HasDerivAt (quadraticTaylorTailSecond f z) (iteratedDeriv 3 f y) y
        rw [heq]
        simpa only [← iteratedDeriv_succ] using
          ((hf.differentiable_iteratedDeriv 2
            (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)) y).hasDerivAt).sub_const
              (iteratedDeriv 2 f z)
      | succ j =>
        change HasDerivAt (iteratedDeriv (j + 3) f) (iteratedDeriv ((j + 3) + 1) f y) y
        simpa only [← iteratedDeriv_succ] using
          (hf.differentiable_iteratedDeriv (j + 3)
            (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (j + 3))) y).hasDerivAt

def quadraticResidualSpatialKJet (f : ℝ → ℝ) (z : ℝ) (j : ℕ) (y y₁ y₂ : ℝ) : MomentKJet :=
  ⟨quadraticResidualSpatialJet f z j y,
    quadraticResidualSpatialJet f z (j + 1) y * y₁,
    quadraticResidualSpatialJet f z (j + 2) y * y₁ ^ 2 +
      quadraticResidualSpatialJet f z (j + 1) y * y₂⟩

theorem quadraticResidualSpatialKJet_differentiates {f y y₁ y₂ : ℝ → ℝ} {k z : ℝ}
    (hf : ContDiff ℝ ∞ f) (hy : HasDerivAt y (y₁ k) k) (hy₁ : HasDerivAt y₁ (y₂ k) k)
    (j : ℕ) :
    MomentKJet.Differentiates (fun x => quadraticResidualSpatialKJet f z j (y x) (y₁ x) (y₂ x)) k := by
  refine ⟨(quadraticResidualSpatialJet_hasDerivAt hf z (y k) j).comp k hy, ?_⟩
  convert (((quadraticResidualSpatialJet_hasDerivAt hf z (y k) (j + 1)).comp k hy).mul hy₁) using 1 <;>
    dsimp only [quadraticResidualSpatialKJet, Function.comp_apply, Pi.mul_apply] <;>
    first | rfl | ring

private theorem scalar_curve_jet_bound {a b c v w A D E R : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hE : 0 ≤ E) (hR : 0 ≤ R)
    (ha : |a| ≤ A) (hb : |b| ≤ D) (hc : |c| ≤ E) (hv : |v| ≤ R) (hw : |w| ≤ R) :
    MomentKJet.Bound ⟨a, b * v, c * v ^ 2 + b * w⟩ (A + D * R + E * R ^ 2) := by
  have H₁ : |b * v| ≤ D * R := by
    rw [abs_mul]
    exact mul_le_mul hb hv (abs_nonneg _) hD
  have H₂ : |c * v ^ 2| ≤ E * R ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hc (pow_le_pow_left₀ (abs_nonneg _) hv 2) (by positivity) hE
  have H₃ : |b * w| ≤ D * R := by
    rw [abs_mul]
    exact mul_le_mul hb hw (abs_nonneg _) hD
  refine ⟨ha.trans ?_, H₁.trans ?_, ((abs_add_le _ _).trans (add_le_add H₂ H₃)).trans ?_⟩ <;>
    nlinarith [mul_nonneg hD hR, mul_nonneg hE (sq_nonneg R)]

theorem quadraticResidualSpatialKJet_bound {f : ℝ → ℝ} {B R z y y₁ y₂ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hb : ∀ j : ℕ, 3 ≤ j → j ≤ 5 → ∀ x, |iteratedDeriv j f x| ≤ B)
    (hy : |y - z| ≤ R) (hy₁ : |y₁| ≤ R) (hy₂ : |y₂| ≤ R) (j : Fin 4) :
    MomentKJet.Bound (quadraticResidualSpatialKJet f z j.val y y₁ y₂)
      (4 * B * (1 + R) ^ 2 * R ^ (3 - j.val)) := by
  have H := quadraticTaylorTail_bounds hf (hb 3 le_rfl (by norm_num)) z y
  have H₀ : |quadraticTaylorTail f z y| ≤ B * R ^ 3 / 6 := H.1.trans (by gcongr)
  have H₁ : |quadraticTaylorTailFirst f z y| ≤ B * R ^ 2 / 2 := H.2.1.trans (by gcongr)
  have H₂ : |quadraticTaylorTailSecond f z y| ≤ B * R := H.2.2.trans (by gcongr)
  have H₃ := hb 3 le_rfl (by norm_num) y
  have H₄ := hb 4 (by norm_num) (by norm_num) y
  have H₅ := hb 5 (by norm_num) le_rfl y
  have hlarge : 1 ≤ (1 + R) ^ 2 := by nlinarith
  fin_cases j
  · exact (scalar_curve_jet_bound (by positivity) (by positivity) (by positivity) hR
      H₀ H₁ H₂ hy₁ hy₂).mono (by
        norm_num
        have hp : 0 ≤ B * R ^ 3 := by positivity
        have H := mul_le_mul_of_nonneg_right hlarge hp
        nlinarith [hp])
  · exact (scalar_curve_jet_bound (by positivity) (by positivity) hB hR
      H₁ H₂ H₃ hy₁ hy₂).mono (by
        norm_num
        have H := mul_le_mul_of_nonneg_right hlarge (by positivity : 0 ≤ B * R ^ 2)
        nlinarith)
  · exact (scalar_curve_jet_bound (by positivity) hB hB hR H₂ H₃ H₄ hy₁ hy₂).mono (by
      norm_num
      have H : 2 + R ≤ 4 * (1 + R) ^ 2 := by nlinarith
      have H' := mul_le_mul_of_nonneg_right H (mul_nonneg hB hR)
      nlinarith)
  · exact (scalar_curve_jet_bound hB hB hB hR H₃ H₄ H₅ hy₁ hy₂).mono (by
      norm_num
      have H : 1 + R + R ^ 2 ≤ 4 * (1 + R) ^ 2 := by nlinarith
      have H' := mul_le_mul_of_nonneg_right H hB
      nlinarith)

theorem scalarData_quadraticResidualSpatialKJet_bound {β s h R z y y₁ y₂ : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (hR : 0 ≤ R)
    (hy : |y - z| ≤ R) (hy₁ : |y₁| ≤ R) (hy₂ : |y₂| ≤ R) (j : Fin 4) :
    MomentKJet.Bound
      (quadraticResidualSpatialKJet (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z j.val y y₁ y₂)
      (4 * scalarTerminalJetBound D 5 * (1 + R) ^ 2 * R ^ (3 - j.val)) := by
  exact quadraticResidualSpatialKJet_bound (scalarData_phi_contDiff D ht)
    (scalarTerminalJetBound_nonneg D 5) hR
    (fun j hj hj₅ x => scalarData_jet_le D (by omega) hj₅ ht x) hy hy₁ hy₂ j

end SKBarriers2.Corner
