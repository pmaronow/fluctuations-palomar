module

public import SKBarriers2.Corner.FrozenRowsMoments
public import SKBarriers2.Corner.FrozenDiffJets

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def centeredSpatialWeight (c : Vec3) (ρ : ℝ) (p : ℕ) (x : Vec3) : ℝ :=
  (ρ + ‖x - c‖) ^ p

theorem centeredSpatialWeight_nonneg (c : Vec3) {ρ : ℝ} (hρ : 0 ≤ ρ) (p : ℕ) (x : Vec3) :
    0 ≤ centeredSpatialWeight c ρ p x := by
  unfold centeredSpatialWeight
  positivity

theorem affine_tilt_centered_moment {f ψ : Vec3 → ℝ} {L M ρ : ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (c : Vec3) (p : ℕ) (hbound : ∀ y, |ψ y| ≤ M * centeredSpatialWeight c ρ p y)
    (m : ℝ) (a w : Vec3) :
    let ν := (gaussianReal 0 1).tilted (fun t => m * f (a + t • w))
    Integrable (fun t => ψ (a + t • w)) ν ∧
      |∫ t, ψ (a + t • w) ∂ν| ≤
        (M * (ρ + ‖a - c‖ + ‖w‖) ^ p) * gaussianTiltPolynomialConstant (|m| * L * ‖w‖) p := by
  let ν := (gaussianReal 0 1).tilted (fun t => m * f (a + t • w))
  have hnoise (t : ℝ) : |m * f (a + t • w) - m * f (a + (0 : ℝ) • w)| ≤
      (|m| * L * ‖w‖) * |t| := by
    rw [zero_smul, add_zero, ← mul_sub, abs_mul]
    have H := mul_le_mul_of_nonneg_left (hLip (a + t • w) a) (abs_nonneg m)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at H
    exact H.trans_eq (by ring)
  have hpoly := gaussian_tilt_polynomial_bound (g := fun t => m * f (a + t • w))
    (by fun_prop) (by positivity : 0 ≤ |m| * L * ‖w‖) hnoise p
  have htest (t : ℝ) : |ψ (a + t • w)| ≤
      (M * (ρ + ‖a - c‖ + ‖w‖) ^ p) * (1 + |t|) ^ p := by
    have hn : ρ + ‖a + t • w - c‖ ≤ (ρ + ‖a - c‖ + ‖w‖) * (1 + |t|) := by
      have he : a + t • w - c = (a - c) + t • w := by module
      have H := norm_add_le (a - c) (t • w)
      rw [norm_smul, Real.norm_eq_abs] at H
      rw [he]
      nlinarith [mul_nonneg hρ (abs_nonneg t), mul_nonneg (norm_nonneg (a - c)) (abs_nonneg t),
        norm_nonneg w]
    exact (hbound _).trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hn p) hM).trans_eq (by
        rw [mul_pow]
        ring))
  have hmeas : AEStronglyMeasurable (fun t => ψ (a + t • w)) ν :=
    (hψ.comp (by fun_prop)).aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _)
  have hi : Integrable (fun t => ψ (a + t • w)) ν :=
    (hpoly.1.const_mul (M * (ρ + ‖a - c‖ + ‖w‖) ^ p)).mono' hmeas
      (ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using htest t))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t, |ψ (a + t • w)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ t, (M * (ρ + ‖a - c‖ + ‖w‖) ^ p) * (1 + |t|) ^ p ∂ν :=
      integral_mono hi.abs (hpoly.1.const_mul _) htest
    _ = (M * (ρ + ‖a - c‖ + ‖w‖) ^ p) * ∫ t, (1 + |t|) ^ p ∂ν := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoly.2 (by positivity)

namespace QuadraticTerminal

theorem slope_eq_centerGradient (Q : QuadraticTerminal) (v c : Vec3) :
    Q.slope v c = ∑ i, Q.slopeVector c i * v i := by
  simp only [slope, slopeVector, linearDirection, hessianDirection, Fin.sum_univ_succ]
  ring

theorem slope_abs_le_centerGradient {Q : QuadraticTerminal} {G : ℝ} {c : Vec3} (_hG : 0 ≤ G)
    (hgrad : ∀ i, |Q.slopeVector c i| ≤ G) (v : Vec3) :
    |Q.slope v c| ≤ G * directionSize v := by
  rw [slope_eq_centerGradient]
  calc
    _ ≤ ∑ i, |Q.slopeVector c i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, G * |v i| := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hgrad i) (abs_nonneg (v i)))
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem update_centerGradient (Q : QuadraticTerminal) (m : ℝ) (v c : Vec3) (i : Fin 3) :
    (Q.update m v).slopeVector c i = Q.slopeVector c i +
      m / Q.precision m v * Q.slope v c * Q.hessianDirection v i := by
  simp only [slopeVector, update, slope, linearDirection, Fin.sum_univ_succ]
  ring

theorem update_centerGradient_bound {Q : QuadraticTerminal} {B G m : ℝ} {c : Vec3}
    (hB : 0 < B) (hG : 0 ≤ G) (hQ : ∀ i j, |Q.hessian i j| ≤ B)
    (hgrad : ∀ i, |Q.slopeVector c i| ≤ G) (hm : m ∈ Icc (0 : ℝ) 1)
    (v : Vec3) (hv : 2 * B * directionEnergy v ≤ 1) :
    ∀ i, |(Q.update m v).slopeVector c i| ≤ 2 * G := by
  have hp := (Q.update_small hB hQ hm v hv).1
  have hD : 0 < Q.precision m v := by linarith
  have hcoef : 0 ≤ m / Q.precision m v := div_nonneg hm.1 hD.le
  have hcoef₂ : m / Q.precision m v ≤ 2 := (div_le_iff₀ hD).mpr (by linarith [hm.2])
  intro i
  rw [update_centerGradient]
  calc
    _ ≤ |Q.slopeVector c i| + |m / Q.precision m v * Q.slope v c * Q.hessianDirection v i| := abs_add_le _ _
    _ ≤ G + 2 * (G * directionSize v) * (B * directionSize v) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hcoef]
      exact add_le_add (hgrad i) (mul_le_mul
        (mul_le_mul hcoef₂ (Q.slope_abs_le_centerGradient hG hgrad v) (abs_nonneg _) (by norm_num))
        (Q.hessianDirection_abs_le hB.le hQ v i) (abs_nonneg _) (by positivity [directionSize_nonneg v]))
    _ ≤ 2 * G := by
      have H := mul_le_mul_of_nonneg_left hv hG
      unfold directionEnergy at H
      nlinarith

end QuadraticTerminal

theorem riccati_centerGradient_bound (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    {B G : ℝ} {c : Vec3} (hB : 0 < B) (hG : 0 ≤ G)
    (hQ : ∀ i j, |Q.hessian i j| ≤ B) (hgrad : ∀ i, |Q.slopeVector c i| ≤ G)
    (hm : ∀ w ∈ l, 0 < w.1 ∧ w.1 ≤ 1)
    (hv : ∀ w ∈ l, 2 * (2 ^ l.length * B) * directionEnergy w.2 ≤ 1) :
    ∀ i, |(riccatiRecursion l Q).slopeVector c i| ≤ 2 ^ l.length * G := by
  induction l with
  | nil => simpa only [riccatiRecursion, List.length_nil, pow_zero, one_mul] using hgrad
  | cons w t ih =>
    have he (v : Vec3) : 2 * (2 ^ t.length * B) * directionEnergy v ≤
        2 * (2 ^ (w :: t).length * B) * directionEnergy v := by
      simp only [List.length_cons, pow_succ]
      have H : 0 ≤ (2 : ℝ) ^ t.length * B * directionEnergy v := by positivity [directionEnergy_nonneg v]
      nlinarith
    have hmt := fun v hv' => hm v (List.mem_cons_of_mem w hv')
    have hvt := fun v hv' => (he v.2).trans (hv v (List.mem_cons_of_mem w hv'))
    have ht := riccatiAdmissible_of_small_directions t Q hB hQ hmt hvt
    have hg := ih hmt hvt
    have H := QuadraticTerminal.update_centerGradient_bound
      (Q := riccatiRecursion t Q) (by positivity : 0 < 2 ^ t.length * B)
      (by positivity : 0 ≤ 2 ^ t.length * G) ht.2 hg ⟨(hm w List.mem_cons_self).1.le,
        (hm w List.mem_cons_self).2⟩ w.2 ((he w.2).trans (hv w List.mem_cons_self))
    intro i
    exact (H i).trans_eq (by simp only [List.length_cons, pow_succ]; ring)

theorem completedSquare_centered_moment (Q : QuadraticTerminal)
    {L M ρ A m : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (_hA : 0 ≤ A)
    (v c : Vec3) (hD : 0 < Q.precision m v)
    {f ψ : Vec3 → ℝ} (hf : Continuous f) (hψ : Continuous ψ)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (p : ℕ) (hbound : ∀ y, |ψ y| ≤ M * centeredSpatialWeight c ρ p y)
    (hscale : ∀ x, ρ + ‖quadraticMeanTransition Q m v x - c‖ +
      ‖(Real.sqrt (Q.precision m v)⁻¹) • v‖ ≤ A * (ρ + ‖x - c‖)) (x : Vec3) :
    |(∫ t, Real.exp (m * (Q.value (x + t • v) + f (x + t • v))) * ψ (x + t • v)
        ∂gaussianReal 0 1) /
      (∫ t, Real.exp (m * (Q.value (x + t • v) + f (x + t • v))) ∂gaussianReal 0 1)| ≤
      (M * A ^ p * gaussianTiltPolynomialConstant
        (|m| * L * ‖(Real.sqrt (Q.precision m v)⁻¹) • v‖) p) * centeredSpatialWeight c ρ p x := by
  rw [completedSquare_normalized_moment Q m v x hD hf hψ hLip]
  have H := (affine_tilt_centered_moment hf hψ hL hM hρ hLip c p hbound m
    (quadraticMeanTransition Q m v x) ((Real.sqrt (Q.precision m v)⁻¹) • v)).2
  refine H.trans ?_
  calc
    _ ≤ (M * (A * (ρ + ‖x - c‖)) ^ p) * gaussianTiltPolynomialConstant
        (|m| * L * ‖(Real.sqrt (Q.precision m v)⁻¹) • v‖) p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (hscale x) p) hM)
        (gaussianTiltPolynomialConstant_pos _ _).le
    _ = _ := by unfold centeredSpatialWeight; rw [mul_pow]; ring

theorem norm_le_directionSize (v : Vec3) : ‖v‖ ≤ directionSize v := by
  apply (pi_norm_le_iff_of_nonneg (directionSize_nonneg v)).mpr
  intro i
  change |v i| ≤ ∑ j, |v j|
  exact Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)

theorem quadraticMeanTransition_center_bound {Q : QuadraticTerminal} {G m : ℝ}
    {v c : Vec3} (hG : 0 ≤ G) (hgrad : ∀ i, |Q.slopeVector c i| ≤ G)
    (hm : m ∈ Icc (0 : ℝ) 1) (hp : 1 / 2 ≤ Q.precision m v) :
    ‖quadraticMeanTransition Q m v c - c‖ ≤ 2 * G * directionEnergy v := by
  have hD : 0 < Q.precision m v := by linarith
  have hcoef : 0 ≤ m / Q.precision m v := div_nonneg hm.1 hD.le
  have hcoef₂ : m / Q.precision m v ≤ 2 := (div_le_iff₀ hD).mpr (by linarith [hm.2])
  have he : quadraticMeanTransition Q m v c - c = (m / Q.precision m v * Q.slope v c) • v := by
    ext i
    simp only [quadraticMeanTransition, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoef]
  exact (mul_le_mul
    (mul_le_mul hcoef₂ (Q.slope_abs_le_centerGradient hG hgrad v) (abs_nonneg _) (by norm_num))
    (norm_le_directionSize v) (norm_nonneg _) (by positivity [directionSize_nonneg v])).trans_eq (by
      unfold directionEnergy
      ring)

theorem quadraticTransition_centered_scale {Q : QuadraticTerminal} {B G K ρ m : ℝ}
    {v c : Vec3} (hB : 0 ≤ B) (hG : 0 ≤ G) (hK : 0 ≤ K) (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hQ : ∀ i j, |Q.hessian i j| ≤ B) (hgrad : ∀ i, |Q.slopeVector c i| ≤ G)
    (hm : m ∈ Icc (0 : ℝ) 1) (hp : 1 / 2 ≤ Q.precision m v)
    (hsmall : 6 * B * directionEnergy v ≤ 1)
    (hv : ‖v‖ ≤ K * ρ) (henergy : directionEnergy v ≤ K ^ 2 * ρ ^ 2) :
    ‖(Real.sqrt (Q.precision m v)⁻¹) • v‖ ≤ 2 * K * ρ ∧
      ∀ x, ρ + ‖quadraticMeanTransition Q m v x - c‖ +
        ‖(Real.sqrt (Q.precision m v)⁻¹) • v‖ ≤
          (3 + 2 * G * K ^ 2 + 2 * K) * (ρ + ‖x - c‖) := by
  have hρ₀ : 0 ≤ ρ := hρ.1
  have hE : 0 ≤ directionEnergy v := directionEnergy_nonneg v
  have hD : 0 < Q.precision m v := by linarith
  have hI : (Q.precision m v)⁻¹ ≤ 2 := by
    have H := one_div_le_one_div_of_le (by norm_num : 0 < (1 / 2 : ℝ)) hp
    simpa only [one_div, inv_div, inv_one, div_one, inv_inv] using H
  have hsqrt : Real.sqrt (Q.precision m v)⁻¹ ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hw : ‖(Real.sqrt (Q.precision m v)⁻¹) • v‖ ≤ 2 * K * ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul hsqrt hv (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hS : 1 + 3 * m * B * directionEnergy v / Q.precision m v ≤ 2 := by
    have Hm : 3 * m * B * directionEnergy v ≤ 3 * B * directionEnergy v := by
      have H := mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 3 * B * directionEnergy v)
      nlinarith
    have H : 3 * m * B * directionEnergy v ≤ Q.precision m v := by linarith
    have H' := (div_le_one hD).mpr H
    linarith
  have hcent : ‖quadraticMeanTransition Q m v c - c‖ ≤ 2 * G * K ^ 2 * ρ := by
    calc
      _ ≤ 2 * G * directionEnergy v := quadraticMeanTransition_center_bound hG hgrad hm hp
      _ ≤ 2 * G * (K ^ 2 * ρ ^ 2) := mul_le_mul_of_nonneg_left henergy (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * G * K ^ 2 * ρ) (sub_nonneg.mpr hρ.2)]
  refine ⟨hw, ?_⟩
  intro x
  have hx : ‖quadraticMeanTransition Q m v x - c‖ ≤ 2 * ‖x - c‖ + 2 * G * K ^ 2 * ρ := by
    have he : quadraticMeanTransition Q m v x - c =
        (quadraticMeanTransition Q m v x - quadraticMeanTransition Q m v c) +
          (quadraticMeanTransition Q m v c - c) := by module
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add
      ((quadraticMeanTransition_lipschitz Q hB hQ hm.1 v hD x c).trans
        (mul_le_mul_of_nonneg_right hS (norm_nonneg _))) hcent)
  have H₀ := mul_nonneg (by positivity : 0 ≤ 1 + 2 * G * K ^ 2 + 2 * K) (norm_nonneg (x - c))
  nlinarith

theorem terminalTaylorQuadratic_scaled_centerGradient (β : ℝ) (α : ℝ → ℝ)
    (s h z ε : ℝ) (i : Fin 3) :
    ((terminalTaylorQuadratic β α s h z).scale (1 - ε)).slopeVector (fun _ => z) i =
      (1 - ε) * jet β α 1 (s + 4 * h) z := by
  fin_cases i <;>
    norm_num [QuadraticTerminal.slopeVector, QuadraticTerminal.scale, terminalTaylorQuadratic,
      separableTaylorQuadratic, Fin.sum_univ_succ]
  all_goals ring

theorem frozenSchedule_centered_direction_scale {β a h k : ℝ}
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) {w : ℝ × Vec3}
    (hw : w ∈ frozenSchedule β a (1 / 2) h k) :
    ‖w.2‖ ≤ (6 * (|β| + 1)) * Real.sqrt h ∧
      directionEnergy w.2 ≤ (6 * (|β| + 1)) ^ 2 * (Real.sqrt h) ^ 2 := by
  have hE : directionEnergy w.2 ≤ 36 * β ^ 2 * h := by
    calc
      _ ≤ 3 * squaredLength w.2 := directionEnergy_le_squaredLength _
      _ ≤ 3 * chainEnergy (frozenSchedule β a (1 / 2) h k) :=
        mul_le_mul_of_nonneg_left (squaredLength_le_chainEnergy hw) (by norm_num)
      _ = _ := by rw [frozenSchedule_chainEnergy β a h k hh hk]; ring
  have hβ : 36 * β ^ 2 ≤ (6 * (|β| + 1)) ^ 2 := by nlinarith [sq_abs β, abs_nonneg β]
  have HE : directionEnergy w.2 ≤ (6 * (|β| + 1)) ^ 2 * (Real.sqrt h) ^ 2 := by
    rw [Real.sq_sqrt hh]
    exact hE.trans (mul_le_mul_of_nonneg_right hβ hh)
  refine ⟨(norm_le_directionSize w.2).trans ?_, HE⟩
  have hsize := directionSize_nonneg w.2
  have hright : 0 ≤ (6 * (|β| + 1)) * Real.sqrt h := by positivity
  unfold directionEnergy at HE
  nlinarith

theorem scalarData_frozen_centered_moment_transitions {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ T : ℝ, 0 < h₀ ∧ 1 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∀ M : ℝ, 0 ≤ M → ∀ p : ℕ, p ≤ 9 → ∀ ψ : Vec3 → ℝ, Continuous ψ →
        (∀ y, |ψ y| ≤ M * centeredSpatialWeight (fun _ => z) (Real.sqrt h) p y) →
        ∀ x : Vec3,
          let F := epsilonChain t
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) ε
          |(∫ g, Real.exp (w.1 * F (x + g • w.2)) * ψ (x + g • w.2) ∂gaussianReal 0 1) /
            (∫ g, Real.exp (w.1 * F (x + g • w.2)) ∂gaussianReal 0 1)| ≤
              T * M * centeredSpatialWeight (fun _ => z) (Real.sqrt h) p x := by
  rcases scalarData_frozen_suffix_lipschitz_frames D hl hu with ⟨hF, L, hhF, hL, HF⟩
  let B := scalarTerminalJetBound D 3 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 3]
  let G := (2 : ℝ) ^ 12 * (2 * B)
  have hG : 0 < G := by dsimp only [G]; positivity
  let K := 6 * (|β| + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  let A := 3 + 2 * G * K ^ 2 + 2 * K
  have hA : 0 < A := by dsimp only [A]; positivity
  let R := 2 * L * K
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let C : Fin 10 → ℝ := fun i => A ^ i.val * gaussianTiltPolynomialConstant R i.val
  have hC (i : Fin 10) : 0 ≤ C i := mul_nonneg (pow_nonneg hA.le _) (gaussianTiltPolynomialConstant_pos _ _).le
  let T := 1 + ∑ i : Fin 10, C i
  have hT : 1 ≤ T := by
    have H := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 10))) => hC i)
    dsimp only [T]
    linarith
  have hCT (p : ℕ) (hp : p ≤ 9) : A ^ p * gaussianTiltPolynomialConstant R p ≤ T := by
    let i : Fin 10 := ⟨p, by omega⟩
    have H := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 10))) => hC j)
      (Finset.mem_univ i)
    dsimp only [T]
    exact H.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  let S := 72 * (2 ^ 12 * (20 * B)) * (β ^ 2 + 1)
  have hS : 0 < S := by dsimp only [S]; positivity
  let h₀ := min hF (min 1 (min (l / 2) (min ((D.q - u) / 6) S⁻¹)))
  have hh₀ : 0 < h₀ := lt_min hhF (lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (inv_pos.mpr hS))))
  refine ⟨h₀, T, hh₀, hT, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε w t ht M hM p hp ψ hψ hψbound x
  have hhF' : h ≤ hF := hhsmall.trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhS : h ≤ S⁻¹ :=
    (((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let Qε := Q.scale (1 - ε)
  let Qt := riccatiRecursion t Qε
  let c : Vec3 := fun _ => z
  have hε' : ε ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have htt : t <:+ full := (List.suffix_cons w t).trans ht
  have hmem : w ∈ full := ht.subset List.mem_cons_self
  have hlen : t.length ≤ 12 := by simpa only [full, frozenSchedule_length] using htt.length_le
  have hmfull := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hm : w.1 ∈ Icc (0 : ℝ) 1 := ⟨(hmfull w hmem).1.le, (hmfull w hmem).2⟩
  have hsmall : 72 * (2 ^ 12 * (20 * B)) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ S * h := by dsimp only [S]; nlinarith
      _ ≤ S * S⁻¹ := mul_le_mul_of_nonneg_left hhS hS.le
      _ = 1 := mul_inv_cancel₀ hS.ne'
  have hnoise (v : ℝ × Vec3) (hv : v ∈ full) : 2 * (2 ^ 12 * (20 * B)) * directionEnergy v.2 ≤ 1 := by
    simpa only [frozenSchedule_length] using
      frozenSchedule_small_directions β _ h k (B := 20 * B) (by positivity) hh.le hk hsmall v hv
  have hQ : ∀ i j, |Qε.hessian i j| ≤ 2 * B := by
    intro i j
    change |(1 - ε) * Q.hessian i j| ≤ _
    rw [abs_mul]
    have H := terminalTaylorQuadratic_hessian_bound β α (r - h) h z B hB.le
      ((scalarData_jet_le D (r := 3) (by norm_num) (by norm_num) htime z).trans (by
        dsimp only [B]; linarith)) i j
    exact mul_le_mul (abs_le.mpr ⟨by linarith [hε.1, hε.2], by linarith [hε.1, hε.2]⟩)
      H (abs_nonneg _) (by norm_num)
  have hgrad : ∀ i, |Qε.slopeVector c i| ≤ 2 * B := by
    intro i
    rw [terminalTaylorQuadratic_scaled_centerGradient]
    rw [abs_mul]
    have H := (scalarData_jet_le D (r := 3) (by norm_num : 1 ≤ 1) (by norm_num) htime z).trans
      (by dsimp only [B]; linarith : scalarTerminalJetBound D 3 ≤ B)
    exact mul_le_mul (abs_le.mpr ⟨by linarith [hε.1, hε.2], by linarith [hε.1, hε.2]⟩)
      H (abs_nonneg _) (by norm_num)
  have hvt (v : ℝ × Vec3) (hv : v ∈ t) : 2 * (2 ^ t.length * (2 * B)) * directionEnergy v.2 ≤ 1 := by
    refine le_trans ?_ (hnoise v (htt.subset hv))
    apply mul_le_mul_of_nonneg_right _ (directionEnergy_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : 0 ≤ (2 : ℝ))
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen)
      (by linarith : 2 * B ≤ 20 * B) (by positivity) (by positivity)
  have hess : ∀ i j, |Qt.hessian i j| ≤ G := by
    intro i j
    exact ((riccatiAdmissible_of_small_directions t Qε (by positivity) hQ
      (fun v hv => hmfull v (htt.subset hv)) hvt).2 i j).trans
      (by
        dsimp only [G]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen) (by positivity))
  have grad : ∀ i, |Qt.slopeVector c i| ≤ G := by
    intro i
    exact (riccati_centerGradient_bound t Qε (by positivity) (by positivity) hQ hgrad
      (fun v hv => hmfull v (htt.subset hv)) hvt i).trans (by
        dsimp only [G]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen) (by positivity))
  have hprec : 1 / 2 ≤ Qt.precision w.1 w.2 :=
    (HF r hr h hh hhF' k hk z ε hε' (w :: t) ht).2.1 _ List.mem_cons_self
  rcases (HF r hr h hh hhF' k hk z ε hε' t htt).2.2 with ⟨f, hf, hLip, hfeq⟩
  have hsmallw : 6 * G * directionEnergy w.2 ≤ 1 := by
    refine le_trans ?_ (hnoise w hmem)
    apply mul_le_mul_of_nonneg_right _ (directionEnergy_nonneg _)
    dsimp only [G]
    norm_num
    linarith
  have hdir := frozenSchedule_centered_direction_scale hh.le hk hmem
  have hρ : Real.sqrt h ∈ Icc (0 : ℝ) 1 := ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hh₁⟩
  have Hscale := quadraticTransition_centered_scale hG.le hG.le hK.le hρ hess grad hm hprec
    hsmallw hdir.1 hdir.2
  have H := completedSquare_centered_moment Qt hL.le hM (Real.sqrt_nonneg h) hA.le w.2 c
    (by linarith : 0 < Qt.precision w.1 w.2) hf hψ hLip p hψbound Hscale.2 x
  change |(∫ g, Real.exp (w.1 * epsilonChain t Q (terminalResidual β α (r - h) h z) ε (x + g • w.2)) *
      ψ (x + g • w.2) ∂gaussianReal 0 1) / _| ≤ _
  rw [hfeq]
  refine H.trans ?_
  have hR' : |w.1| * L * ‖(Real.sqrt (Qt.precision w.1 w.2)⁻¹) • w.2‖ ≤ R := by
    rw [abs_of_nonneg hm.1]
    calc
      _ ≤ 1 * L * (2 * K * Real.sqrt h) := by
        gcongr
        · exact hm.2
        · exact Hscale.1
      _ ≤ R := by dsimp only [R]; nlinarith [mul_le_mul_of_nonneg_left hρ.2 (by positivity : 0 ≤ 2 * L * K)]
  have HC : A ^ p * gaussianTiltPolynomialConstant
      (|w.1| * L * ‖(Real.sqrt (Qt.precision w.1 w.2)⁻¹) • w.2‖) p ≤ T :=
    (mul_le_mul_of_nonneg_left (gaussianTiltPolynomialConstant_mono hR' p) (pow_nonneg hA.le _)).trans (hCT p hp)
  exact mul_le_mul_of_nonneg_right
    (by nlinarith [mul_le_mul_of_nonneg_left HC hM] : M * A ^ p *
      gaussianTiltPolynomialConstant (|w.1| * L * ‖(Real.sqrt (Qt.precision w.1 w.2)⁻¹) • w.2‖) p ≤ T * M)
    (centeredSpatialWeight_nonneg c (Real.sqrt_nonneg h) p x)

theorem scalarData_frozen_suffix_joint_epsilon_jets {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ l / 2 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      (∀ t : List (ℝ × Vec3),
        t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        EpsilonJetControl (fun e => epsilonChain t
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
          (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e) (Ioo (-1 : ℝ) 2)) ∧
      ∀ w t, w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        ∃ P : QuadraticTerminal, 1 / 2 ≤ P.precision w.1 w.2 ∧
          ∀ e ∈ Ioo (-1 : ℝ) 2, ∀ x,
            epsilonChain t (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
              (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e x ≤ P.value x := by
  rcases scalarData_frozen_suffix_lipschitz_frames D hl hu with ⟨hF, C, hhF, hC, HF⟩
  let B : ℝ := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  let R : ℝ := 72 * (2 ^ 12 * (20 * B)) * (β ^ 2 + 1)
  have hR : 0 < R := by dsimp only [R]; positivity
  let h₀ := min hF (min (l / 2) (min ((D.q - u) / 6) R⁻¹))
  have hh₀ : 0 < h₀ := lt_min hhF (lt_min (by positivity) (lt_min (by positivity) (inv_pos.mpr hR)))
  have hhl₀ : h₀ ≤ l / 2 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨h₀, hh₀, hhl₀, ?_⟩
  intro r hr h hh hhsmall k hk z
  have hhF' : h ≤ hF := hhsmall.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := hhsmall.trans hhl₀
  have hhq : h ≤ (D.q - u) / 6 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhR : h ≤ R⁻¹ :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let K := terminalResidual β α (r - h) h z
  let P := terminalUpperQuadratic β α (r - h) h z B
  have hUS : Ioo (-1 : ℝ) 2 ⊆ Icc (-1 : ℝ) 2 := fun _ he => ⟨he.1.le, he.2.le⟩
  have hm := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hsmall : 72 * (2 ^ 12 * (20 * B)) * β ^ 2 * h ≤ 1 := by
    calc
      _ ≤ R * h := by dsimp only [R]; nlinarith
      _ ≤ R * R⁻¹ := mul_le_mul_of_nonneg_left hhR hR.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hR)
  have hstartup (j : List (ℝ × Vec3)) (hj : j <:+ full) :
      RiccatiAdmissible j P ∧ ∀ d ∈ riccatiPrecisions j P, 1 / 2 ≤ d := by
    have hlen : j.length ≤ 12 := by simpa only [full, frozenSchedule_length] using hj.length_le
    have hmass : ∀ v ∈ j, 0 < v.1 ∧ v.1 ≤ 1 := fun v hv => hm v (hj.subset hv)
    have hv (v : ℝ × Vec3) (hv : v ∈ j) : 2 * (2 ^ j.length * (20 * B)) * directionEnergy v.2 ≤ 1 := by
      have H := frozenSchedule_small_directions β _ h k (B := 20 * B) (by positivity)
        hh.le hk hsmall v (hj.subset hv)
      rw [frozenSchedule_length] at H
      refine le_trans ?_ H
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen)
          (by positivity : 0 ≤ 20 * B)) (by norm_num : 0 ≤ (2 : ℝ))) (directionEnergy_nonneg _)
    exact ⟨(riccatiAdmissible_of_small_directions j P (by positivity : 0 < 20 * B)
      (terminalUpperQuadratic_hessian hB.le) hmass hv).1,
      riccatiPrecisions_ge_half j P (by positivity : 0 < 20 * B)
        (terminalUpperQuadratic_hessian hB.le) hmass hv⟩
  have hf (j : List (ℝ × Vec3)) (hj : j <:+ full) (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 2) :
      RiccatiAdmissible j (Q.scale (1 - e)) ∧ ∃ g : Vec3 → ℝ, Continuous g ∧
        (∀ x y, |g x - g y| ≤ C * ‖x - y‖) ∧
        epsilonChain j Q K e = fun x => (riccatiRecursion j (Q.scale (1 - e))).value x + g x := by
    have H := HF r hr h hh hhF' k hk z e he j hj
    exact ⟨H.1, H.2.2⟩
  have h₁ (y : ℝ) : |jet β α 1 ((r - h) + 4 * h) y| ≤ B :=
    (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) ht y).trans (by dsimp only [B]; linarith)
  have h₂ : |jet β α 2 ((r - h) + 4 * h) z| ≤ B :=
    (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) ht z).trans (by dsimp only [B]; linarith)
  have hbase (e : ℝ) (he : e ∈ Ioo (-1 : ℝ) 2) (x : Vec3) : Q.value x + e * K x ≤ P.value x :=
    terminal_epsilon_le_upper_quadratic β α (r - h) h z B hB.le (scalarData_phi_regular D ht) h₁ h₂
      (abs_le.mpr ⟨by linarith [he.1], by linarith [he.2]⟩) x
  have hmajor (w : ℝ × Vec3) (j : List (ℝ × Vec3)) (hj : w :: j <:+ full) :
      ∃ Pj : QuadraticTerminal, 1 / 2 ≤ Pj.precision w.1 w.2 ∧
        ∀ e ∈ Ioo (-1 : ℝ) 2, ∀ x, epsilonChain j Q K e x ≤ Pj.value x := by
    have hj' := (List.suffix_cons w j).trans hj
    refine ⟨riccatiRecursion j P, (hstartup (w :: j) hj).2 _ List.mem_cons_self, ?_⟩
    exact epsilonChain_common_majorant j Q P K hUS (hstartup j hj').1
      (fun v hv => (hm v (hj'.subset hv)).1) (fun t ht => hf t (ht.trans hj')) hbase
  have hKc : Continuous K := terminalResidual_continuous β α (r - h) h z (scalarData_phi_regular D ht)
  have hKg : UniformPolynomialGrowth (Ioo (-1 : ℝ) 2) (fun _ => K) :=
    terminalResidual_uniformPolynomialGrowth β α (r - h) h z B hB.le (scalarData_phi_regular D ht) h₁ h₂ _
  have Hcontrols (j : List (ℝ × Vec3)) (hj : j <:+ full) :
      EpsilonJetControl (fun e => epsilonChain j Q K e) (Ioo (-1 : ℝ) 2) :=
    epsilonJetControl_chain j Q K isOpen_Ioo isCompact_Icc hUS hC.le hKc hKg
      (fun v hv => (hm v (hj.subset hv)).1)
      (fun t ht => hf t (ht.trans hj)) (fun w t ht => hmajor w t (ht.trans hj))
  exact ⟨Hcontrols, hmajor⟩

theorem EpsilonChainDominationOn.drop {l : List (ℝ × Vec3)} {Q : QuadraticTerminal}
    {K : Vec3 → ℝ} {U : Set ℝ} (H : EpsilonChainDominationOn l Q K U) (j : ℕ) :
    EpsilonChainDominationOn (l.drop j) Q K U := by
  induction j generalizing l with
  | zero => simpa only [List.drop_zero] using H
  | succ j ih =>
    cases l with
    | nil => exact True.intro
    | cons w t => simpa only [List.drop_succ_cons] using ih H.1

theorem scalarData_frozen_partition_pos {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j : ℕ, j < 12 →
        0 < partitionIntegral (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j) 0 k := by
  rcases scalarData_frozen_suffix_polynomial_bounds D hl hu with ⟨h₀, hh₀, hhl, HP⟩
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε j hj
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let K := terminalResidual β α (r - h) h z
  have hs : 0 < r - h := by linarith [hr.1, hhsmall.trans hhl]
  have hm := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have H : EpsilonChainDominationOn full Q K (Ioo (-1 : ℝ) 2) :=
    epsilonChainDominationOn_of_polynomial_bounds isOpen_Ioo
      (fun w hw => ne_of_gt (hm w hw).1) (HP r hr h hh hhsmall k hk z)
  have HD := H.drop j
  have hlen : 0 < (full.drop j).length := by
    rw [List.length_drop]
    simp only [full, frozenSchedule_length]
    omega
  cases heq : full.drop j with
  | nil => simp only [heq, List.length_nil, lt_self_iff_false] at hlen
  | cons w t =>
    rw [heq] at HD
    have hε' : ε ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
    change 0 < ∫ g, epsilonPartitionWeight (full.drop j) Q K (fun _ => z) ε 0 g ∂gaussianReal 0 1
    rw [heq]
    exact integral_exp_pos ((HD.2 (fun _ => z) ε hε').1.integrable)

theorem epsilonStep_jet_values {F : ℝ → Vec3 → ℝ} {U : Set ℝ}
    (H : EpsilonJetControl F U) (hU : IsOpen U) (P : QuadraticTerminal) {m : ℝ}
    (hm : 0 < m) (v : Vec3) (hP : 1 / 2 ≤ P.precision m v)
    (hmajor : ∀ e ∈ U, ∀ y, F e y ≤ P.value y) :
    let f₁ := epsilonSpatialJet F 1
    let f₂ := epsilonSpatialJet F 2
    let f₃ := epsilonSpatialJet F 3
    let A₁ := epsilonMoment m v F f₁
    let A₂ := epsilonMoment m v F (fun e x => f₂ e x + m * f₁ e x ^ 2)
    let A₃ := epsilonMoment m v F (fun e x => f₃ e x + 3 * m * f₁ e x * f₂ e x + m ^ 2 * f₁ e x ^ 3)
    ∀ e ∈ U, ∀ x : Vec3,
      epsilonSpatialJet (fun e => vectorStep m v (F e)) 1 e x = A₁ e x ∧
      epsilonSpatialJet (fun e => vectorStep m v (F e)) 2 e x = A₂ e x - m * A₁ e x ^ 2 ∧
      epsilonSpatialJet (fun e => vectorStep m v (F e)) 3 e x =
        A₃ e x - 3 * m * A₁ e x * A₂ e x + 2 * m ^ 2 * A₁ e x ^ 3 := by
  let f₁ := epsilonSpatialJet F 1
  let f₂ := epsilonSpatialJet F 2
  let f₃ := epsilonSpatialJet F 3
  let ψ₁ := f₁
  let ψ₂ : ℝ → Vec3 → ℝ := fun e x => f₂ e x + m * f₁ e x ^ 2
  let ψ₃ : ℝ → Vec3 → ℝ := fun e x => f₃ e x + 3 * m * f₁ e x * f₂ e x + m ^ 2 * f₁ e x ^ 3
  let Z : ℝ → Vec3 → ℝ := fun e x => ∫ t, Real.exp (m * F e (x + t • v)) ∂gaussianReal 0 1
  let Z₁ : ℝ → Vec3 → ℝ := fun e x => m * ∫ t, Real.exp (m * F e (x + t • v)) * ψ₁ e (x + t • v) ∂gaussianReal 0 1
  let Z₂ : ℝ → Vec3 → ℝ := fun e x => m * ∫ t, Real.exp (m * F e (x + t • v)) * ψ₂ e (x + t • v) ∂gaussianReal 0 1
  let Z₃ : ℝ → Vec3 → ℝ := fun e x => m * ∫ t, Real.exp (m * F e (x + t • v)) * ψ₃ e (x + t • v) ∂gaussianReal 0 1
  have hd (x : Vec3) (e : ℝ) (he : e ∈ U) : HasDerivAt (fun a => Z a x) (Z₁ e x) e ∧
      HasDerivAt (fun a => Z₁ a x) (Z₂ e x) e ∧ HasDerivAt (fun a => Z₂ a x) (Z₃ e x) e := by
    have H' := H.integral_controls hU P hm.le v hP hmajor x he
    simpa only [NonlinearEpsilonStep.weight, NonlinearEpsilonStep.weightFirst,
      NonlinearEpsilonStep.weightSecond, NonlinearEpsilonStep.weightThird, integral_const_mul] using
      And.intro H'.1.hasDerivAt (And.intro H'.2.1.hasDerivAt H'.2.2.hasDerivAt)
  have hZ (e : ℝ) (he : e ∈ U) (x : Vec3) : Z e x ≠ 0 :=
    ne_of_gt (integral_exp_pos (H.integral_controls hU P hm.le v hP hmajor x he).1.integrable)
  let A₁ := epsilonMoment m v F ψ₁
  let A₂ := epsilonMoment m v F ψ₂
  let A₃ := epsilonMoment m v F ψ₃
  let G : ℝ → Vec3 → ℝ := fun e => vectorStep m v (F e)
  have hfun (x : Vec3) : (fun e => G e x) = fun e => Real.log (Z e x) / m := by
    funext e
    simp only [G, vectorStep, gaussianStep, ite_eq_right (ne_of_gt hm), positiveGaussianLogStep, Z]
  have hids (e : ℝ) (he : e ∈ U) (x : Vec3) :
      epsilonSpatialJet G 1 e x = A₁ e x ∧
      epsilonSpatialJet G 2 e x = A₂ e x - m * A₁ e x ^ 2 ∧
      epsilonSpatialJet G 3 e x = A₃ e x - 3 * m * A₁ e x * A₂ e x + 2 * m ^ 2 * A₁ e x ^ 3 := by
    have H' := logPartition_jet_values hU (ne_of_gt hm) he
      (fun a ha => (hd x a ha).1) (fun a ha => (hd x a ha).2.1) (fun a ha => (hd x a ha).2.2) (hZ e he x)
    have h₁ : Z₁ e x / (m * Z e x) = A₁ e x := by dsimp only [Z₁, A₁, epsilonMoment, Z]; field_simp
    have h₂ : Z₂ e x / (m * Z e x) = A₂ e x := by dsimp only [Z₂, A₂, epsilonMoment, Z]; field_simp
    have h₃ : Z₃ e x / (m * Z e x) = A₃ e x := by dsimp only [Z₃, A₃, epsilonMoment, Z]; field_simp
    rw [h₁, h₂, h₃] at H'
    simpa only [epsilonSpatialJet, hfun x] using H'
  exact hids

private theorem cubic_moment_polynomials_bound {a b c m R : ℝ} (hR : 0 ≤ R)
    (hm : m ∈ Icc (0 : ℝ) 1) (ha : |a| ≤ R) (hb : |b| ≤ R ^ 2) (hc : |c| ≤ R ^ 3) :
    |b + m * a ^ 2| ≤ 2 * R ^ 2 ∧
      |c + 3 * m * a * b + m ^ 2 * a ^ 3| ≤ 5 * R ^ 3 ∧
      |b - m * a ^ 2| ≤ 2 * R ^ 2 ∧
      |c - 3 * m * a * b + 2 * m ^ 2 * a ^ 3| ≤ 6 * R ^ 3 := by
  have ha₂ : |a ^ 2| ≤ R ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have ha₃ : |a ^ 3| ≤ R ^ 3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ha 3
  have hab : |a * b| ≤ R ^ 3 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) hR).trans_eq (by ring)
  have hm₂ : m ^ 2 ≤ 1 := by nlinarith [mul_nonneg hm.1 (sub_nonneg.mpr hm.2)]
  have hma : |m * a ^ 2| ≤ R ^ 2 := by
    rw [abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left ha₂ hm.1).trans (mul_le_of_le_one_left (sq_nonneg _) hm.2)
  have hmab : |3 * m * a * b| ≤ 3 * R ^ 3 := by
    have he : 3 * m * a * b = (3 * m) * (a * b) := by ring
    rw [he, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hm.1)]
    exact (mul_le_mul_of_nonneg_left hab (mul_nonneg (by norm_num) hm.1)).trans
      (mul_le_mul_of_nonneg_right (by linarith [hm.2] : 3 * m ≤ 3) (pow_nonneg hR _))
  have hmc : |m ^ 2 * a ^ 3| ≤ R ^ 3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left ha₃ (sq_nonneg _)).trans (mul_le_of_le_one_left (pow_nonneg hR _) hm₂)
  have hmc₂ : |2 * m ^ 2 * a ^ 3| ≤ 2 * R ^ 3 := by
    calc
      _ = 2 * |m ^ 2 * a ^ 3| := by rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmc (by norm_num)
  refine ⟨((abs_add_le _ _).trans (add_le_add hb hma)).trans_eq (by ring),
    ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hc hmab)) hmc)).trans_eq (by ring),
    ((abs_sub _ _).trans (add_le_add hb hma)).trans_eq (by ring),
    ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hc hmab)) hmc₂)).trans_eq (by ring)⟩

private theorem epsilon_cumulant_bounds {a b c m T Y : ℝ} (hT : 1 ≤ T) (hY : 0 ≤ Y)
    (hm : m ∈ Icc (0 : ℝ) 1) (ha : |a| ≤ T * Y) (hb : |b| ≤ 2 * T * Y ^ 2)
    (hc : |c| ≤ 5 * T * Y ^ 3) :
    |a| ≤ 4 * T * Y ∧ |b - m * a ^ 2| ≤ (4 * T * Y) ^ 2 ∧
      |c - 3 * m * a * b + 2 * m ^ 2 * a ^ 3| ≤ (4 * T * Y) ^ 3 := by
  have hT₀ : 0 ≤ T := by linarith
  have hT₂ : T ≤ T ^ 2 := by nlinarith [mul_nonneg hT₀ (sub_nonneg.mpr hT)]
  have hT₃ : T ^ 2 ≤ T ^ 3 := by nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hT)]
  have ha' : |a| ≤ 2 * T * Y := ha.trans (by nlinarith [mul_nonneg hT₀ hY])
  have hb' : |b| ≤ (2 * T * Y) ^ 2 := hb.trans (by
    have H := mul_le_mul_of_nonneg_right (by nlinarith : 2 * T ≤ 4 * T ^ 2) (sq_nonneg Y)
    nlinarith)
  have hc' : |c| ≤ (2 * T * Y) ^ 3 := hc.trans (by
    have H := mul_le_mul_of_nonneg_right (by nlinarith : 5 * T ≤ 8 * T ^ 3) (pow_nonneg hY 3)
    nlinarith)
  have H := cubic_moment_polynomials_bound (by positivity : 0 ≤ 2 * T * Y) hm ha' hb' hc'
  refine ⟨ha.trans (by nlinarith [mul_nonneg hT₀ hY]), H.2.2.1.trans ?_, H.2.2.2.trans ?_⟩
  · nlinarith [sq_nonneg (T * Y)]
  · have HR : 0 ≤ (T * Y) ^ 3 := pow_nonneg (mul_nonneg hT₀ hY) _
    nlinarith

def CubicEpsilonJetBound (F : ℝ → Vec3 → ℝ) (V : Set ℝ) (c : Vec3) (ρ M : ℝ) : Prop :=
  ∀ e ∈ V, ∀ x : Vec3,
    |epsilonSpatialJet F 1 e x| ≤ M * centeredSpatialWeight c ρ 3 x ∧
    |epsilonSpatialJet F 2 e x| ≤ M ^ 2 * centeredSpatialWeight c ρ 6 x ∧
    |epsilonSpatialJet F 3 e x| ≤ M ^ 3 * centeredSpatialWeight c ρ 9 x

theorem CubicEpsilonJetBound.step {F : ℝ → Vec3 → ℝ} {U V : Set ℝ}
    {c : Vec3} {ρ M T m : ℝ} (H : EpsilonJetControl F U) (hU : IsOpen U) (hVU : V ⊆ U)
    (P : QuadraticTerminal) (hm : m ∈ Ioc (0 : ℝ) 1) (v : Vec3)
    (hP : 1 / 2 ≤ P.precision m v) (hmajor : ∀ e ∈ U, ∀ y, F e y ≤ P.value y)
    (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (hT : 1 ≤ T) (HB : CubicEpsilonJetBound F V c ρ M)
    (HM : ∀ e ∈ V, ∀ N : ℝ, 0 ≤ N → ∀ p : ℕ, p ≤ 9 → ∀ ψ : Vec3 → ℝ,
      Continuous ψ → (∀ y, |ψ y| ≤ N * centeredSpatialWeight c ρ p y) → ∀ x,
        |epsilonMoment m v F (fun _ => ψ) e x| ≤ T * N * centeredSpatialWeight c ρ p x) :
    CubicEpsilonJetBound (fun e => vectorStep m v (F e)) V c ρ (4 * T * M) := by
  intro e he x
  let f₁ := epsilonSpatialJet F 1
  let f₂ := epsilonSpatialJet F 2
  let f₃ := epsilonSpatialJet F 3
  let ψ₂ : Vec3 → ℝ := fun y => f₂ e y + m * f₁ e y ^ 2
  let ψ₃ : Vec3 → ℝ := fun y => f₃ e y + 3 * m * f₁ e y * f₂ e y + m ^ 2 * f₁ e y ^ 3
  have hcont (n : ℕ) (hn : n ≤ 3) : Continuous (epsilonSpatialJet F n e) :=
    (H.continuous n hn).comp_continuous (show Continuous (fun y : Vec3 => (e, y)) by fun_prop)
      (fun _ => ⟨hVU he, mem_univ _⟩)
  have hpoly (y : Vec3) : |ψ₂ y| ≤ (2 * M ^ 2) * centeredSpatialWeight c ρ 6 y ∧
      |ψ₃ y| ≤ (5 * M ^ 3) * centeredSpatialWeight c ρ 9 y := by
    let Y := M * centeredSpatialWeight c ρ 3 y
    have hY : 0 ≤ Y := mul_nonneg hM (centeredSpatialWeight_nonneg c hρ _ _)
    have hb : |f₂ e y| ≤ Y ^ 2 := (HB e he y).2.1.trans_eq (by
      dsimp only [Y, centeredSpatialWeight]
      ring)
    have hc : |f₃ e y| ≤ Y ^ 3 := (HB e he y).2.2.trans_eq (by
      dsimp only [Y, centeredSpatialWeight]
      ring)
    have HP := cubic_moment_polynomials_bound hY ⟨hm.1.le, hm.2⟩ (HB e he y).1 hb hc
    exact ⟨HP.1.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring),
      HP.2.1.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring)⟩
  let A₁ := epsilonMoment m v F f₁ e x
  let A₂ := epsilonMoment m v F (fun _ => ψ₂) e x
  let A₃ := epsilonMoment m v F (fun _ => ψ₃) e x
  let Y := M * centeredSpatialWeight c ρ 3 x
  have hY : 0 ≤ Y := mul_nonneg hM (centeredSpatialWeight_nonneg c hρ _ _)
  have hA₁ : |A₁| ≤ T * Y := by
    have HP := HM e he M hM 3 (by norm_num) (f₁ e) (hcont 1 (by norm_num))
      (fun y => (HB e he y).1) x
    exact HP.trans_eq (by dsimp only [Y]; ring)
  have hA₂ : |A₂| ≤ 2 * T * Y ^ 2 := by
    have HP := HM e he (2 * M ^ 2) (by positivity) 6 (by norm_num) ψ₂
      ((hcont 2 (by norm_num)).add (continuous_const.mul ((hcont 1 (by norm_num)).pow 2)))
      (fun y => (hpoly y).1) x
    exact HP.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring)
  have hA₃ : |A₃| ≤ 5 * T * Y ^ 3 := by
    have HP := HM e he (5 * M ^ 3) (by positivity) 9 (by norm_num) ψ₃
      (((hcont 3 (by norm_num)).add ((continuous_const.mul (hcont 1 (by norm_num))).mul
        (hcont 2 (by norm_num)))).add (continuous_const.mul ((hcont 1 (by norm_num)).pow 3)))
      (fun y => (hpoly y).2) x
    exact HP.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring)
  have HC := epsilon_cumulant_bounds hT hY ⟨hm.1.le, hm.2⟩ hA₁ hA₂ hA₃
  have HE := epsilonStep_jet_values H hU P hm.1 v hP hmajor e (hVU he) x
  rw [HE.1, HE.2.1, HE.2.2]
  exact ⟨HC.1.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring),
    HC.2.1.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring),
    HC.2.2.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring)⟩

theorem CubicEpsilonJetBound.mono {F : ℝ → Vec3 → ℝ} {V : Set ℝ} {c : Vec3} {ρ M N : ℝ}
    (H : CubicEpsilonJetBound F V c ρ M) (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (hMN : M ≤ N) :
    CubicEpsilonJetBound F V c ρ N := by
  intro e he x
  exact ⟨(H e he x).1.trans (mul_le_mul_of_nonneg_right hMN (centeredSpatialWeight_nonneg c hρ _ _)),
    (H e he x).2.1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM hMN 2)
      (centeredSpatialWeight_nonneg c hρ _ _)),
    (H e he x).2.2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM hMN 3)
      (centeredSpatialWeight_nonneg c hρ _ _))⟩

theorem scalarData_terminalResidual_centered_bound {β s h ρ : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (hρ : 0 ≤ ρ) (z : ℝ) (y : Vec3) :
    |terminalResidual β (cdf (D.μ : Measure ℝ)) s h z y| ≤
      (scalarTerminalJetBound D 3 + 1) * centeredSpatialWeight (fun _ => z) ρ 3 y := by
  let B := scalarTerminalJetBound D 3
  have hB : 0 ≤ B := scalarTerminalJetBound_nonneg D 3
  rw [terminalResidual_eq_quadraticTaylorTails]
  calc
    _ ≤ ∑ i : Fin 3, |quadraticTaylorTail (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z (y i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 3, B / 6 * ‖y - (fun _ => z)‖ ^ 3 := by
      apply Finset.sum_le_sum
      intro i _
      have H := (quadraticTaylorTail_bounds (scalarData_phi_contDiff D ht)
        (fun x => scalarData_jet_le D (by norm_num : 1 ≤ 3) le_rfl ht x) z (y i)).1
      have hi : |y i - z| ≤ ‖y - (fun _ => z)‖ := by
        have H := norm_le_pi_norm (y - fun _ => z) i
        change ‖y i - z‖ ≤ ‖y - (fun _ => z)‖ at H
        simpa only [Real.norm_eq_abs] using H
      calc
        _ ≤ B * |y i - z| ^ 3 / 6 := H
        _ ≤ B * ‖y - (fun _ => z)‖ ^ 3 / 6 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hi 3) hB) (by norm_num)
        _ = B / 6 * ‖y - (fun _ => z)‖ ^ 3 := by ring
    _ ≤ (B + 1) * centeredSpatialWeight (fun _ => z) ρ 3 y := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      unfold centeredSpatialWeight
      have HP := pow_le_pow_left₀ (norm_nonneg (y - fun _ => z))
        (le_add_of_nonneg_left hρ : ‖y - (fun _ => z)‖ ≤ ρ + ‖y - (fun _ => z)‖) 3
      nlinarith [mul_le_mul_of_nonneg_left HP (by positivity : 0 ≤ B + 1), pow_nonneg (norm_nonneg (y - fun _ => z)) 3]

private theorem epsilon_nil_deriv (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    deriv (fun e => epsilonChain [] Q K e x) = fun _ => K x := by
  funext e
  simpa only [epsilonChain, vectorIncrementChain, id_eq, one_mul] using
    (((hasDerivAt_id e).mul_const (K x)).const_add (Q.value x)).deriv

private theorem epsilon_nil_second (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 2 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext e
  rw [iteratedDeriv_succ, iteratedDeriv_one, epsilon_nil_deriv]
  exact deriv_const e (K x)

private theorem epsilon_nil_third (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) :
    iteratedDeriv 3 (fun e => epsilonChain [] Q K e x) = fun _ => 0 := by
  funext e
  rw [iteratedDeriv_succ, epsilon_nil_second]
  exact deriv_const e 0

theorem scalarData_frozen_cubic_epsilon_jets {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ M : ℝ, 0 < h₀ ∧ 1 ≤ M ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ t, t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
        CubicEpsilonJetBound (fun e => epsilonChain t
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
          (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) e)
          (Icc (0 : ℝ) 1) (fun _ => z) (Real.sqrt h) M := by
  rcases scalarData_frozen_suffix_joint_epsilon_jets D hl hu with ⟨hJ, hhJ, hJl, HJ⟩
  rcases scalarData_frozen_centered_moment_transitions D hl hu with ⟨hT, T, hhT, hT₁, HT⟩
  let M₀ := scalarTerminalJetBound D 3 + 1
  have hM₀ : 1 ≤ M₀ := by dsimp only [M₀]; linarith [scalarTerminalJetBound_nonneg D 3]
  have hbase : 1 ≤ 4 * T := by linarith
  let M := (4 * T) ^ 12 * M₀
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hbase) hM₀
  let h₀ := min hJ (min hT (min (l / 2) ((D.q - u) / 6)))
  refine ⟨h₀, M, lt_min hhJ (lt_min hhT (lt_min (by positivity) (by positivity))), hM, ?_⟩
  intro r hr h hh hhsmall k hk z t ht
  have hhJ' : h ≤ hJ := hhsmall.trans (min_le_left _ _)
  have hhT' : h ≤ hT := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 := ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let K := terminalResidual β α (r - h) h z
  have HJ' := HJ r hr h hh hhJ' k hk z
  have hm := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have Hbound : ∀ j, j <:+ full → CubicEpsilonJetBound (fun e => epsilonChain j Q K e)
      (Icc (0 : ℝ) 1) (fun _ => z) (Real.sqrt h) ((4 * T) ^ j.length * M₀) := by
    intro j
    induction j with
    | nil =>
      intro _ e he x
      simp only [List.length_nil, pow_zero, one_mul, epsilonSpatialJet, iteratedDeriv_one,
        epsilon_nil_deriv, epsilon_nil_second, epsilon_nil_third, abs_zero]
      exact ⟨scalarData_terminalResidual_centered_bound D htime (Real.sqrt_nonneg h) z x,
        mul_nonneg (sq_nonneg _) (centeredSpatialWeight_nonneg _ (Real.sqrt_nonneg h) _ _),
        mul_nonneg (pow_nonneg (by linarith : 0 ≤ M₀) _) (centeredSpatialWeight_nonneg _ (Real.sqrt_nonneg h) _ _)⟩
    | cons w j ih =>
      intro hj
      have hj' : j <:+ full := (List.suffix_cons w j).trans hj
      rcases HJ'.2 w j hj with ⟨P, hP, hmajor⟩
      have Hstep := CubicEpsilonJetBound.step (HJ'.1 j hj') isOpen_Ioo
        (fun e he => ⟨by linarith [he.1], by linarith [he.2]⟩) P (hm w (hj.subset List.mem_cons_self)) w.2 hP hmajor
        (Real.sqrt_nonneg h) (by positivity : 0 ≤ (4 * T) ^ j.length * M₀) hT₁ (ih hj')
        (fun e he N hN p hp ψ hψ hψb x => HT r hr h hh hhT' k hk z e he w j hj N hN p hp ψ hψ hψb x)
      have heq : (4 * T) ^ (w :: j).length * M₀ = 4 * T * ((4 * T) ^ j.length * M₀) := by
        rw [List.length_cons, pow_succ]
        ring
      rw [heq]
      exact Hstep
  have hlen : t.length ≤ 12 := by simpa only [full, frozenSchedule_length] using ht.length_le
  exact (Hbound t ht).mono (Real.sqrt_nonneg h) (by positivity)
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hlen) (by positivity))

theorem epsilonPartitionMoment_cons_ratio (w : ℝ × Vec3) (t : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) (e : ℝ)
    (hZ : epsilonPartitionMoment (w :: t) Q K x e 0 ≠ 0) (n : Fin 4) :
    let F := fun e => epsilonChain t Q K e
    let f₁ := epsilonSpatialJet F 1
    let f₂ := epsilonSpatialJet F 2
    let f₃ := epsilonSpatialJet F 3
    epsilonPartitionMoment (w :: t) Q K x e n / epsilonPartitionMoment (w :: t) Q K x e 0 =
      ![1, w.1 * epsilonMoment w.1 w.2 F f₁ e x,
        w.1 * epsilonMoment w.1 w.2 F (fun a y => f₂ a y + w.1 * f₁ a y ^ 2) e x,
        w.1 * epsilonMoment w.1 w.2 F
          (fun a y => f₃ a y + 3 * w.1 * f₁ a y * f₂ a y + w.1 ^ 2 * f₁ a y ^ 3) e x] n := by
  fin_cases n
  · exact div_self hZ
  all_goals
    simp only [epsilonPartitionMoment, epsilonPartitionWeight, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
      epsilonSuffixNoiseJet, NonlinearEpsilonStep.weight, NonlinearEpsilonStep.weightFirst,
      NonlinearEpsilonStep.weightSecond, NonlinearEpsilonStep.weightThird,
      iteratedDeriv_zero, integral_const_mul, epsilonMoment, epsilonSpatialJet]
    ring

theorem cubicEpsilonJetBound_partition_ratios {w : ℝ × Vec3} {t : List (ℝ × Vec3)}
    {Q : QuadraticTerminal} {K : Vec3 → ℝ} {U V : Set ℝ} {c : Vec3} {ρ M T : ℝ}
    (H : EpsilonJetControl (fun e => epsilonChain t Q K e) U) (hVU : V ⊆ U)
    (hm : w.1 ∈ Icc (0 : ℝ) 1) (hρ : 0 ≤ ρ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (HB : CubicEpsilonJetBound (fun e => epsilonChain t Q K e) V c ρ M)
    (HM : ∀ e ∈ V, ∀ N : ℝ, 0 ≤ N → ∀ p : ℕ, p ≤ 9 → ∀ ψ : Vec3 → ℝ,
      Continuous ψ → (∀ y, |ψ y| ≤ N * centeredSpatialWeight c ρ p y) → ∀ x,
        |epsilonMoment w.1 w.2 (fun a => epsilonChain t Q K a) (fun _ => ψ) e x| ≤
          T * N * centeredSpatialWeight c ρ p x)
    {e : ℝ} (he : e ∈ V) (x : Vec3)
    (hZ : epsilonPartitionMoment (w :: t) Q K x e 0 ≠ 0) (n : Fin 4) :
    |epsilonPartitionMoment (w :: t) Q K x e n / epsilonPartitionMoment (w :: t) Q K x e 0| ≤
      (5 * T * M ^ 3) * centeredSpatialWeight c ρ (3 * n.val) x := by
  let F := fun e => epsilonChain t Q K e
  let f₁ := epsilonSpatialJet F 1
  let f₂ := epsilonSpatialJet F 2
  let f₃ := epsilonSpatialJet F 3
  let ψ₂ : Vec3 → ℝ := fun y => f₂ e y + w.1 * f₁ e y ^ 2
  let ψ₃ : Vec3 → ℝ := fun y => f₃ e y + 3 * w.1 * f₁ e y * f₂ e y + w.1 ^ 2 * f₁ e y ^ 3
  have hM₀ : 0 ≤ M := by linarith
  have hT₀ : 0 ≤ T := by linarith
  have hM₂ : M ≤ M ^ 2 := by nlinarith [mul_nonneg hM₀ (sub_nonneg.mpr hM)]
  have hM₃ : M ^ 2 ≤ M ^ 3 := by nlinarith [mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hM)]
  have hB : 1 ≤ 5 * T * M ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hT (pow_nonneg hM₀ 3)]
  have hcont (q : ℕ) (hq : q ≤ 3) : Continuous (epsilonSpatialJet F q e) :=
    (H.continuous q hq).comp_continuous (show Continuous (fun y : Vec3 => (e, y)) by fun_prop)
      (fun _ => ⟨hVU he, mem_univ _⟩)
  have hpoly (y : Vec3) : |ψ₂ y| ≤ (2 * M ^ 2) * centeredSpatialWeight c ρ 6 y ∧
      |ψ₃ y| ≤ (5 * M ^ 3) * centeredSpatialWeight c ρ 9 y := by
    let Y := M * centeredSpatialWeight c ρ 3 y
    have hY : 0 ≤ Y := mul_nonneg hM₀ (centeredSpatialWeight_nonneg c hρ _ _)
    have hb : |f₂ e y| ≤ Y ^ 2 := (HB e he y).2.1.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring)
    have hc : |f₃ e y| ≤ Y ^ 3 := (HB e he y).2.2.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring)
    have HP := cubic_moment_polynomials_bound hY hm (HB e he y).1 hb hc
    exact ⟨HP.1.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring),
      HP.2.1.trans_eq (by dsimp only [Y, centeredSpatialWeight]; ring)⟩
  have H₁ := HM e he M hM₀ 3 (by norm_num) (f₁ e) (hcont 1 (by norm_num)) (fun y => (HB e he y).1) x
  have H₂ := HM e he (2 * M ^ 2) (by positivity) 6 (by norm_num) ψ₂
    ((hcont 2 (by norm_num)).add (continuous_const.mul ((hcont 1 (by norm_num)).pow 2)))
    (fun y => (hpoly y).1) x
  have H₃ := HM e he (5 * M ^ 3) (by positivity) 9 (by norm_num) ψ₃
    (((hcont 3 (by norm_num)).add ((continuous_const.mul (hcont 1 (by norm_num))).mul
      (hcont 2 (by norm_num)))).add (continuous_const.mul ((hcont 1 (by norm_num)).pow 3)))
    (fun y => (hpoly y).2) x
  have hmass (a R : ℝ) (hR : 0 ≤ R) (ha : |a| ≤ R) : |w.1 * a| ≤ R := by
    rw [abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left ha hm.1).trans (mul_le_of_le_one_left hR hm.2)
  rw [epsilonPartitionMoment_cons_ratio w t Q K x e hZ n]
  fin_cases n
  · simpa only [Matrix.cons_val_zero', abs_one, Fin.val_zero, mul_zero, centeredSpatialWeight, pow_zero, mul_one] using hB
  · change |w.1 * epsilonMoment w.1 w.2 F f₁ e x| ≤ _
    exact (hmass _ _ (mul_nonneg (mul_nonneg hT₀ hM₀) (centeredSpatialWeight_nonneg c hρ 3 x)) H₁).trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left (hM₂.trans hM₃) hT₀] : T * M ≤ 5 * T * M ^ 3)
      (centeredSpatialWeight_nonneg c hρ 3 x))
  · change |w.1 * epsilonMoment w.1 w.2 F (fun a y => f₂ a y + w.1 * f₁ a y ^ 2) e x| ≤ _
    exact (hmass _ _ (mul_nonneg (mul_nonneg hT₀ (by positivity)) (centeredSpatialWeight_nonneg c hρ 6 x)) H₂).trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left hM₃ hT₀] : T * (2 * M ^ 2) ≤ 5 * T * M ^ 3)
      (centeredSpatialWeight_nonneg c hρ 6 x))
  · change |w.1 * epsilonMoment w.1 w.2 F
        (fun a y => f₃ a y + 3 * w.1 * f₁ a y * f₂ a y + w.1 ^ 2 * f₁ a y ^ 3) e x| ≤ _
    exact (hmass _ _ (mul_nonneg (mul_nonneg hT₀ (by positivity)) (centeredSpatialWeight_nonneg c hρ 9 x)) H₃).trans_eq
      (by change T * (5 * M ^ 3) * centeredSpatialWeight c ρ 9 x =
            (5 * T * M ^ 3) * centeredSpatialWeight c ρ 9 x; ring)

theorem scalarData_frozen_raw_moments_zero {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ B : ℝ, 0 < h₀ ∧ 1 ≤ B ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j : ℕ, j < 12 → ∀ n : Fin 4,
        |partitionIntegral (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j) n k /
          partitionIntegral (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j) 0 k| ≤
          B * (Real.sqrt h * h) ^ n.val := by
  rcases scalarData_frozen_cubic_epsilon_jets D hl hu with ⟨hB, M, hhB, hM, HB⟩
  rcases scalarData_frozen_centered_moment_transitions D hl hu with ⟨hT, T, hhT, hT₁, HT⟩
  rcases scalarData_frozen_suffix_joint_epsilon_jets D hl hu with ⟨hJ, hhJ, hJl, HJ⟩
  rcases scalarData_frozen_partition_pos D hl hu with ⟨hP, hhP, HP⟩
  let B := 5 * T * M ^ 3
  have hM₀ : 0 ≤ M := by linarith
  have hB₁ : 1 ≤ B := by
    have hpow : 1 ≤ M ^ 3 := one_le_pow₀ hM
    have H := one_le_mul_of_one_le_of_one_le hT₁ hpow
    dsimp only [B]
    nlinarith
  let h₀ := min hB (min hT (min hJ hP))
  refine ⟨h₀, B, lt_min hhB (lt_min hhT (lt_min hhJ hhP)), hB₁, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε j hj n
  have hhB' : h ≤ hB := hhsmall.trans (min_le_left _ _)
  have hhT' : h ≤ hT := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhJ' : h ≤ hJ := ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhP' : h ≤ hP := ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let K := terminalResidual β α (r - h) h z
  have hs : 0 < r - h := by linarith [hr.1, hhJ'.trans hJl]
  have hm := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hZ : epsilonPartitionMoment (full.drop j) Q K (fun _ => z) ε 0 ≠ 0 :=
    ne_of_gt (HP r hr h hh hhP' k hk z ε hε j hj)
  have hlen : 0 < (full.drop j).length := by
    rw [List.length_drop]
    simp only [full, frozenSchedule_length]
    omega
  change |epsilonPartitionMoment (full.drop j) Q K (fun _ => z) ε n /
    epsilonPartitionMoment (full.drop j) Q K (fun _ => z) ε 0| ≤ _
  cases heq : full.drop j with
  | nil => simp only [heq, List.length_nil, lt_self_iff_false] at hlen
  | cons w t =>
    rw [heq] at hZ
    have hwt : w :: t <:+ full := by rw [← heq]; exact List.drop_suffix j full
    have ht : t <:+ full := (List.suffix_cons w t).trans hwt
    have Hinner : EpsilonJetControl (fun e => epsilonChain t Q K e) (Ioo (-1 : ℝ) 2) :=
      (HJ r hr h hh hhJ' k hk z).1 t ht
    have HR := cubicEpsilonJetBound_partition_ratios Hinner
      (fun e he => ⟨by linarith [he.1], by linarith [he.2]⟩)
      ⟨(hm w (hwt.subset List.mem_cons_self)).1.le, (hm w (hwt.subset List.mem_cons_self)).2⟩
      (Real.sqrt_nonneg h) hM hT₁ (HB r hr h hh hhB' k hk z t ht)
      (fun e he N hN p hp ψ hψ hψb x => HT r hr h hh hhT' k hk z e he w t hwt N hN p hp ψ hψ hψb x)
      hε (fun _ => z) hZ n
    have hscale : centeredSpatialWeight (fun _ => z) (Real.sqrt h) (3 * n.val) (fun _ => z) =
        (Real.sqrt h * h) ^ n.val := by
      simp only [centeredSpatialWeight, sub_self, norm_zero, add_zero, pow_mul]
      have hc : (Real.sqrt h) ^ 3 = Real.sqrt h * h := by
        calc
          _ = Real.sqrt h * (Real.sqrt h) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hh.le]
      rw [hc]
    exact HR.trans_eq (congrArg (fun a : ℝ => B * a) hscale)

end SKBarriers2.Corner
