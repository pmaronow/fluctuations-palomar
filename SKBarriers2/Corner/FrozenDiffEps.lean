module

public import SKBarriers2.Corner.FrozenDiffBounds

@[expose] public section

noncomputable section
open scoped BigOperators Topology NNReal
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def terminalUpperQuadratic (β : ℝ) (α : ℝ → ℝ) (s h z B : ℝ) : QuadraticTerminal :=
  separableTaylorQuadratic (|Phi β α (s + 4 * h) z| + 5 * B) 0 (20 * B) z

theorem terminalUpperQuadratic_hessian {β s h z B : ℝ} {α : ℝ → ℝ} (hB : 0 ≤ B) :
    ∀ i j, |(terminalUpperQuadratic β α s h z B).hessian i j| ≤ 20 * B := by
  intro i j
  change |if i = j then 20 * B else 0| ≤ 20 * B
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
  · simpa only [abs_zero] using mul_nonneg (by norm_num : 0 ≤ (20 : ℝ)) hB

theorem terminal_epsilon_le_upper_quadratic (β : ℝ) (α : ℝ → ℝ) (s h z B : ℝ)
    (hB : 0 ≤ B) (hΦ : BoundedDerivs (Phi β α (s + 4 * h)))
    (h₁ : ∀ y, |jet β α 1 (s + 4 * h) y| ≤ B)
    (h₂ : |jet β α 2 (s + 4 * h) z| ≤ B) {ε : ℝ} (hε : |ε| ≤ 2) (x : Vec3) :
    (terminalTaylorQuadratic β α s h z).value x + ε * terminalResidual β α s h z x ≤
      (terminalUpperQuadratic β α s h z B).value x := by
  let S : ℝ := ∑ i : Fin 3, (x i - z) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hQ : (terminalTaylorQuadratic β α s h z).value x ≤
      3 * |Phi β α (s + 4 * h) z| + 3 * B + 2 * B * S := by
    rw [terminalTaylorQuadratic_value]
    calc
      _ ≤ ∑ i : Fin 3, (|Phi β α (s + 4 * h) z| + B + 2 * B * (x i - z) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        have hu : jet β α 1 (s + 4 * h) z * (x i - z) ≤ B * |x i - z| := by
          exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (h₁ z) (abs_nonneg _))
        have hχ : jet β α 2 (s + 4 * h) z / 2 * (x i - z) ^ 2 ≤ B / 2 * (x i - z) ^ 2 :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ((le_abs_self _).trans h₂) (by norm_num))
            (sq_nonneg _)
        have hd : |x i - z| ≤ 1 + (x i - z) ^ 2 := by
          nlinarith [sq_nonneg (|x i - z| - 1), sq_abs (x i - z)]
        have H := mul_le_mul_of_nonneg_left hd hB
        linarith [le_abs_self (Phi β α (s + 4 * h) z), mul_nonneg hB (sq_nonneg (x i - z))]
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]; ring
  have hK : |terminalResidual β α s h z x| ≤ 6 * B + 4 * B * S := by
    have H := terminalResidual_growth β α s h z B hB hΦ h₁ h₂ (fun _ => z) (x - fun _ => z) 1
    simpa only [S, one_smul, add_sub_cancel, Pi.sub_apply, sub_self, sq, mul_zero,
      Finset.sum_const_zero, add_zero, squaredLength, one_pow, mul_one] using H
  have hεK : ε * terminalResidual β α s h z x ≤ 2 * (6 * B + 4 * B * S) := by
    calc
      _ ≤ |ε * terminalResidual β α s h z x| := le_abs_self _
      _ = |ε| * |terminalResidual β α s h z x| := abs_mul _ _
      _ ≤ _ := mul_le_mul hε hK (abs_nonneg _) (by norm_num)
  rw [terminalUpperQuadratic, separableTaylorQuadratic_value]
  have he : (∑ i : Fin 3, (|Phi β α (s + 4 * h) z| + 5 * B + 0 * (x i - z) +
      (20 * B) / 2 * (x i - z) ^ 2)) = 3 * |Phi β α (s + 4 * h) z| + 15 * B + 10 * B * S := by
    simp only [zero_mul, add_zero, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
    ring
  rw [he]
  linarith

theorem vectorStep_le_quadratic (P : QuadraticTerminal) {m : ℝ} (hm : 0 < m)
    (v x : Vec3) (hP : 0 < P.precision m v) {f : Vec3 → ℝ}
    (hi : Integrable (fun t => Real.exp (m * f (x + t • v))) (gaussianReal 0 1))
    (hle : ∀ y, f y ≤ P.value y) : vectorStep m v f x ≤ (P.update m v).value x := by
  have hzero (a b : Vec3) : |(0 : ℝ) - 0| ≤ (0 : ℝ) * ‖a - b‖ := by simp only [sub_self, abs_zero, zero_mul, le_refl]
  have hPint := integrable_exp_quadratic_lipschitz_line P continuous_const hzero v x hP
  simp only [add_zero] at hPint
  have H := integral_mono hi hPint (fun t => Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (hle _) hm.le))
  have Hlog := Real.log_le_log (integral_exp_pos hi) H
  have Hdiv := div_le_div_of_nonneg_right Hlog hm.le
  have he := congrFun (P.vectorStep_value m v (ne_of_gt hm) hP) x
  simp only [vectorStep, gaussianStep, ite_eq_right (ne_of_gt hm), positiveGaussianLogStep] at he
  simpa only [vectorStep, gaussianStep, ite_eq_right (ne_of_gt hm), positiveGaussianLogStep] using Hdiv.trans_eq he

theorem epsilonChain_le_quadratic (l : List (ℝ × Vec3)) (Q P : QuadraticTerminal)
    (K : Vec3 → ℝ) (ε : ℝ) (hP : RiccatiAdmissible l P)
    (hm : ∀ u ∈ l, 0 < u.1)
    (hi : ∀ u t, u :: t <:+ l → ∀ x : Vec3,
      Integrable (fun s => Real.exp (u.1 * epsilonChain t Q K ε (x + s • u.2))) (gaussianReal 0 1))
    (hle : ∀ x, Q.value x + ε * K x ≤ P.value x) :
    ∀ x, epsilonChain l Q K ε x ≤ (riccatiRecursion l P).value x := by
  induction l with
  | nil => exact hle
  | cons u t ih =>
    have H := ih hP.1 (fun w hw => hm w (List.mem_cons_of_mem u hw))
      (fun w s hs => hi w s (hs.trans (List.suffix_cons u t)))
    intro x
    exact vectorStep_le_quadratic (riccatiRecursion t P) (hm u List.mem_cons_self) u.2 x
      hP.2.2 (hi u t (List.suffix_refl _) x) H

theorem QuadraticTerminal.noise_envelope (P : QuadraticTerminal) {m : ℝ} (v x : Vec3)
    (hP : 1 / 2 ≤ P.precision m v) :
    ∃ A : ℝ, ∀ t : ℝ, m * P.value (x + t • v) ≤ A + (3 / 8 : ℝ) * t ^ 2 := by
  refine ⟨m * P.value x + 2 * (m * P.slope v x) ^ 2, ?_⟩
  intro t
  have hc : m * P.curvature v ≤ 1 / 2 := by unfold precision at hP; linarith
  have H := sq_nonneg (t - 4 * (m * P.slope v x))
  rw [P.value_shift]
  have H' := mul_le_mul_of_nonneg_right hc (sq_nonneg t)
  nlinarith

theorem scalarData_frozen_suffix_value_envelope {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ, ∀ w : ℝ × Vec3, ∀ t : List (ℝ × Vec3),
      w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ x : Vec3, ∃ A : ℝ,
      let F := epsilonSuffixNoiseJet t
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) w x
      (∀ ε ∈ Ioo (-1 : ℝ) 2, Continuous (F 0 ε)) ∧
      (∀ ε ∈ Ioo (-1 : ℝ) 2, ∀ s, w.1 * F 0 ε s ≤ A + (3 / 8 : ℝ) * s ^ 2) := by
  rcases scalarData_frozen_suffix_lipschitz_frames D hl hu with ⟨hF, C, hhF, _, HF⟩
  let B : ℝ := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  let R : ℝ := 72 * (2 ^ 12 * (20 * B)) * (β ^ 2 + 1)
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨min hF (min (l / 2) (min ((D.q - u) / 6) R⁻¹)),
    lt_min hhF (lt_min (by positivity) (lt_min (by positivity) (inv_pos.mpr hR))), ?_⟩
  intro r hr h hh hh₀ k hk z w t ht x
  have hhF' : h ≤ hF := hh₀.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    ((hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhR : h ≤ R⁻¹ :=
    ((hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  let full := frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z
  let K := terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z
  let P := terminalUpperQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z B
  have hm := frozenSchedule_masses β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k
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
  have ht' : t <:+ full := (List.suffix_cons w t).trans ht
  have hprec : 1 / 2 ≤ (riccatiRecursion t P).precision w.1 w.2 :=
    (hstartup (w :: t) ht).2 _ List.mem_cons_self
  rcases (riccatiRecursion t P).noise_envelope w.2 x hprec with ⟨A, hA⟩
  refine ⟨A, ?_, ?_⟩
  · intro ε hε
    rcases (HF r hr h hh hhF' k hk z ε ⟨hε.1.le, hε.2.le⟩ t ht').2.2 with ⟨g, hg, _, heq⟩
    change Continuous (fun s => epsilonChain t Q K ε (x + s • w.2))
    rw [heq]
    exact ((show Continuous (riccatiRecursion t (Q.scale (1 - ε))).value by
      unfold QuadraticTerminal.value; fun_prop).add hg).comp (by fun_prop)
  · intro ε hε s
    have hi (v : ℝ × Vec3) (j : List (ℝ × Vec3)) (hj : v :: j <:+ t) (y : Vec3) :
        Integrable (fun a => Real.exp (v.1 * epsilonChain j Q K ε (y + a • v.2))) (gaussianReal 0 1) := by
      have hjfull := hj.trans ht'
      have hchild := (List.suffix_cons v j).trans hjfull
      have hD := (HF r hr h hh hhF' k hk z ε ⟨hε.1.le, hε.2.le⟩ (v :: j) hjfull).1.2.2
      rcases (HF r hr h hh hhF' k hk z ε ⟨hε.1.le, hε.2.le⟩ j hchild).2.2 with ⟨g, hg, hLip, heq⟩
      rw [heq]
      exact integrable_exp_quadratic_lipschitz_line _ hg hLip v.2 y hD
    have h₁ (y : ℝ) : |jet β (cdf (D.μ : Measure ℝ)) 1 ((r - h) + 4 * h) y| ≤ B :=
      (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) htime y).trans (by dsimp only [B]; linarith)
    have h₂ : |jet β (cdf (D.μ : Measure ℝ)) 2 ((r - h) + 4 * h) z| ≤ B :=
      (scalarData_jet_le D (r := 2) (by norm_num) (by norm_num) htime z).trans (by dsimp only [B]; linarith)
    have hmajor := epsilonChain_le_quadratic t Q P K ε (hstartup t ht').1
      (fun v hv => (hm v (ht'.subset hv)).1) hi
      (terminal_epsilon_le_upper_quadratic β _ (r - h) h z B hB.le (scalarData_phi_regular D htime)
        h₁ h₂ (abs_le.mpr ⟨by linarith [hε.1], by linarith [hε.2]⟩))
    change w.1 * epsilonChain t Q K ε (x + s • w.2) ≤ _
    exact (mul_le_mul_of_nonneg_left (hmajor _) (hm w (ht.subset List.mem_cons_self)).1.le).trans (hA s)

def epsilonThirdPartitionRow (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (x : Vec3) (ε : ℝ) (i : Fin 3) : ℝ :=
  match l with
  | [] => 0
  | w :: t =>
    let F := epsilonSuffixNoiseJet t Q K w x
    let Z := ∫ s, NonlinearEpsilonStep.weight w.1 (F 0) ε s ∂gaussianReal 0 1
    let Z₁ := ∫ s, NonlinearEpsilonStep.weightFirst w.1 (F 0) (F 1) ε s ∂gaussianReal 0 1
    let Z₂ := ∫ s, NonlinearEpsilonStep.weightSecond w.1 (F 0) (F 1) (F 2) ε s ∂gaussianReal 0 1
    let Z₃ := ∫ s, NonlinearEpsilonStep.weightThird w.1 (F 0) (F 1) (F 2) (F 3) ε s ∂gaussianReal 0 1
    ![Z₃ / (w.1 * Z), Z₂ * Z₁ / (w.1 * Z ^ 2), Z₁ ^ 3 / (w.1 * Z ^ 3)] i

theorem epsilonChain_third_eq_partition_rows {w : ℝ × Vec3} {t : List (ℝ × Vec3)}
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) {U : Set ℝ} (hU : IsOpen U)
    (hm : w.1 ≠ 0) (H : EpsilonChainDominationOn (w :: t) Q K U) {ε : ℝ} (hε : ε ∈ U) :
    iteratedDeriv 3 (fun e => epsilonChain (w :: t) Q K e x) ε =
      epsilonThirdPartitionRow (w :: t) Q K x ε 0 -
        3 * epsilonThirdPartitionRow (w :: t) Q K x ε 1 +
        2 * epsilonThirdPartitionRow (w :: t) Q K x ε 2 := by
  let F := epsilonSuffixNoiseJet t Q K w x
  let Z : ℝ → ℝ := fun e => ∫ s, NonlinearEpsilonStep.weight w.1 (F 0) e s ∂gaussianReal 0 1
  let Z₁ : ℝ → ℝ := fun e => ∫ s, NonlinearEpsilonStep.weightFirst w.1 (F 0) (F 1) e s ∂gaussianReal 0 1
  let Z₂ : ℝ → ℝ := fun e => ∫ s, NonlinearEpsilonStep.weightSecond w.1 (F 0) (F 1) (F 2) e s ∂gaussianReal 0 1
  let Z₃ : ℝ → ℝ := fun e => ∫ s, NonlinearEpsilonStep.weightThird w.1 (F 0) (F 1) (F 2) (F 3) e s ∂gaussianReal 0 1
  have hZ : Z ε ≠ 0 := ne_of_gt (integral_exp_pos (H.2 x ε hε).1.integrable)
  have H₃ := logPartition_third_of_tower hU hm hε
    (fun e he => (H.2 x e he).1.hasDerivAt)
    (fun e he => (H.2 x e he).2.1.hasDerivAt)
    (fun e he => (H.2 x e he).2.2.hasDerivAt) hZ
  have heq : (fun e => epsilonChain (w :: t) Q K e x) = fun e => Real.log (Z e) / w.1 := by
    funext e
    simp only [epsilonChain, vectorIncrementChain, vectorStep, gaussianStep, ite_eq_right hm,
      positiveGaussianLogStep, Z, F, NonlinearEpsilonStep.weight, epsilonSuffixNoiseJet, iteratedDeriv_zero]
  rw [heq]
  have Hderiv := H₃.deriv
  rw [← iteratedDeriv_succ] at Hderiv
  rw [Hderiv]
  change (Z₃ ε * Z ε ^ 2 - 3 * Z₂ ε * Z₁ ε * Z ε + 2 * Z₁ ε ^ 3) / Z ε ^ 3 / w.1 =
    Z₃ ε / (w.1 * Z ε) - 3 * (Z₂ ε * Z₁ ε / (w.1 * Z ε ^ 2)) +
      2 * (Z₁ ε ^ 3 / (w.1 * Z ε ^ 3))
  field_simp [hm, hZ]

def frozenThirdPartitionRow (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (i : Fin 3) (k : ℝ) : ℝ :=
  epsilonThirdPartitionRow ((frozenSchedule β a (1 / 2) h k).drop j)
    (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) (fun _ => z) ε i

def FrozenKRegularity (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) (C h₀ κ : ℝ) : Prop :=
  ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
    ∀ j : ℕ, j < 12 → ∃ d₁ d₂ : Fin 3 → ℝ → ℝ,
      (∀ i : Fin 3, ∀ k ∈ Icc (-κ) κ,
        HasDerivAt (frozenThirdPartitionRow β α (α (r - h)) (r - h) h z ε j i) (d₁ i k) k ∧
          HasDerivAt (d₁ i) (d₂ i k) k) ∧
      (∀ i : Fin 3, ∀ k ∈ Icc (-κ) κ, |d₂ i k| ≤ C * Real.sqrt h * h ^ 3)

theorem iteratedDeriv_three_sub_of_regular {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ∀ e ∈ U, EpsilonRegularAt f e) (hg : ∀ e ∈ U, EpsilonRegularAt g e)
    {ε : ℝ} (hε : ε ∈ U) :
    iteratedDeriv 3 (fun e => f e - g e) ε = iteratedDeriv 3 f ε - iteratedDeriv 3 g ε := by
  have he₁ (e : ℝ) (he : e ∈ U) : deriv (fun a => f a - g a) =ᶠ[𝓝 e]
      (fun a => deriv f a - deriv g a) := by
    filter_upwards [hU.mem_nhds he] with a ha
    exact ((hf a ha).1.sub (hg a ha).1).deriv
  have hd₂ (e : ℝ) (he : e ∈ U) : HasDerivAt (deriv (fun a => f a - g a))
      (iteratedDeriv 2 f e - iteratedDeriv 2 g e) e :=
    ((hf e he).2.1.sub (hg e he).2.1).congr_of_eventuallyEq (he₁ e he)
  have he₂ : iteratedDeriv 2 (fun a => f a - g a) =ᶠ[𝓝 ε]
      (fun a => iteratedDeriv 2 f a - iteratedDeriv 2 g a) := by
    filter_upwards [hU.mem_nhds hε] with a ha
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using (hd₂ a ha).deriv
  simpa only [iteratedDeriv_succ] using
    (((hf ε hε).2.2.sub (hg ε hε).2.2).congr_of_eventuallyEq he₂).deriv

theorem thetaThirdInTilt_eq_partition_rows (β : ℝ) (α : ℝ → ℝ) (a s h z ε k : ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hε : ε ∈ U) (ha : a ∈ Ioc (0 : ℝ) 1)
    (Hk : EpsilonChainDominationOn (frozenSchedule β a (1 / 2) h k)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) U)
    (H₀ : EpsilonChainDominationOn (frozenSchedule β a (1 / 2) h 0)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) U) :
    thetaThirdInTilt β α a s h z ε k =
      (frozenThirdPartitionRow β α a s h z ε 0 0 k -
        3 * frozenThirdPartitionRow β α a s h z ε 0 1 k +
        2 * frozenThirdPartitionRow β α a s h z ε 0 2 k) -
      (frozenThirdPartitionRow β α a s h z ε 0 0 0 -
        3 * frozenThirdPartitionRow β α a s h z ε 0 1 0 +
        2 * frozenThirdPartitionRow β α a s h z ε 0 2 0) := by
  have hmass (k : ℝ) : ∀ w ∈ frozenSchedule β a (1 / 2) h k, w.1 ≠ 0 :=
    fun w hw => ne_of_gt (frozenSchedule_masses β a (1 / 2) h k ha w hw).1
  have hthird (k : ℝ) (H : EpsilonChainDominationOn (frozenSchedule β a (1 / 2) h k)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) U) :
      iteratedDeriv 3 (frozenTerminalTheta β α a s h k z) ε =
        frozenThirdPartitionRow β α a s h z ε 0 0 k -
          3 * frozenThirdPartitionRow β α a s h z ε 0 1 k +
          2 * frozenThirdPartitionRow β α a s h z ε 0 2 k := by
    have hm : a / 3 ≠ 0 := ne_of_gt (div_pos ha.1 (by norm_num))
    exact epsilonChain_third_eq_partition_rows _ _ _ hU hm H hε
  have hrk (e : ℝ) (he : e ∈ U) : EpsilonRegularAt (frozenTerminalTheta β α a s h k z) e :=
    Hk.regular hU (hmass k) (fun _ => z) he
  have hr₀ (e : ℝ) (he : e ∈ U) : EpsilonRegularAt (frozenTerminalTheta β α a s h 0 z) e :=
    H₀.regular hU (hmass 0) (fun _ => z) he
  unfold thetaThirdInTilt frozenThetaDifference
  rw [iteratedDeriv_three_sub_of_regular hU hrk hr₀ hε, hthird k Hk, hthird 0 H₀]

theorem scalarData_terminalMixedThirdControl_of_polynomial_bounds_and_kRegularity
    {β C h₀ κ l u : ℝ} (D : ScalarData β) (hl : 0 < l) (hu : u < D.q)
    (hh₀ : 0 < h₀) (hκhalf : κ < 1 / 2)
    (Hε : ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      EpsilonSuffixPolynomialBounds
        (frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k)
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) (Ioo (-1 : ℝ) 2))
    (HK : FrozenKRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₀ κ) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ ≤ h₀ ∧
      TerminalMixedThirdControl β (cdf (D.μ : Measure ℝ)) (Icc l u) (6 * C) h₁ κ := by
  rcases scalarData_thetaThirdInTilt_even D hl hu with ⟨hE, hhE, HE⟩
  refine ⟨min h₀ (min hE (l / 2)), lt_min hh₀ (lt_min hhE (by positivity)), min_le_left _ _, ?_⟩
  intro r hr h hh hh₁ z
  have hhsmall : h ≤ h₀ := hh₁.trans (min_le_left _ _)
  have hhE' : h ≤ hE := (hh₁.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hh₁.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  have ha : a ∈ Ioc (0 : ℝ) 1 := ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hmass (k : ℝ) : ∀ w ∈ frozenSchedule β a (1 / 2) h k, w.1 ≠ 0 :=
    fun w hw => ne_of_gt (frozenSchedule_masses β a (1 / 2) h k ha w hw).1
  have hdom (k : ℝ) (hk : |k| ≤ 1 / 2) : EpsilonChainDominationOn
      (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α (r - h) h z)
        (terminalResidual β α (r - h) h z) (Ioo (-1 : ℝ) 2) :=
    epsilonChainDominationOn_of_polynomial_bounds isOpen_Ioo (hmass k)
      (Hε r hr h hh hhsmall k hk z)
  constructor
  · intro k hk ε hε
    exact frozenThetaDifference_regular_of_polynomial_bounds β α a (r - h) h k z ha isOpen_Ioo
      (Hε r hr h hh hhsmall k (hk.trans hκhalf.le) z)
      (Hε r hr h hh hhsmall 0 (by norm_num) z) ⟨by linarith [hε.1], by linarith [hε.2]⟩
  · intro ε hε
    rcases HK r hr h hh hhsmall z ε hε 0 (by norm_num) with ⟨d₁, d₂, hd, hb⟩
    let g₁ : ℝ → ℝ := fun k => d₁ 0 k - 3 * d₁ 1 k + 2 * d₁ 2 k
    let g₂ : ℝ → ℝ := fun k => d₂ 0 k - 3 * d₂ 1 k + 2 * d₂ 2 k
    refine ⟨g₁, g₂, ?_, ?_, ?_⟩
    · intro k hk
      let b₀ := frozenThirdPartitionRow β α a (r - h) h z ε 0 0 0 -
        3 * frozenThirdPartitionRow β α a (r - h) h z ε 0 1 0 +
        2 * frozenThirdPartitionRow β α a (r - h) h z ε 0 2 0
      have heq : (thetaThirdInTilt β α a (r - h) h z ε) =ᶠ[𝓝 k]
          (fun y => (frozenThirdPartitionRow β α a (r - h) h z ε 0 0 y -
            3 * frozenThirdPartitionRow β α a (r - h) h z ε 0 1 y +
            2 * frozenThirdPartitionRow β α a (r - h) h z ε 0 2 y) - b₀) := by
        have hkopen : k ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
          constructor <;> linarith [hk.1, hk.2]
        filter_upwards [isOpen_Ioo.mem_nhds hkopen] with y hy
        exact thetaThirdInTilt_eq_partition_rows β α a (r - h) h z ε y isOpen_Ioo
          ⟨by linarith [hε.1], by linarith [hε.2]⟩ ha
          (hdom y (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)) (hdom 0 (by norm_num))
      exact ⟨((((hd 0 k hk).1.sub ((hd 1 k hk).1.const_mul 3)).add
        ((hd 2 k hk).1.const_mul 2)).sub_const b₀).congr_of_eventuallyEq heq,
        ((hd 0 k hk).2.sub ((hd 1 k hk).2.const_mul 3)).add ((hd 2 k hk).2.const_mul 2)⟩
    · intro k hk
      change |d₂ 0 k - 3 * d₂ 1 k + 2 * d₂ 2 k| ≤ _
      calc
        _ ≤ |d₂ 0 k| + 3 * |d₂ 1 k| + 2 * |d₂ 2 k| := by
          have H := (abs_add_le (d₂ 0 k - 3 * d₂ 1 k) (2 * d₂ 2 k)).trans
            (add_le_add (abs_sub (d₂ 0 k) (3 * d₂ 1 k)) (le_refl |2 * d₂ 2 k|))
          simpa only [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (3 : ℝ)),
            abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] using H
        _ ≤ (6 * C) * Real.sqrt h * h ^ 3 := by
          linarith [hb 0 k hk, hb 1 k hk, hb 2 k hk]
    · intro k hk
      apply HE r hr h hh hhE' z ε hε k
      constructor <;> linarith [hk.1, hk.2]

theorem continuousOn_quadratic_dominated_moment (P : QuadraticTerminal)
    {m M : ℝ} (hm : 0 ≤ m) (hM : 0 ≤ M) (v : Vec3) (hP : 1 / 2 ≤ P.precision m v)
    {U : Set ℝ} {F ψ : ℝ → Vec3 → ℝ}
    (hF : ContinuousOn (fun p : ℝ × Vec3 => F p.1 p.2) (U ×ˢ univ))
    (hψ : ContinuousOn (fun p : ℝ × Vec3 => ψ p.1 p.2) (U ×ˢ univ))
    (hmajor : ∀ ε ∈ U, ∀ y, F ε y ≤ P.value y)
    (p : ℕ) (hbound : ∀ ε ∈ U, ∀ y, |ψ ε y| ≤ M * (1 + ‖y‖) ^ p) :
    ContinuousOn (fun a : ℝ × Vec3 => ∫ s, Real.exp (m * F a.1 (a.2 + s • v)) *
      ψ a.1 (a.2 + s • v) ∂gaussianReal 0 1) (U ×ˢ univ) := by
  let A : Vec3 → ℝ := fun x => m * P.value x + 2 * (m * P.slope v x) ^ 2
  have hAc : Continuous A := by unfold A QuadraticTerminal.value QuadraticTerminal.slope; fun_prop
  have hAval (x : Vec3) (s : ℝ) : m * P.value (x + s • v) ≤ A x + (3 / 8 : ℝ) * s ^ 2 := by
    have hc : m * P.curvature v ≤ 1 / 2 := by unfold QuadraticTerminal.precision at hP; linarith
    have H := sq_nonneg (s - 4 * (m * P.slope v x))
    rw [P.value_shift]
    have H' := mul_le_mul_of_nonneg_right hc (sq_nonneg s)
    dsimp only [A]
    nlinarith
  intro a ha
  let C := M * (2 * (2 + ‖a.2‖ + ‖v‖)) ^ p
  let b : ℝ → ℝ := fun s => C * ((1 + s ^ 2) ^ p * Real.exp (A a.2 + 1 + (3 / 8 : ℝ) * s ^ 2))
  have hb : Integrable b (gaussianReal 0 1) :=
    (integrable_polynomial_exp_square (by norm_num : 0 ≤ (3 / 8 : ℝ)) (by norm_num) (A a.2 + 1) p).const_mul C
  have hAn : ∀ᶠ y : ℝ × Vec3 in 𝓝 a, A y.2 < A a.2 + 1 :=
    (hAc.comp continuous_snd).continuousAt.eventually (Iio_mem_nhds (lt_add_one _))
  have hxn : ∀ᶠ y : ℝ × Vec3 in 𝓝 a, ‖y.2‖ < ‖a.2‖ + 1 :=
    continuous_snd.norm.continuousAt.eventually (Iio_mem_nhds (lt_add_one _))
  apply continuousWithinAt_of_dominated (bound := b) ?_ ?_ hb ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hline : Continuous (fun s : ℝ => (y.1, y.2 + s • v)) := by fun_prop
    have hFc : Continuous (fun s : ℝ => F y.1 (y.2 + s • v)) :=
      hF.comp_continuous hline (fun s => ⟨hy.1, mem_univ _⟩)
    have hψc : Continuous (fun s : ℝ => ψ y.1 (y.2 + s • v)) :=
      hψ.comp_continuous hline (fun s => ⟨hy.1, mem_univ _⟩)
    exact ((Real.continuous_exp.comp (continuous_const.mul hFc)).mul hψc).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hAn.filter_mono nhdsWithin_le_nhds,
      hxn.filter_mono nhdsWithin_le_nhds] with y hy hAy hxy
    refine ae_of_all _ (fun s => ?_)
    have hn : 1 + ‖y.2 + s • v‖ ≤ (2 * (2 + ‖a.2‖ + ‖v‖)) * (1 + s ^ 2) := by
      have H := norm_add_le y.2 (s • v)
      rw [norm_smul, Real.norm_eq_abs] at H
      have hs : 1 + |s| ≤ 2 * (1 + s ^ 2) := by nlinarith [sq_nonneg (|s| - 1), sq_abs s]
      calc
        _ ≤ (2 + ‖a.2‖ + ‖v‖) * (1 + |s|) := by
          nlinarith [norm_nonneg v, abs_nonneg s,
            mul_nonneg (norm_nonneg a.2) (abs_nonneg s)]
        _ ≤ (2 + ‖a.2‖ + ‖v‖) * (2 * (1 + s ^ 2)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by ring
    have htest : |ψ y.1 (y.2 + s • v)| ≤ C * (1 + s ^ 2) ^ p := by
      refine (hbound y.1 hy.1 _).trans ?_
      calc
        _ ≤ M * ((2 * (2 + ‖a.2‖ + ‖v‖)) * (1 + s ^ 2)) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn p) hM
        _ = _ := by dsimp only [C]; rw [mul_pow]; ring
    have he : Real.exp (m * F y.1 (y.2 + s • v)) ≤ Real.exp (A a.2 + 1 + (3 / 8 : ℝ) * s ^ 2) :=
      Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (hmajor y.1 hy.1 _) hm).trans
        ((hAval y.2 s).trans (by linarith)))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul he htest (abs_nonneg _) (Real.exp_pos _).le).trans_eq (by dsimp only [b]; ring)
  · refine ae_of_all _ (fun s => ?_)
    have hc (H : ContinuousOn (fun p : ℝ × Vec3 => F p.1 p.2) (U ×ˢ univ)) :
        ContinuousOn (fun p : ℝ × Vec3 => F p.1 (p.2 + s • v)) (U ×ˢ univ) :=
      H.comp (show Continuous (fun p : ℝ × Vec3 => (p.1, p.2 + s • v)) by fun_prop).continuousOn
        (fun y hy => ⟨hy.1, mem_univ _⟩)
    have hψc : ContinuousOn (fun p : ℝ × Vec3 => ψ p.1 (p.2 + s • v)) (U ×ˢ univ) :=
      hψ.comp (show Continuous (fun p : ℝ × Vec3 => (p.1, p.2 + s • v)) by fun_prop).continuousOn
        (fun y hy => ⟨hy.1, mem_univ _⟩)
    exact ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hc hF))).mul hψc) a ha

theorem epsilonSuffixPolynomialBounds_of_jet_bounds (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) (U : Set ℝ)
    (hvalue : ∀ w t, w :: t <:+ l → ∀ x : Vec3, ∃ A : ℝ,
      let F := epsilonSuffixNoiseJet t Q K w x
      (∀ e ∈ U, Continuous (F 0 e)) ∧
      (∀ e ∈ U, ∀ s, w.1 * F 0 e s ≤ A + (3 / 8 : ℝ) * s ^ 2))
    (hjets : ∀ w t, w :: t <:+ l → ∀ x : Vec3, ∃ M : ℝ, ∃ p : ℕ, 0 ≤ M ∧
      let F := epsilonSuffixNoiseJet t Q K w x
      (∀ e ∈ U, Continuous (F 1 e) ∧ Continuous (F 2 e) ∧ Continuous (F 3 e)) ∧
      (∀ e ∈ U, ∀ s, |F 1 e s| ≤ M * (1 + s ^ 2) ^ p ∧
        |F 2 e s| ≤ M * (1 + s ^ 2) ^ p ∧ |F 3 e s| ≤ M * (1 + s ^ 2) ^ p)) :
    EpsilonSuffixPolynomialBounds l Q K U := by
  induction l with
  | nil => exact True.intro
  | cons w t ih =>
    refine ⟨ih (fun v j hj => hvalue v j (hj.trans (List.suffix_cons w t)))
      (fun v j hj => hjets v j (hj.trans (List.suffix_cons w t))), ?_⟩
    intro x
    rcases hvalue w t (List.suffix_refl _) x with ⟨A, hc₀, hval⟩
    rcases hjets w t (List.suffix_refl _) x with ⟨M, p, hM, hc, hg⟩
    refine ⟨A, 3 / 8, M, p, by norm_num, by norm_num, hM, ?_, hval, hg⟩
    intro e he
    exact ⟨hc₀ e he, hc e he⟩

theorem scalarData_epsilon_controls_of_jet_bounds
    {β h₀ l u : ℝ} (D : ScalarData β) (hl : 0 < l) (hu : u < D.q) (hh₀ : 0 < h₀)
    (Hjets : ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ w t, w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k →
      ∀ x : Vec3, ∃ M : ℝ, ∃ p : ℕ, 0 ≤ M ∧
      let F := epsilonSuffixNoiseJet t (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) w x
      (∀ e ∈ Ioo (-1 : ℝ) 2, Continuous (F 1 e) ∧ Continuous (F 2 e) ∧ Continuous (F 3 e)) ∧
      (∀ e ∈ Ioo (-1 : ℝ) 2, ∀ s, |F 1 e s| ≤ M * (1 + s ^ 2) ^ p ∧
        |F 2 e s| ≤ M * (1 + s ^ 2) ^ p ∧ |F 3 e s| ≤ M * (1 + s ^ 2) ^ p)) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ h₁ ≤ h₀ ∧
      TerminalChainDifferentiation β (cdf (D.μ : Measure ℝ)) (Icc l u) h₁ (1 / 2) ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, EpsilonRegularAt
        (frozenThetaDifference β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h k z) ε := by
  rcases scalarData_frozen_suffix_value_envelope D hl hu with ⟨hV, hhV, HV⟩
  let h₁ := min h₀ (min hV (l / 2))
  have hh₁ : 0 < h₁ := lt_min hh₀ (lt_min hhV (by positivity))
  have hh₁₀ : h₁ ≤ h₀ := min_le_left _ _
  have hh₁V : h₁ ≤ hV := (min_le_right _ _).trans (min_le_left _ _)
  have hh₁l : h₁ ≤ l / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have Hpoly : ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      EpsilonSuffixPolynomialBounds
        (frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k)
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) (Ioo (-1 : ℝ) 2) := by
    intro r hr h hh hhsmall k hk z
    exact epsilonSuffixPolynomialBounds_of_jet_bounds _ _ _ _
      (HV r hr h hh (hhsmall.trans hh₁V) k hk z)
      (Hjets r hr h hh (hhsmall.trans hh₁₀) k hk z)
  refine ⟨h₁, hh₁, hh₁₀, scalarData_terminalChainDifferentiation_of_polynomial_bounds D hl hh₁l
    isOpen_Ioo (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 by constructor <;> norm_num) Hpoly, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε
  have hs : 0 < r - h := by linarith [hr.1]
  exact frozenThetaDifference_regular_of_polynomial_bounds β (cdf (D.μ : Measure ℝ))
    (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h k z
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩ isOpen_Ioo
    (Hpoly r hr h hh hhsmall k hk z) (Hpoly r hr h hh hhsmall 0 (by norm_num) z)
    ⟨by linarith [hε.1], by linarith [hε.2]⟩

end SKBarriers2.Corner
