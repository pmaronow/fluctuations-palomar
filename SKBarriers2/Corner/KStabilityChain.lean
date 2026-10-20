module

public import SKBarriers2.Corner.KStability

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace SKBarriers2.Corner

section Gronwall

variable {ι : Type}

def variationEnergy (e : ι → ℝ) (l : List ι) : ℝ := (l.map e).sum

theorem variationEnergy_nonneg {e : ι → ℝ} {l : List ι}
    (he : ∀ p ∈ l, 0 ≤ e p) : 0 ≤ variationEnergy e l := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact he p hp

theorem variationEnergy_append (e : ι → ℝ) (l t : List ι) :
    variationEnergy e (l ++ t) = variationEnergy e l + variationEnergy e t := by
  simp only [variationEnergy, List.map_append, List.sum_append]

theorem variation_recursion_le {e : ι → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (a : List ι → ℝ) (l : List ι) (he : ∀ p ∈ l, 0 ≤ e p) (hzero : a [] ≤ 0)
    (hrec : ∀ front p tail, l = front ++ p :: tail →
      a (p :: tail) ≤ (1 + C * e p) * a tail + D * e p)
    (hsmall : 2 * C * variationEnergy e l ≤ 1) :
    a l ≤ 2 * D * variationEnergy e l := by
  induction l with
  | nil => simpa only [variationEnergy, List.map_nil, List.sum_nil, mul_zero] using hzero
  | cons p l ih =>
    have hp : 0 ≤ e p := he p (List.mem_cons_self ..)
    have ht : ∀ q ∈ l, 0 ≤ e q := fun q hq => he q (List.mem_cons_of_mem p hq)
    have hEt : 0 ≤ variationEnergy e l := variationEnergy_nonneg ht
    have hsum : variationEnergy e (p :: l) = e p + variationEnergy e l := rfl
    have htail : 2 * C * variationEnergy e l ≤ 1 := by
      rw [hsum] at hsmall
      nlinarith [mul_nonneg hC hp]
    have hrecTail : ∀ front q tail, l = front ++ q :: tail →
        a (q :: tail) ≤ (1 + C * e q) * a tail + D * e q := by
      intro front q tail h
      apply hrec (p :: front) q tail
      simpa only [List.cons_append, List.cons.injEq, true_and] using h
    have hi := ih ht hrecTail htail
    calc
      a (p :: l) ≤ (1 + C * e p) * a l + D * e p := hrec [] p l rfl
      _ ≤ (1 + C * e p) * (2 * D * variationEnergy e l) + D * e p := by
        gcongr
      _ ≤ 2 * D * variationEnergy e (p :: l) := by
        rw [hsum]
        nlinarith [mul_le_mul_of_nonneg_left htail (mul_nonneg hD hp)]

theorem variation_recursion_tail_le {e : ι → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (a : List ι → ℝ) (l : List ι)
    (he : ∀ p ∈ l, 0 ≤ e p) (hzero : a [] ≤ 0)
    (hrec : ∀ front p tail, l = front ++ p :: tail →
      a (p :: tail) ≤ (1 + C * e p) * a tail + D * e p)
    (hsmall : 2 * C * variationEnergy e l ≤ 1)
    (front tail : List ι) (hsplit : l = front ++ tail) :
    a tail ≤ 2 * D * variationEnergy e tail := by
  have hEt : 0 ≤ variationEnergy e front := variationEnergy_nonneg
    (fun p hp => he p (hsplit.symm ▸ List.mem_append_left tail hp))
  apply variation_recursion_le hC hD a tail
    (fun p hp => he p (hsplit.symm ▸ List.mem_append_right front hp)) hzero
  · intro f p t h
    apply hrec (front ++ f) p t
    rw [List.append_assoc, ← h]
    exact hsplit
  · rw [hsplit, variationEnergy_append] at hsmall
    nlinarith [mul_nonneg hC hEt]

theorem two_level_variation_recursion_le {e : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (a b : List ι → ℝ) (l : List ι) (he : ∀ p ∈ l, 0 ≤ e p)
    (ha : ∀ t, 0 ≤ a t) (ha0 : a [] ≤ 0) (hb0 : b [] ≤ 0)
    (hfirst : ∀ front p tail, l = front ++ p :: tail →
      a (p :: tail) ≤ (1 + C * e p) * a tail + C * e p)
    (hsecond : ∀ front p tail, l = front ++ p :: tail →
      b (p :: tail) ≤ (1 + C * e p) * b tail +
        C * e p * (1 + a tail + a tail ^ 2))
    (hsmall : 2 * C * variationEnergy e l ≤ 1) :
    a l ≤ 2 * C * variationEnergy e l ∧
      b l ≤ 6 * C * variationEnergy e l := by
  refine ⟨variation_recursion_le hC hC a l he ha0 hfirst hsmall, ?_⟩
  have hrec : ∀ front p tail, l = front ++ p :: tail →
      b (p :: tail) ≤ (1 + C * e p) * b tail + (3 * C) * e p := by
    intro front p tail hsplit
    have htail := variation_recursion_tail_le hC hC a l he ha0 hfirst hsmall
      (front ++ [p]) tail (by simpa only [List.append_assoc, List.singleton_append] using hsplit)
    have heTail : variationEnergy e tail ≤ variationEnergy e l := by
      rw [hsplit, variationEnergy_append]
      change variationEnergy e tail ≤ variationEnergy e front + (e p + variationEnergy e tail)
      have hfront := variationEnergy_nonneg
        (fun q hq => he q (hsplit.symm ▸ List.mem_append_left (p :: tail) hq))
      have hp := he p (hsplit.symm ▸ List.mem_append_right front (List.mem_cons_self ..))
      linarith
    have ha1 : a tail ≤ 1 := htail.trans
      ((mul_le_mul_of_nonneg_left heTail (by positivity)).trans hsmall)
    have hsq : a tail ^ 2 ≤ 1 := by nlinarith [ha tail]
    have hp := he p (hsplit.symm ▸ List.mem_append_right front (List.mem_cons_self ..))
    apply (hsecond front p tail hsplit).trans
    have H := mul_le_mul_of_nonneg_left (show 1 + a tail + a tail ^ 2 ≤ 3 by linarith)
      (mul_nonneg hC hp)
    nlinarith
  have H := variation_recursion_le hC (show 0 ≤ 3 * C by positivity)
    b l he hb0 hrec hsmall
  convert H using 1
  ring

end Gronwall

local notation "E" => (Fin 3 → ℝ)

def windowVariationEnergy (k : ℝ) (p : ℝ → ℝ × E) : ℝ :=
  ‖(p k).2‖ ^ 2 + ‖deriv (fun t => (p t).2) k‖ ^ 2 +
    ‖deriv (deriv (fun t => (p t).2)) k‖ ^ 2

theorem windowVariationEnergy_nonneg (k : ℝ) (p : ℝ → ℝ × E) :
    0 ≤ windowVariationEnergy k p := by
  dsimp only [windowVariationEnergy]
  positivity

theorem windowVariationEnergy_sum (k : ℝ) (ps : List (ℝ → ℝ × E)) :
    variationEnergy (windowVariationEnergy k) ps =
      (ps.map fun p => ‖(p k).2‖ ^ 2).sum +
      (ps.map fun p => ‖deriv (fun t => (p t).2) k‖ ^ 2).sum +
      (ps.map fun p => ‖deriv (deriv (fun t => (p t).2)) k‖ ^ 2).sum := by
  change (ps.map (fun p => ‖(p k).2‖ ^ 2 + ‖deriv (fun t => (p t).2) k‖ ^ 2 +
    ‖deriv (deriv (fun t => (p t).2)) k‖ ^ 2)).sum = _
  rw [List.sum_map_add, List.sum_map_add]

def windowFirstVariationSource (k : ℝ) (p : ℝ → ℝ × E) : ℝ :=
  ‖(p k).2‖ * ‖deriv (fun t => (p t).2) k‖ +
    ‖(p k).2‖ ^ 2 * |deriv (fun t => (p t).1) k|

def windowSecondVariationSource (k : ℝ) (p : ℝ → ℝ × E) (a : ℝ) : ℝ :=
  ‖(p k).2‖ ^ 2 * a ^ 2 +
    ‖(p k).2‖ * ‖deriv (fun t => (p t).2) k‖ * a +
    ‖(p k).2‖ ^ 2 * |deriv (fun t => (p t).1) k| * a +
    ‖(p k).2‖ * ‖deriv (deriv (fun t => (p t).2)) k‖ +
    ‖deriv (fun t => (p t).2) k‖ ^ 2 +
    ‖(p k).2‖ ^ 2 * |deriv (deriv (fun t => (p t).1)) k| +
    ‖(p k).2‖ ^ 2 * |deriv (fun t => (p t).1) k| ^ 2

private theorem variation_sources_le {x y z d e a : ℝ}
    (_hx : 0 ≤ x) (_hy : 0 ≤ y) (_hz : 0 ≤ z)
    (hd : d ∈ Icc (0 : ℝ) 1) (he : e ∈ Icc (0 : ℝ) 1) (ha : 0 ≤ a) :
    x * y + x ^ 2 * d ≤ 2 * (x ^ 2 + y ^ 2 + z ^ 2) ∧
      x ^ 2 * a ^ 2 + x * y * a + x ^ 2 * d * a + x * z + y ^ 2 +
        x ^ 2 * e + x ^ 2 * d ^ 2 ≤
          4 * (x ^ 2 + y ^ 2 + z ^ 2) * (1 + a + a ^ 2) := by
  let S := x ^ 2 + y ^ 2 + z ^ 2
  have hE : 0 ≤ S := by dsimp only [S]; positivity
  have hxy : x * y ≤ S := by dsimp only [S]; nlinarith [sq_nonneg (x - y), sq_nonneg z]
  have hxz : x * z ≤ S := by dsimp only [S]; nlinarith [sq_nonneg (x - z), sq_nonneg y]
  have hx2 : x ^ 2 ≤ S := by dsimp only [S]; nlinarith [sq_nonneg y, sq_nonneg z]
  have hy2 : y ^ 2 ≤ S := by dsimp only [S]; nlinarith [sq_nonneg x, sq_nonneg z]
  have hxd : x ^ 2 * d ≤ S :=
    (mul_le_of_le_one_right (sq_nonneg x) hd.2).trans hx2
  have hxe : x ^ 2 * e ≤ S :=
    (mul_le_of_le_one_right (sq_nonneg x) he.2).trans hx2
  have hd2 : d ^ 2 ≤ 1 := by nlinarith [hd.1, hd.2]
  have hxd2 : x ^ 2 * d ^ 2 ≤ S :=
    (mul_le_of_le_one_right (sq_nonneg x) hd2).trans hx2
  constructor
  · change x * y + x ^ 2 * d ≤ 2 * S
    linarith
  · change _ ≤ 4 * S * (1 + a + a ^ 2)
    have hxa2 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg a)
    have hxya := mul_le_mul_of_nonneg_right hxy ha
    have hxda := mul_le_mul_of_nonneg_right hxd ha
    nlinarith [mul_nonneg hE ha, mul_nonneg hE (sq_nonneg a)]

theorem window_variation_sources_le (k : ℝ) (p : ℝ → ℝ × E)
    (hm1 : |deriv (fun t => (p t).1) k| ≤ 1)
    (hm2 : |deriv (deriv (fun t => (p t).1)) k| ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    windowFirstVariationSource k p ≤ 2 * windowVariationEnergy k p ∧
      windowSecondVariationSource k p a ≤
        4 * windowVariationEnergy k p * (1 + a + a ^ 2) := by
  exact variation_sources_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    ⟨abs_nonneg _, hm1⟩ ⟨abs_nonneg _, hm2⟩ ha

theorem window_two_level_recursion_le (ps : List (ℝ → ℝ × E)) (k : ℝ)
    {K : ℝ} (hK : 0 ≤ K) (a b : List (ℝ → ℝ × E) → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) (ha0 : a [] ≤ 0) (hb0 : b [] ≤ 0)
    (hm : ∀ p ∈ ps, |deriv (fun t => (p t).1) k| ≤ 1 ∧
      |deriv (deriv (fun t => (p t).1)) k| ≤ 1)
    (hfirst : ∀ front p tail, ps = front ++ p :: tail →
      a (p :: tail) ≤ (1 + K * ‖(p k).2‖ ^ 2) * a tail +
        K * windowFirstVariationSource k p)
    (hsecond : ∀ front p tail, ps = front ++ p :: tail →
      b (p :: tail) ≤ (1 + K * ‖(p k).2‖ ^ 2) * b tail +
        K * windowSecondVariationSource k p (a tail))
    (hsmall : 8 * K * variationEnergy (windowVariationEnergy k) ps ≤ 1) :
    a ps ≤ 8 * K * variationEnergy (windowVariationEnergy k) ps ∧
      b ps ≤ 24 * K * variationEnergy (windowVariationEnergy k) ps := by
  have hrec1 : ∀ front p tail, ps = front ++ p :: tail →
      a (p :: tail) ≤ (1 + (4 * K) * windowVariationEnergy k p) * a tail +
        (4 * K) * windowVariationEnergy k p := by
    intro front p tail hsplit
    have hp : p ∈ ps := hsplit.symm ▸ List.mem_append_right front (List.mem_cons_self ..)
    have hsource := (window_variation_sources_le k p (hm p hp).1 (hm p hp).2 (ha tail)).1
    have he := windowVariationEnergy_nonneg k p
    have hv : ‖(p k).2‖ ^ 2 ≤ windowVariationEnergy k p := by
      dsimp only [windowVariationEnergy]
      nlinarith [sq_nonneg ‖deriv (fun t => (p t).2) k‖,
        sq_nonneg ‖deriv (deriv (fun t => (p t).2)) k‖]
    apply (hfirst front p tail hsplit).trans
    have hc : K * ‖(p k).2‖ ^ 2 ≤ (4 * K) * windowVariationEnergy k p := by
      exact (mul_le_mul_of_nonneg_left hv hK).trans (by nlinarith [mul_nonneg hK he])
    have hgain := mul_le_mul_of_nonneg_right (add_le_add_left hc 1) (ha tail)
    have hs := mul_le_mul_of_nonneg_left hsource hK
    nlinarith [mul_nonneg hK he]
  have hrec2 : ∀ front p tail, ps = front ++ p :: tail →
      b (p :: tail) ≤ (1 + (4 * K) * windowVariationEnergy k p) * b tail +
        (4 * K) * windowVariationEnergy k p * (1 + a tail + a tail ^ 2) := by
    intro front p tail hsplit
    have hp : p ∈ ps := hsplit.symm ▸ List.mem_append_right front (List.mem_cons_self ..)
    have hsource := (window_variation_sources_le k p (hm p hp).1 (hm p hp).2 (ha tail)).2
    have he := windowVariationEnergy_nonneg k p
    have hv : ‖(p k).2‖ ^ 2 ≤ windowVariationEnergy k p := by
      dsimp only [windowVariationEnergy]
      nlinarith [sq_nonneg ‖deriv (fun t => (p t).2) k‖,
        sq_nonneg ‖deriv (deriv (fun t => (p t).2)) k‖]
    apply (hsecond front p tail hsplit).trans
    have hc : K * ‖(p k).2‖ ^ 2 ≤ (4 * K) * windowVariationEnergy k p := by
      exact (mul_le_mul_of_nonneg_left hv hK).trans (by nlinarith [mul_nonneg hK he])
    have hgain := mul_le_mul_of_nonneg_right (add_le_add_left hc 1) (hb tail)
    have hs := mul_le_mul_of_nonneg_left hsource hK
    nlinarith
  have H := two_level_variation_recursion_le (show 0 ≤ 4 * K by positivity)
    a b ps (fun p _ => windowVariationEnergy_nonneg k p) ha ha0 hb0 hrec1 hrec2
    (by nlinarith [hsmall])
  exact ⟨by nlinarith [H.1], by nlinarith [H.2]⟩

theorem scalarData_window_variation_budget {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ N : ℕ, 1 ≤ N →
      ∀ k : ℝ, |k| ≤ 1 / 2 →
      let ps := windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N
      variationEnergy (windowVariationEnergy k) ps ≤ C * h ∧
      ∀ p ∈ ps, |deriv (fun t => (p t).1) k| ≤ 1 ∧
        |deriv (deriv (fun t => (p t).1)) k| ≤ 1 := by
  obtain ⟨A, h₁, hA, hh₁, hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  obtain ⟨K, h₂, hK, hh₂, henergy⟩ := scalarData_window_parameter_energies D hl hlu hu
  refine ⟨3 * K + 1, min (min h₁ h₂) (1 / A), by positivity,
    lt_min (lt_min hh₁ hh₂) (one_div_pos.mpr hA), ?_⟩
  intro r hr h hh hh0 N hN k hk
  have hh1 : h ≤ h₁ := hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : h ≤ h₂ := hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hAh : A * h ≤ 1 := by
    have H := hh0.trans (min_le_right _ _)
    have H' := (le_div_iff₀ hA).mp H
    nlinarith
  obtain ⟨he0, he1, he2⟩ := henergy r hr h hh hh2 N hN k hk
  constructor
  · rw [windowVariationEnergy_sum]
    linarith
  · intro p hp
    have H := hparam r hr h hh hh1 N hN p hp k hk
    exact ⟨H.2.1.trans hAh, H.2.2.1.trans hAh⟩

end SKBarriers2.Corner
