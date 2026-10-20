module

public import SKConstants.FiniteChainPruning
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic

public section

noncomputable section
open scoped Classical
namespace SKConstants
namespace Cheeger

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def weightedMass (pi : V → ℝ) (f : V → ℝ) : ℝ := ∑ x, pi x * f x
@[expose] def variation (q : V → V → ℝ) (f : V → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, q x y * |f x - f y|
@[expose] def dirichlet (q : V → V → ℝ) (f : V → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, q x y * (f x - f y) ^ 2
@[expose] def indicator (S : Finset V) (x : V) : ℝ := if x ∈ S then 1 else 0

omit [Fintype V] [DecidableEq V] in
lemma cutFlow_swap (q : V → V → ℝ) (hq : ∀ x y, q x y = q y x)
    (S T : Finset V) : cutFlow q S T = cutFlow q T S := by
  unfold cutFlow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  exact hq x y

lemma weightedMass_indicator (pi : V → ℝ) (S : Finset V) :
    weightedMass pi (indicator S) = cutMass pi S := by
  simp only [weightedMass, indicator, mul_ite, mul_one, mul_zero]
  exact (Finset.sum_subset (Finset.subset_univ S) (by
    intro x _ hx
    simp [hx])).symm.trans (by simp [cutMass])

lemma variation_indicator (q : V → V → ℝ) (hq : ∀ x y, q x y = q y x)
    (S : Finset V) : variation q (indicator S) = cutFlow q S Sᶜ := by
  have inner : ∀ x, (∑ y, q x y * |indicator S x - indicator S y|) =
      if x ∈ S then ∑ y ∈ Sᶜ, q x y else ∑ y ∈ S, q x y := by
    intro x
    by_cases hx : x ∈ S
    · simp only [indicator, hx, ite_true]
      have hterm : ∀ y, q x y * |1 - (if y ∈ S then 1 else 0)| =
          if y ∈ Sᶜ then q x y else 0 := by
        intro y
        by_cases hy : y ∈ S <;> simp [hy]
      simp_rw [hterm]
      rw [← Finset.sum_filter]
      have heq : (Finset.univ.filter fun y => y ∈ Sᶜ) = Sᶜ := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq]
    · simp only [indicator, hx, ite_false]
      have hterm : ∀ y, q x y * |0 - (if y ∈ S then 1 else 0)| =
          if y ∈ S then q x y else 0 := by
        intro y
        by_cases hy : y ∈ S <;> simp [hy]
      simp_rw [hterm]
      simp
  unfold variation
  simp_rw [inner]
  have hsplit : (∑ x, if x ∈ S then ∑ y ∈ Sᶜ, q x y else ∑ y ∈ S, q x y) =
      cutFlow q S Sᶜ + cutFlow q Sᶜ S := by
    unfold cutFlow
    conv_lhs => rw [← Finset.sum_add_sum_compl S]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro x hx
      simp [hx]
    · apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_compl.mp hx]
  rw [hsplit, cutFlow_swap q hq Sᶜ S]
  ring

omit [DecidableEq V] in
lemma variation_nonneg (q : V → V → ℝ) (hq : ∀ x y, 0 ≤ q x y)
    (f : V → ℝ) : 0 ≤ variation q f := by
  unfold variation
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => mul_nonneg (hq x y) (abs_nonneg _))

lemma coarea_support (pi : V → ℝ) (q : V → V → ℝ) (B : ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (_hq : ∀ x y, 0 ≤ q x y)
    (hsym : ∀ x y, q x y = q y x)
    (hexpand : ∀ S : Finset V, cutMass pi S ≤ cutMass pi Finset.univ / 2 →
      B * cutMass pi S ≤ cutFlow q S Sᶜ)
    (S : Finset V) (hhalf : cutMass pi S ≤ cutMass pi Finset.univ / 2)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ S → f x = 0) :
    B * weightedMass pi f ≤ variation q f := by
  classical
  induction S using Finset.strongInduction generalizing f with
  | H S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S f hS
      let m := f a
      let g : V → ℝ := fun x => f x - m * indicator S x
      have hm : 0 ≤ m := hf a
      have hg : ∀ x, 0 ≤ g x := by
        intro x
        by_cases hx : x ∈ S
        · simp only [g, indicator, hx, ite_true, mul_one]
          exact sub_nonneg.mpr (hmin x hx)
        · simp [g, indicator, hx, hsupport x hx]
      have hgsupport : ∀ x, x ∉ S.erase a → g x = 0 := by
        intro x hx
        by_cases hxa : x = a
        · subst x
          simp [g, indicator, ha, m]
        · have hxS : x ∉ S := by
            intro hxS
            exact hx (Finset.mem_erase.mpr ⟨hxa, hxS⟩)
          simp [g, indicator, hxS, hsupport x hxS]
      have hhalf' : cutMass pi (S.erase a) ≤ cutMass pi Finset.univ / 2 :=
        (cutMass_mono pi hpi (Finset.erase_subset a S)).trans hhalf
      have hrec := ih (S.erase a) (Finset.erase_ssubset ha) hhalf' g hg hgsupport
      have hmass : weightedMass pi f = weightedMass pi g + m * cutMass pi S := by
        rw [← weightedMass_indicator pi S]
        unfold weightedMass
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [g]
        ring
      have hvar : variation q f = variation q g + m * variation q (indicator S) := by
        have hsum : (∑ x, ∑ y, q x y * |f x - f y|) =
            (∑ x, ∑ y, q x y * |g x - g y|) +
              m * ∑ x, ∑ y, q x y * |indicator S x - indicator S y| := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro y hy
          have habs : |f x - f y| = |g x - g y| + m * |indicator S x - indicator S y| := by
            by_cases hxS : x ∈ S <;> by_cases hyS : y ∈ S
            · simp [g, indicator, hxS, hyS]
            · have hy0 := hsupport y hyS
              have hmx := hmin x hxS
              change m ≤ f x at hmx
              simp [g, indicator, hxS, hyS, hy0, abs_of_nonneg (hf x),
                abs_of_nonneg (sub_nonneg.mpr hmx)]
            · have hx0 := hsupport x hxS
              have hmy := hmin y hyS
              change m ≤ f y at hmy
              simp [g, indicator, hxS, hyS, hx0, abs_neg, abs_of_nonneg (hf y),
                abs_of_nonpos (sub_nonpos.mpr hmy)]
            · simp [g, indicator, hxS, hyS]
          rw [habs]
          ring
        unfold variation
        rw [hsum]
        ring
      rw [hmass, hvar, variation_indicator q hsym S]
      nlinarith [mul_le_mul_of_nonneg_left (hexpand S hhalf) hm]
    · have hzero : f = fun _ => 0 := by
        funext x
        exact hsupport x (by simp [Finset.not_nonempty_iff_eq_empty.mp hS])
      simp [hzero, weightedMass, variation]

omit [DecidableEq V] in
lemma square_variation_cauchy (q : V → V → ℝ) (hq : ∀ x y, 0 ≤ q x y)
    (f : V → ℝ) :
    (∑ x, ∑ y, q x y * |f x ^ 2 - f y ^ 2|) ^ 2 ≤
      (∑ x, ∑ y, q x y * (f x - f y) ^ 2) *
        (∑ x, ∑ y, q x y * (f x + f y) ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (V × V))
    (r := fun z => q z.1 z.2 * |f z.1 ^ 2 - f z.2 ^ 2|)
    (f := fun z => q z.1 z.2 * (f z.1 - f z.2) ^ 2)
    (g := fun z => q z.1 z.2 * (f z.1 + f z.2) ^ 2)
    (fun z _ => mul_nonneg (hq z.1 z.2) (sq_nonneg _))
    (fun z _ => mul_nonneg (hq z.1 z.2) (sq_nonneg _)) (fun z _ => by
      rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (q z.1 z.2 * (f z.1 ^ 2 - f z.2 ^ 2))])
  simpa only [Fintype.sum_prod_type] using h

omit [DecidableEq V] in
lemma sum_symmetric_second (q : V → V → ℝ) (hsym : ∀ x y, q x y = q y x)
    (f : V → ℝ) :
    (∑ x, ∑ y, q x y * f y) = ∑ x, ∑ y, q x y * f x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hsym y x]

omit [DecidableEq V] in
lemma sum_plus_sq_le (pi : V → ℝ) (q : V → V → ℝ) (R : ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (hsym : ∀ x y, q x y = q y x)
    (hrow : ∀ x, ∑ y, q x y ≤ R * pi x) (f : V → ℝ) :
    (∑ x, ∑ y, q x y * (f x + f y) ^ 2) ≤
      4 * R * weightedMass pi (fun x => f x ^ 2) := by
  have hpoint : ∀ x y, q x y * (f x + f y) ^ 2 ≤
      2 * (q x y * f x ^ 2 + q x y * f y ^ 2) := by
    intro x y
    have h := mul_le_mul_of_nonneg_left
      (show (f x + f y) ^ 2 ≤ 2 * (f x ^ 2 + f y ^ 2) by
        nlinarith [sq_nonneg (f x - f y)]) (hq x y)
    nlinarith
  have hsum : (∑ x, ∑ y, q x y * (f x + f y) ^ 2) ≤
      ∑ x, ∑ y, 2 * (q x y * f x ^ 2 + q x y * f y ^ 2) := by
    exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hpoint x y))
  have hsums : (∑ x, ∑ y, 2 * (q x y * f x ^ 2 + q x y * f y ^ 2)) =
      4 * ∑ x, (∑ y, q x y) * f x ^ 2 := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_symmetric_second q hsym]
    simp_rw [← Finset.sum_mul]
    ring
  have hrows : (∑ x, (∑ y, q x y) * f x ^ 2) ≤
      R * weightedMass pi (fun x => f x ^ 2) := by
    unfold weightedMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have h := mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg (f x))
    nlinarith
  exact (hsum.trans_eq hsums).trans (by nlinarith)

lemma half_supported_cheeger (pi : V → ℝ) (q : V → V → ℝ) (B R : ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (hq : ∀ x y, 0 ≤ q x y)
    (hsym : ∀ x y, q x y = q y x) (hB : 0 < B) (hR : 0 ≤ R)
    (hrow : ∀ x, ∑ y, q x y ≤ R * pi x)
    (hexpand : ∀ S : Finset V, cutMass pi S ≤ cutMass pi Finset.univ / 2 →
      B * cutMass pi S ≤ cutFlow q S Sᶜ)
    (S : Finset V) (hhalf : cutMass pi S ≤ cutMass pi Finset.univ / 2)
    (f : V → ℝ) (hsupport : ∀ x, x ∉ S → f x = 0) :
    B ^ 2 * weightedMass pi (fun x => f x ^ 2) ≤ 2 * R * dirichlet q f := by
  let A := weightedMass pi (fun x => f x ^ 2)
  change B ^ 2 * A ≤ 2 * R * dirichlet q f
  have hA : 0 ≤ A := Finset.sum_nonneg fun x _ => mul_nonneg (hpi x) (sq_nonneg _)
  have hco := coarea_support pi q B hpi hq hsym hexpand S hhalf
    (fun x => f x ^ 2) (fun x => sq_nonneg _) (by
      intro x hx
      simp [hsupport x hx])
  change B * A ≤ variation q (fun x => f x ^ 2) at hco
  have hco_sq : (B * A) ^ 2 ≤ (variation q (fun x => f x ^ 2)) ^ 2 :=
    sq_le_sq₀ (mul_nonneg hB.le hA) (variation_nonneg q hq _) |>.mpr hco
  have hCS := square_variation_cauchy q hq f
  have hplus := sum_plus_sq_le pi q R hq hsym hrow f
  change _ ≤ 4 * R * A at hplus
  have hD : 0 ≤ ∑ x, ∑ y, q x y * (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hq x y) (sq_nonneg _)
  have hproduct := mul_le_mul_of_nonneg_left hplus hD
  unfold variation at hco_sq
  change _ ≤ (1 / 2 * ∑ x, ∑ y, q x y * |f x ^ 2 - f y ^ 2|) ^ 2 at hco_sq
  by_cases hAz : A = 0
  · rw [hAz]
    have hRprod : 0 ≤ R * dirichlet q f :=
      mul_nonneg hR (by unfold dirichlet; exact mul_nonneg (by norm_num) hD)
    nlinarith
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hmain : B ^ 2 * A ^ 2 ≤
        2 * R * ((1 / 2) * ∑ x, ∑ y, q x y * (f x - f y) ^ 2) * A := by
      nlinarith [hco_sq, hCS, hproduct]
    unfold dirichlet
    exact (mul_le_mul_iff_of_pos_right hApos).mp (by nlinarith [hmain])

lemma cutMass_add_compl (pi : V → ℝ) (S : Finset V) :
    cutMass pi S + cutMass pi Sᶜ = cutMass pi Finset.univ := by
  unfold cutMass
  exact Finset.sum_add_sum_compl S (fun x => pi x)

@[expose] def lowerCut (u : V → ℝ) (m : ℝ) : Finset V := Finset.univ.filter (fun x => u x < m)
@[expose] def upperCut (u : V → ℝ) (m : ℝ) : Finset V := Finset.univ.filter (fun x => m < u x)
@[expose] def weakLowerCut (u : V → ℝ) (m : ℝ) : Finset V :=
  Finset.univ.filter (fun x => u x ≤ m)

lemma exists_weighted_median (pi : V → ℝ) (u : V → ℝ)
    (hM : 0 < cutMass pi Finset.univ) :
    ∃ m : ℝ, cutMass pi (lowerCut u m) ≤ cutMass pi Finset.univ / 2 ∧
      cutMass pi (upperCut u m) ≤ cutMass pi Finset.univ / 2 := by
  classical
  have hV : (Finset.univ : Finset V).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [cutMass, he] at hM
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image Finset.univ u hV
  let S : Finset V := Finset.univ.filter (fun x =>
    cutMass pi Finset.univ / 2 ≤ cutMass pi (weakLowerCut u (u x)))
  have hbS : b ∈ S := by
    have hfull : weakLowerCut u (u b) = Finset.univ := by
      ext x
      simp only [weakLowerCut, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ => trivial, fun _ => hmax x (Finset.mem_univ _)⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfull]
    linarith
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S u ⟨b, hbS⟩
  refine ⟨u a, ?_, ?_⟩
  · by_cases hl : (lowerCut u (u a)).Nonempty
    · obtain ⟨b', hb', hmax'⟩ := Finset.exists_max_image (lowerCut u (u a)) u hl
      have hb'lt : u b' < u a := (Finset.mem_filter.mp hb').2
      have heq : weakLowerCut u (u b') = lowerCut u (u a) := by
        ext x
        simp only [weakLowerCut, lowerCut, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun hx => lt_of_le_of_lt hx hb'lt
        · intro hx
          exact hmax' x (by simp [lowerCut, hx])
      by_contra h
      have hb'S : b' ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [heq]
        exact (lt_of_not_ge h).le
      exact (not_lt_of_ge (hmin b' hb'S)) hb'lt
    · rw [Finset.not_nonempty_iff_eq_empty.mp hl, cutMass_empty]
      linarith
  · have hle : cutMass pi Finset.univ / 2 ≤ cutMass pi (weakLowerCut u (u a)) :=
      (Finset.mem_filter.mp ha).2
    have hcompl : upperCut u (u a) = (weakLowerCut u (u a))ᶜ := by
      ext x
      simp [upperCut, weakLowerCut, not_le]
    rw [hcompl]
    have hsum := cutMass_add_compl pi (weakLowerCut u (u a))
    linarith

@[expose] def weightedMean (pi : V → ℝ) (u : V → ℝ) : ℝ :=
  weightedMass pi u / cutMass pi Finset.univ

@[expose] def weightedVariance (pi : V → ℝ) (u : V → ℝ) : ℝ :=
  weightedMass pi (fun x => (u x - weightedMean pi u) ^ 2)

omit [DecidableEq V] in
lemma weightedVariance_le_center (pi : V → ℝ) (u : V → ℝ) (m : ℝ)
    (hM : 0 < cutMass pi Finset.univ) :
    weightedVariance pi u ≤ weightedMass pi (fun x => (u x - m) ^ 2) := by
  have hsum : weightedMass pi (fun x => u x - weightedMean pi u) = 0 := by
      unfold weightedMass weightedMean
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      change weightedMass pi u -
        cutMass pi Finset.univ * (weightedMass pi u / cutMass pi Finset.univ) = 0
      rw [mul_comm (cutMass pi Finset.univ)]
      rw [div_mul_cancel₀ _ (ne_of_gt hM), sub_self]
  have hid : weightedMass pi (fun x => (u x - m) ^ 2) =
        weightedVariance pi u +
          cutMass pi Finset.univ * (weightedMean pi u - m) ^ 2 := by
      unfold weightedVariance
      have hpoint : ∀ x, pi x * (u x - m) ^ 2 =
          pi x * (u x - weightedMean pi u) ^ 2 +
            2 * (weightedMean pi u - m) * (pi x * (u x - weightedMean pi u)) +
            pi x * (weightedMean pi u - m) ^ 2 := by
        intro x
        ring
      unfold weightedMass
      simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      change _ = _
      change (∑ x, pi x * (u x - weightedMean pi u) ^ 2) +
        2 * (weightedMean pi u - m) * weightedMass pi (fun x => u x - weightedMean pi u) +
        cutMass pi Finset.univ * (weightedMean pi u - m) ^ 2 = _
      rw [hsum]
      ring
  rw [hid]
  exact le_add_of_nonneg_right (mul_nonneg hM.le (sq_nonneg _))

@[expose] def positivePart (u : V → ℝ) (m : ℝ) (x : V) : ℝ := max (u x - m) 0
@[expose] def negativePart (u : V → ℝ) (m : ℝ) (x : V) : ℝ := max (m - u x) 0

omit [Fintype V] [DecidableEq V] in
lemma parts_sq (u : V → ℝ) (m : ℝ) (x : V) :
    (u x - m) ^ 2 = positivePart u m x ^ 2 + negativePart u m x ^ 2 := by
  by_cases hx : m ≤ u x
  · simp [positivePart, negativePart, max_eq_left (sub_nonneg.mpr hx),
      max_eq_right (sub_nonpos.mpr hx)]
  · have hx' : u x ≤ m := (lt_of_not_ge hx).le
    simp [positivePart, negativePart, max_eq_right (sub_nonpos.mpr hx'),
      max_eq_left (sub_nonneg.mpr hx')]
    ring

omit [Fintype V] [DecidableEq V] in
lemma parts_edge_sq_le (u : V → ℝ) (m : ℝ) (x y : V) :
    (positivePart u m x - positivePart u m y) ^ 2 +
      (negativePart u m x - negativePart u m y) ^ 2 ≤ (u x - u y) ^ 2 := by
  by_cases hx : m ≤ u x <;> by_cases hy : m ≤ u y
  · simp [positivePart, negativePart, max_eq_left (sub_nonneg.mpr hx),
      max_eq_right (sub_nonpos.mpr hx), max_eq_left (sub_nonneg.mpr hy),
      max_eq_right (sub_nonpos.mpr hy)]
  · have hy' : u y ≤ m := (lt_of_not_ge hy).le
    simp only [positivePart, negativePart, max_eq_left (sub_nonneg.mpr hx),
      max_eq_right (sub_nonpos.mpr hx), max_eq_right (sub_nonpos.mpr hy'),
      max_eq_left (sub_nonneg.mpr hy')]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy')]
  · have hx' : u x ≤ m := (lt_of_not_ge hx).le
    simp only [positivePart, negativePart, max_eq_right (sub_nonpos.mpr hx'),
      max_eq_left (sub_nonneg.mpr hx'), max_eq_left (sub_nonneg.mpr hy),
      max_eq_right (sub_nonpos.mpr hy)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy)]
  · have hx' : u x ≤ m := (lt_of_not_ge hx).le
    have hy' : u y ≤ m := (lt_of_not_ge hy).le
    simp only [positivePart, negativePart, max_eq_right (sub_nonpos.mpr hx'),
      max_eq_left (sub_nonneg.mpr hx'), max_eq_right (sub_nonpos.mpr hy'),
      max_eq_left (sub_nonneg.mpr hy')]
    nlinarith

omit [DecidableEq V] in
lemma parts_dirichlet_le (q : V → V → ℝ) (hq : ∀ x y, 0 ≤ q x y)
    (u : V → ℝ) (m : ℝ) :
    dirichlet q (positivePart u m) + dirichlet q (negativePart u m) ≤ dirichlet q u := by
  unfold dirichlet
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y hy
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (parts_edge_sq_le u m x y) (hq x y)

theorem finite_cheeger (pi : V → ℝ) (q : V → V → ℝ) (B R : ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (hM : 0 < cutMass pi Finset.univ)
    (hq : ∀ x y, 0 ≤ q x y) (hsym : ∀ x y, q x y = q y x)
    (hB : 0 < B) (hR : 0 ≤ R) (hrow : ∀ x, ∑ y, q x y ≤ R * pi x)
    (hexpand : ∀ S : Finset V, cutMass pi S ≤ cutMass pi Finset.univ / 2 →
      B * cutMass pi S ≤ cutFlow q S Sᶜ)
    (u : V → ℝ) : weightedVariance pi u ≤ (2 * R / B ^ 2) * dirichlet q u := by
  obtain ⟨m, hlower, hupper⟩ := exists_weighted_median pi u hM
  have hp := half_supported_cheeger pi q B R hpi hq hsym hB hR hrow hexpand
    (upperCut u m) hupper (positivePart u m) (by
      intro x hx
      have hxm : u x ≤ m := by simpa [upperCut, not_lt] using hx
      simp [positivePart, max_eq_right (sub_nonpos.mpr hxm)])
  have hn := half_supported_cheeger pi q B R hpi hq hsym hB hR hrow hexpand
    (lowerCut u m) hlower (negativePart u m) (by
      intro x hx
      have hxm : m ≤ u x := by simpa [lowerCut, not_lt] using hx
      simp [negativePart, max_eq_right (sub_nonpos.mpr hxm)])
  have hmass : weightedMass pi (fun x => (u x - m) ^ 2) =
      weightedMass pi (fun x => positivePart u m x ^ 2) +
        weightedMass pi (fun x => negativePart u m x ^ 2) := by
    unfold weightedMass
    simp_rw [parts_sq, mul_add, Finset.sum_add_distrib]
  have hcenter := weightedVariance_le_center pi u m hM
  have hpart := parts_dirichlet_le q hq u m
  have hmain : B ^ 2 * weightedVariance pi u ≤ 2 * R * dirichlet q u := calc
    _ ≤ B ^ 2 * weightedMass pi (fun x => (u x - m) ^ 2) :=
      mul_le_mul_of_nonneg_left hcenter (sq_nonneg _)
    _ = B ^ 2 * (weightedMass pi (fun x => positivePart u m x ^ 2) +
        weightedMass pi (fun x => negativePart u m x ^ 2)) := by rw [hmass]
    _ ≤ 2 * R * (dirichlet q (positivePart u m) + dirichlet q (negativePart u m)) := by
      nlinarith [hp, hn]
    _ ≤ 2 * R * dirichlet q u := mul_le_mul_of_nonneg_left hpart (by positivity)
  have hdiv : weightedVariance pi u ≤ (2 * R * dirichlet q u) / B ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hB)).mpr (by nlinarith [hmain])
  convert hdiv using 1
  ring

omit [Fintype V] [DecidableEq V] in
lemma sum_core_subtype (C : Finset V) (f : V → ℝ) :
    (∑ x : C, f x) = ∑ x ∈ C, f x := by
  exact (Finset.sum_subtype (p := fun x => x ∈ C) C (fun x => Iff.rfl) f).symm

omit [Fintype V] in
lemma map_core_compl (C : Finset V) (S : Finset C) :
    Sᶜ.map (Function.Embedding.subtype (fun x => x ∈ C)) =
      C \ S.map (Function.Embedding.subtype (fun x => x ∈ C)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    subst x
    refine Finset.mem_sdiff.mpr ⟨y.property, ?_⟩
    intro hmem
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hmem
    have hzy' : z = y := Subtype.ext hzy
    subst z
    exact (Finset.mem_compl.mp hy) hz
  · intro hx
    obtain ⟨hxC, hxS⟩ := Finset.mem_sdiff.mp hx
    let y : C := ⟨x, hxC⟩
    apply Finset.mem_map.mpr
    refine ⟨y, Finset.mem_compl.mpr ?_, rfl⟩
    intro hy
    exact hxS (Finset.mem_map.mpr ⟨y, hy, rfl⟩)

@[expose] def coreMean (pi : V → ℝ) (C : Finset V) (u : V → ℝ) : ℝ :=
  (∑ x ∈ C, pi x * u x) / cutMass pi C

@[expose] def coreVariance (pi : V → ℝ) (C : Finset V) (u : V → ℝ) : ℝ :=
  ∑ x ∈ C, pi x * (u x - coreMean pi C u) ^ 2

@[expose] def coreDirichlet (q : V → V → ℝ) (C : Finset V) (u : V → ℝ) : ℝ :=
  (1 / 2) * ∑ x ∈ C, ∑ y ∈ C, q x y * (u x - u y) ^ 2

theorem retained_core_cheeger (pi : V → ℝ) (q : V → V → ℝ) (C : Finset V)
    (B R : ℝ) (hpi : ∀ x, 0 ≤ pi x) (hM : 0 < cutMass pi C)
    (hq : ∀ x y, 0 ≤ q x y) (hsym : ∀ x y, q x y = q y x)
    (hB : 0 < B) (hR : 0 ≤ R) (hrow : ∀ x, ∑ y, q x y ≤ R * pi x)
    (hexpand : ∀ S : Finset V, S ⊆ C → cutMass pi S ≤ cutMass pi C / 2 →
      B * cutMass pi S ≤ cutFlow q S (C \ S))
    (u : V → ℝ) : coreVariance pi C u ≤ (2 * R / B ^ 2) * coreDirichlet q C u := by
  classical
  let pi' : C → ℝ := fun x => pi x
  let q' : C → C → ℝ := fun x y => q x y
  let u' : C → ℝ := fun x => u x
  have hmass : cutMass pi' Finset.univ = cutMass pi C := by
    unfold cutMass
    exact sum_core_subtype C pi
  have hrow' : ∀ x : C, ∑ y : C, q' x y ≤ R * pi' x := by
    intro x
    change (∑ y : C, q x y) ≤ R * pi x
    rw [sum_core_subtype C (fun y => q x y)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
      (fun y _ _ => hq x y)).trans (hrow x)
  have hexpand' : ∀ S : Finset C, cutMass pi' S ≤ cutMass pi' Finset.univ / 2 →
      B * cutMass pi' S ≤ cutFlow q' S Sᶜ := by
    intro S hS
    let e := Function.Embedding.subtype (fun x => x ∈ C)
    let U := S.map e
    have hU : U ⊆ C := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
      rw [← hyx]
      exact y.property
    have hm : cutMass pi U = cutMass pi' S := by
      unfold cutMass
      exact Finset.sum_map S e pi
    have hflow : cutFlow q U (C \ U) = cutFlow q' S Sᶜ := by
      change cutFlow q (S.map e) (C \ S.map e) = _
      rw [← map_core_compl C S]
      unfold cutFlow
      simp only [Finset.sum_map]
      rfl
    have h := hexpand U hU (by rw [hm, ← hmass]; exact hS)
    rw [hm, hflow] at h
    exact h
  have h := finite_cheeger pi' q' B R (fun x => hpi x) (by rw [hmass]; exact hM)
    (fun x y => hq x y) (fun x y => hsym x y) hB hR hrow' hexpand' u'
  have hmean : weightedMean pi' u' = coreMean pi C u := by
    unfold weightedMean weightedMass coreMean
    rw [hmass]
    dsimp only [pi', u']
    rw [sum_core_subtype C (fun x => pi x * u x)]
  have hvar : weightedVariance pi' u' = coreVariance pi C u := by
    unfold weightedVariance weightedMass coreVariance
    rw [hmean]
    exact sum_core_subtype C (fun x => pi x * (u x - coreMean pi C u) ^ 2)
  have hdir : dirichlet q' u' = coreDirichlet q C u := by
    unfold dirichlet coreDirichlet
    dsimp only [q', u']
    congr 1
    calc
      (∑ x : C, ∑ y : C, q x y * (u x - u y) ^ 2) =
          ∑ x : C, ∑ y ∈ C, q x y * (u x - u y) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact sum_core_subtype C (fun y => q x y * (u x - u y) ^ 2)
      _ = ∑ x ∈ C, ∑ y ∈ C, q x y * (u x - u y) ^ 2 :=
        sum_core_subtype C (fun x => ∑ y ∈ C, q x y * (u x - u y) ^ 2)
  rwa [hvar, hdir] at h

omit [DecidableEq V] in
lemma coreDirichlet_le (q : V → V → ℝ) (hq : ∀ x y, 0 ≤ q x y)
    (C : Finset V) (u : V → ℝ) : coreDirichlet q C u ≤ dirichlet q u := by
  unfold coreDirichlet dirichlet
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ x ∈ C, ∑ y, q x y * (u x - u y) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun y _ _ => mul_nonneg (hq x y) (sq_nonneg _))
    _ ≤ ∑ x, ∑ y, q x y * (u x - u y) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun x _ _ => Finset.sum_nonneg fun y _ => mul_nonneg (hq x y) (sq_nonneg _))

theorem retained_core_cheeger_full (pi : V → ℝ) (q : V → V → ℝ) (C : Finset V)
    (B R : ℝ) (hpi : ∀ x, 0 ≤ pi x) (hM : 0 < cutMass pi C)
    (hq : ∀ x y, 0 ≤ q x y) (hsym : ∀ x y, q x y = q y x)
    (hB : 0 < B) (hR : 0 ≤ R) (hrow : ∀ x, ∑ y, q x y ≤ R * pi x)
    (hexpand : ∀ S : Finset V, S ⊆ C → cutMass pi S ≤ cutMass pi C / 2 →
      B * cutMass pi S ≤ cutFlow q S (C \ S))
    (u : V → ℝ) : coreVariance pi C u ≤ (2 * R / B ^ 2) * dirichlet q u := by
  exact (retained_core_cheeger pi q C B R hpi hM hq hsym hB hR hrow hexpand u).trans
    (mul_le_mul_of_nonneg_left (coreDirichlet_le q hq C u) (by positivity))

end Cheeger
end SKConstants
