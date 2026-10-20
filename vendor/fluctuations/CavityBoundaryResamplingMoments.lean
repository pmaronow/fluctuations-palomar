module

public import CavityBoundaryProducts

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem finite_weighted_product_square_scales {A : Type} [Fintype A] {a : ℕ}
    (ha : 0<a) (w : A → ℝ) (F : Fin a → A → ℝ) (hw : ∀ σ, 0≤w σ)
    (rho : Fin a → ℝ) (hrho : ∀ i, 0<rho i)
    (hm : ∀ i, (∑ σ, w σ*|F i σ|^(2*a)) ≤ (rho i)^(2*a)) :
    (∑ σ, w σ*(∏ i, F i σ)^2) ≤ (∏ i, rho i)^2 := by
  have hm' (i : Fin a) : (∑ σ, w σ*|(F i σ)^2|^a) ≤ ((rho i)^2)^a := by
    simpa only [abs_pow,←pow_mul] using hm i
  have H := finite_weighted_product_scales ha w (fun i σ => (F i σ)^2) hw
    (fun i => (rho i)^2) (fun i => sq_pos_of_pos (hrho i)) hm'
  simp only [Finset.prod_pow] at H ⊢
  exact (le_abs_self _).trans H

theorem finite_weighted_resampled_product_square {A : Type} [Fintype A] {a : ℕ}
    (ha : 0<a) (w : A → ℝ) (f g : Fin a → A → ℝ) (hw : ∀ σ, 0≤w σ)
    (rho : Fin a → ℝ) (hrho : ∀ i, 0<rho i) {xi : ℝ} (hxi : 0<xi)
    (hf : ∀ i, (∑ σ, w σ*|f i σ|^(2*a)) ≤ (rho i)^(2*a))
    (hg : ∀ i, (∑ σ, w σ*|g i σ|^(2*a)) ≤ (rho i)^(2*a))
    (hd : ∀ i, (∑ σ, w σ*|f i σ-g i σ|^(2*a)) ≤ (xi*rho i)^(2*a)) :
    (∑ σ, w σ*((∏ i, f i σ)-(∏ i, g i σ))^2) ≤
      ((a:ℝ)*xi*(∏ i, rho i))^2 := by
  let F : Fin a → Fin a → A → ℝ := fun i j σ =>
    boundaryTelescopingFactor (fun t => f t σ) (fun t => g t σ) i j
  let r : Fin a → Fin a → ℝ := fun i j => if j = i then xi*rho j else rho j
  have hr (i j : Fin a) : 0<r i j := by
    dsimp [r]
    have hj := hrho j
    split_ifs <;> positivity
  have hm (i j : Fin a) : (∑ σ, w σ*|F i j σ|^(2*a)) ≤ (r i j)^(2*a) := by
    dsimp [F,r,boundaryTelescopingFactor]
    by_cases he : j = i
    · simp only [if_pos he]
      exact hd j
    · simp only [if_neg he]
      by_cases hl : j < i
      · simp only [if_pos hl]; exact hg j
      · simp only [if_neg hl]; exact hf j
  have hrprod (i : Fin a) : (∏ j, r i j)=xi*(∏ j, rho j) := by
    calc
      _ = (∏ j, (if j = i then xi else 1)*rho j) := by
        apply Finset.prod_congr rfl
        intro j _
        dsimp [r]
        split_ifs <;> simp
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hterm (i : Fin a) : (∑ σ, w σ*(∏ j, F i j σ)^2) ≤
      (xi*(∏ j, rho j))^2 := by
    have H := finite_weighted_product_square_scales ha w (F i) hw (r i) (hr i) (hm i)
    simpa only [hrprod] using H
  have hsum (σ : A) : ((∏ i, f i σ)-(∏ i, g i σ))^2 ≤
      (a:ℝ)*(∑ i, (∏ j, F i j σ)^2) := by
    rw [boundary_product_resampling_telescopes]
    have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin a => (1:ℝ)) (fun i => ∏ j, F i j σ)
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using H
  calc
    _ ≤ ∑ σ, w σ*((a:ℝ)*(∑ i, (∏ j, F i j σ)^2)) :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hsum σ) (hw σ)
    _ = (a:ℝ)*(∑ i, ∑ σ, w σ*(∏ j, F i j σ)^2) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ ≤ (a:ℝ)*(∑ _i : Fin a, (xi*(∏ j, rho j))^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem actual_boundary_polynomial_resampling_square (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (v : FeatureIndex n → ℝ) (q : ℕ → FeatureIndex n → ℝ) (x : FeatureIndex n → ℝ)
    {a : ℕ} (ha : 0<a) (h b : Fin a → ℝ) (i j k : Fin a → T.Slot)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e)
    (hlow : ∀ e, T.splitIndex (i e) (j e)=T.splitIndex (i e) (k e))
    (hgap : ∀ e, T.splitIndex (i e) (j e) < T.splitIndex (j e) (k e))
    (rho : Fin a → ℝ) (hrho : ∀ e, 0<rho e) {xi : ℝ} (hxi : 0<xi)
    (hraw : ∀ e, (ClockTree.pairClock as (T.splitIndex (i e) (j e))).disorderExpect
      (uniformWeight n) (finiteFeature n) v q
      (fun σ => |boundaryAffineFactor n (h e) (b e)
        (ClockTree.pairSpin as (T.splitIndex (i e) (j e)) σ).2
        (ClockTree.pairSpin as (T.splitIndex (i e) (j e)) σ).1|^(2*a)) x ≤ (rho e)^(2*a))
    (herror : ∀ e, (ClockTree.boundaryTripleClock (S := Spin n) as
      (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e))).disorderExpect
      (uniformWeight n) (finiteFeature n) v q
      (fun σ => let z := (ClockTree.boundaryTripleSpin as
        (T.splitIndex (i e) (j e)) (T.splitIndex (j e) (k e)) σ);
        |b e*(orderedOverlap n z.2.1 z.1-orderedOverlap n z.2.2 z.1)|^(2*a)) x ≤
      (xi*rho e)^(2*a)) :
    T.disorderExpect (uniformWeight n) (finiteFeature n) v q
      (fun σ => (boundaryAffineProduct n h b (fun e => T.atSlot σ (j e))
        (fun e => T.atSlot σ (i e))-
        boundaryAffineProduct n h b (fun e => T.atSlot σ (k e))
          (fun e => T.atSlot σ (i e)))^2) x ≤
      ((a:ℝ)*xi*(∏ e, rho e))^2 := by
  let w := fun σ => T.disorderWeight (uniformWeight n) (finiteFeature n) v q σ x
  let f := fun e σ => boundaryAffineFactor n (h e) (b e)
    (T.atSlot σ (j e)) (T.atSlot σ (i e))
  let g := fun e σ => boundaryAffineFactor n (h e) (b e)
    (T.atSlot σ (k e)) (T.atSlot σ (i e))
  apply finite_weighted_resampled_product_square ha w f g
    (T.disorderWeight_probability (uniformWeight_pos n) (finiteFeature n) ho v q x).1 rho hrho hxi
  · intro e
    change T.disorderExpect (uniformWeight n) (finiteFeature n) v q
      (fun σ => |f e σ|^(2*a)) x ≤ _
    rw [T.disorderExpect_pairAtSlot_actual (uniformWeight_pos n) (finiteFeature n)
      ho v q x (i e) (j e) (hij e) (fun d c => |boundaryAffineFactor n (h e) (b e) c d|^(2*a))]
    exact hraw e
  · intro e
    change T.disorderExpect (uniformWeight n) (finiteFeature n) v q
      (fun σ => |g e σ|^(2*a)) x ≤ _
    rw [T.disorderExpect_pairAtSlot_actual (uniformWeight_pos n) (finiteFeature n)
      ho v q x (i e) (k e) (hik e) (fun d c => |boundaryAffineFactor n (h e) (b e) c d|^(2*a)),←hlow e]
    exact hraw e
  · intro e
    change T.disorderExpect (uniformWeight n) (finiteFeature n) v q
      (fun σ => |f e σ-g e σ|^(2*a)) x ≤ _
    have he : (fun σ => |f e σ-g e σ|^(2*a)) =
        fun σ => |b e*(orderedOverlap n (T.atSlot σ (j e)) (T.atSlot σ (i e))-
          orderedOverlap n (T.atSlot σ (k e)) (T.atSlot σ (i e)))|^(2*a) := by
      funext σ
      congr 2
      dsimp [f,g,boundaryAffineFactor]
      ring
    rw [he,T.disorderExpect_boundary_threeAtSlot (uniformWeight_pos n) (finiteFeature n)
      ho v q x (i e) (j e) (k e) (hjk e) (hlow e) (hgap e)
        (fun d c f => |b e*(orderedOverlap n c d-orderedOverlap n f d)|^(2*a))]
    exact herror e

end OAI.SKFluctuations.Cavity
