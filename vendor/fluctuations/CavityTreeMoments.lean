module

public import CavityMomentAllocation
public import CavityPhysicalJetBounds

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy

theorem product_abs_le_average_powers {k : ℕ} (hk : 0 < k) (f : Fin k → ℝ) :
    (∏ i, |f i|) ≤ (∑ i, |f i|^k)/(k:ℝ) := by
  have hk0 : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have H := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin k => (k:ℝ)⁻¹) (fun i => |f i|^k)
    (fun _ _ => inv_nonneg.mpr hk0.le)
    (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];
        exact mul_inv_cancel₀ hk0.ne') (fun _ _ => pow_nonneg (abs_nonneg _) _)
  have he (i : Fin k) : (|f i|^k)^((k:ℝ)⁻¹) = |f i| := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),mul_inv_cancel₀ hk0.ne',Real.rpow_one]
  simp only [he] at H
  calc
    _ ≤ ∑ i, (k:ℝ)⁻¹ * |f i|^k := H
    _ = (∑ i, |f i|^k)/(k:ℝ) := by
      rw [← Finset.mul_sum, div_eq_mul_inv]
      ring

theorem finite_weighted_product_abs_le {A : Type*} [Fintype A] {k : ℕ}
    (hk : 0 < k) (w P : A → ℝ) (F : Fin k → A → ℝ)
    (hw : ∀ a, 0 ≤ w a) {C rho : ℝ} (hC : 0 ≤ C) (hP : ∀ a, |P a| ≤ C)
    (hmoment : ∀ i, (∑ a, w a*|F i a|^k) ≤ rho^k) :
    |∑ a, w a*P a*(∏ i, F i a)| ≤ C*rho^k := by
  have hk0 : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have H : (∑ a, w a*(∏ i, |F i a|)) ≤ rho^k := by
    calc
      _ ≤ ∑ a, w a*((∑ i, |F i a|^k)/(k:ℝ)) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
          (product_abs_le_average_powers hk (fun i => F i a)) (hw a))
      _ = (∑ i : Fin k, ∑ a, w a*|F i a|^k)/(k:ℝ) := by
        simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ (∑ _i : Fin k, rho^k)/(k:ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hmoment i)) hk0.le
      _ = rho^k := by simp [hk0.ne']
  calc
    _ ≤ ∑ a, |w a*P a*(∏ i, F i a)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w a * |P a| * (∏ i, |F i a|) := by
      simp only [abs_mul,abs_of_nonneg (hw _),Finset.abs_prod]
    _ ≤ ∑ a, w a*C*(∏ i, |F i a|) := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hP a) (hw a))
        (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    _ = C*(∑ a, w a*(∏ i, |F i a|)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ C*rho^k := mul_le_mul_of_nonneg_left H hC

variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S]

theorem ClockTree.disorderExpect_product_abs_le {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    {k : ℕ} (hk : 0 < k) (P : T.Assignment → ℝ) (F : Fin k → T.Assignment → ℝ)
    {C rho : ℝ} (hC : 0 ≤ C) (hP : ∀ σ, |P σ| ≤ C)
    (x : ι → ℝ)
    (hmoment : ∀ i, T.disorderExpect w φ v q (fun σ => |F i σ|^k) x ≤ rho^k) :
    |T.disorderExpect w φ v q (fun σ => P σ*(∏ i, F i σ)) x| ≤ C*rho^k := by
  simpa only [ClockTree.disorderExpect,mul_assoc] using finite_weighted_product_abs_le hk
    (fun σ => T.disorderWeight w φ v q σ x) P F
    (T.disorderWeight_probability hw φ ho v q x).1 hC hP hmoment

end OAI.SKFluctuations.Hierarchy
