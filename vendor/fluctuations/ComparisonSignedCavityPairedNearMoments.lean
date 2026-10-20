module

public import ComparisonSignedCavityRetainedPairedHighBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem finite_weighted_difference_fourth_le {Ω : Type} [Fintype Ω]
    (w f g : Ω → ℝ) (hw : ∀σ,0 ≤ w σ) {A : ℝ}
    (hf : (∑σ,w σ*|f σ|^4) ≤ A^4) (hg : (∑σ,w σ*|g σ|^4) ≤ A^4) :
    (∑σ,w σ*|f σ-g σ|^4) ≤ (2*A)^4 := by
  have Hpoint σ : |f σ-g σ|^4 ≤ 8*(|f σ|^4+|g σ|^4) := by
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) 4).trans
    convert add_pow_le (abs_nonneg (f σ)) (abs_nonneg (g σ)) 4 using 1
    norm_num
  have H:=Finset.sum_le_sum fun σ (_ : σ∈Finset.univ)=>
    mul_le_mul_of_nonneg_left (Hpoint σ) (hw σ)
  have HE : (∑σ,w σ*(8*(|f σ|^4+|g σ|^4)))=
      8*((∑σ,w σ*|f σ|^4)+(∑σ,w σ*|g σ|^4)) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [HE] at H
  nlinarith only [H,hf,hg]

theorem finite_weighted_two_differences_square {Ω : Type} [Fintype Ω]
    (w f g p q : Ω → ℝ) (hw : ∀σ,0 ≤ w σ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hf : (∑σ,w σ*|f σ|^4) ≤ A^4) (hg : (∑σ,w σ*|g σ|^4) ≤ A^4)
    (hp : (∑σ,w σ*|p σ|^4) ≤ B^4) (hq : (∑σ,w σ*|q σ|^4) ≤ B^4) :
    (∑σ,w σ*((f σ-g σ)*(p σ-q σ))^2) ≤ (4*A*B)^2 := by
  have HD:=finite_weighted_difference_fourth_le w f g hw hf hg
  have HP:=finite_weighted_difference_fourth_le w p q hw hp hq
  have H:=finite_weighted_product_square_scales (by norm_num : 0<2) w
    ![fun σ=>f σ-g σ,fun σ=>p σ-q σ] hw ![2*A,2*B]
    (by
      intro i
      fin_cases i
      · change 0 < 2*A
        positivity
      · change 0 < 2*B
        positivity)
    (by intro i; fin_cases i; exact HD; exact HP)
  simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    show 2*A*(2*B)=4*A*B by ring] using H

theorem native_rest_two_differences_square (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (law : ℕ → RestCoordinate n → ℝ) (F G P Q : T.cavityLeft.Assignment → ℝ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hF : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 law (fun σ=>|F σ|^4) 0 ≤ A^4)
    (hG : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 law (fun σ=>|G σ|^4) 0 ≤ A^4)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 law (fun σ=>|P σ|^4) 0 ≤ B^4)
    (hQ : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 law (fun σ=>|Q σ|^4) 0 ≤ B^4) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 law
      (fun σ=>((F σ-G σ)*(P σ-Q σ))^2) 0 ≤ (4*A*B)^2 := by
  exact finite_weighted_two_differences_square
    (fun σ=>T.cavityLeft.disorderWeight (restWeight n) (restFeature n) 0 law σ 0)
    F G P Q (T.cavityLeft.disorderWeight_probability (restWeight_pos n) (restFeature n) ho 0 law 0).1
    hA hB hF hG hP hQ

end OAI.SKFluctuations.Cavity
