module

public import CavityRealMomentHolder
public import CavityAttachedTree

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 theorem disorderExpect_bounded_test_three_holder {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (T : ClockTree S as)
    (P F G H : T.Assignment → ℝ) {C p : ℝ} (hC : 0 ≤ C)
    (hP : ∀ σ, |P σ| ≤ C) (hp : 2 < p) :
    |T.disorderExpect w φ v q (fun σ => P σ*(F σ*G σ*H σ)) x| ≤
      C*(T.disorderExpect w φ v q (fun σ => |F σ|^p) x)^(1/p)*
        (T.disorderExpect w φ v q (fun σ => |G σ|^p) x)^(1/p)*
        (T.disorderExpect w φ v q (fun σ => |H σ|^(p/(p-2))) x)^((p-2)/p) := by
  let z := fun σ => T.disorderWeight w φ v q σ x
  have hz := (T.disorderWeight_probability hw φ ho v q x).1
  have HH := finite_weighted_three_holder z F G H hz hp
  have HC : |T.disorderExpect w φ v q (fun σ => P σ*(F σ*G σ*H σ)) x| ≤
      C*(∑ σ, z σ*|F σ*G σ*H σ|) := by
    unfold disorderExpect
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    simp only [abs_mul,abs_of_nonneg (hz σ)]
    have H' := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hP σ) (abs_nonneg (F σ*G σ*H σ))) (hz σ)
    simpa only [z,abs_mul,mul_assoc,mul_left_comm,mul_comm] using H'
  exact HC.trans (by simpa only [disorderExpect,z,mul_assoc] using mul_le_mul_of_nonneg_left HH hC)

 theorem disorderExpect_abs_rpow_le_square_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (T : ClockTree S as)
    (E : T.Assignment → ℝ) {B p : ℝ} (hB : 0 ≤ B) (hp : 2 ≤ p)
    (hE : ∀ σ, |E σ| ≤ B) :
    T.disorderExpect w φ v q (fun σ => |E σ|^p) x ≤
      B^(p-2)*T.disorderExpect w φ v q (fun σ => (E σ)^2) x := by
  have hpm : 0 ≤ p-2 := by linarith
  have hpoint (σ : T.Assignment) : |E σ|^p ≤ B^(p-2)*(E σ)^2 := by
    have hr := Real.rpow_le_rpow (abs_nonneg (E σ)) (hE σ) hpm
    have H := mul_le_mul_of_nonneg_right hr (sq_nonneg (E σ))
    have he : |E σ|^p = |E σ|^(p-2)*(E σ)^2 := by
      calc
        _ = |E σ|^((p-2)+2) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add_of_nonneg (abs_nonneg _) hpm (by norm_num),Real.rpow_two,sq_abs]
    rw [he]
    exact H
  unfold disorderExpect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have H := mul_le_mul_of_nonneg_left (hpoint σ)
    ((T.disorderWeight_probability hw φ ho v q x).1 σ)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using H

 theorem disorderExpect_pair_product_rpow_scales {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (T : ClockTree S as)
    {a : ℕ} (ha : 0 < a) (E : Fin a → S → S → ℝ) (s t : Fin a → T.Slot)
    (hst : ∀ i, s i ≠ t i) (rho : Fin a → ℝ) (hrho : ∀ i, 0 < rho i)
    {p : ℝ} (hp : 0 < p)
    (hmoment : ∀ i, (pairClock as (T.splitIndex (s i) (t i))).disorderExpect w φ v q
      (fun σ => |E i (pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (pairSpin as (T.splitIndex (s i) (t i)) σ).2|^(p*(a:ℝ))) x ≤ (rho i)^(p*(a:ℝ))) :
    T.disorderExpect w φ v q
      (fun σ => |∏ i, E i (T.atSlot σ (s i)) (T.atSlot σ (t i))|^p) x ≤ (∏ i, rho i)^p := by
  let F := fun i σ => |E i (T.atSlot σ (s i)) (T.atSlot σ (t i))/rho i|^p
  have hnorm : ∀ i, T.disorderExpect w φ v q (fun σ => |F i σ|^a) x ≤ (1:ℝ)^a := by
    intro i
    have hpow (z : ℝ) : (|z/rho i|^p)^a = |z/rho i|^(p*(a:ℝ)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    have htest : (fun σ => |F i σ|^a) =
        (fun σ => |E i (T.atSlot σ (s i)) (T.atSlot σ (t i))/rho i|^(p*(a:ℝ))) := by
      funext σ
      dsimp only [F]
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact hpow _
    rw [htest]
    simp only [abs_div,abs_of_pos (hrho i)]
    simp only [Real.div_rpow (abs_nonneg _) (hrho i).le,disorderExpect,←mul_div_assoc,←Finset.sum_div,one_pow]
    apply (div_le_one (Real.rpow_pos_of_pos (hrho i) _)).2
    have Hmi := hmoment i
    rw [←T.disorderExpect_pairAtSlot_actual hw φ ho v q x (s i) (t i) (hst i)
      (fun σ τ => |E i σ τ|^(p*(a:ℝ)))] at Hmi
    exact Hmi
  have H := T.disorderExpect_product_abs_le hw φ ho v q ha (fun _ => 1) F
    (by norm_num : (0:ℝ) ≤ 1) (by intro σ; norm_num) x hnorm
  simp only [one_pow,one_mul] at H
  let R := ∏ i, rho i
  have hR : 0 < R := Finset.prod_pos fun i _ => hrho i
  have He : T.disorderExpect w φ v q (fun σ => ∏ i, F i σ) x =
      T.disorderExpect w φ v q
        (fun σ => |∏ i, E i (T.atSlot σ (s i)) (T.atSlot σ (t i))|^p) x / R^p := by
    unfold disorderExpect
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [F]
    rw [Real.finsetProd_rpow Finset.univ _ (fun i _ => abs_nonneg _) p,←Finset.abs_prod,
      Finset.prod_div_distrib,show (∏ i, rho i)=R from rfl,abs_div,abs_of_pos hR,
      Real.div_rpow (abs_nonneg _) hR.le]
    ring
  rw [He] at H
  have HH := (le_abs_self _).trans H
  exact (div_le_one (Real.rpow_pos_of_pos hR _)).mp HH

end OAI.SKFluctuations.Hierarchy.ClockTree
