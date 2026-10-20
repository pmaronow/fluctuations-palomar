module

public import ComparisonSignedCavityWholeLawTwoErrorPairs

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
 theorem disorderExpect_mixedError_wholeLaw_product_budget {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (T : ClockTree S as)
    (P : T.Assignment → ℝ) {C p M1 M2 D1 D2 : ℝ} (hC : 0 ≤ C) (hp : 2 < p)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^(2*(p/(p-2)))) x ≤ C^(2*(p/(p-2))))
    (A B : S → S → ℝ) (u1 z1 u2 z2 : T.Slot) (hne1 : u1 ≠ z1) (hne2 : u2 ≠ z2)
    (hA : ∀ σ τ, |A σ τ| ≤ M1) (hB : ∀ σ τ, |B σ τ| ≤ M2)
    (hsecond1 : (pairClock as (T.splitIndex u1 z1)).disorderExpect w φ v q
      (fun σ => (A (pairSpin as (T.splitIndex u1 z1) σ).1 (pairSpin as (T.splitIndex u1 z1) σ).2)^2) x ≤ D1^2)
    (hsecond2 : (pairClock as (T.splitIndex u2 z2)).disorderExpect w φ v q
      (fun σ => (B (pairSpin as (T.splitIndex u2 z2) σ).1 (pairSpin as (T.splitIndex u2 z2) σ).2)^2) x ≤ D2^2)
    {a : ℕ} (E : Fin a → S → S → ℝ) (s t : Fin a → T.Slot) (hst : ∀ i, s i ≠ t i)
    (rho : Fin a → ℝ) (hrho : ∀ i, 0 < rho i)
    (hmoment : ∀ i, (pairClock as (T.splitIndex (s i) (t i))).disorderExpect w φ v q
      (fun σ => |E i (pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (pairSpin as (T.splitIndex (s i) (t i)) σ).2|^((2*(p/(p-2)))*(a:ℝ))) x
        ≤ (rho i)^((2*(p/(p-2)))*(a:ℝ))) :
    |T.disorderExpect w φ v q (fun σ => P σ*
      (A (T.atSlot σ u1) (T.atSlot σ z1)*B (T.atSlot σ u2) (T.atSlot σ z2)*
        (∏ i, E i (T.atSlot σ (s i)) (T.atSlot σ (t i))))) x| ≤
      C*(∏ i, rho i)*M1^((p-2)/p)*M2^((p-2)/p)*
        (D1^(2/p)*D2^(2/p)) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hpi : 0 ≤ 1/p := by positivity
  have hqi : 0 ≤ (p-2)/p := by positivity
  let F := fun σ => A (T.atSlot σ u1) (T.atSlot σ z1)
  let G := fun σ => B (T.atSlot σ u2) (T.atSlot σ z2)
  let L := fun σ => ∏ i, E i (T.atSlot σ (s i)) (T.atSlot σ (t i))
  let H := fun σ=>P σ*L σ
  let R := ∏ i, rho i
  have hR : 0 < R := Finset.prod_pos fun i _ => hrho i
  have hF2 : T.disorderExpect w φ v q (fun σ => (F σ)^2) x ≤ D1^2 := by
    dsimp only [F]
    rw [T.disorderExpect_pairAtSlot_actual hw φ ho v q x u1 z1 hne1 (fun σ τ => (A σ τ)^2)]
    exact hsecond1
  have hG2 : T.disorderExpect w φ v q (fun σ => (G σ)^2) x ≤ D2^2 := by
    dsimp only [G]
    rw [T.disorderExpect_pairAtSlot_actual hw φ ho v q x u2 z2 hne2 (fun σ τ => (B σ τ)^2)]
    exact hsecond2
  have hFp : T.disorderExpect w φ v q (fun σ => |F σ|^p) x ≤ M1^(p-2)*D1^2 :=
    (T.disorderExpect_abs_rpow_le_square_actual hw φ ho v q x F hM1 hp.le (fun σ => hA _ _)).trans
      (mul_le_mul_of_nonneg_left hF2 (Real.rpow_nonneg hM1 _))
  have hGp : T.disorderExpect w φ v q (fun σ => |G σ|^p) x ≤ M2^(p-2)*D2^2 :=
    (T.disorderExpect_abs_rpow_le_square_actual hw φ ho v q x G hM2 hp.le (fun σ => hB _ _)).trans
      (mul_le_mul_of_nonneg_left hG2 (Real.rpow_nonneg hM2 _))
  have hLq : T.disorderExpect w φ v q (fun σ => |L σ|^(2*(p/(p-2)))) x ≤ R^(2*(p/(p-2))) := by
    by_cases ha : a=0
    · subst a
      simp only [L,R,Fin.prod_univ_zero,abs_one,Real.one_rpow,T.disorderExpect_one hw φ ho]
      norm_num
    · exact T.disorderExpect_pair_product_rpow_scales hw φ ho v q x (Nat.pos_of_ne_zero ha)
        E s t hst rho hrho (by positivity) hmoment
  have hHq : T.disorderExpect w φ v q (fun σ=>|H σ|^(p/(p-2))) x ≤ (C*R)^(p/(p-2)) :=
    T.disorderExpect_product_wholeLaw_rpow_le hw φ ho v q x P L hC hR.le hP hLq
  have hFnon : 0 ≤ T.disorderExpect w φ v q (fun σ => |F σ|^p) x := by
    unfold disorderExpect
    exact Finset.sum_nonneg fun σ _ => mul_nonneg
      ((T.disorderWeight_probability hw φ ho v q x).1 σ) (Real.rpow_nonneg (abs_nonneg _) _)
  have hGnon : 0 ≤ T.disorderExpect w φ v q (fun σ => |G σ|^p) x := by
    unfold disorderExpect
    exact Finset.sum_nonneg fun σ _ => mul_nonneg
      ((T.disorderWeight_probability hw φ ho v q x).1 σ) (Real.rpow_nonneg (abs_nonneg _) _)
  have hHnon : 0 ≤ T.disorderExpect w φ v q (fun σ => |H σ|^(p/(p-2))) x := by
    unfold disorderExpect
    exact Finset.sum_nonneg fun σ _ => mul_nonneg
      ((T.disorderWeight_probability hw φ ho v q x).1 σ) (Real.rpow_nonneg (abs_nonneg _) _)
  have hFnorm := Real.rpow_le_rpow hFnon hFp hpi
  have hGnorm := Real.rpow_le_rpow hGnon hGp hpi
  have hHnorm := Real.rpow_le_rpow hHnon hHq hqi
  have hcancel : (p/(p-2))*((p-2)/p)=1 := by field_simp
  rw [←Real.rpow_mul (mul_nonneg hC hR.le),hcancel,Real.rpow_one] at hHnorm
  have hpow1 : (M1^(p-2)*D1^2)^(1/p) = M1^((p-2)/p)*D1^(2/p) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hM1 _) (sq_nonneg D1),
      ←Real.rpow_mul hM1,←Real.rpow_natCast D1 2,←Real.rpow_mul hD1]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  have hpow2 : (M2^(p-2)*D2^2)^(1/p) = M2^((p-2)/p)*D2^(2/p) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hM2 _) (sq_nonneg D2),
      ←Real.rpow_mul hM2,←Real.rpow_natCast D2 2,←Real.rpow_mul hD2]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  rw [hpow1] at hFnorm
  rw [hpow2] at hGnorm
  have Hmain := T.disorderExpect_bounded_test_three_holder hw φ ho v q x
    (fun _=>1) F G H (by norm_num : (0:ℝ) ≤ 1) (by intro _;norm_num) hp
  have HE : (fun σ=>(1:ℝ)*(F σ*G σ*H σ))=(fun σ=>P σ*(F σ*G σ*L σ)) := by
    funext σ
    dsimp only [H]
    ring
  rw [HE] at Hmain
  have Hnorm := mul_le_mul_of_nonneg_right
    (mul_le_mul hFnorm hGnorm (Real.rpow_nonneg hGnon _) (by positivity))
    (Real.rpow_nonneg hHnon ((p-2)/p))
  have HH := Hmain.trans (by
    simpa only [one_mul] using Hnorm.trans (mul_le_mul_of_nonneg_left hHnorm (by positivity)))
  simpa only [R,L,F,G,mul_assoc,mul_left_comm,mul_comm] using HH

end OAI.SKFluctuations.Hierarchy.ClockTree
