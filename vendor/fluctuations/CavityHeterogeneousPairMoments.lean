module

public import CavityOneErrorPairProducts

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 theorem disorderExpect_oneError_product_scales {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (T : ClockTree S as) {k : ℕ} (hk : 0 < k)
    (P : T.Assignment → ℝ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : ∀ σ, |P σ| ≤ C)
    (A : ℕ → S → S → ℝ) (u z : T.Slot) (hne : u ≠ z)
    (E : Fin k → ℕ → S → S → ℝ) (s t : Fin k → T.Slot) (hst : ∀ i, s i ≠ t i)
    (rho : Fin k → ℝ) (hrho : ∀ i, 0 < rho i)
    (hsecond : (pairClock as (T.splitIndex u z)).disorderExpect w φ v q
      (fun σ => (A (T.splitIndex u z) (pairSpin as (T.splitIndex u z) σ).1
        (pairSpin as (T.splitIndex u z) σ).2)^2) x ≤ D^2)
    (hmoment : ∀ i, (pairClock as (T.splitIndex (s i) (t i))).disorderExpect w φ v q
      (fun σ => |E i (T.splitIndex (s i) (t i))
        (pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (pairSpin as (T.splitIndex (s i) (t i)) σ).2|^(2*k)) x ≤ (rho i)^(2*k)) :
    |T.disorderExpect w φ v q (fun σ => P σ*
      A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
      (∏ i, E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i)))) x|
      ≤ C*D*(∏ i, rho i) := by
  let En := fun i j σ τ => E i j σ τ/rho i
  have hnorm : ∀ i, (pairClock as (T.splitIndex (s i) (t i))).disorderExpect w φ v q
      (fun σ => |En i (T.splitIndex (s i) (t i))
        (pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (pairSpin as (T.splitIndex (s i) (t i)) σ).2|^(2*k)) x ≤ (1:ℝ)^(2*k) := by
    intro i
    dsimp only [En]
    simp only [abs_div,abs_of_pos (hrho i),div_pow,disorderExpect,←mul_div_assoc,←Finset.sum_div,one_pow]
    apply (div_le_one (pow_pos (hrho i) _)).2
    exact hmoment i
  have H := T.disorderExpect_oneError_product_actual hw φ ho v q x hk P hC
    (by norm_num : (0:ℝ) ≤ 1) hD hP A u z hne En s t hst hsecond hnorm
  simp only [one_pow,mul_one] at H
  let R := ∏ i, rho i
  have hR : 0 < R := Finset.prod_pos fun i _ => hrho i
  have hEq : T.disorderExpect w φ v q (fun σ => P σ*
      A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
      (∏ i, E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i)))) x =
      R*T.disorderExpect w φ v q (fun σ => P σ*
      A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
      (∏ i, En i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i)))) x := by
    unfold disorderExpect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [En,Finset.prod_div_distrib]
    have hRdef : (∏ i, rho i)=R := rfl
    rw [hRdef]
    field_simp [hR.ne']
    <;> ring
  rw [hEq,abs_mul,abs_of_pos hR]
  have hh := mul_le_mul_of_nonneg_left H hR.le
  simpa only [R,mul_assoc,mul_left_comm,mul_comm] using hh

end OAI.SKFluctuations.Hierarchy.ClockTree
