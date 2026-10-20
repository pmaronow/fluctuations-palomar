module

public import CavityProfilePairMoments
public import CavityOffDiagonalErrorBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 theorem disorderExpect_oneError_product_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (T : ClockTree S as) {k : ℕ} (hk : 0 < k)
    (P : T.Assignment → ℝ) {C rho D : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho) (hD : 0 ≤ D)
    (hP : ∀ σ, |P σ| ≤ C)
    (A : ℕ → S → S → ℝ) (u z : T.Slot) (hne : u ≠ z)
    (E : Fin k → ℕ → S → S → ℝ) (s t : Fin k → T.Slot) (hst : ∀ i, s i ≠ t i)
    (hsecond : (pairClock as (T.splitIndex u z)).disorderExpect w φ v q
      (fun σ => (A (T.splitIndex u z) (pairSpin as (T.splitIndex u z) σ).1
        (pairSpin as (T.splitIndex u z) σ).2)^2) x ≤ D^2)
    (hmoment : ∀ i, (pairClock as (T.splitIndex (s i) (t i))).disorderExpect w φ v q
      (fun σ => |E i (T.splitIndex (s i) (t i))
        (pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (pairSpin as (T.splitIndex (s i) (t i)) σ).2|^(2*k)) x ≤ rho^(2*k)) :
    |T.disorderExpect w φ v q (fun σ => P σ*
      A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*
      (∏ i, E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i)))) x|
      ≤ C*D*rho^k := by
  let L := fun σ => ∏ i, E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i))
  let R := fun σ => A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)
  have hR : T.disorderExpect w φ v q (fun σ => (R σ)^2) x ≤ D^2 := by
    simp only [R]
    rw [T.disorderExpect_pairAtSlot_actual hw φ ho v q x u z hne
      (fun a b => (A (T.splitIndex u z) a b)^2)]
    exact hsecond
  have hL : T.disorderExpect w φ v q (fun σ => (L σ)^2) x ≤ rho^(2*k) := by
    have H := T.disorderExpect_pair_product_actual hw φ ho v q x hk s t hst
      (fun _ => 1) (fun i a b => (E i (T.splitIndex (s i) (t i)) a b)^2)
      (by norm_num : (0:ℝ) ≤ 1) (by intro σ; norm_num)
      (rho := rho^2) (fun i => by
        simpa only [abs_pow,←pow_mul] using hmoment i)
    have HL : |T.disorderExpect w φ v q (fun σ => (L σ)^2) x| ≤ rho^(2*k) := by
      simpa only [one_mul,Finset.prod_pow,L,←pow_mul] using H
    exact (le_abs_self _).trans HL
  have hPR : T.disorderExpect w φ v q (fun σ => (P σ*R σ)^2) x ≤ C^2*D^2 := by
    have H : T.disorderExpect w φ v q (fun σ => (P σ*R σ)^2) x ≤
        C^2*T.disorderExpect w φ v q (fun σ => (R σ)^2) x := by
      unfold disorderExpect
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro σ _
      have hPsq : (P σ)^2 ≤ C^2 := by nlinarith [sq_abs (P σ),hP σ,abs_nonneg (P σ)]
      have hh := mul_le_mul_of_nonneg_right hPsq (sq_nonneg (R σ))
      have hh' := mul_le_mul_of_nonneg_left hh
        ((T.disorderWeight_probability hw φ ho v q x).1 σ)
      simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hh'
    exact H.trans (mul_le_mul_of_nonneg_left hR (sq_nonneg C))
  have hn : 0 ≤ T.disorderExpect w φ v q (fun σ => (L σ)^2) x := by
    unfold disorderExpect
    exact Finset.sum_nonneg fun σ _ => mul_nonneg
      ((T.disorderWeight_probability hw φ ho v q x).1 σ) (sq_nonneg _)
  have HC := T.disorderExpect_mul_sq_le hw φ ho v q (fun σ => P σ*R σ) L x
  have Hsq : (T.disorderExpect w φ v q (fun σ => P σ*R σ*L σ) x)^2 ≤
      (C*D*rho^k)^2 := by
    calc
      _ ≤ T.disorderExpect w φ v q (fun σ => (P σ*R σ)^2) x*
        T.disorderExpect w φ v q (fun σ => (L σ)^2) x := HC
      _ ≤ (C^2*D^2)*T.disorderExpect w φ v q (fun σ => (L σ)^2) x :=
        mul_le_mul_of_nonneg_right hPR hn
      _ ≤ (C^2*D^2)*rho^(2*k) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := by rw [mul_pow,mul_pow,←pow_mul]; ring
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C*D*rho^k)).mp
  simpa only [sq_abs,R,L] using Hsq

end OAI.SKFluctuations.Hierarchy.ClockTree
