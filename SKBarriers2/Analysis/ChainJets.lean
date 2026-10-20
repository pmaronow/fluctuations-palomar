module

public import SKBarriers2.Analysis.StepStability
public import SKBarriers2.Corner.Evenness

@[expose] public section

noncomputable section
open Set OAI.SK.Analytic
open scoped BigOperators

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def chainEnergy (l : List (ℝ × E)) : ℝ := (l.map fun p => ‖p.2‖ ^ 2).sum

theorem chainEnergy_nonneg (l : List (ℝ × E)) : 0 ≤ chainEnergy l := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  exact sq_nonneg _

theorem chainEnergy_cons (p : ℝ × E) (l : List (ℝ × E)) :
    chainEnergy (p :: l) = ‖p.2‖ ^ 2 + chainEnergy l := by rfl

theorem chainEnergy_append (l t : List (ℝ × E)) :
    chainEnergy (l ++ t) = chainEnergy l + chainEnergy t := by
  simp only [chainEnergy, List.map_append, List.sum_append]

theorem qPotential_chain (l : List (ℝ × E)) {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r)
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1)
    (hbudget : (stepStabilityCoefficient r (B + 1) + 1) * chainEnergy l ≤ 1)
    (hcurv : (B + 1) * chainEnergy l ≤ 1 / 2) :
    QPotential r (B + stepStabilityCoefficient r (B + 1) * chainEnergy l)
      (vectorIncrementChain l f) := by
  have hB : 0 ≤ B := hf.nonneg
  have hBp : 0 ≤ B + 1 := by positivity
  have hK : 0 ≤ stepStabilityCoefficient r (B + 1) := stepStabilityCoefficient_nonneg r hBp
  induction l with
  | nil => simpa only [chainEnergy, List.map_nil, List.sum_nil, mul_zero, add_zero, vectorIncrementChain] using hf
  | cons p l ih =>
    have hE : 0 ≤ chainEnergy l := chainEnergy_nonneg l
    have hEt : chainEnergy l ≤ chainEnergy (p :: l) := by rw [chainEnergy_cons]; exact le_add_of_nonneg_left (sq_nonneg _)
    have hhead : ‖p.2‖ ^ 2 ≤ chainEnergy (p :: l) := by rw [chainEnergy_cons]; exact le_add_of_nonneg_right hE
    have hTailBudget : (stepStabilityCoefficient r (B + 1) + 1) * chainEnergy l ≤ 1 :=
      (mul_le_mul_of_nonneg_left hEt (by positivity)).trans hbudget
    have hTailCurv : (B + 1) * chainEnergy l ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hEt hBp).trans hcurv
    have hinner := ih (fun q hq => hm q (List.mem_cons_of_mem p hq)) hTailBudget hTailCurv
    have hBound : B + stepStabilityCoefficient r (B + 1) * chainEnergy l ≤ B + 1 := by
      nlinarith
    have hSmall : p.1 * ((B + stepStabilityCoefficient r (B + 1) * chainEnergy l) * ‖p.2‖ ^ 2) ≤ 1 / 2 := by
      calc
        _ ≤ (B + stepStabilityCoefficient r (B + 1) * chainEnergy l) * ‖p.2‖ ^ 2 :=
          mul_le_of_le_one_left (by positivity) (hm p (List.mem_cons_self ..)).2
        _ ≤ (B + 1) * ‖p.2‖ ^ 2 := mul_le_mul_of_nonneg_right hBound (sq_nonneg _)
        _ ≤ (B + 1) * chainEnergy (p :: l) := mul_le_mul_of_nonneg_left hhead hBp
        _ ≤ 1 / 2 := hcurv
    have hStep := qPotential_step hinner hr (hm p (List.mem_cons_self ..)) p.2 hSmall
    apply hStep.mono
    have hCoeff := stepStabilityCoefficient_mono r hinner.nonneg hBound
    rw [chainEnergy_cons]
    nlinarith [mul_le_mul_of_nonneg_right hCoeff (sq_nonneg ‖p.2‖)]

theorem qPotential_chain_uniform (l : List (ℝ × E)) {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r)
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1)
    (hbudget : (stepStabilityCoefficient r (B + 1) + 1) * chainEnergy l ≤ 1)
    (hcurv : (B + 1) * chainEnergy l ≤ 1 / 2) :
    QPotential r (B + 1) (vectorIncrementChain l f) := by
  have hK : 0 ≤ stepStabilityCoefficient r (B + 1) := stepStabilityCoefficient_nonneg r (by linarith [hf.nonneg])
  apply (qPotential_chain l hf hr hm hbudget hcurv).mono
  have hE := chainEnergy_nonneg l
  nlinarith

theorem qPotential_chain_tail (front tail : List (ℝ × E)) {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r)
    (hm : ∀ p ∈ front ++ tail, p.1 ∈ Icc (0 : ℝ) 1)
    (hbudget : (stepStabilityCoefficient r (B + 1) + 1) * chainEnergy (front ++ tail) ≤ 1)
    (hcurv : (B + 1) * chainEnergy (front ++ tail) ≤ 1 / 2) :
    QPotential r (B + 1) (vectorIncrementChain tail f) := by
  have hB : 0 ≤ B := hf.nonneg
  have hK := stepStabilityCoefficient_nonneg r (by linarith : 0 ≤ B + 1)
  have hE : chainEnergy tail ≤ chainEnergy (front ++ tail) := by
    rw [chainEnergy_append]
    exact le_add_of_nonneg_left (chainEnergy_nonneg front)
  apply qPotential_chain_uniform tail hf hr
    (fun p hp => hm p (List.mem_append_right front hp))
  · exact (mul_le_mul_of_nonneg_left hE (by positivity)).trans hbudget
  · exact (mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ B + 1)).trans hcurv

private theorem norm_sq_le_coordinate_square (v : E) : ‖v‖ ^ 2 ≤ ∑ i, (v i) ^ 2 := by
  have hsum : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hnorm : ‖v‖ ≤ Real.sqrt (∑ i, (v i) ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt hsum]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have h := (sq_le_sq₀ (norm_nonneg v) (Real.sqrt_nonneg _)).mpr hnorm
  simpa only [Real.sq_sqrt hsum] using h

theorem chainEnergy_le_covariance_trace (l : List (ℝ × E)) :
    chainEnergy l ≤ ∑ i, matrixChainCovariance l i i := by
  induction l with
  | nil => simp [chainEnergy]
  | cons p l ih =>
    rw [chainEnergy_cons]
    simp only [matrixChainCovariance_cons, Pi.add_apply, rankOneMatrix, ← pow_two, Finset.sum_add_distrib]
    exact add_le_add (norm_sq_le_coordinate_square p.2) ih

theorem chainEnergy_scale (β : ℝ) (l : List (ℝ × E)) :
    chainEnergy (l.map fun p => (p.1, β • p.2)) = β ^ 2 * chainEnergy l := by
  induction l with
  | nil => simp [chainEnergy]
  | cons p l ih =>
    simp only [List.map_cons, chainEnergy_cons, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ih]
    ring

theorem window_chainEnergy_le (β : ℝ) (α : ℝ → ℝ) (s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    chainEnergy ((OW.window α (1 / 2) s h k N).map fun p => (p.1, β • p.2)) ≤ 12 * β ^ 2 * h := by
  have hCov := OW.window_full_covariance α (1 / 2) s h k hN hh (by norm_num)
    (OW.repairLength_mem (by norm_num) hk)
  have hdiag (i : Fin 3) : matrixChainCovariance (OW.window α (1 / 2) s h k N) i i = 4 * h := by
    have hi := congrArg (fun Q => Q i i) hCov
    fin_cases i <;> simp [tripleGram] at hi ⊢ <;> linarith
  have htrace : (∑ i, matrixChainCovariance (OW.window α (1 / 2) s h k N) i i) = 12 * h := by
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [chainEnergy_scale]
  calc
    β ^ 2 * chainEnergy (OW.window α (1 / 2) s h k N) ≤ β ^ 2 * (12 * h) :=
      mul_le_mul_of_nonneg_left ((chainEnergy_le_covariance_trace _).trans_eq htrace) (sq_nonneg β)
    _ = _ := by ring

private theorem interpolatedProfile_mem (α : ℝ → ℝ) (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1)
    {a lam : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hlam : lam ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    Corner.interpolatedProfile α a lam t ∈ Icc (0 : ℝ) 1 := by
  have hl : 0 ≤ 1 - lam := by linarith [hlam.2]
  have h₁ := mul_nonneg hl ha.1
  have h₂ := mul_nonneg hlam.1 (hα t).1
  have h₃ := mul_le_mul_of_nonneg_left ha.2 hl
  have h₄ := mul_le_mul_of_nonneg_left (hα t).2 hlam.1
  dsimp only [Corner.interpolatedProfile]
  constructor <;> nlinarith

def windowJetRadius (r : ℕ) (B β : ℝ) : ℝ :=
  min (12 * β ^ 2 * (stepStabilityCoefficient r (B + 1) + 1) + 1)⁻¹
    (24 * β ^ 2 * (B + 1) + 1)⁻¹

theorem windowJetRadius_pos (r : ℕ) {B : ℝ} (hB : 0 ≤ B) (β : ℝ) :
    0 < windowJetRadius r B β := by
  have hK := stepStabilityCoefficient_nonneg r (by linarith : 0 ≤ B + 1)
  apply lt_min (inv_pos.mpr (by positivity)) (inv_pos.mpr (by positivity))

theorem qPotential_interpolated_window (β : ℝ) (α : ℝ → ℝ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) {a lam : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (s h k : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h)
    (hh0 : h ≤ windowJetRadius r B β) (hk : |k| ≤ 1 / 2) :
    QPotential r (B + 1)
      (vectorIncrementChain
        ((OW.window (Corner.interpolatedProfile α a lam) (1 / 2) s h k N).map
          fun p => (p.1, β • p.2)) f) := by
  have hB : 0 ≤ B := hf.nonneg
  have hK := stepStabilityCoefficient_nonneg r (by linarith : 0 ≤ B + 1)
  have hmass : ∀ p ∈
      ((OW.window (Corner.interpolatedProfile α a lam) (1 / 2) s h k N).map fun p => (p.1, β • p.2)),
      p.1 ∈ Icc (0 : ℝ) 1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact OW.window_mass_mem _ (interpolatedProfile_mem α hα ha hlam) _ _ _ _ _ q hq
  have hE := window_chainEnergy_le β (Corner.interpolatedProfile α a lam) s h k hN hh hk
  have hh₁ : h ≤ (12 * β ^ 2 * (stepStabilityCoefficient r (B + 1) + 1) + 1)⁻¹ :=
    hh0.trans (min_le_left _ _)
  have hh₂ : h ≤ (24 * β ^ 2 * (B + 1) + 1)⁻¹ := hh0.trans (min_le_right _ _)
  have h₁ : h * (12 * β ^ 2 * (stepStabilityCoefficient r (B + 1) + 1) + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (by simpa only [one_div] using hh₁)
  have h₂ : h * (24 * β ^ 2 * (B + 1) + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (by simpa only [one_div] using hh₂)
  apply qPotential_chain_uniform _ hf hr hmass
  · have he := mul_le_mul_of_nonneg_left hE (show 0 ≤ stepStabilityCoefficient r (B + 1) + 1 by positivity)
    nlinarith
  · have he := mul_le_mul_of_nonneg_left hE (show 0 ≤ B + 1 by positivity)
    nlinarith

end SKBarriers2.StepCalculus
