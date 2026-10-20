module

public import SKFluctuationsOAI.Probability.SKFluctuations.OrderedSKCumulativeChord

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section

open Hierarchy

theorem chord_penalty_eq_penalty_sub_gain {e delta r : ℝ}
    (he : 0 ≤ e) (hd : 0 ≤ delta) :
    (e * r) ^ 2 / (e + delta) =
      e * r ^ 2 - delta * e / (e + delta) * r ^ 2 := by
  by_cases hz : e + delta = 0
  · have he0 : e = 0 := by linarith
    simp [he0]
  · field_simp [hz]
    ring

theorem finite_pressure_gain_of_compensated_comparison
    (n : ℕ) (hn : 0 < n) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ a ∈ as, a.val ≤ 1)
    (b₀ b₁ e r : ℕ → ℝ) (error : ℝ)
    (he : ∀ j, 0 ≤ e j) (hb01 : ∀ j, b₁ j ≤ b₀ j)
    (hb0 : Monotone b₀) (hbchild : Monotone (fun j => b₁ j - e j))
    (hhchild : Monotone (fun j => e j * r j))
    (hb00 : 0 ≤ b₀ 0) (hbc0 : 0 ≤ b₁ 0 - e 0) (hr0 : 0 ≤ r 0)
    (x : OrderedFeatureIndex n → ℝ)
    (hcomparison : finiteCompensatedPressure n as b₁ (fun _ => 0) e r x ≤
      orderedSKPressure n as b₁ (fun _ => 0) x + error) :
    (1 / 4 : ℝ) * massStepSum as 0
        (fun j => (b₀ j - b₁ j) * e j / (b₀ j - b₁ j + e j) * (r j) ^ 2) -
      error ≤
        orderedSKPressure n as b₁ (fun _ => 0) x -
          orderedSKPressure n as b₀ (fun _ => 0) x := by
  have hchord := orderedSK_cumulative_chord n hn as ho hu
    (fun j => b₁ j - e j) (fun j => e j * r j) b₀ (fun _ => 0)
    hbchild hhchild hb0 (fun _ _ _ => le_rfl)
    hbc0 (mul_nonneg (he 0) hr0) hb00 (le_refl 0)
    (fun j _ => by linarith [he j, hb01 j])
    (fun j _ hz => by
      have he0 : e j = 0 := by linarith [he j, hb01 j]
      simp [he0]) x
  have hcost (j : ℕ) :
      (e j * r j - 0) ^ 2 / (b₀ j - (b₁ j - e j)) =
        e j * (r j) ^ 2 -
          (b₀ j - b₁ j) * e j / (b₀ j - b₁ j + e j) * (r j) ^ 2 := by
    rw [sub_zero, show b₀ j - (b₁ j - e j) = e j + (b₀ j - b₁ j) by ring]
    simpa only [add_comm] using
      (chord_penalty_eq_penalty_sub_gain (he j) (sub_nonneg.mpr (hb01 j))
        (r := r j))
  simp_rw [hcost] at hchord
  rw [massStepSum_sub] at hchord
  unfold finiteCompensatedPressure at hcomparison
  simp only [zero_add] at hcomparison
  linarith

end

end OAI.SKFluctuations.LaplaceWindowFormalization
