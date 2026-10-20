module

public import Mathlib

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Filter
open scoped Topology

theorem tendsto_response_of_uniform_taylor
    {f : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {g : ℕ → ℝ} {G M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ s, Tendsto (f s) atTop (𝓝 (F s)))
    (hfn : ∀ s n, |f s n-f 0 n-s*g n| ≤ M*s^2)
    (hF : ∀ s, |F s-F 0-s*G| ≤ M*s^2) :
    Tendsto g atTop (𝓝 G) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let s := ε/(4*(M+1))
  have hden : 0 < 4*(M+1) := by positivity
  have hs : 0 < s := div_pos hε hden
  have hsM : M*s ≤ ε/4 := by
    dsimp only [s]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hquot (n : ℕ) : |(f s n-f 0 n)/s-g n| ≤ M*s := by
    have he : (f s n-f 0 n)/s-g n=(f s n-f 0 n-s*g n)/s := by
      field_simp
    rw [he, abs_div, abs_of_pos hs]
    apply (div_le_div_of_nonneg_right (hfn s n) hs.le).trans_eq
    field_simp
  have hquotF : |(F s-F 0)/s-G| ≤ M*s := by
    have he : (F s-F 0)/s-G=(F s-F 0-s*G)/s := by field_simp
    rw [he, abs_div, abs_of_pos hs]
    apply (div_le_div_of_nonneg_right (hF s) hs.le).trans_eq
    field_simp
  have ht := ((hf s).sub (hf 0)).div_const s
  filter_upwards [ht.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with n hn
  rw [Real.dist_eq] at hn
  rw [Real.dist_eq]
  have ha := abs_sub_le (g n) ((f s n-f 0 n)/s) G
  have hb := abs_sub_le ((f s n-f 0 n)/s) ((F s-F 0)/s) G
  have hquotn := hquot n
  rw [abs_sub_comm] at hquotn
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
