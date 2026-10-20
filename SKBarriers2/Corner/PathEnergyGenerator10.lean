module

public import SKBarriers2.Corner.PathEnergyGenerator8

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem tiltedGeneratorDefect_const_mul {C : ℝ} {g : E → ℝ}
    (hg : QBoundedJets 2 C g) (m c : ℝ) (v : E) (f : E → ℝ) (x : E) :
    tiltedGeneratorDefect m v f (fun y => c*g y) x =
      c*tiltedGeneratorDefect m v f g x := by
  have hgc := hg.smooth.differentiable (by norm_num)
  have hdc := (hg.derivativeJets.apply_const v).smooth.differentiable (by norm_num)
  have hdir₁ : directionalJet v 1 (fun y => c*g y) =
      fun y => c*directionalJet v 1 g y := by
    funext y
    change fderiv ℝ (fun y => c*g y) y v = c*fderiv ℝ g y v
    rw [fderiv_const_mul (hgc y)]
    rfl
  have hdir₂ : directionalJet v 2 (fun y => c*g y) x = c*directionalJet v 2 g x := by
    change fderiv ℝ (directionalJet v 1 (fun y => c*g y)) x v = _
    rw [hdir₁]
    change fderiv ℝ (fun y => c*fderiv ℝ g y v) x v =
      c*fderiv ℝ (fun y => fderiv ℝ g y v) x v
    rw [fderiv_const_mul (hdc x)]
    rfl
  have havg : tiltedAverage m v f (fun y => c*g y) x = c*tiltedAverage m v f g x := by
    unfold tiltedAverage
    rw [integral_const_mul]
  unfold tiltedGeneratorDefect pathGenerator
  rw [havg,fderiv_const_mul (hgc x),hdir₂]
  simp only [smul_apply,smul_eq_mul]
  ring

theorem eventually_tiltedGeneratorDefect_energy_le {B C₀ h eps L : ℝ}
    (hB : 0 ≤ B) (hC₀ : 0 < C₀) (hh : 0 < h) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ f g : E → ℝ,
      QPotential 8 B f → QBoundedJets 8 (C₀*h/(N:ℝ)) g →
      ∀ m : ℝ, m ∈ Icc (0:ℝ) 1 → ∀ (v : E) (e : ℝ),
      0 ≤ e → ‖v‖^2 ≤ e → e ≤ L*h/(N:ℝ) →
      QBoundedJets 4 ((eps/(N:ℝ))*e) (tiltedGeneratorDefect m v f g) := by
  let δ := eps/(C₀*h+1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [normalized_tiltedGeneratorDefect_spatial_eventually
    (M := L) (h := h) hB (by norm_num : (0:ℝ) ≤ 1) hδ,
    eventually_ge_atTop (1:ℕ)] with N hN hN1
  intro f g hf hg m hm v e he0 hve hmesh
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN1
  let C := C₀*h/(N:ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hδC : δ*(C₀*h) ≤ eps := by
    calc
      _ = eps*((C₀*h)/(C₀*h+1)) := by dsimp only [δ]; ring
      _ ≤ eps*1 := mul_le_mul_of_nonneg_left
        ((div_le_one (by positivity : 0 < C₀*h+1)).mpr (by linarith)) heps.le
      _ = eps := mul_one _
  by_cases hv : v = 0
  · have H := qBoundedJets_tiltedGeneratorDefect_coarse 4
      (hf.of_le (by norm_num : 6 ≤ 8)) (hg.of_le (by norm_num : 6 ≤ 8))
      hm v (by simp [hv]) (by simp [hv])
    apply H.mono
    simp only [hv,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero]
    positivity
  · let g₀ := fun y => C⁻¹*g y
    have hg₀ : QBoundedJets 8 1 g₀ := by
      have H := hg.const_smul C⁻¹
      convert H using 1
      rw [abs_inv,abs_of_pos hC,inv_mul_cancel₀ hC.ne']
    have H := (hN f g₀ hf hg₀ m hm v (hve.trans hmesh)).const_smul (C*‖v‖^2)
    have hv2 : ‖v‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    have H' : QBoundedJets 4 (δ*C*‖v‖^2) (tiltedGeneratorDefect m v f g) := by
      convert H using 1
      · rw [abs_of_nonneg (mul_nonneg hC.le (sq_nonneg ‖v‖))]
        ring
      · funext x
        simp only [smul_eq_mul,g₀,tiltedGeneratorDefect_const_mul
          (hg.of_le (by norm_num : 2 ≤ 8))]
        field_simp [hv2,hC.ne']
    apply H'.mono
    calc
      _ ≤ δ*C*e := mul_le_mul_of_nonneg_left hve (mul_nonneg hδ.le hC.le)
      _ = (δ*(C₀*h)/(N:ℝ))*e := by dsimp only [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hδC hn.le) he0

end SKBarriers2.StepCalculus
