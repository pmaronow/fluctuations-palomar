module

public import ComparisonNativeActualIntermediateMassScale
public import ComparisonNativeActualHighMassFloorNormalization

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem actual_intermediate_mass_target_local_le {x W s v : ℝ}
    (hx : 0 < x) (hW : 0 < W) (hs : 0 < s) (hv : 0 < v) (hsv : s ≤ 4*v) :
    x^4*s/(actualIntermediateMassEffectiveScale W s)^2 ≤
      4*(x^4*v/(actualIntermediateMassEffectiveScale W v)^2) := by
  let Bs := actualIntermediateMassEffectiveScale W s
  let Bv := actualIntermediateMassEffectiveScale W v
  have hBs : 0 < Bs := actualIntermediateMassEffectiveScale_pos hW hs
  have hBv : 0 < Bv := actualIntermediateMassEffectiveScale_pos hW hv
  have hBsc : Bs^3=W^2*s := actualIntermediateMassEffectiveScale_cube hW.le hs.le
  have hBvc : Bv^3=W^2*v := actualIntermediateMassEffectiveScale_cube hW.le hv.le
  have Hcube : (s*Bv^2)^3 ≤ (4*v*Bs^2)^3 := by
    calc
      _ = s*(W^4*s^2*v^2) := by
        rw [mul_pow,show (Bv^2)^3=(Bv^3)^2 by ring,hBvc]
        ring
      _ ≤ (64*v)*(W^4*s^2*v^2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
        rw [mul_pow,show (Bs^2)^3=(Bs^3)^2 by ring,hBsc]
        ring
  have Hmul : s*Bv^2 ≤ 4*v*Bs^2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (3:ℕ) ≠ 0)).mp Hcube
  have HH := mul_le_mul_of_nonneg_left Hmul (pow_nonneg hx.le 4)
  calc
    _ ≤ (4*(x^4*v))/Bv^2 :=
      (div_le_div_iff₀ (sq_pos_of_pos hBs) (sq_pos_of_pos hBv)).mpr (by nlinarith only [HH])
    _ = _ := by dsimp only [Bv]; ring

theorem mass_intermediate_floor_slab_normalized_le {x W v U N delta cu c C K : ℝ}
    (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) (hcu : 0 < cu) (hc : 0 < c)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hvlo : c*x ≤ v) (hvupper : v ≤ C*W) :
    (K*(x+2*v)^2*N^delta*U^2/(v/cu))/
        (x^4*v/(actualIntermediateMassEffectiveScale W v)^2) ≤
      (K*cu*(1/c+2)^2*(max 1 C)^2)*N^delta*(U^2*W^2/x^4) := by
  let B := actualIntermediateMassEffectiveScale W v
  have hB : 0 < B := actualIntermediateMassEffectiveScale_pos hW hv
  have hxv : x ≤ v/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
  have hs : x+2*v ≤ (1/c+2)*v := by
    calc
      _ ≤ v/c+2*v := add_le_add hxv le_rfl
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ x+2*v) hs 2
  have hm := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ K*N^delta*U^2*cu*B^2/(x^4*v^2) by positivity)
  have he₁ : (K*N^delta*U^2*cu*B^2/(x^4*v^2))*(x+2*v)^2=
      (K*(x+2*v)^2*N^delta*U^2/(v/cu))/(x^4*v/B^2) := by field_simp
  have he₂ : (K*N^delta*U^2*cu*B^2/(x^4*v^2))*((1/c+2)*v)^2=
      (K*cu*(1/c+2)^2)*N^delta*(U^2*B^2/x^4) := by field_simp
  rw [he₁,he₂] at hm
  apply hm.trans
  have HB := (actualIntermediateMassEffectiveScale_upper hW hv hvupper).2
  have HH := mul_le_mul_of_nonneg_left HB
    (show 0 ≤ (K*cu*(1/c+2)^2)*N^delta*U^2/x^4 by positivity)
  convert HH using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
