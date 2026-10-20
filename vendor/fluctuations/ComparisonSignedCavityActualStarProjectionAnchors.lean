module

public import ComparisonSignedCavityActualSlowWindowSequence

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
set_option maxHeartbeats 4000000

def actualStarProjectionAnchorConstant (a Kv Ks cl cu F : ℝ) : ℝ :=
  Kv*max (F/((cl/8)^2*Ks)) ((1+4*cu)*Ks/a^2)

theorem actual_star_projection_anchor_bounds
    {a Kv Ks cl cu F W : ℝ}
    (ha : 0 < a) (hKv : 0 < Kv) (hKs : 0 < Ks) (_hcl : 0 < cl)
    (hcu : 0 ≤ cu) (hW : 0 < W) :
    let H0 := actualStarProjectionAnchorConstant a Kv Ks cl cu F
    let H := H0/(Kv*W)
    0 < H0 ∧ 0 < H ∧
    F/((cl/8)^2*(Ks*W)) ≤ H ∧ (1+4*cu)*(Ks*W) ≤ H*(a*W)^2 := by
  let B := max (F/((cl/8)^2*Ks)) ((1+4*cu)*Ks/a^2)
  have hB : 0 < B := (div_pos (mul_pos (by positivity : 0 < 1+4*cu) hKs)
    (sq_pos_of_pos ha)).trans_le (le_max_right _ _)
  have he : actualStarProjectionAnchorConstant a Kv Ks cl cu F/(Kv*W)=B/W := by
    dsimp only [actualStarProjectionAnchorConstant,B]
    field_simp
  dsimp only
  rw [he]
  refine ⟨mul_pos hKv hB,div_pos hB hW,?_,?_⟩
  · have H := div_le_div_of_nonneg_right (le_max_left (F/((cl/8)^2*Ks))
      ((1+4*cu)*Ks/a^2)) hW.le
    simpa only [div_div,mul_assoc] using H
  · have H := (div_le_iff₀ (sq_pos_of_pos ha)).mp
      (le_max_right (F/((cl/8)^2*Ks)) ((1+4*cu)*Ks/a^2))
    have Hmul := mul_le_mul_of_nonneg_right H hW.le
    have he' : (B/W)*(a*W)^2=B*a^2*W := by field_simp
    rw [he']
    nlinarith only [Hmul]

end OAI.SKFluctuations.LaplaceWindowFormalization
