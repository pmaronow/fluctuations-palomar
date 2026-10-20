module

public import SKBarriers2.Corner.FrozenRowsPotential13
public import SKBarriers2.Corner.FrozenRowsMixed7

@[expose] public section

noncomputable section
open scoped Topology

namespace SKBarriers2.Corner

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affine_first_score_weighted {r : ℕ} {B : ℝ}
    {G : E → ℝ} {DF : E → E →L[ℝ] ℝ}
    (hG : QBoundedJets r B G) (hDF : QBoundedJets r B DF)
    (A U : E →L[ℝ] E) (b v u w : E) (t : ℝ) :
    WJets r
      (B * max 1 ‖A‖ ^ r *
        (1 + (2 : ℝ) ^ r * (‖U‖ + ‖u‖ + ‖w‖)) * (1 + |t|)) 1
      (fun y => G (A y + b + t • v) +
        DF (A y + b + t • v) (U y + u + t • w)) := by
  let D := B * max 1 ‖A‖ ^ r
  let C := ‖U‖ + ‖u‖ + ‖w‖
  have hD : 0 ≤ D := by dsimp only [D]; positivity [hG.nonneg]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hGc : WJets r D 0 (fun y => G (A y + (b + t • v))) := by
    simpa only [pow_zero,mul_one] using (hG.weighted (p := 0)).comp_affine A (b + t • v)
  have hDFc : WJets r D 0 (fun y => DF (A y + (b + t • v))) := by
    simpa only [pow_zero,mul_one] using (hDF.weighted (p := 0)).comp_affine A (b + t • v)
  have hvel : ‖U‖ + ‖u + t • w‖ ≤ C * (1 + |t|) := by
    have H := norm_add_le u (t • w)
    rw [norm_smul,Real.norm_eq_abs] at H
    dsimp only [C]
    nlinarith [norm_nonneg U,norm_nonneg u,norm_nonneg w,abs_nonneg t,
      mul_nonneg (norm_nonneg U) (abs_nonneg t),
      mul_nonneg (norm_nonneg u) (abs_nonneg t)]
  have hV := (WJets.affine r U (u + t • w)).mono hvel le_rfl
  have HS := (hGc.mono le_rfl (by omega : 0 ≤ 1)).add (hDFc.clm_apply hV)
  have hbound : D + (2 : ℝ) ^ r * D * (C * (1 + |t|)) ≤
      D * (1 + (2 : ℝ) ^ r * C) * (1 + |t|) := by
    nlinarith [mul_nonneg hD (abs_nonneg t)]
  convert HS.mono hbound le_rfl using 1
  simp only [add_assoc]

theorem affine_first_score_contDiff {r : ℕ} {B : ℝ}
    {G : E → ℝ} {DF : E → E →L[ℝ] ℝ}
    (hG : QBoundedJets r B G) (hDF : QBoundedJets r B DF)
    (A U : E →L[ℝ] E) (b v u w : E) :
    ContDiff ℝ r (fun z : ℝ × E => G (A z.2 + b + z.1 • v) +
      DF (A z.2 + b + z.1 • v) (U z.2 + u + z.1 • w)) := by
  have hY : ContDiff ℝ r (fun z : ℝ × E => A z.2 + b + z.1 • v) :=
    ((A.contDiff.comp contDiff_snd).add contDiff_const).add
      (contDiff_fst.smul contDiff_const)
  have hV : ContDiff ℝ r (fun z : ℝ × E => U z.2 + u + z.1 • w) :=
    ((U.contDiff.comp contDiff_snd).add contDiff_const).add
      (contDiff_fst.smul contDiff_const)
  exact (hG.smooth.comp hY).add ((hDF.smooth.comp hY).clm_apply hV)

end SKBarriers2.Corner
