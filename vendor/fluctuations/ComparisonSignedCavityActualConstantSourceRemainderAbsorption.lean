module

public import ComparisonSignedCavityActualConstantSourceRemainderParts

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity

theorem susceptibility_bootstrap_remainder_reduction
    {J C Cr W xs a E R Z cS : ℝ}
    (hW : 0 < W) (hcS : 0 < cS) (hxs : 0 ≤ xs) (hxW : xs ≤ W) (hCr : 0 ≤ Cr)
    (hJ : J ≤ C*W^2+2*(a*E+|R|/(cS*W)))
    (hR : |R| ≤ Cr*W*xs^2+|Z|) :
    J ≤ (C+2*Cr/cS)*W^2+2*(a*E+|Z|/(cS*W)) := by
  have Hdiv:=div_le_div_of_nonneg_right hR (mul_pos hcS hW).le
  have Hsquare:=pow_le_pow_left₀ hxs hxW 2
  have Hscale:=mul_le_mul_of_nonneg_left Hsquare (div_nonneg hCr hcS.le)
  have Hnorm : (Cr*W*xs^2+|Z|)/(cS*W)=(Cr/cS)*xs^2+|Z|/(cS*W):=by
    field_simp
  rw [Hnorm] at Hdiv
  rw [show 2*Cr/cS=2*(Cr/cS) by ring]
  nlinarith only [hJ,Hdiv,Hscale]

end OAI.SKFluctuations.Cavity
