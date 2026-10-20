module

public import ComparisonSignedCavityJointFreshAnchorBound
public import ComparisonSignedCavityCalibratedStarSubtreeProjection

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_subtree_projection_same_zero (n : ℕ)
    {as es : List PositiveMass} (T : ClockTree (Spin n) as) (s : T.Slot)
    (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (e : E.Slot)
    (qE qD : ℕ→RestCoordinate n→ℝ≥0) (xE xD : RestCoordinate n→ℝ) :
    nativeSubtreeExteriorProjectionFourth n T s s E H e qE qD xE xD=0 := by
  simp [nativeSubtreeExteriorProjectionFourth,ClockTree.expect]

theorem native_subtree_projection_swap (n : ℕ)
    {as es : List PositiveMass} (T : ClockTree (Spin n) as) (s t : T.Slot)
    (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (e : E.Slot)
    (qE qD : ℕ→RestCoordinate n→ℝ≥0) (xE xD : RestCoordinate n→ℝ) :
    nativeSubtreeExteriorProjectionFourth n T s t E H e qE qD xE xD=
      nativeSubtreeExteriorProjectionFourth n T t s E H e qE qD xE xD := by
  unfold nativeSubtreeExteriorProjectionFourth
  congr 1
  funext σ
  rw [inner_sub_left,inner_sub_left]
  ring

theorem observed_whole_law_gamma_saved_scale
    {G F Cg Cp saving p x W v : ℝ}
    (hCg : 0 ≤ Cg) (hCp : 0 ≤ Cp) (hsaving : 0 ≤ saving) (hp : 0 ≤ p)
    (hx : 0 ≤ x) (hW : 0<W) (hv : 0<v)
    (hG : |G| ≤ Cg*v)
    (hF : |F| ≤ p*(Cp*saving*savedProjectedScale x W v)) :
    |G*F| ≤ (Cg*Cp)*saving*p*(x^3/W) := by
  have H:=mul_le_mul hG hF (abs_nonneg F) (mul_nonneg hCg hv.le)
  rw [abs_mul]
  apply H.trans_eq
  unfold savedProjectedScale
  field_simp
  <;> ring

theorem observed_whole_law_gamma_saved_cubic
    {G F Cg Cp Cl saving p0 x W v : ℝ}
    (hCg : 0 ≤ Cg) (hCp : 0 ≤ Cp) (hCl : 0 ≤ Cl) (hsaving : 0 ≤ saving)
    (hp0 : 0 ≤ p0) (hx : 0 ≤ x) (hW : 0<W) (hv : 0<v) (hxW : x ≤ W)
    (hG : |G| ≤ Cg*v)
    (hF : |F| ≤ (Cl*W*p0)*(Cp*saving*savedProjectedScale x W v)) :
    |G*F| ≤ (Cg*Cp*Cl)*saving*(W*x^2*p0) := by
  have H:=observed_whole_law_gamma_saved_scale hCg hCp hsaving (by positivity) hx hW hv hG hF
  have he : (Cg*Cp)*saving*(Cl*W*p0)*(x^3/W)=(Cg*Cp*Cl)*saving*p0*x^3 := by
    field_simp
    <;> ring
  rw [he] at H
  apply H.trans
  have hsmall : x^3 ≤ W*x^2 := by nlinarith [mul_le_mul_of_nonneg_right hxW (sq_nonneg x)]
  have Hmul:=mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ (Cg*Cp*Cl)*saving*p0)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using Hmul

end OAI.SKFluctuations.Cavity
