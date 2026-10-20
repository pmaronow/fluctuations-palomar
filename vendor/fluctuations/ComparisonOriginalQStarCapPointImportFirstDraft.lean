module

public import ComparisonActualHighWallThetaZeroInitialCapPoint
public import ComparisonActualHighWallThetaZeroCapTravelCore
public import ComparisonActualHighWallThetaZeroCapComponents
public import ComparisonActualHighWallStarMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.original_q_bracket_first_variation_ae_import_first_draft
    (P : Q.Potential) :
    ∀ᵐ r, r ∈ Icc Q.data.rmin 1 → HasDerivAt P.H
      (Q.controlFactor r*
        laplaceComparisonStrength Q.data.d Q.lam r*
        comparisonBracket
          (comparisonLogSlope
            (laplaceComparisonStrength Q.data.d Q.lam) r)
          r (Q.radiusS r) (Q.radiusB r)) r := by
  filter_upwards [P.hD] with r hD hr
  have hrpos : 0 < r := Q.data.hrbounds.1.trans_le hr.1
  have hstrength : 0 < laplaceComparisonStrength Q.data.d Q.lam r :=
    laplaceComparisonStrength_pos Q.data.d Q.hlam r
  rw [comparison_gradient_slope hrpos.ne' hstrength.ne'] at hD
  convert hD hr using 1
  dsimp [radiusS,radiusB,comparisonBracket]
  ring

theorem Potential.original_q_star_cap_point_squared_mismatch_import_first_draft
    (P : Q.Potential) {l z r : ℝ}
    (hl : Q.data.rmin ≤ l) (hz : z ≤ 1) (hr : r ∈ Ioo l z)
    (hleft : P.H l = 0) (hright : P.H z = 0 ∨ z = 1)
    (hneg : P.H r < 0) :
    (Q.radiusS r-r)^2 ≤
      16*(z-l)^2+2*(Q.radiusB r-(Q.radiusS r)^2) := by
  let g := laplaceComparisonStrength Q.data.d Q.lam
  let slope := comparisonLogSlope g
  let S := Q.radiusS
  let B := Q.radiusB
  let J := fun t => Q.controlFactor t*g t
  have hmom := Q.radius_moments
  have hsub : Icc l z ⊆ Icc Q.data.rmin 1 := Icc_subset_Icc hl hz
  have hsubo : Ioo l z ⊆ Ioc Q.data.rmin 1 :=
    fun t ht => ⟨hl.trans_lt ht.1,ht.2.le.trans hz⟩
  have hJ t (_ht : t ∈ Icc Q.data.rmin 1) : 0 < J t :=
    mul_pos (inverseControlFactor_pos _ _ t)
      (laplaceComparisonStrength_pos Q.data.d Q.hlam _)
  have hDp : ∀ᵐ t, t ∈ Icc Q.data.rmin 1 → HasDerivAt P.H
      (J t*comparisonBracket (slope t) t (S t) (B t)) t := by
    simpa only [J,slope,g,S,B] using
      P.original_q_bracket_first_variation_ae_import_first_draft
  have hpm : MonotoneOn slope (Ioc Q.data.rmin 1) := by
    intro s hs t ht hst
    dsimp [slope,g]
    rw [laplaceComparisonStrength_logSlope Q.data.hd.ne' Q.hlam.ne',
      laplaceComparisonStrength_logSlope Q.data.hd.ne' Q.hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hst Q.hlam.le)
      (pow_nonneg Q.data.hd.le _))
  have hpb t (_ht : t ∈ Ioc Q.data.rmin 1) :
      slope t ∈ Icc (0:ℝ) 1 := by
    have H := laplaceComparisonStrength_logSlope_mem
      Q.data.hd.ne' Q.hlam.ne' t
    exact ⟨H.1,H.2.le⟩
  have hSr : MonotoneOn S (Ioc Q.data.rmin 1) :=
    hmom.1.mono Ioc_subset_Icc_self
  have hBr : MonotoneOn B (Ioc Q.data.rmin 1) :=
    hmom.2.1.mono Ioc_subset_Icc_self
  have hS0 t (ht : t ∈ Ioc Q.data.rmin 1) : 0 ≤ S t :=
    (hmom.2.2 t (Ioc_subset_Icc_self ht)).1.1
  have hB2 t (ht : t ∈ Ioc Q.data.rmin 1) :
      (S t)^2 ≤ B t :=
    (hmom.2.2 t (Ioc_subset_Icc_self ht)).2.1
  have hac : AbsolutelyContinuousOnInterval P.H l z :=
    P.hH.mono (by
      simpa only [uIcc_of_le Q.data.hr,
        uIcc_of_le (hr.1.trans hr.2).le] using hsub)
  have hDsub := hDp.mono (fun t ht hti => ht (hsub hti))
  rcases hright with hc | hterminal
  · exact cap_interior_mismatch (Q.data.hrbounds.1.le.trans hl)
      hr hac (fun t ht => hJ t (hsub ht)) hDsub hleft hc hneg
      (hpm.mono hsubo) (fun t ht => hpb t (hsubo ht))
      (hSr.mono hsubo) (hBr.mono hsubo)
      (fun t ht => hS0 t (hsubo ht))
      (fun t ht => hB2 t (hsubo ht))
  · have hri : r ∈ Ioc Q.data.rmin 1 := hsubo hr
    have hSr1 : S r ≤ z := by
      rw [hterminal]
      exact (hmom.2.2 r (Ioc_subset_Icc_self hri)).1.2
    have hthermal : 0 ≤ B r-(S r)^2 :=
      sub_nonneg.mpr (hB2 r hri)
    by_cases hSr' : S r ≤ r
    · have hsubleft : Icc l r ⊆ Icc Q.data.rmin 1 :=
        Icc_subset_Icc hl (hr.2.le.trans hz)
      obtain ⟨t,hti,hgl⟩ := potential_negative_left_witness
        hr.1
        (P.hH.mono (by
          simpa only [uIcc_of_le Q.data.hr,
            uIcc_of_le hr.1.le] using hsubleft))
        (fun u hu => hJ u (hsubleft hu))
        (hDp.mono (fun u hu hui => hu (hsubleft hui)))
        (by simpa only [hleft] using hneg)
      have ht : t ∈ Ioc Q.data.rmin 1 :=
        ⟨hl.trans_lt hti.1,hti.2.le.trans hri.2⟩
      have hbracket :
          comparisonBracket (slope r) t (S r) (B r) ≤ 0 :=
        (comparisonBracket_mono_moments
          (Q.data.hrbounds.1.trans ht.1)
          (hpb r hri) (hSr ht hri hti.2.le)
          (hBr ht hri hti.2.le)).trans
          ((comparisonBracket_antitone
            (Q.data.hrbounds.1.trans ht.1)
            (hB2 t ht) (hpm ht hri hti.2.le)).trans hgl.le)
      have hmis := comparisonBracket_left_mismatch
        (Q.data.hrbounds.1.trans ht.1) hti.2.le
        (hpb r hri) (hS0 r hri) hSr' (hB2 r hri) hbracket
      have hlength : 0 ≤ r-t := sub_nonneg.mpr hti.2.le
      have hlength' : r-t ≤ z-l := by linarith [hti.1,hr.2]
      have hs := pow_le_pow_left₀ hlength hlength' 2
      nlinarith only [hmis,hs,hthermal]
    · have hdiff : 0 ≤ S r-r := by linarith
      have hbound : S r-r ≤ z-l := by linarith [hr.1,hSr1]
      have hs := pow_le_pow_left₀ hdiff hbound 2
      have hlenSq : 0 ≤ (z-l)^2 := sq_nonneg _
      nlinarith only [hs,hthermal,hlenSq]

theorem Potential.original_q_star_cap_point_travel_import_first_draft
    (P : Q.Potential) (c : ShiftedCapInterval Q P)
    (hleft : P.H c.left = 0)
    (hright : P.H c.right = 0 ∨ c.right = 1)
    {r : ℝ} (hr : r ∈ Ioo c.left c.right) :
    (Q.radiusS r-r)^2 ≤
      16*Q.cavityCapTravel^2+
        2*(Q.radiusB r-(Q.radiusS r)^2) := by
  have hwidth :=
    (P.cap_interval_travel Q c.hleft c.hlt.le c.hright c.negative).2.1
  have H := P.original_q_star_cap_point_squared_mismatch_import_first_draft
    c.hleft c.hright hr hleft hright (c.negative r hr)
  have hs := pow_le_pow_left₀
    (sub_nonneg.mpr c.hlt.le) hwidth 2
  nlinarith only [H,hs]

theorem Potential.original_q_star_initial_cap_travel_import_first_draft
    (P : Q.Potential) (c : ShiftedCapInterval Q P)
    (hstart : c.left = Q.data.rmin)
    (hright : P.H c.right = 0 ∨ c.right = 1)
    {r : ℝ} (hr : r ∈ Ioo c.left c.right) :
    (Q.radiusS r-r)^2 ≤
      (Q.data.rmin+Q.cavityCapTravel)^2 := by
  have hwidth :=
    (P.cap_interval_travel Q c.hleft c.hlt.le c.hright c.negative).2.1
  have htravel : 0 ≤ Q.cavityCapTravel :=
    (sub_nonneg.mpr c.hlt.le).trans hwidth
  have hr' : r ∈ Ioo Q.data.rmin c.right := by
    simpa only [hstart] using hr
  exact P.initial_cap_point_squared_mismatch c.hright hr'
    (c.negative r hr) hright (by simpa only [hstart] using hwidth)
    htravel

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
