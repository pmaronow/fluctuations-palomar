module

public import ComparisonOriginalQStarCapPointImportFirstDraft

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

theorem Potential.star_cap_point_squared_mismatch (P : Q.Potential)
    {l z r : ℝ} (hl : Q.data.rmin ≤ l) (hz : z ≤ 1)
    (hr : r ∈ Ioo l z) (hleft : P.H l = 0)
    (hright : P.H z = 0 ∨ z = 1) (hneg : P.H r < 0) :
    (Q.radiusS r-r)^2 ≤
      16*(z-l)^2+2*(Q.radiusB r-(Q.radiusS r)^2) :=
  P.original_q_star_cap_point_squared_mismatch_import_first_draft
    hl hz hr hleft hright hneg

theorem Potential.star_negative_point_squared_mismatch_split
    (P : Q.Potential) {r : ℝ}
    (hr : r ∈ Ioo Q.data.rmin 1) (hneg : P.H r < 0) :
    (Q.radiusS r-r)^2 ≤
        (Q.data.rmin+Q.cavityCapTravel)^2 ∨
      (Q.radiusS r-r)^2 ≤
        16*Q.cavityCapTravel^2+
          2*(Q.radiusB r-(Q.radiusS r)^2) := by
  have hrneg : r ∈ P.negativeSet := ⟨hr,hneg⟩
  obtain ⟨c,_hcl,_hcr,heq,hcLeft,hcRight⟩ :=
    P.negative_component_endpoints hrneg
  have hrc : r ∈ Ioo c.left c.right := by
    rw [heq]
    exact self_mem_ordConnectedComponent.mpr hrneg
  rcases hcLeft with hcontact | hinitial
  · exact Or.inr
      (P.original_q_star_cap_point_travel_import_first_draft
        c hcontact hcRight hrc)
  · exact Or.inl
      (P.original_q_star_initial_cap_travel_import_first_draft
        c hinitial hcRight hrc)

theorem Potential.star_negative_point_squared_mismatch (P : Q.Potential)
    {r : ℝ} (hr : r ∈ Ioo Q.data.rmin 1) (hneg : P.H r < 0)
    (haway : Q.data.rmin+Q.cavityCapTravel < r) :
    (Q.radiusS r-r)^2 ≤
      16*Q.cavityCapTravel^2+
        2*(Q.radiusB r-(Q.radiusS r)^2) := by
  have hrneg : r ∈ P.negativeSet := ⟨hr,hneg⟩
  obtain ⟨c,_hcl,_hcr,heq,hcLeft,hcRight⟩ :=
    P.negative_component_endpoints hrneg
  have hrc : r ∈ Ioo c.left c.right := by
    rw [heq]
    exact self_mem_ordConnectedComponent.mpr hrneg
  have hwidth :=
    (P.cap_interval_travel Q c.hleft c.hlt.le c.hright c.negative).2.1
  have hcontact : P.H c.left = 0 := by
    rcases hcLeft with hcontact | hinitial
    · exact hcontact
    · rw [hinitial] at hwidth
      exfalso
      linarith only [hwidth,hrc.2,haway]
  exact P.original_q_star_cap_point_travel_import_first_draft
    c hcontact hcRight hrc

theorem Potential.star_nonpositive_squared_mismatch_ae (P : Q.Potential) :
    ∀ᵐ r, r ∈ Icc Q.data.rmin 1 →
      Q.data.rmin+Q.cavityCapTravel < r → P.H r ≤ 0 →
      (Q.radiusS r-r)^2 ≤
        16*Q.cavityCapTravel^2+
          2*(Q.radiusB r-(Q.radiusS r)^2) := by
  have hmom := Q.radius_moments
  filter_upwards [P.hzero, volume.ae_ne Q.data.rmin,
    volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri haway hnonpos
  have hro : r ∈ Ioo Q.data.rmin 1 :=
    ⟨lt_of_le_of_ne hri.1 hr0.symm,
      lt_of_le_of_ne hri.2 hr1⟩
  rcases hnonpos.eq_or_lt with hz | hneg
  · have H := (hrzero hri hz).2.2
    change (Q.radiusS r-r)^2 ≤
      Q.radiusB r-(Q.radiusS r)^2 at H
    have hthermal := sub_nonneg.mpr (hmom.2.2 r hri).2.1
    nlinarith only [H,hthermal,sq_nonneg Q.cavityCapTravel]
  · exact P.star_negative_point_squared_mismatch hro hneg haway

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
