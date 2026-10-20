module

public import ComparisonActualHighWallThetaZeroEq7RegularFamilyPhysicalTailDraft
public import ComparisonActualHighWallThetaZeroEq7QuantitativePrefixCorrected
public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonConditionalErrorSize
public import SKProof.RegularEq7OuterGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem eq7_regular_prefix_le_inner_cut_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    {C : ℝ} (hC : 24 ≤ C)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs) :
    Q.eq7InnerPrefixEnd ≤ min (C*Q.xs) 1 := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  have hCxs : 24*Q.xs ≤ C*Q.xs := by
    have H := mul_nonneg (sub_nonneg.mpr hC) Q.hxs.le
    nlinarith only [H]
  have hUxs : 24*U ≤ 24*Q.xs :=
    mul_le_mul_of_nonneg_left hUA (by norm_num)
  by_cases hsU : Q.data.s < U
  · dsimp only [eq7InnerPrefixEnd]
    rw [ite_eq_left hsU]
    exact min_le_min (hUxs.trans hCxs) le_rfl
  · dsimp only [eq7InnerPrefixEnd]
    rw [ite_eq_right hsU]
    have hs2U : Q.data.s+2*U ≤ 3*Q.xs := by
      nlinarith only [Q.hsxs,hUA]
    have h3C : 3*Q.xs ≤ C*Q.xs := by
      nlinarith only [hCxs,Q.hxs]
    exact min_le_min (hs2U.trans h3C) le_rfl

theorem eq7_inner_positive_radius_width_price_on_carrier
    {C lo hi : ℝ} (_hC : 0 ≤ C) (hlohi : lo ≤ hi)
    (hwidth : hi-lo ≤ C*Q.xs)
    (htravelU : Q.cavityCapTravel ≤
      comparisonSmallMass Q.data.N Q.data.E)
    (hUxs : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (hcarrier : Q.xs =
      comparisonConditionalScale Q.data.N delta Q.data.E Q.lam) :
    16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*(hi-lo) ≤
      64*C*Q.data.N^(2*delta)*Q.data.E := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  let R := Q.data.rmin+Q.cavityCapTravel
  have hR0 : 0 ≤ R := add_nonneg Q.data.hrbounds.1.le Q.cavityCapTravel_nonneg
  have hR : R ≤ 2*U := by
    dsimp only [R,U]
    linarith only [Q.radius_le_smallMass,htravelU]
  have hRsq : R^2 ≤ 4*Q.xs*U := by
    have H1 := pow_le_pow_left₀ hR0 hR 2
    have H2 := mul_le_mul_of_nonneg_right hUxs Q.data.hU.le
    nlinarith only [H1,H2]
  have Hprice : Q.lam*R^2*(hi-lo) ≤
      4*C*(Q.lam*Q.xs^2*U) := by
    have H1 := mul_le_mul_of_nonneg_left hRsq Q.hlam.le
    have H2 := mul_le_mul_of_nonneg_right H1 (sub_nonneg.mpr hlohi)
    have H3 := mul_le_mul_of_nonneg_left hwidth
      (mul_nonneg Q.hlam.le (mul_nonneg Q.hxs.le Q.data.hU.le))
    nlinarith only [H2,H3]
  have Hcarrier : Q.lam*Q.xs^2*U =
      Q.data.N^(2*delta)*Q.data.E := by
    rw [hcarrier]
    exact comparison_conditional_small_mass_cost Q.data.hN Q.data.hE Q.hlam
  have H := mul_le_mul_of_nonneg_left Hprice (by norm_num : (0:ℝ)≤16)
  calc
    16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*(hi-lo) ≤
        16*(4*C*(Q.lam*Q.xs^2*U)) := by
      dsimp only [R] at Hprice H
      nlinarith only [H]
    _ = 64*C*Q.data.N^(2*delta)*Q.data.E := by
      rw [Hcarrier]
      ring

theorem eventually_regular_inner_family
    (Bclock C : ℝ)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hC : 2 ≤ C) :
    ∃ ell : ℕ, 2 < ell ∧ (14+3*delta)/((ell:ℝ)-1) ≤ delta ∧
      ∃ Kinner : ℝ, 0 ≤ Kinner ∧ ∀ᶠ n : ℕ in atTop,
        ∀ (Q : ActualThetaZeroOverlapMinimum
            (n+1) m delta cl cu Az C0 Ct D Bclock) (P : Q.Potential),
          Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam →
          Q.data.N^(-(10:ℝ)) ≤ Q.lam →
          ∀ F : Finset (ordConnectedSection P.negativeSet),
            Q.lam*(∑ p : Eq7InnerCoverPiece (P.capFamily F) (min (C*Q.xs) 1),
              eq7InnerThermalPiece (P.capFamily F) (min (C*Q.xs) 1) p) ≤
              Kinner*(Real.log Q.data.N)^6*Q.data.N^(3*delta)*Q.data.E := by
  obtain ⟨ell, hell, horder, qLow, qPost, qBroad, _, _, _, H⟩ :=
    eventually_eq7_inner_regular_family_from_physical_draft Bclock C delta
      hm hdelta hroom hcl hcu hAz hC0 hCt hC hdelta
  let Kinner := max 1 (OriginalQEq7RegularFamilyRateDraft.familyConstant
    delta cl Az D C qLow qPost qBroad)
  refine ⟨ell, hell, horder, Kinner, zero_le_one.trans (le_max_left _ _), ?_⟩
  filter_upwards [H] with n hn Q P hcarrier hlam F
  have Hraw := hn Q P (min (C*Q.xs) 1) hcarrier hlam
    (min_le_right _ _) (min_le_left _ _) F
  rw [show 2*delta+delta = 3*delta by ring] at Hraw
  exact Hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      (Real.rpow_pos_of_pos Q.data.hN _).le) Q.data.hE.le)

theorem eventually_regular_prefix
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Kprefix : ℝ, 0 < Kprefix ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam →
        comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs →
        (∫ u in (0:ℝ)..Q.eq7InnerPrefixEnd,
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
          Kprefix*Q.data.N^(2*delta)*Q.data.E := by
  exact eventually_theta_zero_eq7_unified_prefix_quantitative_corrected_draft
    hm hdelta hroom hcl hcu hAz hC0 hCt

theorem eventually_regular_travel_le_small_mass (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.cavityCapTravel ≤ comparisonSmallMass Q.data.N Q.data.E := by
  have Hlog : ∀ᶠ n : ℕ in atTop,
      2*Real.log ((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ)^delta := by
    have H := (tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 1)).eventually
        (comparison_log_loss_eventually (C:=2) (p:=1) (by norm_num) hdelta)
    simpa only [Real.rpow_one, Function.comp_def] using H
  filter_upwards [Hlog, eventually_ge_atTop (1:ℕ)] with n hn hn1 Q
  have hN : 2 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ hn1
  have hlog : 2*Real.log Q.data.N ≤ Q.data.N^delta := hn
  have hp : 0 < Q.data.N^delta := Real.rpow_pos_of_pos Q.data.hN _
  calc
    Q.cavityCapTravel ≤
        2*Real.log Q.data.N*comparisonSmallMass Q.data.N Q.data.E/
          Q.data.N^delta := eq7_outer_cap_travel_le Q hN
    _ ≤ Q.data.N^delta*comparisonSmallMass Q.data.N Q.data.E/
          Q.data.N^delta :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlog Q.data.hU.le) hp.le
    _ = comparisonSmallMass Q.data.N Q.data.E := by field_simp [hp.ne']

theorem eventually_regular_inner_radius {C : ℝ} (hC : 24 ≤ C)
    (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock,
        comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs →
        Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam →
        16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*
          (min (C*Q.xs) 1-Q.eq7InnerPrefixEnd) ≤
          64*C*Q.data.N^(2*delta)*Q.data.E := by
  filter_upwards [eventually_regular_travel_le_small_mass
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0)
    (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta] with n hn Q hUA hcarrier
  have hp0 : 0 ≤ Q.eq7InnerPrefixEnd :=
    Q.data.hs.1.le.trans Q.eq7_inner_s_le_prefix_end
  exact eq7_inner_positive_radius_width_price_on_carrier Q (by linarith only [hC])
    (eq7_regular_prefix_le_inner_cut_draft Q hC hUA)
    (by linarith only [min_le_left (C*Q.xs) 1, hp0]) (hn Q) hUA hcarrier

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
