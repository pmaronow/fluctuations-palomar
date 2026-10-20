module

public import SKProof.RegularEq7OuterAtoms

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable

def OriginalQOuterLocalSourceAtCutCorrectedC0
    {n : ℕ} {m cl cu Az C0 Ct D Bclock : ℝ}
    (Q : ActualThetaZeroOverlapMinimum (n+1) m (m/10000)
      cl cu Az C0 Ct D Bclock)
    (P : Q.Potential) (ell : ℕ) (q K h : ℝ) : Prop :=
  ∀j : ℕ, j < tailCount h →
    let lo := tailGrid h j
    let hi := tailGrid h (j+1)
    (∫u in lo..hi,
      (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      3*(max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo)*
        (∑t : LocalShiftedMassDyad Q lo hi,
          let v := comparisonSmallMass Q.data.N Q.data.E*
            (2:ℝ)^(t.val.val:ℕ)
          outerTruncatedGroupBudget Q ell q K
            (Q.data.N^(-(30:ℝ))) v)+
        128*(max 1 cu)*(Real.log Q.data.N)^3*
          (C0^3*Q.data.N^(-3*m)*Q.data.E)/
          (Q.data.N^(m/10000))^2

theorem eventually_original_q_outer_five_atom_finite_tail_corrected_c0_draft
    (m cl cu Az C0 K : ℝ)
    (hm : 0 < m) (hmmax : m < 1/300)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hK : 4 ≤ K)
    (ell : ℕ) (hell : 2 < ell)
    (horder : ((m/10000)+(1:ℝ)/3+20*m+1)/
      ((ell:ℝ)-1) ≤ (m/10000)/2)
    (q : ℝ) (hq : 1 ≤ q) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {Ct D Bclock : ℝ}
        (Q : ActualThetaZeroOverlapMinimum (n+1) m (m/10000)
          cl cu Az C0 Ct D Bclock)
        (P : Q.Potential),
        Q.data.E = wallHighError m (n+1) →
        Q.data.d = wallHighD m (n+1) →
        Q.data.s = wallHighMass m (n+1) →
        1/Q.data.N ≤ Q.data.d →
        1 ≤ Real.log Q.data.N →
        comparisonSmallMass Q.data.N Q.data.E ≤ 1 →
        1/Q.data.N ≤ comparisonSmallMass Q.data.N Q.data.E →
        ∀ {h : ℝ},
          0 < h → h ≤ 1 →
          Real.log (1/h) ≤ Real.log Q.data.N →
          2*cu*(Az+1)*Q.xs ≤ h →
          2*Q.data.s < (cl/(4*cu))*h →
          IntervalIntegrable
            (fun u => (P.negativeSet∪P.contactSet).indicator
              (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
                Q.data.thetaZeroErrorDensity Q.lam Q.alpha u)
              volume h 1 →
          OriginalQOuterLocalSourceAtCutCorrectedC0 Q P ell q K h →
          let L := Real.log Q.data.N
          let G := max 1 cu
          let Cprice := outerGroupPriceConstant
            C0 cl Az K q
          let Bband := 24*G*Cprice*L^8*
            Q.data.N^(-(m/10000)/2)*Q.data.E+
            128*G*L^3*(C0^3*Q.data.N^(-3*m)*Q.data.E)/
              (Q.data.N^(m/10000))^2
          (∫u in h..1,
            (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
              (Q.shiftedNativeModel.R u)*
              Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
            (1/Real.log 2+2)*L*Bband := by
  have Hgroup := eventually_outer_truncated_five_atom_group_price_corrected_c0_draft
    m cl cu Az C0 K hm hmmax hcl hcu hAz hC0 hK
      ell hell horder q hq
  filter_upwards [Hgroup] with n hnGroup
  intro Ct D Bclock Q P hE hd hs hnd hL hU1 hUN
    h h0 h1 hlog houter0 hstart0 hfi hphysical
  let L := Real.log Q.data.N
  let G := max 1 cu
  let Cprice := outerGroupPriceConstant
    C0 cl Az K q
  let Bband := 24*G*Cprice*L^8*Q.data.N^(-(m/10000)/2)*Q.data.E+
    128*G*L^3*(C0^3*Q.data.N^(-3*m)*Q.data.E)/
      (Q.data.N^(m/10000))^2
  have hCprice : 0 ≤ Cprice :=
    outerGroupPriceConstant_nonneg
      hC0 hcl hAz hK
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact zero_le_one.trans (le_max_left _ _)
  have hBband : 0 ≤ Bband := by
    dsimp [Bband,L]
    positivity [Q.data.hN, Q.data.hE]
  have hband (j : ℕ)
      (hj : j < tailCount h) :
      let lo := tailGrid h j
      let hi := tailGrid h (j+1)
      (∫u in lo..hi,
        (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ Bband := by
    let lo := tailGrid h j
    let hi := tailGrid h (j+1)
    have hloStart : h ≤ lo :=
      tailGrid_ge_start h0.le h1 j
    have hhiStart : h ≤ hi :=
      tailGrid_ge_start h0.le h1 (j+1)
    have hlo : lo ∈ Ioc (0:ℝ) 1 :=
      ⟨h0.trans_le hloStart,
        tailGrid_le_one h j⟩
    have hhi : hi ∈ Ioc (0:ℝ) 1 :=
      ⟨h0.trans_le hhiStart,
        tailGrid_le_one h (j+1)⟩
    have hwidth : hi ≤ 2*lo :=
      tailGrid_next_le_twice h0.le j
    have houter : 2*cu*(Az+1)*Q.xs ≤ lo :=
      houter0.trans hloStart
    have hratio : 0 ≤ cl/(4*cu) := by positivity
    have hstart : 2*Q.data.s ≤ (cl/(4*cu))*lo :=
      hstart0.le.trans (mul_le_mul_of_nonneg_left hloStart hratio)
    have hprice (t : LocalShiftedMassDyad Q lo hi) :
        let v := comparisonSmallMass Q.data.N Q.data.E*
          (2:ℝ)^(t.val.val:ℕ)
        laplaceComparisonStrength Q.data.d Q.lam v*
          outerTruncatedGroupBudget Q ell q K
            (Q.data.N^(-(30:ℝ))) v ≤
          Cprice*L^7*Q.data.N^(-(m/10000)/2)*Q.data.E := by
      let v := comparisonSmallMass Q.data.N Q.data.E*
        (2:ℝ)^(t.val.val:ℕ)
      have hv := comparison_mass_dyadic_scale Q.data.hU t.val
      have hvI : v ∈ Ioc (0:ℝ) 1 := ⟨hv.1,hv.2.2⟩
      have hgroup : (cl/(4*cu))*lo ≤ v := t.property.1
      simpa only [v,L,Cprice] using hnGroup Q hE hd hs hnd hL
        hvI houter hgroup hstart
    have hlocal := hphysical j hj
    have Hband := Potential.outer_band_error_of_dyadic_prices_draft Q P
      ell q K (Q.data.N^(-(30:ℝ))) Cprice
      hCprice (by linarith : 0 ≤ K) (zero_le_one.trans hq)
      (by positivity : 0 ≤ Q.data.N^(-(30:ℝ)))
      hlo hhi hwidth hL hU1 hUN hprice hlocal
    simpa only [lo,hi,L,G,Cprice,Bband] using Hband
  have Htail :=
    outer_nonpositive_tail_of_band_price_draft
      h0 h1 hL hlog hBband hfi hband
  simpa only [L,G,Cprice,Bband] using Htail

def outerTailPriceConstant (C0 cl cu Az K q : ℝ) : ℝ :=
  24*(1/Real.log 2+2)*(max 1 cu)*outerGroupPriceConstant C0 cl Az K q

def outerTailTravelConstant (C0 cu : ℝ) : ℝ :=
  128*(1/Real.log 2+2)*(max 1 cu)*C0^3

theorem outerTailPriceConstant_nonneg
    {C0 cl cu Az K q : ℝ} (hC0 : 0 < C0) (hcl : 0 < cl)
    (hAz : 0 ≤ Az) (hK : 4 ≤ K) :
    0 ≤ outerTailPriceConstant C0 cl cu Az K q := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hG : 0 ≤ max 1 cu := zero_le_one.trans (le_max_left _ _)
  have hp := outerGroupPriceConstant_nonneg (q:=q) hC0 hcl hAz hK
  unfold outerTailPriceConstant
  positivity

theorem outerTailTravelConstant_nonneg
    {C0 cu : ℝ} (hC0 : 0 < C0) :
    0 ≤ outerTailTravelConstant C0 cu := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hG : 0 ≤ max 1 cu := zero_le_one.trans (le_max_left _ _)
  unfold outerTailTravelConstant
  positivity

theorem eventually_original_q_outer_five_atom_two_rate_tail_corrected_c0
    (m cl cu Az C0 K : ℝ)
    (hm : 0 < m) (hmmax : m < 1/300)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hK : 4 ≤ K)
    (ell : ℕ) (hell : 2 < ell)
    (horder : ((m/10000)+(1:ℝ)/3+20*m+1)/
      ((ell:ℝ)-1) ≤ (m/10000)/2)
    (q : ℝ) (hq : 1 ≤ q) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {Ct D Bclock : ℝ}
        (Q : ActualThetaZeroOverlapMinimum (n+1) m (m/10000)
          cl cu Az C0 Ct D Bclock)
        (P : Q.Potential),
        Q.data.E = wallHighError m (n+1) →
        Q.data.d = wallHighD m (n+1) →
        Q.data.s = wallHighMass m (n+1) →
        1/Q.data.N ≤ Q.data.d →
        1 ≤ Real.log Q.data.N →
        comparisonSmallMass Q.data.N Q.data.E ≤ 1 →
        1/Q.data.N ≤ comparisonSmallMass Q.data.N Q.data.E →
        ∀ {h : ℝ},
          0 < h → h ≤ 1 →
          Real.log (1/h) ≤ Real.log Q.data.N →
          2*cu*(Az+1)*Q.xs ≤ h →
          2*Q.data.s < (cl/(4*cu))*h →
          IntervalIntegrable
            (fun u => (P.negativeSet∪P.contactSet).indicator
              (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
                Q.data.thetaZeroErrorDensity Q.lam Q.alpha u)
              volume h 1 →
          OriginalQOuterLocalSourceAtCutCorrectedC0 Q P ell q K h →
          (∫u in h..1,
            (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
              (Q.shiftedNativeModel.R u)*
              Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
            outerTailPriceConstant C0 cl cu Az K q*(Real.log Q.data.N)^9*
              Q.data.N^(-(m/10000)/2)*Q.data.E+
            outerTailTravelConstant C0 cu*(Real.log Q.data.N)^4*
              Q.data.N^(-3*m-2*(m/10000))*Q.data.E := by
  have Htail := eventually_original_q_outer_five_atom_finite_tail_corrected_c0_draft
    m cl cu Az C0 K hm hmmax hcl hcu hAz hC0 hK ell hell horder q hq
  filter_upwards [Htail] with n hn
  intro Ct D Bclock Q P hE hd hs hnd hL hU1 hUN
    h h0 h1 hlog houter hstart hfi hphysical
  have H := hn Q P hE hd hs hnd hL hU1 hUN h0 h1 hlog houter hstart hfi hphysical
  have hpow : Q.data.N^(-3*m)/(Q.data.N^(m/10000))^2 =
      Q.data.N^(-3*m-2*(m/10000)) := by
    rw [←Real.rpow_mul_natCast Q.data.hN.le, ←Real.rpow_sub Q.data.hN]
    congr 1
    push_cast
    ring
  dsimp only at H
  calc
    _ ≤ _ := H
    _ = _ := by
      unfold outerTailPriceConstant outerTailTravelConstant
      rw [←hpow]
      ring

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
