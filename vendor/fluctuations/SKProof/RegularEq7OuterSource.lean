module

public import SKProof.RegularEq7OuterThermal
public import SKProof.RegularEq7OuterFiveAtomTail

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eq7_regular_tail_index_forces_cut_below_one_draft
    {h : ℝ} (hhi : h ≤ 1) {j : ℕ}
    (hj : j < tailCount h) :
    h < 1 := by
  rcases lt_or_eq_of_le hhi with hh | hh
  · exact hh
  · subst h
    simp [tailCount] at hj

theorem eq7_regular_outer_start_gates_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    {C lo : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (_hAz : 0 ≤ Az)
    (hCouter : 2*cu*(Az+1) ≤ C)
    (hCU : 2*cu/cl ≤ C)
    (hCs : 8*cu/cl < C)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (hcut : min (C*Q.xs) 1 < 1)
    (hlo : min (C*Q.xs) 1 ≤ lo) :
    2*cu*(Az+1)*Q.xs ≤ lo ∧
      comparisonSmallMass Q.data.N Q.data.E ≤
        (cl/(2*cu))*lo ∧
      2*Q.data.s < (cl/(4*cu))*lo := by
  have hCx1 : C*Q.xs < 1 := by
    by_contra hh
    have H : 1 ≤ C*Q.xs := le_of_not_gt hh
    have Hmin : min (C*Q.xs) 1 = 1 := min_eq_right H
    rw [Hmin] at hcut
    exact (lt_irrefl (1:ℝ)) hcut
  have hloCx : C*Q.xs ≤ lo := by
    rw [min_eq_left hCx1.le] at hlo
    exact hlo
  have houter0 := mul_le_mul_of_nonneg_right hCouter Q.hxs.le
  have houter : 2*cu*(Az+1)*Q.xs ≤ lo := by
    nlinarith only [houter0,hloCx]
  have hfac2 : 0 ≤ cl/(2*cu) := by positivity
  have hCUX := mul_le_mul_of_nonneg_right hCU Q.hxs.le
  have hUX : Q.xs ≤ (cl/(2*cu))*(C*Q.xs) := by
    calc
      Q.xs = (cl/(2*cu))*((2*cu/cl)*Q.xs) := by
        field_simp [hcl.ne',hcu.ne']
      _ ≤ (cl/(2*cu))*(C*Q.xs) :=
        mul_le_mul_of_nonneg_left hCUX hfac2
  have hU : comparisonSmallMass Q.data.N Q.data.E ≤
      (cl/(2*cu))*lo :=
    hUA.trans (hUX.trans
      (mul_le_mul_of_nonneg_left hloCx hfac2))
  have hfac4 : 0 < cl/(4*cu) := by positivity
  have hCsX := mul_lt_mul_of_pos_right hCs Q.hxs
  have hsX : 2*Q.data.s ≤ 2*Q.xs := by
    linarith only [Q.hsxs]
  have hstartX : 2*Q.xs < (cl/(4*cu))*(C*Q.xs) := by
    calc
      2*Q.xs = (cl/(4*cu))*((8*cu/cl)*Q.xs) := by
        field_simp [hcl.ne',hcu.ne']
        ring
      _ < (cl/(4*cu))*(C*Q.xs) :=
        mul_lt_mul_of_pos_left hCsX hfac4
  have hstart : 2*Q.data.s < (cl/(4*cu))*lo :=
    hsX.trans_lt (hstartX.trans_le
      (mul_le_mul_of_nonneg_left hloCx hfac4.le))
  exact ⟨houter,hU,hstart⟩

theorem eq7_regular_outer_tail_band_gates_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    {C : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC : 24 ≤ C)
    (hCouter : 2*cu*(Az+1) ≤ C)
    (hCU : 2*cu/cl ≤ C)
    (hCs : 8*cu/cl < C)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (j : ℕ)
    (hj : j < tailCount
      (min (C*Q.xs) 1)) :
    let h := min (C*Q.xs) 1
    let lo := tailGrid h j
    let hi := tailGrid h (j+1)
    lo ∈ Icc Q.data.s 1 ∧ hi ∈ Icc Q.data.s 1 ∧
      lo ≤ hi ∧ hi-lo ≤ lo ∧
      2*cu*(Az+1)*Q.xs ≤ lo ∧
      comparisonSmallMass Q.data.N Q.data.E ≤ (cl/(2*cu))*lo ∧
      2*Q.data.s < (cl/(4*cu))*lo := by
  let h := min (C*Q.xs) 1
  let lo := tailGrid h j
  let hi := tailGrid h (j+1)
  have hh0 : 0 ≤ h := by
    have hC0 : 0 < C := by linarith only [hC]
    exact (lt_min (mul_pos hC0 Q.hxs) zero_lt_one).le
  have hh1 : h ≤ 1 := min_le_right _ _
  have hcut : h < 1 :=
    eq7_regular_tail_index_forces_cut_below_one_draft hh1 hj
  have hhS : Q.data.s ≤ h := by
    apply le_min _ Q.data.hs1
    have hC1 : 1 ≤ C := by linarith only [hC]
    exact Q.hsxs.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 Q.hxs.le)
  have hloH : h ≤ lo :=
    tailGrid_ge_start hh0 hh1 j
  have hlo1 : lo ≤ 1 :=
    tailGrid_le_one h j
  have hhi1 : hi ≤ 1 :=
    tailGrid_le_one h (j+1)
  have hlohi : lo ≤ hi :=
    tailGrid_mono hh0 j
  have hwidth : hi-lo ≤ lo := by
    have H := tailGrid_next_le_twice hh0 j
    change hi ≤ 2*lo at H
    linarith only [H]
  obtain ⟨houter,hU,hstart⟩ := eq7_regular_outer_start_gates_draft Q
    hcl hcu hAz hCouter hCU hCs hUA hcut hloH
  exact ⟨⟨hhS.trans hloH,hlo1⟩,
    ⟨hhS.trans (hloH.trans hlohi),hhi1⟩,
    hlohi,hwidth,houter,hU,hstart⟩

theorem exists_outer_local_source_at_fixed_cut_from_localized_draft
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    {m cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    {K : ℝ} (hK : 4 ≤ K) (hKcap : 4*cu/cl ≤ K) :
    ∃q : ℝ, 1 ≤ q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum
          (n+1) m (m/10000) cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) {h : ℝ},
        0 < h → h ≤ 1 →
        Q.data.s ≤ h →
        1/Q.data.N ≤ Q.data.d →
        1 ≤ Real.log Q.data.N →
        Q.cavityCapTravel ≤ Q.xs →
        2*cu*(Az+1)*Q.xs ≤ h →
        comparisonSmallMass Q.data.N Q.data.E ≤ (cl/(2*cu))*h →
        2*Q.data.s < (cl/(4*cu))*h →
        OriginalQOuterLocalSourceAtCutCorrectedC0 Q P ell q K h := by
  obtain ⟨q,hq,Hsource⟩ :=
    eventually_original_q_outer_localized_nonpositive_budget_draft
      ell hell Bclock (D:=D) hm
      (by positivity : 0 < m/10000)
      (by linarith [hm] : m/10000 < 3*m)
      hcl hcu hAz hC0 hCt
  refine ⟨q,hq,?_⟩
  filter_upwards [Hsource,eventually_ge_atTop (1:ℕ)] with n hnSource hn1
  intro Q P h h0 h1 hs hnd hL htravel houter0 hU0 hstart0 j hj
  let lo := tailGrid h j
  let hi := tailGrid h (j+1)
  have hloStart : h ≤ lo :=
    tailGrid_ge_start h0.le h1 j
  have hhiStart : h ≤ hi :=
    tailGrid_ge_start h0.le h1 (j+1)
  have hlo : lo ∈ Icc Q.data.s 1 :=
    ⟨hs.trans hloStart,
      tailGrid_le_one h j⟩
  have hhi : hi ∈ Icc Q.data.s 1 :=
    ⟨hs.trans hhiStart,
      tailGrid_le_one h (j+1)⟩
  have hlohi : lo ≤ hi :=
    tailGrid_mono h0.le j
  have hwidth : hi-lo ≤ (1:ℝ)*lo := by
    have H := tailGrid_next_le_twice
      h0.le j
    dsimp only [lo,hi] at H ⊢
    linarith only [H]
  have houter : 2*cu*(Az+1)*Q.xs ≤ lo :=
    houter0.trans hloStart
  have hratioU : 0 ≤ cl/(2*cu) := by positivity
  have hU : comparisonSmallMass Q.data.N Q.data.E ≤
      (cl/(2*cu))*lo :=
    hU0.trans (mul_le_mul_of_nonneg_left hloStart hratioU)
  have hratioS : 0 ≤ cl/(4*cu) := by positivity
  have hstart : 2*Q.data.s < (cl/(4*cu))*lo :=
    hstart0.trans_le (mul_le_mul_of_nonneg_left hloStart hratioS)
  have hN2 : 2 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ hn1
  have hLside : 0 ≤ 30*Real.log Q.data.N := by linarith only [hL]
  have hcut : 0 < Q.data.N^(-(30:ℝ)) :=
    Real.rpow_pos_of_pos Q.data.hN _
  have hlogcut : Real.log (1/Q.data.N^(-(30:ℝ))) ≤
      30*Real.log Q.data.N := by
    rw [one_div,Real.log_inv,Real.log_rpow Q.data.hN]
    nlinarith
  have H := hnSource Q P lo hi K 1
    (30*Real.log Q.data.N) (Q.data.N^(-(30:ℝ)))
    hN2 hnd hL hlo hhi hlohi (by norm_num) hwidth
    htravel houter hU hstart hK hKcap hLside hcut hlogcut
  simpa only [OriginalQOuterLocalSourceAtCutCorrectedC0,
    outerTruncatedGroupBudget,one_mul,mul_one,lo,hi] using H

theorem outer_nonpositive_integral_at_one_eq_zero
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (P : Q.Potential) :
    (∫u in (1:ℝ)..1,
      (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) = 0 := by
  exact intervalIntegral.integral_same

private theorem eventually_cap_travel_le_small_mass
    (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {Ct D Bclock : ℝ}
        (Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock),
        Q.cavityCapTravel ≤ comparisonSmallMass Q.data.N Q.data.E := by
  have Hlog : ∀ᶠ n : ℕ in atTop,
      2*Real.log ((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ)^delta := by
    have H := (tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 1)).eventually
        (comparison_log_loss_eventually (C:=2) (p:=1) (by norm_num) hdelta)
    simpa only [Real.rpow_one,Function.comp_def] using H
  filter_upwards [Hlog,eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro Ct D Bclock Q
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
    _ = comparisonSmallMass Q.data.N Q.data.E := by
      field_simp [hp.ne']

theorem exists_regular_outer_local_source_at_cut
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    {m cl cu Az C0 Ct D C K : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 24 ≤ C)
    (hCouter : 2*cu*(Az+1) ≤ C)
    (hCU : 2*cu/cl ≤ C) (hCs : 8*cu/cl < C)
    (hK : 4 ≤ K) (hKcap : 4*cu/cl ≤ K) :
    ∃q : ℝ, 1 ≤ q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum
          (n+1) m (m/10000) cl cu Az C0 Ct D Bclock)
        (P : Q.Potential),
        comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs →
        1/Q.data.N ≤ Q.data.d →
        1 ≤ Real.log Q.data.N →
        OriginalQOuterLocalSourceAtCutCorrectedC0 Q P ell q K
          (min (C*Q.xs) 1) := by
  obtain ⟨q,hq,Hsource⟩ :=
    exists_outer_local_source_at_fixed_cut_from_localized_draft
      ell hell Bclock (D:=D) hm hcl hcu hAz hC0 hCt hK hKcap
  have Htravel := eventually_cap_travel_le_small_mass
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0)
    (show 0 < m/10000 by positivity)
  refine ⟨q,hq,?_⟩
  filter_upwards [Hsource,Htravel] with n hnSource hnTravel
  intro Q P hUA hnd hL
  let h := min (C*Q.xs) 1
  have hCpos : 0 < C := by linarith only [hC]
  have h0 : 0 < h := lt_min (mul_pos hCpos Q.hxs) zero_lt_one
  have h1 : h ≤ 1 := min_le_right _ _
  by_cases hterminal : h = 1
  · have hzero := outer_nonpositive_integral_at_one_eq_zero Q P
    have hzeroAtCut :
        (∫u in h..1,
          (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
            (Q.shiftedNativeModel.R u)*
              Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) = 0 := by
      simpa only [hterminal] using hzero
    have _ := hzeroAtCut
    simp only [show min (C*Q.xs) 1 = 1 from hterminal,
      OriginalQOuterLocalSourceAtCutCorrectedC0,tailCount]
    norm_num
  · have hcut : h < 1 := lt_of_le_of_ne h1 hterminal
    have hs : Q.data.s ≤ h := by
      apply le_min _ Q.data.hs1
      have hC1 : 1 ≤ C := by linarith only [hC]
      exact Q.hsxs.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 Q.hxs.le)
    obtain ⟨houter,hU,hstart⟩ := eq7_regular_outer_start_gates_draft Q
      hcl hcu hAz hCouter hCU hCs hUA hcut (le_refl h)
    exact hnSource Q P h0 h1 hs hnd hL
      ((hnTravel Q).trans hUA) houter hU hstart

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
