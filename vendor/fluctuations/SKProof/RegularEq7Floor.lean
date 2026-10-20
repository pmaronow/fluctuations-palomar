module

public import SKProof.RegularEq7FloorPointwise
public import SKProof.RegularEq7TailGrid
public import ComparisonActualQIntermediateDyadCountDirectDraft
public import ComparisonOriginalQEq7FloorRestrictionCoreDraft
public import ComparisonActualHighWallThetaZeroEq7FiniteMaskGeometry
public import ComparisonActualHighWallThetaZeroSmallMassScale
public import ComparisonConditionalOptimizedSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

def floorErrorAt (P : Q.Potential) (u : ℝ) : ℝ :=
  P.positiveSet.indicator (fun _ => (1:ℝ))
    (Q.shiftedNativeModel.R u)*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u

theorem floor_cut_basic_gates_draft {C : ℝ}
    (hC : 1 ≤ C) (houter : cu*Az < C) :
    Q.data.s ≤ min (C*Q.xs) 1 ∧
      cu*Az*Q.xs < C*Q.xs := by
  have hxsC : Q.xs ≤ C*Q.xs := by
    have H := mul_nonneg (sub_nonneg.mpr hC) Q.hxs.le
    nlinarith only [H]
  exact ⟨le_min (Q.hsxs.trans hxsC) Q.data.hs1,
    mul_lt_mul_of_pos_right houter Q.hxs⟩

theorem floor_tail_log_cut_of_regular_carrier_draft
    (hN : 1 ≤ Q.data.N) {C : ℝ} (hC : 1 ≤ C)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs) :
    Real.log (1/(C*Q.xs)) ≤ Real.log Q.data.N := by
  have hcx0 : 0 < C*Q.xs :=
    mul_pos (lt_of_lt_of_le zero_lt_one hC) Q.hxs
  have hxsC : Q.xs ≤ C*Q.xs := by
    have H := mul_nonneg (sub_nonneg.mpr hC) Q.hxs.le
    nlinarith only [H]
  have hUcx : comparisonSmallMass Q.data.N Q.data.E ≤ C*Q.xs :=
    hUA.trans hxsC
  have hInv := one_div_le_one_div_of_le Q.data.hU hUcx
  exact Real.log_le_log (one_div_pos.mpr hcx0)
    (hInv.trans (Q.intermediate_mass_inverse_small_le hN))

theorem eq7_full_positive_floor_error_raw_draft
    (P : Q.Potential)
    (hN : 1 ≤ Q.data.N) (hnd : 1/Q.data.N ≤ Q.data.d)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    {K C h : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hB : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) Q.sweepBf Q.sweepHf u ≤ K*(Q.xs+u)^2)
    (hcarrier : Q.xs = comparisonConditionalScale
      Q.data.N delta Q.data.E Q.lam)
    (hh : h = C*Q.xs) (hsh : Q.data.s ≤ h)
    (h0 : 0 < h) (h1 : h ≤ 1)
    (houter : cu*Az*Q.xs < h)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hlogCut : Real.log (1/h) ≤ Real.log Q.data.N) :
    (∫u in Q.data.s..1, floorErrorAt P u) ≤
      (K+(Az+1/cl)^2)*(1+C)^2*Q.data.N^delta*Q.data.E+
      (1/Real.log 2+2)*Real.log Q.data.N*
        ((cu*(1/C+2))^2*(K+(Az+1/cl)^2)*
          (1+Real.log Q.data.N)*Q.data.N^delta*
            (C0^3*Q.data.N^(-3*m)*Q.data.E)) := by
  let z := tailGrid h
  let J := tailCount h
  let B := (cu*(1/C+2))^2*(K+(Az+1/cl)^2)*
    (1+Real.log Q.data.N)*Q.data.N^delta*
      (C0^3*Q.data.N^(-3*m)*Q.data.E)
  have hC0le : 0 ≤ C := hC.le
  have hInner := positive_floor_inner_error_on_carrier P
    hcl hAz hK hC0le hB hcarrier hsh h1 (by rw [hh])
  have hfloorInt := Q.error_mask_intervalIntegrable
    P.positiveSet P.positiveSet_measurable
  have hOuterInt : IntervalIntegrable (floorErrorAt P) volume h 1 := by
    apply hfloorInt.mono_set
    rw [uIcc_of_le h1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc h0.le le_rfl
  have hInnerInt : IntervalIntegrable (floorErrorAt P) volume Q.data.s h := by
    apply hfloorInt.mono_set
    rw [uIcc_of_le hsh,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc Q.data.hs.1.le h1
  have hBand : ∀j : ℕ, j < J →
      (∫u in z j..z (j+1),floorErrorAt P u) ≤ B := by
    intro j hj
    have hzl : h ≤ z j :=
      tailGrid_ge_start h0.le h1 j
    have hzu : z (j+1) ≤ 1 :=
      tailGrid_le_one h (j+1)
    have hzOrder : z j ≤ z (j+1) :=
      tailGrid_mono h0.le j
    have hzTwo : z (j+1) ≤ 2*z j :=
      tailGrid_next_le_twice h0.le j
    have houter' : cu*Az*Q.xs < z j := houter.trans_le hzl
    have hBandStart : C*Q.xs ≤ z j := by rw [←hh];exact hzl
    have hSrc := eq7_outer_positive_floor_error_rate P
      hN hnd hC0 hcl hcu hAz hK hC (by norm_num : (0:ℝ) ≤ 2)
      hB (hsh.trans hzl) hzOrder hzu houter' hBandStart hzTwo
    simpa only [floorErrorAt,B,z] using hSrc
  have hTail := tail_integral_le_of_uniform_bands
    h0 h1 hOuterInt hBand
  have hCount := tailCount_le_log
    h0 h1 hlog hlogCut
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hL : 0 ≤ Real.log Q.data.N := by linarith
    positivity [Q.data.hN.le, Q.data.hE.le]
  have hTailCount : (∫u in h..1,floorErrorAt P u) ≤
      (1/Real.log 2+2)*Real.log Q.data.N*B :=
    hTail.trans (mul_le_mul_of_nonneg_right hCount hB0)
  have hAdd := intervalIntegral.integral_add_adjacent_intervals
    hInnerInt hOuterInt
  change (∫u in Q.data.s..1,floorErrorAt P u) ≤ _
  rw [←hAdd]
  dsimp only [floorErrorAt] at hTailCount ⊢
  dsimp only [B] at hTailCount
  linarith only [hInner,hTailCount]

theorem eq7_full_positive_floor_error_split_draft
    (P : Q.Potential)
    (hN : 1 ≤ Q.data.N) (hnd : 1/Q.data.N ≤ Q.data.d)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hB : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) Q.sweepBf Q.sweepHf u ≤ K*(Q.xs+u)^2)
    (hcarrier : Q.xs = comparisonConditionalScale
      Q.data.N delta Q.data.E Q.lam)
    (hsh : Q.data.s ≤ min (C*Q.xs) 1)
    (houter : cu*Az*Q.xs < C*Q.xs)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hlogCut : C*Q.xs < 1 →
      Real.log (1/(C*Q.xs)) ≤ Real.log Q.data.N) :
    (∫u in Q.data.s..1, floorErrorAt P u) ≤
      (K+(Az+1/cl)^2)*(1+C)^2*Q.data.N^delta*Q.data.E+
      (1/Real.log 2+2)*Real.log Q.data.N*
        ((cu*(1/C+2))^2*(K+(Az+1/cl)^2)*
          (1+Real.log Q.data.N)*Q.data.N^delta*
            (C0^3*Q.data.N^(-3*m)*Q.data.E)) := by
  by_cases hCA : C*Q.xs < 1
  · have hcut : min (C*Q.xs) 1 = C*Q.xs := min_eq_left hCA.le
    have hs : Q.data.s ≤ C*Q.xs := hcut ▸ hsh
    have hpos : 0 < C*Q.xs := mul_pos hC Q.hxs
    exact eq7_full_positive_floor_error_raw_draft P hN hnd hcl hcu
      hAz hC0 hK hC hB hcarrier rfl hs hpos hCA.le houter
      hlog (hlogCut hCA)
  · have hCA' : 1 ≤ C*Q.xs := le_of_not_gt hCA
    have hinner := positive_floor_inner_error_on_carrier P
      hcl hAz hK hC.le hB hcarrier Q.data.hs1 le_rfl hCA'
    have hTailNonneg : 0 ≤
        (1/Real.log 2+2)*Real.log Q.data.N*
          ((cu*(1/C+2))^2*(K+(Az+1/cl)^2)*
            (1+Real.log Q.data.N)*Q.data.N^delta*
              (C0^3*Q.data.N^(-3*m)*Q.data.E)) := by
      have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
      have hF : 0 ≤ K+(Az+1/cl)^2 :=
        add_nonneg hK (sq_nonneg _)
      positivity [Q.data.hN.le, Q.data.hE.le]
    dsimp only [floorErrorAt] at hinner ⊢
    linarith only [hinner,hTailNonneg]

theorem eq7_full_positive_floor_fixed_rate_draft
    (P : Q.Potential) {K C : ℝ}
    (hRaw : (∫u in Q.data.s..1,floorErrorAt P u) ≤
      (K+(Az+1/cl)^2)*(1+C)^2*Q.data.N^delta*Q.data.E+
      (1/Real.log 2+2)*Real.log Q.data.N*
        ((cu*(1/C+2))^2*(K+(Az+1/cl)^2)*
          (1+Real.log Q.data.N)*Q.data.N^delta*
            (C0^3*Q.data.N^(-3*m)*Q.data.E)))
    (hK : 0 ≤ K) (hC0 : 0 < C0)
    (_hlog : 1 ≤ Real.log Q.data.N)
    (habsorb : (1/Real.log 2+2)*Real.log Q.data.N*
      (1+Real.log Q.data.N)*Q.data.N^(-3*m) ≤ 1) :
    (∫u in Q.data.s..1,floorErrorAt P u) ≤
      (K+(Az+1/cl)^2)*
        ((1+C)^2+(cu*(1/C+2))^2*C0^3)*
          Q.data.N^delta*Q.data.E := by
  let A := (K+(Az+1/cl)^2)*(1+C)^2
  let H := (cu*(1/C+2))^2*(K+(Az+1/cl)^2)*C0^3
  let R := Q.data.N^delta*Q.data.E
  let L := Real.log Q.data.N
  let G := (1/Real.log 2+2)*L*(1+L)*Q.data.N^(-3*m)
  have hF : 0 ≤ K+(Az+1/cl)^2 := add_nonneg hK (sq_nonneg _)
  have hH : 0 ≤ H := by dsimp [H]; positivity [Q.data.hN.le, Q.data.hE.le]
  have hR : 0 ≤ R := by dsimp [R]; positivity [Q.data.hN.le, Q.data.hE.le]
  have hG : G ≤ 1 := habsorb
  have hscaled : G*(H*R) ≤ H*R := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hG (mul_nonneg hH hR))
  calc
    (∫u in Q.data.s..1,floorErrorAt P u) ≤ A*R+G*(H*R) := by
      convert hRaw using 1
      dsimp [A,H,R,L,G]
      ring
    _ ≤ A*R+H*R := add_le_add_right hscaled _
    _ = (K+(Az+1/cl)^2)*
          ((1+C)^2+(cu*(1/C+2))^2*C0^3)*
            Q.data.N^delta*Q.data.E := by dsimp [A,H,R]; ring

theorem eq7_full_positive_floor_post_prefix
    (P : Q.Potential) {B : ℝ}
    (hFloor : (∫u in Q.data.s..1,
      P.positiveSet.indicator (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ B) :
    (∫u in Q.eq7InnerPrefixEnd..1,
      P.positiveSet.indicator (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ B := by
  exact (P.eq7_positive_full_floor_restrict_core
    Q.eq7_inner_s_le_prefix_end Q.eq7_inner_prefix_end_le_one le_rfl).trans hFloor

private theorem eventually_floor_log_absorption {m : ℝ} (hm : 0 < m) :
    ∀ᶠ N : ℝ in atTop,
      1 ≤ Real.log N ∧
      (1/Real.log 2+2)*Real.log N*(1+Real.log N)*N^(-3*m) ≤ 1 := by
  let G : ℝ := 1/Real.log 2+2
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have H := comparison_log_loss_eventually (C:=2*G) (p:=2)
    (by positivity) (show 0 < 3*m by positivity)
  filter_upwards [H, Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (0:ℝ)] with N hpow hlog hN
  refine ⟨hlog, ?_⟩
  rw [Real.rpow_two] at hpow
  have hshape : G*Real.log N*(1+Real.log N) ≤ 2*G*(Real.log N)^2 := by
    have hL : 0 ≤ Real.log N := zero_le_one.trans hlog
    have Hprod := mul_nonneg (mul_nonneg hG hL) (sub_nonneg.mpr hlog)
    nlinarith only [Hprod]
  have Hscaled := mul_le_mul_of_nonneg_right (hshape.trans hpow)
    (Real.rpow_nonneg hN.le (-3*m))
  have hcancel : N^(3*m)*N^(-3*m) = 1 := by
    rw [←Real.rpow_add hN, show 3*m + -3*m = (0:ℝ) by ring, Real.rpow_zero]
  simpa only [hcancel] using Hscaled

theorem eventually_full_floor_on_carrier
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Kf : ℝ, 0 < Kf ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock) (P : Q.Potential),
        Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam →
        (∫u in Q.data.s..1,
          P.positiveSet.indicator (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
            Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
          Kf*Q.data.N^delta*Q.data.E := by
  obtain ⟨K, hK, HB⟩ := eventually_actual_theta_zero_selected_B_normalized
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C : ℝ := max 1 (cu*Az+1)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have houter : cu*Az < C := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  let Kf : ℝ := (K+(Az+1/cl)^2)*
    ((1+C)^2+(cu*(1/C+2))^2*C0^3)
  have hKf : 0 < Kf := by
    have hF : 0 < K+(Az+1/cl)^2 := add_pos_of_pos_of_nonneg hK (sq_nonneg _)
    have hCsq : 0 < (1+C)^2 := sq_pos_of_pos (by positivity)
    dsimp only [Kf]
    positivity
  have Hsmall := ActualThetaZeroOverlapMinimum.eventually_small_mass_le_xs
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    (Bclock:=Bclock) hm hC0
  have Hdepth := (tendsto_add_atTop_nat 1).eventually
    (eventually_comparisonLowerScale_depth hC0 hm)
  have HN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hlog := HN.eventually (eventually_floor_log_absorption hm)
  refine ⟨Kf, hKf, ?_⟩
  filter_upwards [HB, Hsmall, Hdepth, Hlog] with n hnB hnSmall hnDepth hnLog
  intro Q P hcarrier
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_pos n
  have hnd : 1/Q.data.N ≤ Q.data.d := by
    have HD := hnDepth Q.data.E Q.data.d Q.data.hE Q.data.hd Q.hlower
    have HS : comparisonLowerScale Q.data.N Q.data.E Q.data.d ≤ Q.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ Q.data.hd).mpr (by simpa only [pow_two] using Q.hupper)
    exact HD.trans HS
  have hlog : 1 ≤ Real.log Q.data.N := hnLog.1
  have habsorb : (1/Real.log 2+2)*Real.log Q.data.N*
      (1+Real.log Q.data.N)*Q.data.N^(-3*m) ≤ 1 := hnLog.2
  have hgates := floor_cut_basic_gates_draft (Q:=Q) hC1 houter
  have hcut := floor_tail_log_cut_of_regular_carrier_draft
    (Q:=Q) hN hC1 (hnSmall Q)
  have hraw := eq7_full_positive_floor_error_split_draft P hN hnd
    hcl hcu hAz hC0 hK.le hC (hnB Q) hcarrier hgates.1 hgates.2
    hlog (fun _ => hcut)
  exact eq7_full_positive_floor_fixed_rate_draft P hraw hK.le hC0 hlog habsorb

theorem eventually_regular_full_floor
    (Bclock : ℝ) {m delta cl cu C0 D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC0 : 0 < C0) :
    ∃ Kf : ℝ, 0 < Kf ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu 2 C0 1 D Bclock) (P : Q.Potential),
        Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam →
        Q.xs < 1 → Q.z = min (2*Q.xs) 1 →
        (∫u in Q.data.s..1,
          P.positiveSet.indicator (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
            Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
          Kf*Q.data.N^delta*Q.data.E := by
  obtain ⟨Kf, hKf, H⟩ := eventually_full_floor_on_carrier
    (Az:=2) (Ct:=1) (D:=D) Bclock hm hdelta hroom hcl hcu
    (by norm_num) hC0 (by norm_num)
  refine ⟨Kf, hKf, ?_⟩
  filter_upwards [H] with n hn Q P hcarrier _hregular _hz
  exact hn Q P hcarrier

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
