module

public import SKProof.RegularEq7OuterGeometry
public import SKProof.RegularEq7TailGrid
public import ComparisonPhysicalDyadicSum
public import ComparisonActualHighWallThetaZeroDyadicThermalAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem outer_truncated_ordinary_budget_nonneg_draft
    (ell : ℕ) {Qraw K cut v : ℝ}
    (hQraw : 0 ≤ Qraw) (hK : 0 ≤ K)
    (hcut : 0 ≤ cut) (hv : v ∈ Ioc (0:ℝ) 1)
    (_hL : 0 ≤ Real.log Q.data.N) :
    0 ≤ Q.ordinaryOptimizedBudget ell Qraw K
      (30*Real.log Q.data.N) cut (K*v) (v/2)
      (Q.xs+min (K*v) 1) v K
      (Q.shiftedNativeModel.R (min (K*v) 1)) := by
  have hv0 : 0 < v := hv.1
  have hM : 0 ≤ K*v := mul_nonneg hK hv0.le
  have hrho : 0 < v/2 := by positivity
  have hz : 0 ≤ min (K*v) 1 := le_min hM (by norm_num)
  have hy : 0 ≤ Q.xs+min (K*v) 1 := add_nonneg Q.hxs.le hz
  have hP : 0 < Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
      (Q.shiftedNativeModel.R (min (K*v) 1)) :=
    mul_pos Q.data.hN (laplaceComparisonStrength_pos Q.data.d Q.hlam _)
  have hdiam : 0 ≤ Q.localCapDiameter v K := by
    unfold localCapDiameter
    positivity [Q.data.hN, Q.data.hd, Q.data.hE]
  have hF : 0 ≤ nativeBinScaleLoss (30*Real.log Q.data.N)
      (108*K^2*(Real.log Q.data.N)^2)
      (54*K^2*(Real.log Q.data.N)^2) (K*v) (v/2) := by
    unfold nativeBinScaleLoss
    positivity
  unfold ordinaryOptimizedBudget
  positivity

theorem outer_truncated_budget_of_five_atom_rates_draft
    (ell : ℕ) {Qraw K cut Cv Ct Cd Cr Ccut : ℝ}
    (hK : 4 ≤ K) (hL : 1 ≤ Real.log Q.data.N)
    (_hCv : 0 ≤ Cv) (_hCt : 0 ≤ Ct) (_hCd : 0 ≤ Cd)
    (_hCr : 0 ≤ Cr) (hCcut : 0 ≤ Ccut)
    {v : ℝ} (hv : v ∈ Ioc (0:ℝ) 1)
    (hvar :
      let z := min (K*v) 1
      let e := laplaceComparisonStrength Q.data.d Q.lam v
      let P := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
        (Q.shiftedNativeModel.R z)
      let M := K*v
      e*M*(2*((Qraw^2*(Q.xs+z))/(P*M^2))^((2:ℝ)/3)) ≤
        Cv*(Real.log Q.data.N)^3*Q.data.N^(-delta/2)*Q.data.E)
    (htrace :
      let z := min (K*v) 1
      let e := laplaceComparisonStrength Q.data.d Q.lam v
      let P := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
        (Q.shiftedNativeModel.R z)
      let M := K*v
      e*M*(3/(P*M^2)) ≤
        Ct*(Real.log Q.data.N)^3*Q.data.N^(-delta/2)*Q.data.E)
    (hdiam :
      let e := laplaceComparisonStrength Q.data.d Q.lam v
      let M := K*v
      e*M*(Q.localCapDiameter v K)^2 ≤
        Cd*(Real.log Q.data.N)^3*Q.data.N^(-delta/2)*Q.data.E)
    (hreverse :
      let z := min (K*v) 1
      let e := laplaceComparisonStrength Q.data.d Q.lam v
      let M := K*v
      let diam := Q.localCapDiameter v K
      e*M*(diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*Qraw)^(2*ell)*(Q.xs+z)^ell)^(
          1/((ell:ℝ)-1))) ≤
        Cr*(Real.log Q.data.N)^3*Q.data.N^(-delta/2)*Q.data.E)
    (hcut :
      let z := min (K*v) 1
      let e := laplaceComparisonStrength Q.data.d Q.lam v
      let P := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
        (Q.shiftedNativeModel.R z)
      let M := K*v
      e*18*(((Qraw^2*(Q.xs+z))^2*P*M^2)^((1:ℝ)/3)+2)*cut ≤
        Ccut*Q.data.N^(-delta/2)*Q.data.E) :
    laplaceComparisonStrength Q.data.d Q.lam v*
      Q.ordinaryOptimizedBudget ell Qraw K
        (30*Real.log Q.data.N) cut (K*v) (v/2)
        (Q.xs+min (K*v) 1) v K
        (Q.shiftedNativeModel.R (min (K*v) 1)) ≤
      (binConstant K*
          (Cv+Ct+Cd+Cr)+Ccut)*
        (Real.log Q.data.N)^7*Q.data.N^(-delta/2)*Q.data.E := by
  let L := Real.log Q.data.N
  let z := min (K*v) 1
  let e := laplaceComparisonStrength Q.data.d Q.lam v
  let P := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
    (Q.shiftedNativeModel.R z)
  let M := K*v
  let diam := Q.localCapDiameter v K
  let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Qraw)^(2*ell)*(Q.xs+z)^ell)^(1/((ell:ℝ)-1))
  let F := nativeBinScaleLoss (30*L) (108*K^2*L^2)
    (54*K^2*L^2) M (v/2)
  let rate := Q.data.N^(-delta/2)*Q.data.E
  let X := e*M*(2*((Qraw^2*(Q.xs+z))/(P*M^2))^((2:ℝ)/3))+
    e*M*(3/(P*M^2))+e*M*diam^2+e*M*rev
  have hF : F ≤ binConstant K*L^4 :=
    truncated_bin_loss_le_log_four hL hK hv.1
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hv0 : 0 < v := hv.1
  have he0 : 0 ≤ e := (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
  have hM0 : 0 ≤ M := mul_nonneg hK0 hv0.le
  have hz0 : 0 ≤ z := le_min hM0 zero_le_one
  have hy0 : 0 ≤ Q.xs+z := add_nonneg Q.hxs.le hz0
  have hP0 : 0 < P :=
    mul_pos Q.data.hN (laplaceComparisonStrength_pos Q.data.d Q.hlam _)
  have hdiam0 : 0 ≤ diam := by
    dsimp only [diam, localCapDiameter]
    positivity [Q.data.hN, Q.data.hd, Q.data.hE]
  have heven : 0 ≤ (2*Qraw)^(2*ell) := by
    rw [Nat.mul_comm 2 ell, pow_mul]
    exact sq_nonneg _
  have hrev0 : 0 ≤ rev := by
    dsimp only [rev]
    exact mul_nonneg (Real.rpow_nonneg hdiam0 _)
      (Real.rpow_nonneg (mul_nonneg heven (pow_nonneg hy0 ell)) _)
  have hX0 : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hX : X ≤ (Cv+Ct+Cd+Cr)*L^3*rate := by
    dsimp [X,L,rate,z,e,P,M,diam,rev] at *
    linarith only [hvar,htrace,hdiam,hreverse]
  have hB : 0 ≤ binConstant K :=
    binConstant_nonneg (by linarith)
  have hL7 : 1 ≤ L^7 := one_le_pow₀ hL
  have hrate : 0 ≤ rate := by dsimp only [rate]; positivity [Q.data.hN, Q.data.hE]
  have hXscaled := mul_le_mul_of_nonneg_left hX
    (show 0 ≤ binConstant K*L^4 by positivity)
  have hFscaled := mul_le_mul_of_nonneg_right hF hX0
  have hcutScaled : Ccut*rate ≤ Ccut*L^7*rate := by
    have H := mul_le_mul_of_nonneg_left hL7 (mul_nonneg hCcut hrate)
    nlinarith only [H]
  have hEq :
      e*Q.ordinaryOptimizedBudget ell Qraw K (30*L) cut M (v/2)
        (Q.xs+z) v K (Q.shiftedNativeModel.R z) =
        F*X+e*18*(((Qraw^2*(Q.xs+z))^2*P*M^2)^((1:ℝ)/3)+2)*cut := by
    dsimp [X,F,P,M,z,e,diam,rev,L]
    unfold ordinaryOptimizedBudget
    ring
  rw [hEq]
  dsimp only [L,rate,z,e,P,M] at hcut ⊢
  nlinarith only [hFscaled,hXscaled,hcut,hcutScaled]

def outerTruncatedGroupBudget
    (ell : ℕ) (Qraw K cut v : ℝ) : ℝ :=
  let z := min (K*v) 1
  Q.ordinaryOptimizedBudget ell Qraw K
    (30*Real.log Q.data.N) cut (K*v) (v/2)
    (Q.xs+z) v K (Q.shiftedNativeModel.R z)

theorem outer_local_dyad_card_le_four_log_draft
    {lo hi : ℝ} (hL : 1 ≤ Real.log Q.data.N)
    (hU1 : comparisonSmallMass Q.data.N Q.data.E ≤ 1)
    (hUN : 1/Q.data.N ≤ comparisonSmallMass Q.data.N Q.data.E) :
    (Fintype.card (LocalShiftedMassDyad Q lo hi):ℝ) ≤
      4*Real.log Q.data.N := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  let L := Real.log Q.data.N
  let t := Real.log (1/U)/Real.log 2
  have hU : 0 < U := Q.data.hU
  have hN : 0 < Q.data.N := Q.data.hN
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at H
    exact H
  have hInv : 1/U ≤ Q.data.N := by
    apply (div_le_iff₀ hU).mpr
    have H := (div_le_iff₀ hN).mp hUN
    nlinarith only [H]
  have hlogU : Real.log (1/U) ≤ L :=
    Real.log_le_log (one_div_pos.mpr hU) hInv
  have hlogU0 : 0 ≤ Real.log (1/U) := by
    have H : 1 ≤ 1/U := (one_le_div hU).mpr hU1
    exact Real.log_nonneg H
  have ht0 : 0 ≤ t := div_nonneg hlogU0 hlog2.le
  have ht : t ≤ 2*L := by
    have H1 := mul_le_mul_of_nonneg_left hlog2half
      (by linarith : 0 ≤ 2*L)
    apply (div_le_iff₀ hlog2).mpr
    nlinarith only [hlogU,H1]
  have hceil : (Nat.ceil t : ℝ) < t+1 := Nat.ceil_lt_add_one ht0
  have hcard := Q.local_mass_dyad_card_le_log lo hi
  have hcardR : (Fintype.card (LocalShiftedMassDyad Q lo hi):ℝ) ≤
      (Nat.ceil t:ℝ)+1 := by
    exact_mod_cast hcard
  dsimp only [t,L,U] at *
  linarith only [hcardR,hceil,ht,hL]

theorem Potential.outer_band_error_of_dyadic_prices_draft
    (P : Q.Potential) (ell : ℕ) (Qraw K cut Cprice : ℝ)
    (hCprice : 0 ≤ Cprice) (hK : 0 ≤ K)
    (hQraw : 0 ≤ Qraw) (hcut : 0 ≤ cut)
    {lo hi : ℝ} (hlo : lo ∈ Ioc (0:ℝ) 1)
    (_hhi : hi ∈ Ioc (0:ℝ) 1)
    (hwidth : hi ≤ 2*lo)
    (hL : 1 ≤ Real.log Q.data.N)
    (hU1 : comparisonSmallMass Q.data.N Q.data.E ≤ 1)
    (hUN : 1/Q.data.N ≤ comparisonSmallMass Q.data.N Q.data.E)
    (hprice : ∀j : LocalShiftedMassDyad Q lo hi,
      let v := comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val.val:ℕ)
      laplaceComparisonStrength Q.data.d Q.lam v*
        outerTruncatedGroupBudget Q ell Qraw K cut v ≤
          Cprice*(Real.log Q.data.N)^7*
            Q.data.N^(-delta/2)*Q.data.E)
    (hlocal :
      (∫u in lo..hi,
        (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
            Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
        3*(max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo)*
          (∑j : LocalShiftedMassDyad Q lo hi,
            let v := comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val.val:ℕ)
            outerTruncatedGroupBudget Q ell Qraw K cut v)+
        128*(max 1 cu)*(Real.log Q.data.N)^3*
          (C0^3*Q.data.N^(-3*m)*Q.data.E)/(Q.data.N^delta)^2) :
    (∫u in lo..hi,
      (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      24*(max 1 cu)*Cprice*(Real.log Q.data.N)^8*
        Q.data.N^(-delta/2)*Q.data.E+
      128*(max 1 cu)*(Real.log Q.data.N)^3*
        (C0^3*Q.data.N^(-3*m)*Q.data.E)/(Q.data.N^delta)^2 := by
  let L := Real.log Q.data.N
  let rate := Q.data.N^(-delta/2)*Q.data.E
  let e := fun u => laplaceComparisonStrength Q.data.d Q.lam u
  let B := fun j : LocalShiftedMassDyad Q lo hi =>
    outerTruncatedGroupBudget Q ell Qraw K cut
      (comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val.val:ℕ))
  have hcard : (Fintype.card (LocalShiftedMassDyad Q lo hi):ℝ) ≤ 4*L :=
    outer_local_dyad_card_le_four_log_draft Q (lo:=lo) (hi:=hi) hL hU1 hUN
  have hG : 0 ≤ max 1 cu := zero_le_one.trans (le_max_left _ _)
  have hL0 : 0 ≤ L := by linarith
  have hrate : 0 ≤ rate := by dsimp only [rate]; positivity [Q.data.hN, Q.data.hE]
  have hterm (j : LocalShiftedMassDyad Q lo hi) :
      e lo*B j ≤ 2*Cprice*L^7*rate := by
    let v := comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val.val:ℕ)
    have hv := comparison_mass_dyadic_scale Q.data.hU j.val
    have hvI : v ∈ Ioc (0:ℝ) 1 := ⟨hv.1,hv.2.2⟩
    have hvhi : v ≤ hi := j.property.2
    have he := outer_slab_left_strength_le_twice_group_draft Q
      hlo hvI hvhi hwidth
    have hB : 0 ≤ B j := by
      dsimp [B,outerTruncatedGroupBudget]
      exact outer_truncated_ordinary_budget_nonneg_draft Q ell
        hQraw hK hcut hvI hL0
    have H := mul_le_mul_of_nonneg_right he hB
    have Hp := hprice j
    dsimp only [e,B,v] at H Hp ⊢
    nlinarith only [H,Hp]
  have hsum : e lo*(∑j : LocalShiftedMassDyad Q lo hi,B j) ≤
      8*Cprice*L^8*rate := by
    rw [Finset.mul_sum]
    have H := Finset.sum_le_sum (s:=Finset.univ)
      (fun j _ => hterm j)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at H
    have Hcard := mul_le_mul_of_nonneg_right hcard
      (show 0 ≤ 2*Cprice*L^7*rate by positivity)
    nlinarith only [H,Hcard]
  have Hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 3*max 1 cu by positivity)
  dsimp only [L,rate,e,B] at Hscaled hlocal ⊢
  nlinarith only [hlocal,Hscaled]

theorem outer_nonpositive_tail_of_band_price_draft
    {f : ℝ → ℝ} {h L B : ℝ}
    (h0 : 0 < h) (h1 : h ≤ 1)
    (hL : 1 ≤ L) (hlog : Real.log (1/h) ≤ L)
    (hB : 0 ≤ B)
    (hfi : IntervalIntegrable f volume h 1)
    (hband : ∀j : ℕ, j < tailCount h →
      (∫u in tailGrid h j..tailGrid h (j+1), f u) ≤ B) :
    (∫u in h..1,f u) ≤ (1/Real.log 2+2)*L*B := by
  have H := tail_integral_le_of_uniform_bands h0 h1 hfi hband
  have Hcount := tailCount_le_log h0 h1 hL hlog
  exact H.trans (mul_le_mul_of_nonneg_right Hcount hB)

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
