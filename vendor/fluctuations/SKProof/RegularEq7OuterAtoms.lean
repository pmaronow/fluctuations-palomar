module

public import SKProof.RegularEq7OuterBudget
public import ComparisonOriginalQOuterDiameterScalarDraft
public import ComparisonOriginalQOuterReverseScalarDraft
public import ComparisonOriginalQOuterCutoffScalarDraft
public import ComparisonOriginalQOuterInverseTraceQImportFirstDraft
public import ComparisonOriginalQOuterVarianceQCorrectedFiveAtomDraft
public import ConcreteWallPowerBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open ActualThetaZeroOverlapMinimum
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators

variable {n : ℕ} {m cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m (m/10000) cl cu Az C0 Ct D Bclock)

theorem outer_concrete_error_div_cube_eq_small_wall_product_draft
    (hE : Q.data.E = wallHighError m (n+1))
    (hd : Q.data.d = wallHighD m (n+1))
    (hs : Q.data.s = wallHighMass m (n+1)) :
    Q.data.E/Q.data.d^3 =
      comparisonSmallMass Q.data.N Q.data.E*Q.data.s := by
  rw [hE,hd,hs]
  simpa only [ActualHighWallData.N] using
    OriginalQOuterDiameterDraft.concrete_error_div_cube_eq_small_wall_product_draft m
        (show 0 < n+1 by omega)

theorem outer_local_cap_diameter_le_small_mass_draft
    (hE : Q.data.E = wallHighError m (n+1))
    (hd : Q.data.d = wallHighD m (n+1))
    (hs : Q.data.s = wallHighMass m (n+1))
    {lo K v : ℝ} (hK : 0 ≤ K) (hv : 0 < v)
    (hL : 0 ≤ Real.log Q.data.N)
    (hgroup : (cl/(4*cu))*lo ≤ v)
    (hstart : 2*Q.data.s ≤ (cl/(4*cu))*lo) :
    Q.localCapDiameter v K ≤
      9*K*Real.log Q.data.N*(1/Q.data.N^(m/10000))*
        comparisonSmallMass Q.data.N Q.data.E := by
  have _hlog_nonneg : 0 ≤ Real.log Q.data.N := hL
  let L := Real.log Q.data.N
  let U := comparisonSmallMass Q.data.N Q.data.E
  let t := 1/Q.data.N^(m/10000)
  have hwall := outer_concrete_error_div_cube_eq_small_wall_product_draft Q
    hE hd hs
  have hscaled := outer_truncated_local_diameter_scaled_draft Q
    (K:=K) (v:=v) hv hwall
  have hsle : Q.data.s ≤ v := by
    linarith only [hstart,hgroup,Q.data.hs.1]
  have hcoef : 0 ≤ 9*K*L*t*U := by
    dsimp only [L,t,U]
    positivity [Q.data.hU, Q.data.hN]
  have Hs := mul_le_mul_of_nonneg_left hsle hcoef
  apply (mul_le_mul_iff_right₀ hv).mp
  calc
    v*Q.localCapDiameter v K = 9*K*L*t*U*Q.data.s := by
      dsimp only [L,t,U]
      convert hscaled using 1; ring
    _ ≤ (9*K*L*t*U)*v := Hs
    _ = v*(9*K*L*t*U) := by ring

theorem outer_truncated_squared_diameter_atom_rate_draft
    (hC0 : 0 < C0)
    (hE : Q.data.E = wallHighError m (n+1))
    (hd : Q.data.d = wallHighD m (n+1))
    (hs : Q.data.s = wallHighMass m (n+1))
    (hnd : 1/Q.data.N ≤ Q.data.d)
    (hL : 1 ≤ Real.log Q.data.N)
    {lo K v : ℝ} (hK : 4 ≤ K)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (hgroup : (cl/(4*cu))*lo ≤ v)
    (hstart : 2*Q.data.s ≤ (cl/(4*cu))*lo) :
    let e := laplaceComparisonStrength Q.data.d Q.lam v
    e*(K*v)*(Q.localCapDiameter v K)^2 ≤
      162*K^3*(Real.log Q.data.N)^3*
        (1/Q.data.N^(m/10000))^2*
        (C0^3*Q.data.N^(-3*m)*Q.data.E) := by
  let e := laplaceComparisonStrength Q.data.d Q.lam v
  let U := comparisonSmallMass Q.data.N Q.data.E
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hL0 : 0 ≤ Real.log Q.data.N := zero_le_one.trans hL
  let Dloc := Q.localCapDiameter v K
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have he : 0 ≤ e := (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
  have hD : 0 ≤ Dloc := by
    dsimp [Dloc,localCapDiameter]
    positivity [Q.data.hE, Q.data.hd, Q.data.hN, hv.1]
  have hcritical := eq7_native_cap_cubic_price Q hC0
  have hdiam := outer_local_cap_diameter_le_small_mass_draft Q
    hE hd hs (by linarith : 0 ≤ K) hv.1 (zero_le_one.trans hL) hgroup hstart
  have henergy := eq7_outer_group_strength_mass_le Q
    hN hnd hL hv
  have H := OriginalQOuterDiameterDraft.squared_diameter_atom_of_energy_and_wall_draft
      he hv.1 (by linarith : 0 ≤ K) (zero_le_one.trans hL) Q.data.hd.le
      hD (show 0 ≤ 1/Q.data.N^(m/10000) by positivity) Q.data.hU.le
      henergy hdiam hcritical
  simpa only [e,Dloc,U] using H

theorem outer_truncated_squared_diameter_five_atom_input_draft
    (hm : 0 < m) (hC0 : 0 < C0)
    (hE : Q.data.E = wallHighError m (n+1))
    (hd : Q.data.d = wallHighD m (n+1))
    (hs : Q.data.s = wallHighMass m (n+1))
    (hnd : 1/Q.data.N ≤ Q.data.d)
    (hL : 1 ≤ Real.log Q.data.N)
    {lo K v : ℝ} (hK : 4 ≤ K)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (hgroup : (cl/(4*cu))*lo ≤ v)
    (hstart : 2*Q.data.s ≤ (cl/(4*cu))*lo) :
    let e := laplaceComparisonStrength Q.data.d Q.lam v
    let M := K*v
    e*M*(Q.localCapDiameter v K)^2 ≤
      (162*K^3*C0^3)*(Real.log Q.data.N)^3*
        Q.data.N^(-(m/10000)/2)*Q.data.E := by
  have H := outer_truncated_squared_diameter_atom_rate_draft Q
    hC0 hE hd hs hnd hL hK hv hgroup hstart
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpow : (1/Q.data.N^(m/10000))^2*Q.data.N^(-3*m) =
      Q.data.N^(-3*m-2*(m/10000)) := by
    rw [one_div, ←Real.rpow_neg Q.data.hN.le,
      ←Real.rpow_mul_natCast Q.data.hN.le,
      ←Real.rpow_add Q.data.hN]
    congr 1
    ring
  have hexp : -3*m-2*(m/10000) ≤ -(m/10000)/2 := by
    linarith [hm]
  have hrate := Real.rpow_le_rpow_of_exponent_le hN hexp
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hL0 : 0 ≤ Real.log Q.data.N := zero_le_one.trans hL
  have Hscaled := mul_le_mul_of_nonneg_left hrate
    (show 0 ≤ 162*K^3*C0^3*(Real.log Q.data.N)^3*Q.data.E by positivity [Q.data.hN, Q.data.hE])
  dsimp only at H ⊢
  rw [←hpow] at Hscaled
  nlinarith only [H,Hscaled]

theorem outer_truncated_reverse_five_atom_input_draft
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az)
    (hE : Q.data.E = wallHighError m (n+1))
    (hd : Q.data.d = wallHighD m (n+1))
    (hnd : 1/Q.data.N ≤ Q.data.d)
    (hL : 1 ≤ Real.log Q.data.N)
    {K : ℝ} (hK : 4 ≤ K)
    (hHlarge : 2/cl+K ≤ Q.data.N)
    (ell : ℕ) (hell : 2 < ell)
    (horder : ((m/10000)+(1:ℝ)/3+20*m+1)/
      ((ell:ℝ)-1) ≤ (m/10000)/2)
    (q : ℝ) (hq : 1 ≤ q)
    {lo v : ℝ} (hv : v ∈ Ioc (0:ℝ) 1)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hgroup : (cl/(4*cu))*lo ≤ v) :
    let z := min (K*v) 1
    let e := laplaceComparisonStrength Q.data.d Q.lam v
    let M := K*v
    let diam := Q.localCapDiameter v K
    let H := 2/cl+K
    e*M*(diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*q)^(2*ell)*(Q.xs+z)^ell)^(
        1/((ell:ℝ)-1))) ≤
      (18*H*K^2*(2*q)^4)*
        (Real.log Q.data.N)^3*
        Q.data.N^(-(m/10000)/2)*Q.data.E := by
  have _hm0 : 0 ≤ m := hm.le
  let N := Q.data.N
  let delta := m/10000
  let L := Real.log N
  let H := 2/cl+K
  let T := delta+(1:ℝ)/3+20*m
  let z := min (K*v) 1
  let y := Q.xs+z
  let e := laplaceComparisonStrength Q.data.d Q.lam v
  let diam := Q.localCapDiameter v K
  have hN : 1 ≤ N := by
    dsimp only [N,ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hK0 : 0 ≤ K := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have he : 0 ≤ e := (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
  have hz0 : 0 < z := by
    dsimp only [z]
    exact lt_min (mul_pos (by linarith : 0 < K) hv.1) zero_lt_one
  have hy : 0 < y := by dsimp [y]; linarith only [Q.hxs,hz0]
  have hxs := outer_cover_carrier_le_group_draft Q
    hcl hcu hAz houter hgroup
  have hheight : y ≤ H*v := by
    dsimp only [y,H,z]
    linarith only [hxs,min_le_left (K*v) 1]
  have hyN : y ≤ N := by
    have H := mul_le_mul_of_nonneg_left hv.2 hH
    linarith only [hheight,H,hHlarge]
  have hDformula : diam = 9*K*L*Q.data.E/(N^delta*Q.data.d^3*v) := by
    dsimp [diam,localCapDiameter,N,L,delta]
    ring
  have hDpos : 0 < diam := by
    dsimp [diam,localCapDiameter]
    positivity [Q.data.hE, Q.data.hd, Q.data.hN, hv.1, (zero_le_one.trans hL)]
  have hwall : Q.data.E/Q.data.d^3 = N^(-(1:ℝ)/3-20*m) := by
    rw [hE,hd]
    simpa only [N,ActualHighWallData.N] using
      OriginalQOuterReverseDraft.concrete_error_div_d_cube_eq_power_draft
        m (Nat.succ_pos n)
  have hDlow : N^(-T) ≤ diam := by
    dsimp only [T]
    exact OriginalQOuterReverseDraft.local_diameter_concrete_lower_draft
      hN Q.data.hd Q.data.hE hK hL hv.1 hv.2 hwall hDformula
  have hratio : y/diam ≤ N^(T+1) :=
    comparison_reverse_ratio_of_scales hNp hDpos hy.le
      hDlow (by simpa only [Real.rpow_one] using hyN)
  have henergy := eq7_outer_group_strength_mass_le Q
    hN hnd hL hv
  have Hscalar := OriginalQOuterReverseDraft.reverse_atom_of_local_energy_and_ratio_draft
      hell hN Q.data.hd Q.data.hE he hv.1 hK0 (zero_le_one.trans hL) hH
      hq hy hDpos henergy hheight hDformula hratio
      (by simpa only [T,delta] using horder)
  have hpow : N^(delta/2)/N^delta = N^(-delta/2) := by
    rw [←Real.rpow_sub hNp]
    congr 1
    ring
  have hL23 : L^2 ≤ L^3 := by
    have H := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ L^2 by positivity)
    nlinarith only [H]
  have hcoef : 0 ≤ 18*H*K^2*(2*q)^4*N^(-delta/2)*Q.data.E := by
    positivity [Q.data.hE]
  have Hlog := mul_le_mul_of_nonneg_left hL23 hcoef
  dsimp only [N,delta,L,H,T,z,y,e,diam] at Hscalar hpow Hlog ⊢
  unfold comparisonReverseMoment at Hscalar
  rw [hpow] at Hscalar
  nlinarith only [Hscalar,Hlog]

theorem exists_outer_truncated_reverse_order_draft
    {m : ℝ} (hm : 0 < m) :
    ∃ ell : ℕ, 2 < ell ∧
      ((m/10000)+(1:ℝ)/3+20*m+1)/((ell:ℝ)-1) ≤
        (m/10000)/2 := by
  exact exists_comparison_reverse_moment_order
    (T:=(m/10000)+(1:ℝ)/3+20*m+1)
    (eps:=(m/10000)/2) (by positivity)

theorem eventually_outer_truncated_reverse_five_atom_input_draft
    (m cl cu Az K : ℝ)
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hK : 4 ≤ K)
    (ell : ℕ) (hell : 2 < ell)
    (horder : ((m/10000)+(1:ℝ)/3+20*m+1)/
      ((ell:ℝ)-1) ≤ (m/10000)/2)
    (q : ℝ) (hq : 1 ≤ q) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {C0 Ct D Bclock : ℝ}
        (Q : ActualThetaZeroOverlapMinimum (n+1) m (m/10000)
          cl cu Az C0 Ct D Bclock),
        Q.data.E = wallHighError m (n+1) →
        Q.data.d = wallHighD m (n+1) →
        1/Q.data.N ≤ Q.data.d →
        1 ≤ Real.log Q.data.N →
        ∀ {lo v : ℝ},
          v ∈ Ioc (0:ℝ) 1 →
          2*cu*(Az+1)*Q.xs ≤ lo →
          (cl/(4*cu))*lo ≤ v →
          let z := min (K*v) 1
          let e := laplaceComparisonStrength Q.data.d Q.lam v
          let M := K*v
          let diam := Q.localCapDiameter v K
          let H := 2/cl+K
          e*M*(diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
            ((2*q)^(2*ell)*(Q.xs+z)^ell)^(
              1/((ell:ℝ)-1))) ≤
            (18*H*K^2*(2*q)^4)*
              (Real.log Q.data.N)^3*
              Q.data.N^(-(m/10000)/2)*Q.data.E := by
  have HN := (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (eventually_ge_atTop (2/cl+K))
  filter_upwards [HN] with n hnN
  intro C0 Ct D Bclock Q hE hd hnd hL lo v hv houter hgroup
  have hHlarge : 2/cl+K ≤ Q.data.N := by
    simpa only [ActualHighWallData.N, Function.comp_apply] using hnN
  exact outer_truncated_reverse_five_atom_input_draft Q
    hm hcl hcu hAz hE hd hnd hL hK hHlarge ell hell horder
      q hq hv houter hgroup

theorem eventually_outer_truncated_cutoff_five_atom_input_draft
    (m cl cu Az K q : ℝ)
    (hm : 0 < m) (hmmax : m < 1/300)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hK : 4 ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {C0 Ct D Bclock : ℝ}
        (Q : ActualThetaZeroOverlapMinimum (n+1) m (m/10000)
          cl cu Az C0 Ct D Bclock),
        Q.data.E = wallHighError m (n+1) →
        ∀ {lo v : ℝ},
          v ∈ Ioc (0:ℝ) 1 →
          2*cu*(Az+1)*Q.xs ≤ lo →
          (cl/(4*cu))*lo ≤ v →
          let z := min (K*v) 1
          let e := laplaceComparisonStrength Q.data.d Q.lam v
          let P := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
            (Q.shiftedNativeModel.R z)
          let M := K*v
          e*18*(((q^2*(Q.xs+z))^2*P*M^2)^((1:ℝ)/3)+2)*
            Q.data.N^(-(30:ℝ)) ≤
              Q.data.N^(-(m/10000)/2)*Q.data.E := by
  let H := 2/cl+K
  let B := q^4*H^2*K^2
  have Hgate := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le
      (c:=18*(B+3)) (d:=1)
      (q:=-(29:ℝ)) (r:=-(2:ℝ)) zero_lt_one (by norm_num))
  filter_upwards [Hgate] with n hnGate
  intro C0 Ct D Bclock Q hE lo v hv houter hgroup
  let N := Q.data.N
  let z := min (K*v) 1
  let e := laplaceComparisonStrength Q.data.d Q.lam v
  let ez := laplaceComparisonStrength Q.data.d Q.lam
    (Q.shiftedNativeModel.R z)
  let P := N*ez
  let M := K*v
  let y := Q.xs+z
  let Z := (q^2*y)^2*P*M^2
  have hN : 1 ≤ N := by
    dsimp only [N,ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have he : 0 ≤ e := (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
  have hlam1 : Q.lam ≤ 1 :=
    Q.hld.trans (by nlinarith [Q.data.hd,Q.data.hd1] :
      Q.data.d^2 ≤ 1)
  have he1 : e ≤ 1 :=
    (laplaceComparisonStrength_le Q.data.d Q.hlam.le v).trans hlam1
  have hez : 0 ≤ ez := (laplaceComparisonStrength_pos Q.data.d Q.hlam _).le
  have hez1 : ez ≤ 1 :=
    (laplaceComparisonStrength_le Q.data.d Q.hlam.le _).trans hlam1
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hP : P ≤ N := by
    dsimp only [P]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hez1 Q.data.hN.le
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by linarith : 0 ≤ K) hv.1.le
  have hM : M ≤ K := by dsimp [M]; nlinarith only [hv.2,hK]
  have hz0 : 0 ≤ z := le_min hM0 zero_le_one
  have hy0 : 0 ≤ y := by dsimp [y]; exact add_nonneg Q.hxs.le hz0
  have hxs := outer_cover_carrier_le_group_draft Q
    hcl hcu hAz houter hgroup
  have hyv : y ≤ H*v := by
    dsimp only [y,H,z]
    linarith only [hxs,min_le_left (K*v) 1]
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hy : y ≤ H :=
    hyv.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.2 hH)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hZB : Z ≤ B*N := by
    dsimp only [Z,B]
    exact OriginalQOuterCutoffDraft.payload_le_fixed_linear
      hN hP0 hP hy0 hy hM0 hM hH (by linarith : 0 ≤ K)
  have hEfloor : 1/N ≤ Q.data.E := by
    rw [hE,wallHighError_eq m (Nat.succ_pos n)]
    dsimp only [N,ActualHighWallData.N]
    have H := Real.rpow_le_rpow_of_exponent_le hN
      (show -(1:ℝ) ≤ -(5:ℝ)/6+25*m by linarith [hm])
    simpa only [Real.rpow_neg_one, one_div, N, ActualHighWallData.N] using H
  have hgate : 18*(B+3)*N^(-(29:ℝ)) ≤ N^(-(2:ℝ)) := by
    dsimp only [N]
    simpa only [ActualHighWallData.N,one_mul] using hnGate
  have Hatom := OriginalQOuterCutoffDraft.cutoff_atom_of_linear_payload
    hN (by positivity : 0 ≤ m/10000)
    (by linarith [hmmax] : (m/10000)/2 ≤ 1)
    Q.data.hE.le hEfloor he he1 hZ0 hB hZB hgate
  simpa only [N,z,e,ez,P,M,y,Z] using Hatom

def outerHeight (cl K : ℝ) : ℝ := 2/cl+K
def outerStrengthDistortion (cl Az K : ℝ) : ℝ :=
  max 1 ((Az+1/cl)*(outerHeight cl K))
def outerVarianceConstant (C0 cl Az K q : ℝ) : ℝ :=
  (4*C0)*(q^2*outerHeight cl K*
    outerStrengthDistortion cl Az K)^((2:ℝ)/3)
def outerTraceConstant (cl Az K : ℝ) : ℝ :=
  3*outerStrengthDistortion cl Az K
def outerDiameterConstant (C0 K : ℝ) : ℝ := 162*K^3*C0^3
def outerReverseConstant (cl K q : ℝ) : ℝ :=
  18*outerHeight cl K*K^2*(2*q)^4
def outerGroupPriceConstant (C0 cl Az K q : ℝ) : ℝ :=
  binConstant K*
    (outerVarianceConstant C0 cl Az K q+
      outerTraceConstant cl Az K+
      outerDiameterConstant C0 K+
      outerReverseConstant cl K q)+1

theorem outerGroupPriceConstant_nonneg
    {C0 cl Az K q : ℝ} (hC0 : 0 < C0)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hK : 4 ≤ K) :
    0 ≤ outerGroupPriceConstant C0 cl Az K q := by
  have _hAz0 : 0 ≤ Az := hAz
  have hB := binConstant_nonneg
    (K:=K) (by linarith : 0 ≤ K)
  have hH : 0 ≤ outerHeight cl K := by
    dsimp [outerHeight]
    positivity
  have hJ : 0 ≤ outerStrengthDistortion cl Az K := by
    dsimp [outerStrengthDistortion]
    exact zero_le_one.trans (le_max_left _ _)
  dsimp [outerGroupPriceConstant,outerVarianceConstant,
    outerTraceConstant,outerDiameterConstant,outerReverseConstant]
  positivity

theorem eventually_outer_truncated_five_atom_group_price_corrected_c0_draft
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
          cl cu Az C0 Ct D Bclock),
        Q.data.E = wallHighError m (n+1) →
        Q.data.d = wallHighD m (n+1) →
        Q.data.s = wallHighMass m (n+1) →
        1/Q.data.N ≤ Q.data.d →
        1 ≤ Real.log Q.data.N →
        ∀ {lo v : ℝ},
          v ∈ Ioc (0:ℝ) 1 →
          2*cu*(Az+1)*Q.xs ≤ lo →
          (cl/(4*cu))*lo ≤ v →
          2*Q.data.s ≤ (cl/(4*cu))*lo →
          laplaceComparisonStrength Q.data.d Q.lam v*
            outerTruncatedGroupBudget Q ell q K
              (Q.data.N^(-(30:ℝ))) v ≤
            outerGroupPriceConstant
              C0 cl Az K q*(Real.log Q.data.N)^7*
              Q.data.N^(-(m/10000)/2)*Q.data.E := by
  have Hrev := eventually_outer_truncated_reverse_five_atom_input_draft
    m cl cu Az K hm hcl hcu hAz hK ell hell horder q hq
  have Hcut := eventually_outer_truncated_cutoff_five_atom_input_draft
    m cl cu Az K q hm hmmax hcl hcu hAz hK
  filter_upwards [Hrev,Hcut] with n hnRev hnCut
  intro Ct D Bclock Q hE hd hs hnd hL lo v hv houter hgroup hstart
  let H := outerHeight cl K
  let J := outerStrengthDistortion cl Az K
  let Cv := outerVarianceConstant C0 cl Az K q
  let Ct0 := outerTraceConstant cl Az K
  let Cd := outerDiameterConstant C0 K
  let Cr := outerReverseConstant cl K q
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hCv : 0 ≤ Cv := by
    dsimp [Cv,outerVarianceConstant]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by
      dsimp [outerHeight,outerStrengthDistortion]
      positivity) _)
  have hCt : 0 ≤ Ct0 := by
    dsimp [Ct0,outerTraceConstant,
      outerStrengthDistortion]
    positivity
  have hCd : 0 ≤ Cd := by dsimp [Cd,outerDiameterConstant]; positivity
  have hCr : 0 ≤ Cr := by
    dsimp [Cr,outerReverseConstant,
      outerHeight]
    positivity
  have hvar := Q.outer_truncated_variance_five_atom_input_corrected_c0_isolated_draft
    hm (by positivity : 0 < m/10000)
    (by linarith [hm] : (m/10000)/2 ≤ m)
    hcl hcu hAz hC0 hnd hL hK hv houter hgroup q
  have htrace := Q.outer_trace_import_first_five_atom_input_draft
    hm hcl hcu hAz hE hs hL hK hv houter hgroup hstart
  have hdiam := outer_truncated_squared_diameter_five_atom_input_draft Q
    hm hC0 hE hd hs hnd hL hK hv hgroup hstart
  have hreverse := hnRev Q hE hd hnd hL hv houter hgroup
  have hcut := hnCut Q hE hv houter hgroup
  have Hbudget := outer_truncated_budget_of_five_atom_rates_draft Q
    ell (Qraw:=q) (K:=K) (cut:=Q.data.N^(-(30:ℝ)))
    (Cv:=Cv) (Cd:=Cd) (Cr:=Cr) (Ccut:=1)
    hK hL hCv hCt hCd hCr (by norm_num) hv
    (by simpa only [Cv,H,J,
      outerVarianceConstant,
      outerHeight,
      outerStrengthDistortion] using hvar)
    (by simpa only [Ct0,J,
      outerTraceConstant, outerHeight,
      outerStrengthDistortion] using htrace)
    (by simpa only [Cd,
      outerDiameterConstant] using hdiam)
    (by simpa only [Cr,H,
      outerReverseConstant,
      outerHeight] using hreverse)
    (by simpa only [one_mul] using hcut)
  simpa only [outerTruncatedGroupBudget,
    outerGroupPriceConstant,
    Cv,Ct0,Cd,Cr] using Hbudget

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
