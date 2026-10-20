module

public import ComparisonActualHighWallThetaZeroOrdinaryPhysicalBudget
public import ComparisonNativeLogarithmicLoss
public import ComparisonActualHighWallThetaZeroSelectedRadius
public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonNativeActualHighMassDiameter
public import ComparisonActualHighWallThetaZeroStrongStarCapRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators

def binConstant (K : ℝ) : ℝ :=
  nativeBinScalePolynomial (108*K^2) (54*K^2) 30 (2*K)

theorem binConstant_nonneg {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ binConstant K := by
  unfold binConstant
  exact nativeBinScalePolynomial_nonneg
    (by positivity) (by positivity) (by norm_num) (by positivity)

theorem truncated_bin_loss_le_log_four
    {N K v : ℝ} (hL : 1 ≤ Real.log N)
    (hK : 4 ≤ K) (hv : 0 < v) :
    nativeBinScaleLoss (30*Real.log N)
      (108*K^2*(Real.log N)^2) (54*K^2*(Real.log N)^2)
      (K*v) (v/2) ≤ binConstant K*(Real.log N)^4 := by
  have hratio : (K*v)/(v/2) = 2*K := by
    field_simp [hv.ne']
  apply nativeBinScaleLoss_le_log_polynomial hL
    (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity)
    (by positivity) (by positivity) (by norm_num)
    (by positivity)
    (le_refl _) (le_refl _) (le_refl _)
    (by rw [hratio])

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem outer_truncated_endpoint_geometry_draft
    {K v : ℝ} (hK : 1 ≤ K) (hv : v ∈ Ioc (0:ℝ) 1) :
    v ≤ min (K*v) 1 ∧ min (K*v) 1 ≤ K*v ∧
      min (K*v) 1 ∈ Ioc (0:ℝ) 1 := by
  have hvKv : v ≤ K*v := by nlinarith [hv.1]
  have hvz : v ≤ min (K*v) 1 := le_min hvKv hv.2
  exact ⟨hvz,min_le_left _ _,⟨hv.1.trans_le hvz,min_le_right _ _⟩⟩

theorem outer_truncated_strength_le_draft
    {K v : ℝ} (hK : 1 ≤ K) (hv : v ∈ Ioc (0:ℝ) 1) :
    let z := min (K*v) 1
    laplaceComparisonStrength Q.data.d Q.lam v ≤
      K*laplaceComparisonStrength Q.data.d Q.lam z := by
  let z := min (K*v) 1
  obtain ⟨hvz,hzKv,hz⟩ := outer_truncated_endpoint_geometry_draft hK hv
  have hshape := laplaceComparisonStrength_monotonicities
    Q.data.hd.ne' Q.hlam (show (0:ℝ) ≤ 0 by norm_num)
  have He := hshape.2 ⟨hv.1.le,hv.2⟩ ⟨hz.1.le,hz.2⟩ hvz
  have hez : 0 ≤ laplaceComparisonStrength Q.data.d Q.lam z :=
    (laplaceComparisonStrength_pos Q.data.d Q.hlam z).le
  apply le_of_mul_le_mul_right (a:=v) _ hv.1
  calc
    laplaceComparisonStrength Q.data.d Q.lam v*v ≤
        laplaceComparisonStrength Q.data.d Q.lam z*z := He
    _ ≤ laplaceComparisonStrength Q.data.d Q.lam z*(K*v) :=
      mul_le_mul_of_nonneg_left hzKv hez
    _ = (K*laplaceComparisonStrength Q.data.d Q.lam z)*v := by ring

theorem outer_slab_left_strength_le_twice_group_draft
    {lo hi v : ℝ} (hlo : lo ∈ Ioc (0:ℝ) 1)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (hvhi : v ≤ hi) (hwidth : hi ≤ 2*lo) :
    laplaceComparisonStrength Q.data.d Q.lam lo ≤
      2*laplaceComparisonStrength Q.data.d Q.lam v := by
  have hshape := laplaceComparisonStrength_monotonicities
    Q.data.hd.ne' Q.hlam (show (0:ℝ) ≤ 0 by norm_num)
  have hev : 0 ≤ laplaceComparisonStrength Q.data.d Q.lam v :=
    (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
  by_cases hvl : v ≤ lo
  · have H := hshape.1 ⟨hv.1.le,hv.2⟩ ⟨hlo.1.le,hlo.2⟩ hvl
    linarith only [H,hev]
  · have hlv : lo ≤ v := le_of_not_ge hvl
    have H := hshape.2 ⟨hlo.1.le,hlo.2⟩ ⟨hv.1.le,hv.2⟩ hlv
    have hv2 : v ≤ 2*lo := hvhi.trans hwidth
    have H2 := mul_le_mul_of_nonneg_left hv2 hev
    apply le_of_mul_le_mul_right (a:=lo) _ hlo.1
    calc
      laplaceComparisonStrength Q.data.d Q.lam lo*lo ≤
          laplaceComparisonStrength Q.data.d Q.lam v*v := H
      _ ≤ laplaceComparisonStrength Q.data.d Q.lam v*(2*lo) := H2
      _ = (2*laplaceComparisonStrength Q.data.d Q.lam v)*lo := by ring

theorem outer_cover_carrier_le_group_draft
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {lo v : ℝ} (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hgroup : (cl/(4*cu))*lo ≤ v) :
    Q.xs ≤ (2/cl)*v := by
  have hratio : 0 ≤ cl/(4*cu) := by positivity
  have H := mul_le_mul_of_nonneg_left houter hratio
  have hAz1 : 1 ≤ Az+1 := by linarith
  have hxs : 0 ≤ Q.xs := Q.hxs.le
  have hbound : (cl/2)*Q.xs ≤ v := by
    have HH : (cl/2)*Q.xs ≤ (cl/(4*cu))*(2*cu*(Az+1)*Q.xs) := by
      have Hfac := mul_le_mul_of_nonneg_left hAz1
        (show 0 ≤ (cl/2)*Q.xs by positivity)
      have Heq : (cl/(4*cu))*(2*cu*(Az+1)*Q.xs) =
          (cl/2)*((Az+1)*Q.xs) := by
        field_simp [hcu.ne']
        ring
      rw [Heq]
      nlinarith only [Hfac]
    exact HH.trans (H.trans hgroup)
  have htwo : 0 < 2/cl := by positivity
  have Hmul := mul_le_mul_of_nonneg_left hbound htwo.le
  have Heq : (2/cl)*((cl/2)*Q.xs)=Q.xs := by
    field_simp [hcl.ne']
  rw [Heq] at Hmul
  exact Hmul

theorem outer_truncated_actual_endpoint_strength_le_draft
    (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {K H v : ℝ} (hK : 1 ≤ K) (hH : 0 ≤ H)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (hxs : Q.xs ≤ H*v) :
    let z := min (K*v) 1
    let J := max 1 ((Az+1/cl)*(H+K))
    laplaceComparisonStrength Q.data.d Q.lam v ≤
      J*laplaceComparisonStrength Q.data.d Q.lam
        (Q.shiftedNativeModel.R z) := by
  let z := min (K*v) 1
  let r := Q.shiftedNativeModel.R z
  let J := max 1 ((Az+1/cl)*(H+K))
  obtain ⟨_,hzKv,hz⟩ := outer_truncated_endpoint_geometry_draft hK hv
  have hC : 0 ≤ Az+1/cl := by positivity
  have hK0 : 0 ≤ H+K := by linarith
  have hJ : 1 ≤ J := le_max_left _ _
  have hr : 0 < r :=
    Q.data.hrbounds.1.trans_le (Q.shiftedNativeModel.R_bounds z).1
  have hrI : r ∈ Icc (0:ℝ) 1 :=
    ⟨hr.le,(Q.shiftedNativeModel.R_bounds z).2⟩
  have hsource := Q.inverse_radius_le_source_mass hcl hAz
    ⟨hz.1.le,hz.2⟩
  have hrv : r ≤ J*v := by
    have hmass : Q.xs+z ≤ (H+K)*v := by
      linarith only [hxs,hzKv]
    have hbase := mul_le_mul_of_nonneg_left hmass hC
    have hfactor := mul_le_mul_of_nonneg_right
      (le_max_right (1:ℝ) ((Az+1/cl)*(H+K))) hv.1.le
    calc
      r = Q.sweepRadius z := Q.shiftedNativeModel_radius z
      _ ≤ (Az+1/cl)*(Q.xs+z) := hsource
      _ ≤ (Az+1/cl)*((H+K)*v) := hbase
      _ = ((Az+1/cl)*(H+K))*v := by ring
      _ ≤ J*v := hfactor
  have hshape := laplaceComparisonStrength_monotonicities
    Q.data.hd.ne' Q.hlam (show (0:ℝ) ≤ 0 by norm_num)
  have hev : 0 ≤ laplaceComparisonStrength Q.data.d Q.lam v :=
    (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
  have her : 0 ≤ laplaceComparisonStrength Q.data.d Q.lam r :=
    (laplaceComparisonStrength_pos Q.data.d Q.hlam r).le
  by_cases hvr : v ≤ r
  · have H := hshape.2 ⟨hv.1.le,hv.2⟩ hrI hvr
    apply le_of_mul_le_mul_right (a:=v) _ hv.1
    calc
      laplaceComparisonStrength Q.data.d Q.lam v*v ≤
          laplaceComparisonStrength Q.data.d Q.lam r*r := H
      _ ≤ laplaceComparisonStrength Q.data.d Q.lam r*(J*v) :=
        mul_le_mul_of_nonneg_left hrv her
      _ = (J*laplaceComparisonStrength Q.data.d Q.lam r)*v := by ring
  · have H := hshape.1 hrI ⟨hv.1.le,hv.2⟩ (le_of_not_ge hvr)
    exact H.trans (by
      calc
        laplaceComparisonStrength Q.data.d Q.lam r =
            1*laplaceComparisonStrength Q.data.d Q.lam r := by ring
        _ ≤ J*laplaceComparisonStrength Q.data.d Q.lam r :=
          mul_le_mul_of_nonneg_right hJ her)

theorem outer_truncated_local_diameter_scaled_draft
    {K v : ℝ} (hv : 0 < v)
    (hwall : Q.data.E/Q.data.d^3 =
      comparisonSmallMass Q.data.N Q.data.E*Q.data.s) :
    v*Q.localCapDiameter v K =
      9*K*Real.log Q.data.N*
        (comparisonSmallMass Q.data.N Q.data.E*Q.data.s)/Q.data.N^delta := by
  have hpow : 0 < Q.data.N^delta :=
    Real.rpow_pos_of_pos Q.data.hN _
  calc
    v*Q.localCapDiameter v K =
        9*K*Real.log Q.data.N*(Q.data.E/Q.data.d^3)/Q.data.N^delta := by
      unfold localCapDiameter
      field_simp [hv.ne',Q.data.hd.ne',hpow.ne']
    _ = _ := by rw [hwall]

theorem outer_truncated_budget_atoms_draft
    (ell : ℕ) (Qraw K cut v : ℝ) :
    let L := Real.log Q.data.N
    let z := min (K*v) 1
    let e := laplaceComparisonStrength Q.data.d Q.lam v
    let ez := laplaceComparisonStrength Q.data.d Q.lam
      (Q.shiftedNativeModel.R z)
    let y := Q.xs+z
    let M := K*v
    let P := Q.data.N*ez
    let diam := Q.localCapDiameter v K
    let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*Qraw)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
    let F := nativeBinScaleLoss (30*L) (108*K^2*L^2)
      (54*K^2*L^2) M (v/2)
    e*Q.ordinaryOptimizedBudget ell Qraw K (30*L) cut
      M (v/2) y v K (Q.shiftedNativeModel.R z) =
      e*(F*M*(2*((Qraw^2*y)/(P*M^2))^((2:ℝ)/3)+
          3/(P*M^2)+diam^2+rev)+
        18*(((Qraw^2*y)^2*P*M^2)^((1:ℝ)/3)+2)*cut) := by
  rfl

theorem eq7_outer_cap_travel_le
    (hN : 2 ≤ Q.data.N) :
    Q.cavityCapTravel ≤
      2*Real.log Q.data.N*
        comparisonSmallMass Q.data.N Q.data.E/Q.data.N^delta := by
  let N := Q.data.N
  let U := comparisonSmallMass N Q.data.E
  let L := comparisonConstraintLength N Q.data.E Q.data.d
  have hN0 : 0 < N := Q.data.hN
  have hU : 0 < U := Q.data.hU
  have hL : 0 < L := Q.data.hL
  have hNL : 0 < N^delta := Real.rpow_pos_of_pos hN0 _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hLU : L ≤ U := min_le_left _ _
  have hd2 : Q.data.d^2 ≤ 1 :=
    pow_le_one₀ Q.data.hd.le Q.data.hd1
  have hNE : N*Q.data.E ≤ Real.sqrt N := by
    have H : Real.sqrt N*Q.data.E ≤ 1 := Q.hupper.trans hd2
    calc
      N*Q.data.E = (Real.sqrt N)^2*Q.data.E := by
        rw [Real.sq_sqrt hN0.le]
      _ = Real.sqrt N*(Real.sqrt N*Q.data.E) := by ring
      _ ≤ Real.sqrt N*1 :=
        mul_le_mul_of_nonneg_left H (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have hNsq : N ≤ N^2 := by nlinarith only [hN]
  have hNroot : Real.sqrt N ≤ N := by
    simpa only [Real.sqrt_sq hN0.le] using Real.sqrt_le_sqrt hNsq
  have hlogcap : Real.log ((1+U)/U) ≤ 2*Real.log N := by
    have heq : (1+U)/U = 1+N*Q.data.E := by
      dsimp only [U,comparisonSmallMass]
      field_simp [hN0.ne',Q.data.hE.ne']
      ring
    have hpos : 0 < 1+N*Q.data.E := by positivity [Q.data.hE]
    have hle : 1+N*Q.data.E ≤ N^2 := by
      nlinarith only [hNE,hNroot,hN]
    rw [heq]
    calc
      Real.log (1+N*Q.data.E) ≤ Real.log (N^2) :=
        Real.log_le_log hpos hle
      _ = 2*Real.log N := by rw [Real.log_pow]; norm_num
  have hlogcap0 : 0 ≤ Real.log ((1+U)/U) := by
    apply Real.log_nonneg
    exact (one_le_div hU).mpr (by linarith)
  have Hdiv : L/N^delta ≤ U/N^delta :=
    div_le_div_of_nonneg_right hLU hNL.le
  have H := mul_le_mul Hdiv hlogcap hlogcap0
    (div_nonneg hU.le hNL.le)
  dsimp only [cavityCapTravel]
  calc
    (L/N^delta)*Real.log ((1+U)/U) ≤
        (U/N^delta)*(2*Real.log N) := H
    _ = 2*Real.log N*U/N^delta := by ring

theorem eq7_outer_group_strength_mass_le
    (hN : 1 ≤ Q.data.N) (hnd : 1/Q.data.N ≤ Q.data.d)
    (hlog : 1 ≤ Real.log Q.data.N)
    {v : ℝ} (hv : v∈Ioc (0:ℝ) 1) :
    laplaceComparisonStrength Q.data.d Q.lam v*v ≤
      2*Real.log Q.data.N*Q.data.d^3 := by
  have H := laplaceComparisonStrength_le_log_cubic hN Q.data.hd hnd
    Q.hlam Q.hld hv.1 hv.2
  have Hmul := mul_le_mul_of_nonneg_right H hv.1.le
  have hlog2 : 1+Real.log Q.data.N ≤ 2*Real.log Q.data.N := by
    linarith
  have Hd := mul_le_mul_of_nonneg_right hlog2
    (pow_nonneg Q.data.hd.le 3)
  calc
    laplaceComparisonStrength Q.data.d Q.lam v*v ≤
        ((1+Real.log Q.data.N)*Q.data.d^3/v)*v := Hmul
    _ = (1+Real.log Q.data.N)*Q.data.d^3 := by
      field_simp [hv.1.ne']
    _ ≤ 2*Real.log Q.data.N*Q.data.d^3 := by
      nlinarith only [Hd]

theorem eq7_native_cap_cubic_price
    (hC0 : 0 < C0) :
    Q.data.d^3*(comparisonSmallMass Q.data.N Q.data.E)^2 ≤
      C0^3*Q.data.N^(-3*m)*Q.data.E := by
  have H := mul_le_mul_of_nonneg_right
    (Q.original_critical_energy_ratio hC0) Q.data.hE.le
  calc
    Q.data.d^3*(comparisonSmallMass Q.data.N Q.data.E)^2 =
        (Q.data.d^3/(Q.data.N^2*Q.data.E^3))*Q.data.E := by
      dsimp only [comparisonSmallMass]
      field_simp [Q.data.hN.ne',Q.data.hE.ne']
    _ ≤ _ := H

theorem eq7_outer_cap_width_energy_rate
    (hC0 : 0 < C0) (hN : 2 ≤ Q.data.N)
    (hnd : 1/Q.data.N ≤ Q.data.d)
    (hlog : 1 ≤ Real.log Q.data.N)
    {a C v lo hi : ℝ} (_ha : 0 < a) (hC : 0 ≤ C)
    (hv : v∈Ioc (0:ℝ) 1)
    (hwidth : hi-lo ≤ C*v) :
    let K := max 1 (cu/a)
    16*(K*laplaceComparisonStrength Q.data.d Q.lam v)*
        Q.cavityCapTravel^2*(hi-lo) ≤
      128*K*C*(Real.log Q.data.N)^3*
        (C0^3*Q.data.N^(-3*m)*Q.data.E)/(Q.data.N^delta)^2 := by
  let K := max 1 (cu/a)
  let e := laplaceComparisonStrength Q.data.d Q.lam v
  let U := comparisonSmallMass Q.data.N Q.data.E
  let L := Real.log Q.data.N
  have hK : 0 ≤ K := (zero_le_one.trans (le_max_left _ _))
  have he : 0 ≤ e := (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
  have hL : 0 ≤ L := by linarith
  have hU : 0 ≤ U := Q.data.hU.le
  have hNdelta : 0 < Q.data.N^delta :=
    Real.rpow_pos_of_pos Q.data.hN _
  have htravel0 : 0 ≤ Q.cavityCapTravel := Q.cavityCapTravel_nonneg
  have htravel := (eq7_outer_cap_travel_le Q) hN
  have htravelSq := pow_le_pow_left₀ htravel0 htravel 2
  have heMass := (eq7_outer_group_strength_mass_le Q)
    (by linarith : 1 ≤ Q.data.N) hnd hlog hv
  have henergy : e*(hi-lo) ≤ 2*C*L*Q.data.d^3 := by
    calc
      e*(hi-lo) ≤ e*(C*v) := mul_le_mul_of_nonneg_left hwidth he
      _ = C*(e*v) := by ring
      _ ≤ C*(2*L*Q.data.d^3) := mul_le_mul_of_nonneg_left heMass hC
      _ = 2*C*L*Q.data.d^3 := by ring
  have hcritical := (eq7_native_cap_cubic_price Q) hC0
  have hcriticalScaled := mul_le_mul_of_nonneg_left hcritical
    (show 0 ≤ 128*K*C*L^3/(Q.data.N^delta)^2 by positivity)
  change 16*(K*e)*Q.cavityCapTravel^2*(hi-lo) ≤ _
  calc
    16*(K*e)*Q.cavityCapTravel^2*(hi-lo) =
        (16*K)*(e*(hi-lo))*Q.cavityCapTravel^2 := by ring
    _ ≤ (16*K)*(2*C*L*Q.data.d^3)*Q.cavityCapTravel^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left henergy (by positivity))
        (sq_nonneg _)
    _ ≤ (16*K)*(2*C*L*Q.data.d^3)*
        (2*L*U/Q.data.N^delta)^2 := by
      exact mul_le_mul_of_nonneg_left htravelSq (by positivity [Q.data.hd])
    _ = (128*K*C*L^3/(Q.data.N^delta)^2)*
        (Q.data.d^3*U^2) := by
      field_simp [hNdelta.ne']
      ring
    _ ≤ (128*K*C*L^3/(Q.data.N^delta)^2)*
        (C0^3*Q.data.N^(-3*m)*Q.data.E) := hcriticalScaled
    _ = 128*K*C*(Real.log Q.data.N)^3*
        (C0^3*Q.data.N^(-3*m)*Q.data.E)/(Q.data.N^delta)^2 := by
      dsimp only [L]
      ring

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
