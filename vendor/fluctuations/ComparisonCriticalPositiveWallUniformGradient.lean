module

public import ComparisonCriticalPositiveWallSpinProfileCompactness
public import ComparisonCriticalPositiveWallStrengthIdentity
public import ComparisonBoundedPrincipalIntegrability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 12000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem critical_wall_scaled_gradient_bound_of_second_moment
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : M.xs=M.data.d) {B Q : ℝ} (hB : 0 < B) (hQ : 0 ≤ Q)
    (hsecond : ∀t∈Ioc (0:ℝ) B,M.radiusB (M.xs*t)/M.xs^2 ≤ Q) :
    ∀t∈Ioc (0:ℝ) B,
      |M.actualVirtualScaledGradient t| ≤
        2*B+2*(Q+1)+(Q+1)^2+Q := by
  let s:=M.actualRescaledRadiusSpinProfile
  have hsB : 0 ≤ s.mass B := s.nonneg B
  have hsB2 : (s.mass B)^2 ≤ Q := by
    have H := (M.full_radius_moments.2.2 (M.xs*B)).2.1
    have Hq := hsecond B ⟨hB,le_rfl⟩
    dsimp only [s,actualRescaledRadiusSpinProfile,actualScaledRadiusSpin]
    rw [div_pow]
    exact (div_le_div_of_nonneg_right H (sq_nonneg M.xs)).trans Hq
  have hsBbound : s.mass B ≤ Q+1 := by nlinarith [sq_nonneg (s.mass B-1)]
  intro t ht
  have hP : |comparisonScaledStationarity (laplaceComparisonShape t)
      (laplaceComparisonSlope t) t (s.mass t)| ≤
      2*B+2*s.mass B+(s.mass B)^2 := by
    simpa only [one_mul] using
      comparison_bounded_principal_density_bound s (L:=1) (A:=1)
        (by norm_num) (by norm_num) ⟨ht.1.le,ht.2⟩
  have hPbound : |comparisonScaledStationarity (laplaceComparisonShape t)
      (laplaceComparisonSlope t) t (s.mass t)| ≤
      2*B+2*(Q+1)+(Q+1)^2 := by
    have hsq := pow_le_pow_left₀ hsB hsBbound 2
    nlinarith only [hP,hsBbound,hsq]
  have hD0 : 0 ≤ M.wallRadiusPointDefect (M.xs*t)/M.xs^2 :=
    div_nonneg (sub_nonneg.mpr (M.full_radius_moments.2.2 (M.xs*t)).2.1)
      (sq_nonneg _)
  have hDq : M.wallRadiusPointDefect (M.xs*t)/M.xs^2 ≤ Q := by
    exact (div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _))
      (sq_nonneg _)).trans (hsecond t ht)
  have hpt := comparison_shape_slope_div_bound (A:=1) (t:=t)
    (by norm_num) ht.1.le
  have hpt' : laplaceComparisonSlope t/t∈Icc (0:ℝ) 1 := by
    simpa only [one_mul] using hpt
  have hcoef0 : 0 ≤ laplaceComparisonShape t*laplaceComparisonSlope t/t := by
    rw [mul_div_assoc]
    exact mul_nonneg (laplaceComparisonShape_pos t).le hpt'.1
  have hcoef1 : laplaceComparisonShape t*laplaceComparisonSlope t/t ≤ 1 := by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_right (laplaceComparisonShape_le_one t) hpt'.1).trans
      (by simpa only [one_mul] using hpt'.2)
  have hErr : |laplaceComparisonShape t*laplaceComparisonSlope t/t*
      (M.wallRadiusPointDefect (M.xs*t)/M.xs^2)| ≤ Q := by
    rw [abs_of_nonneg (mul_nonneg hcoef0 hD0)]
    exact (mul_le_mul_of_nonneg_right hcoef1 hD0).trans (by simpa using hDq)
  have hExact := M.critical_wall_scaled_gradient_exact hfixed ht.1.ne'
  change M.actualVirtualScaledGradient t =
    comparisonScaledStationarity (laplaceComparisonShape t)
      (laplaceComparisonSlope t) t (s.mass t)-
    laplaceComparisonShape t*laplaceComparisonSlope t/t*
      (M.wallRadiusPointDefect (M.xs*t)/M.xs^2) at hExact
  rw [hExact]
  exact (abs_sub _ _).trans (by linarith only [hPbound,hErr])

theorem critical_wall_scaled_gradient_bound_of_raw_B
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : M.xs=M.data.d) {B C Kraw : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hKraw : 0 ≤ Kraw)
    (hcap : ∀t∈Ioc (0:ℝ) B,M.alpha.val.val (M.xs*t) ≤ C*M.xs)
    (hraw : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) M.bf M.hf u ≤ Kraw*(M.xs+u)^2) :
    ∀t∈Ioc (0:ℝ) B,
      |M.actualVirtualScaledGradient t| ≤
        2*B+2*(Kraw*(1+C)^2+1)+(Kraw*(1+C)^2+1)^2+
          Kraw*(1+C)^2 := by
  let Q:=Kraw*(1+C)^2
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  apply M.critical_wall_scaled_gradient_bound_of_second_moment hfixed hB hQ
  intro t ht
  let u:=M.alpha.val.val (M.xs*t)
  have hu:=M.alpha.val.property.1 (M.xs*t)
  by_cases hu0:u=0
  · have hzero : M.radiusB (M.xs*t)=0 := by
      simp only [radiusB,u] at hu0 ⊢
      rw [hu0]
      simp only [orderedPathB,orderedPathPair_zero]
    rw [hzero,zero_div]
    exact hQ
  · have hup : 0<u:=lt_of_le_of_ne hu.1 (Ne.symm hu0)
    have HB:=hraw u ⟨hup,hu.2⟩
    have hupper : M.xs+u ≤ (1+C)*M.xs := by
      have HC:=hcap t ht
      nlinarith only [HC]
    have hsq := pow_le_pow_left₀ (add_nonneg M.hxs.le hu.1) hupper 2
    have H:=HB.trans (mul_le_mul_of_nonneg_left hsq hKraw)
    apply (div_le_iff₀ (sq_pos_of_pos M.hxs)).mpr
    calc
      M.radiusB (M.xs*t) = orderedPathB (n+1) M.bf M.hf u := by
        simp only [radiusB,u]
      _ ≤ Kraw*((1+C)*M.xs)^2 := H
      _ = Q*M.xs^2 := by dsimp only [Q];ring

end ActualHighWallOverlapMinimum

theorem eventually_critical_positive_wall_virtual_gradient_bound_along
    {m delta cl cu Az C0 Ct D Bclock B : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hB : 0 < B)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ∃KG : ℝ,0 ≤ KG ∧ ∀ᶠn in atTop,∀t∈Ioc (0:ℝ) B,
      |(M n).actualVirtualScaledGradient t| ≤ KG := by
  obtain ⟨Kraw,hKraw,Hraw⟩ := eventually_actual_high_wall_B_normalized
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=cu*(B+Az)+1
  let Q:=Kraw*(1+C)^2
  let KG:=2*B+2*(Q+1)+(Q+1)^2+Q
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hKG : 0 ≤ KG := by dsimp only [KG,Q];positivity
  have Hcut : ∀ᶠn in atTop,(M n).xs*B ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*B) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const B
    exact H.eventually (eventually_le_nhds zero_lt_one)
  refine ⟨KG,hKG,?_⟩
  have hdim1 : Tendsto (fun n=>dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  filter_upwards [hdim1.eventually Hraw,Hcut] with n hn hncut
  have hcap : ∀t∈Ioc (0:ℝ) B,
      (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs := by
    intro t ht
    have htx : (M n).xs*t ≤ (M n).xs*B :=
      mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le
    let z:=max ((M n).xs*t) (M n).z
    have hz : z∈Icc (M n).z 1 :=
      ⟨le_max_right _ _,max_le (htx.trans hncut) (M n).hz.2⟩
    have hsize : z ≤ (B+Az)*(M n).xs := by
      apply max_le
      · nlinarith [htx,mul_nonneg hAz (M n).hxs.le]
      · nlinarith [(M n).hzxs,mul_nonneg hB.le (M n).hxs.le]
    have H := ((M n).alpha.val.property.2 (le_max_left _ _)).trans
      ((M n).regular z hz).2
    have H' := mul_le_mul_of_nonneg_left hsize hcu.le
    dsimp only [C]
    nlinarith only [H,H',(M n).hxs]
  intro t ht
  exact (M n).critical_wall_scaled_gradient_bound_of_raw_B (hfixed n)
    hB hC hKraw.le hcap (hn (M n)) t ht

end OAI.SKFluctuations.LaplaceWindowFormalization
