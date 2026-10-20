module

public import ComparisonActualHighWallRadiusSequence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

theorem actual_high_wall_radius_Eq19_dim_tendsto_zero
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ → ℝ)
    (ha : ∀n,(M n).data.rmin < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (hsize : ∀n,z n ≤ C*W n)
    (houter : ∀n,ca*W n ≤ (M n).alpha.val.val (a n))
    (dphys : ℕ → ℕ) (_e : ∀n,Fin (dphys n+1) ≃ FeatureIndex (dim n+1)) :
    Tendsto (fun n=>(M n).wallRadiusDefect (a n) (z n)/(W n)^3) atTop (𝓝 0) := by
  obtain ⟨B,hB,Hbudget⟩ := eventually_actual_high_wall_radius_physical_budget
    Bclock hm hdelta (by linarith) hcl hcu hAz hC0 hCt
  have hshift : Tendsto (fun n:ℕ=>dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  let x := W
  let N := fun n=>(M n).data.N
  let y := fun n=>(M n).xs+(M n).alpha.val.val (z n)
  let L := fun n=>z n-a n
  let S := fun n r=>(M n).radiusS r
  let inc := fun n=>S n (z n)-S n (a n)
  let g := fun n=>(M n).data.g (z n)
  let F := fun n=>N n*(((1/3)/Real.log (N n))*g n)
  let V := fun tau n=>4*inc n/((M n).alpha.val.val (a n)*(tau*x n)^2*(M n).data.k (z n)*F n)
  let T := fun n=>8*inc n/((M n).alpha.val.val (a n)^2*F n)
  let CY := 1+cu*(C+Az)
  let Cs := B*CY
  let p := 1/((Ct+1)*C)
  let gamma := 1/C0
  have hCY : 0 ≤ CY := by dsimp only [CY];positivity
  have hCs : 0 ≤ Cs := mul_nonneg hB.le hCY
  have hp : 0 < p := by dsimp only [p];positivity
  have hgamm : 0 < gamma := one_div_pos.mpr hC0
  have hx n : 0 < x n := (M n).hxs.trans_le (hxsW n)
  have hN n : 0 < N n := (M n).data.hN
  have hzpos n : 0 < z n := (M n).data.hrbounds.1.trans (ha n) |>.trans_le (haz n)
  have hy n : 0 ≤ y n := add_nonneg (M n).hxs.le ((M n).alpha.val.property.1 (z n)).1
  have hL n : 0 ≤ L n := sub_nonneg.mpr (haz n)
  have hlength n : L n ≤ C*x n := by dsimp only [L];linarith [hsize n,ha n,(M n).data.hrbounds.1]
  have hmass n : y n ≤ CY*x n := by
    let t := max (z n) (M n).z
    have ht : t∈Icc (M n).z 1 := ⟨le_max_right _ _,max_le (hz n) (M n).hz.2⟩
    have hzsmall : (M n).z ≤ Az*x n :=
      (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxsW n) hAz)
    have htbound : t ≤ (C+Az)*x n := by
      apply max_le
      · nlinarith [hsize n,mul_nonneg hAz (hx n).le]
      · nlinarith [hzsmall,mul_nonneg (by linarith : 0 ≤ C) (hx n).le]
    have hup := ((M n).alpha.val.property.2 (le_max_left (z n) (M n).z)).trans
      ((M n).regular t ht).2
    have hmul := mul_le_mul_of_nonneg_left htbound hcu.le
    dsimp only [y,CY]
    linarith [hxsW n]
  have hmom n := (M n).radius_moments
  have hinc n : 0 ≤ inc n := sub_nonneg.mpr ((hmom n).1
    ⟨(ha n).le,(haz n).trans (hz n)⟩
    ⟨(ha n).le.trans (haz n),hz n⟩ (haz n))
  have hD n : 0 ≤ (M n).wallRadiusDefect (a n) (z n) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact sub_nonneg.mpr ((hmom n).2.2 r
      ⟨(ha n).le.trans hr.1.le,hr.2.le.trans (hz n)⟩).2.1
  have hlog n : 0 ≤ Real.log (N n) := Real.log_nonneg (by
    dsimp only [N,ActualHighWallData.N];exact_mod_cast Nat.succ_pos (dim n))
  have hV n tau : 0 ≤ V tau n := by
    have hi := hinc n
    have hA := ((M n).alpha.val.property.1 (a n)).1
    have hg := (laplaceComparisonStrength_pos (M n).data.d
      (sq_pos_of_pos (M n).data.hd) (z n)).le
    have hk := comparisonFloor_pos (δ:=delta) (M n).data.hN (M n).data.hU (hzpos n).le
    have hl := hlog n
    dsimp only [V,F,g];positivity
  have hT n : 0 ≤ T n := by
    have hi := hinc n
    have hg := (laplaceComparisonStrength_pos (M n).data.d
      (sq_pos_of_pos (M n).data.hd) (z n)).le
    have hl := hlog n
    dsimp only [T,F,g];positivity
  have hbound : ∀ᶠn : ℕ in atTop,inc n ≤ Cs*x n := by
    filter_upwards [hdim.eventually Hbudget] with n hn
    have H := (hn (M n) (a n) (z n) (ha n) (haz n) (hz n) (dphys n) (_e n)).1
    have hmul := mul_le_mul_of_nonneg_left (hmass n) hB.le
    dsimp only [inc,S,y,Cs] at *
    linarith
  have hupper n : (M n).data.E ≤ (M n).data.d^2/Real.sqrt (N n) := by
    exact (le_div_iff₀ (Real.sqrt_pos.mpr (hN n))).mpr
      (by simpa only [N,mul_comm] using (M n).hupper)
  have hlower n : gamma*(N n)^(-(2:ℝ)/3+m)*(M n).data.d ≤ (M n).data.E := by
    have H : ((N n)^(-(2:ℝ)/3+m)*(M n).data.d)/C0 ≤ (M n).data.E :=
      (div_le_iff₀ hC0).mpr (by simpa only [N,mul_comm] using (M n).hlower)
    simpa only [gamma,N,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hax n : Real.sqrt (N n)*(M n).data.E/(M n).data.d ≤ x n :=
    (M n).hscale.trans (hxsW n)
  have hstrength n : p*N n*(M n).data.E^2 ≤ g n*(x n)^2 := by
    have H := wall_radius_strength_band_scale (M n).data.hd
      (sq_pos_of_pos (M n).data.hd) (M n).hxs (hzpos n) (hz n)
      (hxsW n) hC (hsize n)
    have hc : 0 < (Ct+1)*C := by positivity
    have H'' : N n*(M n).data.E^2 ≤ ((Ct+1)*C)*(g n*(x n)^2) := by
      have hg := (laplaceComparisonStrength_pos (M n).data.d
        (sq_pos_of_pos (M n).data.hd) (z n)).le
      dsimp only [g,x,N] at *
      nlinarith [(M n).htest,mul_nonneg hg (sq_nonneg (W n))]
    have hd : (N n*(M n).data.E^2)/((Ct+1)*C) ≤ g n*(x n)^2 :=
      (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using H'')
    simpa only [p,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hd
  have hlogevent : ∀ᶠn : ℕ in atTop,1 ≤ Real.log (N n) := by
    simpa only [N,ActualHighWallData.N,Function.comp_def] using
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hshift).eventually
        (eventually_ge_atTop 1)
  have hshiftbound : ∀ᶠn : ℕ in atTop,(N n)^(2*delta)*
      comparisonSmallMass (N n) (M n).data.E ≤ x n := by
    filter_upwards [hshift.eventually (comparison_radius_floor_shift_eventually hgamm hmargin)] with n hn
    exact hn (M n).data.d (M n).data.E (x n) (M n).data.hd
      (hlower n) (hupper n) (hax n)
  have hVupper : ∀ᶠn:ℕ in atTop,∀tau:ℝ,0<tau→V tau n/(x n)^2 ≤
      (12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log (N n)/(N n)^delta := by
    filter_upwards [hbound,hlogevent,hshiftbound] with n hninc hnlog hnshift
    intro tau htau
    have hg : 0 < g n := laplaceComparisonStrength_pos (M n).data.d
      (sq_pos_of_pos (M n).data.hd) (z n)
    have hkC : 0 < comparisonFloor (N n) delta
        (comparisonSmallMass (N n) (M n).data.E) (C*x n) :=
      comparisonFloor_pos (δ:=delta) (M n).data.hN (M n).data.hU
        (mul_nonneg (by linarith) (hx n).le)
    have hF : 0 < F n := by dsimp only [F];positivity
    have hA : 0 < (M n).alpha.val.val (a n) := (mul_pos hca (hx n)).trans_le (houter n)
    have hkz : comparisonFloor (N n) delta
        (comparisonSmallMass (N n) (M n).data.E) (C*x n) ≤ (M n).data.k (z n) := by
      have hnp : 0 < N n := hN n
      have hup : 0 < comparisonSmallMass (N n) (M n).data.E := (M n).data.hU
      have hzp : 0 < z n := hzpos n
      have hden : 0 < z n+(N n)^(2*delta)*comparisonSmallMass (N n) (M n).data.E := by positivity
      unfold ActualHighWallData.k concreteWallFloor comparisonFloor
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden)
        (pow_le_pow_left₀ hden.le (by linarith [hsize n]) 2)
    have hdenC : 0 < (M n).alpha.val.val (a n)*(tau*x n)^2*
        comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).data.E) (C*x n)*F n := by
      have hxp : 0 < x n := hx n
      positivity
    have hmono : V tau n ≤ 4*inc n/((M n).alpha.val.val (a n)*(tau*x n)^2*
        comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).data.E) (C*x n)*F n) := by
      have hi := hinc n
      apply div_le_div_of_nonneg_left (by positivity) hdenC
      gcongr
    have H := comparison_radius_variance_budget_normalized (hN n) (M n).data.hE hg
      (hx n) (by linarith : 0 ≤ C) htau hca hCs hp (hlog n) (hinc n) hninc
      (houter n) hnshift (hstrength n)
    exact (div_le_div_of_nonneg_right hmono (sq_nonneg (x n))).trans H
  have hTupper : ∀ᶠn:ℕ in atTop,T n/(x n)^3 ≤
      ((24*Cs/(ca^2*p))/gamma^6)*Real.log (N n)/(N n)^(6*m) := by
    filter_upwards [hbound] with n hninc
    have hg : 0 < g n := laplaceComparisonStrength_pos (M n).data.d
      (sq_pos_of_pos (M n).data.hd) (z n)
    have H := comparison_radius_covariance_budget_normalized (hN n) (M n).data.hE hg
      (hx n) hca hCs hp (hlog n) (hinc n) hninc (houter n) (hstrength n)
    have hr := comparison_radius_small_mass_ratio (hN n) hgamm (M n).data.hd
      (hlower n) (hupper n) (hax n)
    have H' := comparison_radius_ratio_log_power_bound (hN n) hgamm
      (by positivity : 0 ≤ 24*Cs/(ca^2*p)) (hlog n)
      (div_nonneg (comparisonSmallMass_pos (hN n) (M n).data.hE).le (hx n).le) hr
    exact H.trans H'
  have hVlim tau (htau : 0<tau) : Tendsto (fun n=>V tau n/(x n)^2) atTop (𝓝 0) := by
    have hu : ∀ᶠn:ℕ in atTop,V tau n/(x n)^2 ≤
      (12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log (N n)/(N n)^delta := by
      filter_upwards [hVupper] with n hn
      exact hn tau htau
    exact squeeze_zero' (Eventually.of_forall (fun n=>div_nonneg (hV n tau) (sq_nonneg _))) hu
      (by simpa only [N,ActualHighWallData.N,Function.comp_def,mul_zero,←mul_div_assoc] using
        (((comparison_radius_log_power_tendsto hdelta).comp hshift).const_mul
          (12*Cs*(C+1)^2/(ca*tau^2*p))))
  have hTlim : Tendsto (fun n=>T n/(x n)^3) atTop (𝓝 0) := by
    exact squeeze_zero' (Eventually.of_forall (fun n=>div_nonneg (hT n) (pow_nonneg (hx n).le 3)))
      hTupper (by simpa only [N,ActualHighWallData.N,Function.comp_def,mul_zero,←mul_div_assoc] using
        (((comparison_radius_log_power_tendsto (by linarith : 0<6*m)).comp hshift).const_mul
          ((24*Cs/(ca^2*p))/gamma^6)))
  apply comparisonRadiusOrderedDefect_tendsto_zero x L y
    (fun n=>(M n).wallRadiusDefect (a n) (z n)) T V
    hB.le (by linarith : 0 ≤ C) hCY hx hL
    hlength hy hmass
    hD hT (fun tau htau n=>hV n tau) hVlim hTlim
  intro bins hbins tau htau
  filter_upwards [hdim.eventually Hbudget] with n hn
  have H := (hn (M n) (a n) (z n) (ha n) (haz n) (hz n) (dphys n) (_e n)).2
    bins hbins (tau*x n) (mul_pos htau (hx n))
  simpa only [L,y,V,T,F,g,S,inc,N,ActualHighWallData.N,
    Nat.cast_add,Nat.cast_one,mul_assoc] using H

theorem actual_high_wall_radius_Eq19_regular_band_dim_tendsto_zero
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ → ℝ)
    (ha : ∀n,(M n).data.rmin < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (hsize : ∀n,z n ≤ C*W n)
    (hstart : ∀n,max (M n).z (W n) ≤ a n)
    (dphys : ℕ → ℕ) (e : ∀n,Fin (dphys n+1) ≃ FeatureIndex (dim n+1)) :
    Tendsto (fun n=>(M n).wallRadiusDefect (a n) (z n)/(W n)^3) atTop (𝓝 0) := by
  apply actual_high_wall_radius_Eq19_dim_tendsto_zero Bclock hm hdelta hmargin
    hcl hcu hAz hC0 hCt hC hcl dim hdim M W a z ha haz hz hxsW hsize
  · intro n
    have hreg : a n∈Icc (M n).z 1 :=
      ⟨(le_max_left _ _).trans (hstart n),(haz n).trans (hz n)⟩
    have hlow := ((M n).regular (a n) hreg).1
    exact (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (hstart n)) hcl.le).trans hlow
  · exact e

end OAI.SKFluctuations.LaplaceWindowFormalization
