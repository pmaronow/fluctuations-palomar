module

public import ComparisonNativeCavityRadiusPolynomialAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000

theorem actual_minimum_cavity_radius_band_eventually_polynomial_bound_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ→ℝ)
    (Hgeometry : ∀ᶠn in atTop,
      0 < a n ∧ a n ≤ z n ∧ z n ≤ 1 ∧ (M n).xs ≤ W n ∧ W n ≤ z n ∧
      z n ≤ C*W n ∧ ca*W n ≤ (M n).alpha.val.val (a n) ∧
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (a n) (z n)) ∧
        LipschitzOnWith Kh (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (a n) (z n))) :
    ∀ᶠn in atTop,(M n).cavityRadiusDefect (a n) (z n)/(W n)^3 ≤
      ((dim n+1:ℕ):ℝ)^(-min (delta/64) (1/16)) := by
  obtain ⟨n0,Hn0⟩ := eventually_atTop.mp Hgeometry
  have Hg n := Hn0 (n+n0) (Nat.le_add_left n0 n)
  choose Kb Kh hparent hfield using fun n=>(Hg n).2.2.2.2.2.2.2
  have H := actual_minimum_cavity_radius_band_polynomial_bound_along
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hC hca
    (fun n=>dim (n+n0)) (hdim.comp (tendsto_add_atTop_nat n0))
    (fun n=>M (n+n0)) (fun n=>W (n+n0)) (fun n=>a (n+n0)) (fun n=>z (n+n0))
    (fun n=>(Hg n).1) (fun n=>(Hg n).2.1) (fun n=>(Hg n).2.2.1)
    (fun n=>(Hg n).2.2.2.1) (fun n=>(Hg n).2.2.2.2.1)
    (fun n=>(Hg n).2.2.2.2.2.1) (fun n=>(Hg n).2.2.2.2.2.2.1)
    (fun n=>Fintype.card (FeatureIndex (dim (n+n0)+1))-1)
    (fun n=>cavityCanonicalFeatureEquiv (dim (n+n0))) Kb Kh hparent hfield
  obtain ⟨n1,Hn1⟩ := eventually_atTop.mp H
  filter_upwards [eventually_ge_atTop (n0+n1)] with n hn
  have he : n-n0+n0=n := Nat.sub_add_cancel (by omega)
  obtain ⟨k,rfl⟩ : ∃k,n=k+n0 := ⟨n-n0,he.symm⟩
  exact Hn1 k (by omega)

theorem actual_minimum_cavity_radius_band_eventually_tendsto_zero_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ→ℝ)
    (Hgeometry : ∀ᶠn in atTop,
      0 < a n ∧ a n ≤ z n ∧ z n ≤ 1 ∧ (M n).xs ≤ W n ∧ W n ≤ z n ∧
      z n ≤ C*W n ∧ ca*W n ≤ (M n).alpha.val.val (a n) ∧
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (a n) (z n)) ∧
        LipschitzOnWith Kh (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (a n) (z n))) :
    Tendsto (fun n=>(M n).cavityRadiusDefect (a n) (z n)/(W n)^3) atTop (𝓝 0) := by
  have hp : 0 < min (delta/64) (1/16:ℝ) := lt_min (by positivity) (by norm_num)
  have Hpow : Tendsto (fun n=>((dim n+1:ℕ):ℝ)^(-min (delta/64) (1/16))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  apply squeeze_zero' _ (actual_minimum_cavity_radius_band_eventually_polynomial_bound_along
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hC hca dim hdim M W a z Hgeometry) Hpow
  filter_upwards [Hgeometry] with n hn
  have hW : 0 < W n := (M n).hxs.trans_le hn.2.2.2.1
  apply div_nonneg _ (pow_pos hW 3).le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hmom := comparisonVariableEndpoint_radius_moments (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (dim n+1) (by omega)
    (M n).b (M n).h (M n).context.hd.ne' (M n).hlam.le (M n).hlb
    (M n).hb (M n).hh (M n).hh0 (M n).alpha
  exact sub_nonneg.mpr ((hmom.2.2 r ⟨hn.1.le.trans hr.1.le,hr.2.le.trans hn.2.2.1⟩).2.1)

end OAI.SKFluctuations.LaplaceWindowFormalization
