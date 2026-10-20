module

public import ComparisonNativeRadiusSingleCutIntegral
public import ComparisonNativeCavityRadiusPolynomialSmoothGeneral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000

 theorem actual_minimum_cavity_radius_single_cut_polynomial_bound_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ→ℝ)
    (Hgeometry : ∀ᶠn in atTop,0 < a n ∧ a n ≤ z n ∧ z n ≤ 1 ∧
      (M n).xs ≤ W n ∧ z n ≤ C*W n ∧ ca*W n ≤ (M n).alpha.val.val (a n) ∧
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1) :
    ∀ᶠn in atTop,(M n).cavityRadiusDefect (a n) (z n)/(W n)^3 ≤
      ((dim n+1:ℕ):ℝ)^(-min (delta/64) (1/16)) := by
  classical
  let cut:=fun n=>Classical.epsilon (fun s : ℝ=>∀l r,(0:ℝ) ≤ l → l ≤ r → r ≤ 1 →
    (r < s ∨ s ≤ l) → ∃Kb Kh : ℝ≥0,
      LipschitzOnWith Kb (fun t=>(M n).b ((M n).alpha.val.val t)) (Icc l r) ∧
      LipschitzOnWith Kh (fun t=>(M n).h ((M n).alpha.val.val t)) (Icc l r))
  let gap:=fun n=>((dim n+1:ℕ):ℝ)^(-(2:ℝ))*(W n)^3
  let left:=fun n=>radiusCutLeft (a n) (z n) (cut n) (gap n)
  let right:=fun n=>radiusCutRight (a n) (z n) (cut n)
  have Hpieces : ∀ᶠn in atTop,
      a n ≤ left n ∧ left n ≤ right n ∧ right n ≤ z n ∧ right n-left n ≤ gap n ∧
      (∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (a n) (left n)) ∧
        LipschitzOnWith Kh (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (a n) (left n))) ∧
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (right n) (z n)) ∧
        LipschitzOnWith Kh (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (right n) (z n)) := by
    filter_upwards [Hgeometry] with n hn
    obtain ⟨ha,haz,hz,hxs,hsize,hmass,hreg⟩:=hn
    have hW : 0 < W n:=(M n).hxs.trans_le hxs
    have hgap : 0 < gap n:=mul_pos (Real.rpow_pos_of_pos (M n).context.hN _) (pow_pos hW 3)
    obtain ⟨hal,hlr,hrz,hwidth,hleft,hright⟩:=radius_single_cut_geometry haz hgap (s:=cut n)
    have Hcut : ∀l r,(0:ℝ) ≤ l → l ≤ r → r ≤ 1 → (r < cut n ∨ cut n ≤ l) →
        ∃Kb Kh : ℝ≥0,
          LipschitzOnWith Kb (fun t=>(M n).b ((M n).alpha.val.val t)) (Icc l r) ∧
          LipschitzOnWith Kh (fun t=>(M n).h ((M n).alpha.val.val t)) (Icc l r) :=
      Classical.epsilon_spec hreg.exists_single_cut
    exact ⟨hal,hlr,hrz,hwidth,Hcut (a n) (left n) ha.le hal (hlr.trans (hrz.trans hz)) hleft,
      Hcut (right n) (z n) (ha.le.trans (hal.trans hlr)) hrz hz hright⟩
  have Hleft := actual_minimum_cavity_radius_smooth_general_eventually_polynomial_bound_along
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hC hca dim hdim M W a left
    (by
      filter_upwards [Hgeometry,Hpieces] with n hn hp
      exact ⟨hn.1,hp.1,hp.2.1.trans (hp.2.2.1.trans hn.2.2.1),hn.2.2.2.1,
        (hp.2.1.trans hp.2.2.1).trans hn.2.2.2.2.1,hn.2.2.2.2.2.1,hp.2.2.2.2.1⟩)
  have Hright := actual_minimum_cavity_radius_smooth_general_eventually_polynomial_bound_along
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hC hca dim hdim M W right z
    (by
      filter_upwards [Hgeometry,Hpieces] with n hn hp
      have Hmass:=(M n).alpha.val.property.2 (hp.1.trans hp.2.1)
      exact ⟨hn.1.trans_le (hp.1.trans hp.2.1),hp.2.2.1,hn.2.2.1,hn.2.2.2.1,
        hn.2.2.2.2.1,hn.2.2.2.2.2.1.trans Hmass,hp.2.2.2.2.2⟩)
  let t:=min (delta/64) (1/16:ℝ)
  have ht : 0 < t:=lt_min (by positivity) (by norm_num)
  have htcap : t ≤ (1:ℝ)/16:=min_le_right _ _
  have Habsorb : ∀ᶠn in atTop,3*((dim n+1:ℕ):ℝ)^(-((3/2)*t)) ≤
      ((dim n+1:ℕ):ℝ)^(-t) := by
    have H:=(tendsto_add_atTop_nat 1).comp hdim |>.eventually
      (eventually_coefficient_rpow_le (c:=3) (d:=1) (q:= -((3/2)*t)) (r:= -t)
        (by norm_num) (by linarith))
    simpa only [one_mul,Function.comp_def] using H
  filter_upwards [Hgeometry,Hpieces,Hleft,Hright,Habsorb] with n hn hp hl hr habs
  have hW : 0 < W n:=(M n).hxs.trans_le hn.2.2.2.1
  have hN1 : (1:ℝ) ≤ ((dim n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (dim n))
  have hi : IntegrableOn (M n).cavityRadiusPointDefect (Icc (a n) (z n)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact (M n).cavityRadiusPointDefect_integrableOn hn.1.le hn.2.2.1
  have Hsum:=radius_integral_single_cut_upper hp.1 hp.2.1 hp.2.2.1 hi
    (fun r hr'=>(M n).cavityRadiusPointDefect_le_one ⟨hn.1.le.trans hr'.1,hr'.2.trans hn.2.2.1⟩)
  have Hdiv:=div_le_div_of_nonneg_right Hsum (pow_pos hW 3).le
  have Hgap : (right n-left n)/(W n)^3 ≤ ((dim n+1:ℕ):ℝ)^(-(2:ℝ)) := by
    have H:=div_le_div_of_nonneg_right hp.2.2.2.1 (pow_pos hW 3).le
    simpa only [gap,mul_div_cancel_right₀ _ (pow_ne_zero 3 hW.ne')] using H
  have Hp2 : ((dim n+1:ℕ):ℝ)^(-(2:ℝ)) ≤ ((dim n+1:ℕ):ℝ)^(-((3/2)*t)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  change (∫r in Ioo (a n) (z n),(M n).cavityRadiusPointDefect r)/(W n)^3 ≤ _
  dsimp only [NativeOverlapMinimum.cavityRadiusDefect] at hl hr
  rw [add_div,add_div] at Hdiv
  change (∫r in Ioo (a n) (left n),(M n).cavityRadiusPointDefect r)/(W n)^3 ≤ _ at hl
  change (∫r in Ioo (right n) (z n),(M n).cavityRadiusPointDefect r)/(W n)^3 ≤ _ at hr
  change 3*((dim n+1:ℕ):ℝ)^(-((3/2)*min (delta/64) (1/16))) ≤ _ at habs
  dsimp only [t] at Hp2
  exact Hdiv.trans (by linarith only [hl,hr,Hgap,Hp2,habs])

end OAI.SKFluctuations.LaplaceWindowFormalization
