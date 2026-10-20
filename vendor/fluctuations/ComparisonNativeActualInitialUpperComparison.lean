module

public import ComparisonNativeActualInitialShellSweepRegular
public import ComparisonNativeActualInitialUpperFromRegularSweep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem exists_actual_initial_upper_comparison
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2)
    {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,actualInitialUpperComparison ((beta:ℝ)^2) C m n := by
  have hdelta : 0 < m/10000 := by positivity
  obtain ⟨cl,cu,hcl,hcu,hcl1,hcu1,Hregular⟩:=exists_actual_initial_shell_sweep_regular hbeta hTemp
    (delta:=m/10000) (C0:=1) hm hdelta (by linarith) zero_lt_one
    (by linarith) (by linarith) (by linarith)
  have HD : Tendsto (fun n=>(actualInitialUpperNativeParameters m n).d) atTop (𝓝 0) := by
    have H:=(tendsto_rpow_neg_atTop (by linarith : 0 < (1:ℝ)/6-25*m)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have he : -((1:ℝ)/6-25*m)=-(1:ℝ)/6+25*m := by ring
    simpa only [actualInitialUpperNativeParameters,wallInitialD,Function.comp_def,he] using H
  have Hnum n : (actualInitialUpperNativeParameters m n).d ≤ 1 ∧
      Real.sqrt (actualInitialUpperNativeParameters m n).N*(actualInitialUpperNativeParameters m n).E ≤
        (actualInitialUpperNativeParameters m n).d^2 ∧
      (actualInitialUpperNativeParameters m n).N^(-(2:ℝ)/3+m)*(actualInitialUpperNativeParameters m n).d ≤
        1*(actualInitialUpperNativeParameters m n).E := by
    have H:=actual_initial_upper_native_numeric hm hmmax n
    exact ⟨H.1,H.2.1,by simpa only [one_mul] using H.2.2.1⟩
  have HR:=Hregular (actualInitialUpperNativeParameters m) HD Hnum
    (fun _=>0) (fun _=>0) (fun n=>⟨le_rfl,by positivity⟩) (fun _=>⟨le_rfl,zero_le_one⟩)
    tendsto_const_nhds
  have HB : initialShellMatrixClock ((beta:ℝ)^2) 0 0=(fun _=>((beta:ℝ)^2)) := by
    funext u
    unfold initialShellMatrixClock
    split_ifs <;> simp only [sub_zero]
  simp only [HB] at HR
  refine ⟨max 1 (1/cl),zero_lt_one.trans_le (le_max_left _ _),?_⟩
  exact actual_initial_upper_comparison_of_native_sweep_regular hTemp hcl hcu (hcl1.trans hcu1) hm hmmax HR

theorem exists_actual_initial_upper_comparison_real_beta
    (beta : ℝ) (hbeta : 1 < beta) {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,actualInitialUpperComparison (beta^2) C m n := by
  have hb : 0 < beta := zero_lt_one.trans hbeta
  have H:=exists_actual_initial_upper_comparison (beta:=beta.toNNReal)
    (by simpa only [Real.toNNReal_pos] using hb) (by
      rw [Real.coe_toNNReal _ hb.le]
      nlinarith) hm hmmax
  simpa only [Real.coe_toNNReal _ hb.le] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
