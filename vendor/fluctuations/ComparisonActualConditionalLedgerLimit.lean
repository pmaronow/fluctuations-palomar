module

public import ComparisonNativeBandAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 15000000

theorem actual_conditional_ledger_limit_le
    (B ell : ℕ) (hell : 2<ell) (cut w y Q L diam0 width0 V0 T0 limit : ℝ)
    (hL : 0 ≤ L) (hy : 0 ≤ y) (hdiam0 : 0<diam0)
    (width diam raw V T defect : ℕ→ℝ)
    (hwidth : ∀j,0 ≤ width j) (hdiam : ∀j,0 ≤ diam j)
    (hraw0 : ∀j,0 ≤ raw j) (hraw : ∀j,raw j ≤ Q)
    (hfinite : ∀j,defect j ≤ nativeConditionalLedgerBudget B (width j) cut (w+diam j)
      (V j) (T j) ((diam j)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*raw j)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) L)
    (hwidthlim : Tendsto width atTop (𝓝 width0))
    (hdiamlim : Tendsto diam atTop (𝓝 diam0))
    (hdefectlim : Tendsto defect atTop (𝓝 limit))
    (hV : ∀epsilon : ℝ,0<epsilon→∀ᶠj in atTop,V j ≤ V0+epsilon)
    (hT : ∀epsilon : ℝ,0<epsilon→∀ᶠj in atTop,T j ≤ T0+epsilon) :
    limit ≤ nativeConditionalLedgerBudget B width0 cut (w+diam0) V0 T0
      (diam0^(((ell:ℝ)-2)/((ell:ℝ)-1))*((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) L := by
  let reverse:=fun D : ℝ=>D^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  let C:=66+64*L+65536*(1+L)^2
  have hC : 0 ≤ C:=by dsimp [C];positivity
  have hellR : (2:ℝ)<ell:=by exact_mod_cast hell
  have hden : 0<(ell:ℝ)-1:=by linarith
  have hp : 0 ≤ 1/((ell:ℝ)-1):=div_nonneg zero_le_one hden.le
  have hrev : Tendsto (fun j=>reverse (diam j)) atTop (𝓝 (reverse diam0)):=
    (hdiamlim.rpow_const (Or.inl hdiam0.ne')).mul_const _
  apply le_of_forall_pos_le_add
  intro t ht
  let err:=t/(48+C+1)
  have herr : 0<err:=div_pos ht (by positivity)
  have hupper : ∀ᶠj in atTop,defect j ≤ nativeConditionalLedgerBudget B (width j) cut
      (w+diam j) (V0+err) (T0+err) (reverse (diam j)) L:=by
    filter_upwards [hV err herr,hT err herr] with j hv htj
    have hrj:=hraw0 j
    have hwj:=hwidth j
    have HR : (diam j)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*raw j)^(2*ell)*y^ell)^(1/((ell:ℝ)-1)) ≤ reverse (diam j):=by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hdiam j) _)
      apply Real.rpow_le_rpow (by positivity) _ hp
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hy ell)
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hraw j) (by norm_num)) _
    have HRS:=mul_le_mul_of_nonneg_left HR (show 0 ≤ 32*width j by positivity)
    have HVS:=mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ) ≤ 48)
    have HTS:=mul_le_mul_of_nonneg_left htj hC
    have HF:=hfinite j
    unfold nativeConditionalLedgerBudget at HF ⊢
    dsimp only [C] at HTS
    linarith
  have hlimUpper : Tendsto (fun j=>nativeConditionalLedgerBudget B (width j) cut
      (w+diam j) (V0+err) (T0+err) (reverse (diam j)) L) atTop
      (𝓝 (nativeConditionalLedgerBudget B width0 cut (w+diam0)
        (V0+err) (T0+err) (reverse diam0) L)):=by
    unfold nativeConditionalLedgerBudget
    exact (((tendsto_const_nhds.add
      ((hwidthlim.const_mul _).mul ((hdiamlim.const_add w).pow 2))).add
      ((hwidthlim.const_mul 32).mul hrev)).add tendsto_const_nhds).add tendsto_const_nhds
  have Hlimit:=le_of_tendsto_of_tendsto hdefectlim hlimUpper hupper
  have herrbound : (48+C)*err ≤ t:=by
    dsimp [err]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<48+C+1)).mpr
    nlinarith
  unfold nativeConditionalLedgerBudget at Hlimit ⊢
  dsimp only [C,reverse] at *
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
