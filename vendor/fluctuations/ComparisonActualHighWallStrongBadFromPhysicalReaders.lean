module

public import ComparisonActualHighWallStrongStripFromPhysicalReaders
public import ComparisonActualHighWallStrongScaleRetag

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000

theorem no_actual_high_wall_strong_bad_sequence_from_physical_readers
    {m delta cl cu Az C0 Ct D Bclock T eta : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hD : 0 < D) (hT : 0 < T) (heta : 0 < eta)
    (hclSlack : cl < 2*T*Real.exp (-12*T))
    (hcuSlack :
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hTeq : ∀n,(M n).data.T=T)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (hsD : ∀n,(M n).data.s≤(M n).data.d)
    (hxsD : ∀n,(M n).data.d≤(M n).xs)
    (hstrong : ∀n,eta≤(M n).data.g (M n).xs/(M n).xs^2)
    (hbad : ∀n,(M n).alpha.val.val (M n).xs<cl*(M n).xs ∨
      cu*(M n).xs<(M n).alpha.val.val (M n).xs) :
    False := by
  let K := max 1 (1/Real.sqrt eta)
  have hK : 1≤K := le_max_left _ _
  have hKcap : 1/Real.sqrt eta≤K := le_max_right _ _
  have hroom : delta < 3*m := by linarith only [hmargin,hdelta]
  let Q : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu (Az/Real.sqrt eta) C0 1 D Bclock :=
    fun n=>(M n).atWallScaleOfStrengthLower heta hAz (hsD n) (hstrong n)
  have hAzQ : 0≤Az/Real.sqrt eta := div_nonneg hAz (Real.sqrt_nonneg eta)
  have Hstrip := exists_actual_high_wall_strict_strip_subsequence_from_physical_readers
    hm hdelta hroom hmargin hcl hcu hAzQ hC0 (by norm_num) hD hT
    hclSlack hcuSlack dim hdim Q (fun _=>rfl) hTeq hdlim hsRatio hK
  obtain ⟨chi,_hchi,Hstrict⟩ := Hstrip
  obtain ⟨n,hn⟩ := Hstrict.exists
  have Hcap : (M (chi n)).data.d/Real.sqrt eta ≤ K*(M (chi n)).data.d := by
    have H := mul_le_mul_of_nonneg_right hKcap (M (chi n)).data.hd.le
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using H
  have hr : (M (chi n)).xs∈Icc (Q (chi n)).data.d
      (K*(Q (chi n)).data.d) := by
    change (M (chi n)).data.d≤(M (chi n)).xs ∧
      (M (chi n)).xs≤K*(M (chi n)).data.d
    exact ⟨hxsD (chi n),
      ((M (chi n)).test_le_wall_scale_of_strength_lower heta (hstrong (chi n))).trans Hcap⟩
  have hgood := hn (M (chi n)).xs hr
  change cl*(M (chi n)).xs<(M (chi n)).alpha.val.val (M (chi n)).xs ∧
    (M (chi n)).alpha.val.val (M (chi n)).xs<cu*(M (chi n)).xs at hgood
  rcases hbad (chi n) with hleft | hright
  · exact (not_lt_of_ge hleft.le) hgood.1
  · exact (not_lt_of_ge hright.le) hgood.2

theorem actual_high_wall_bad_test_strength_tendsto_zero_from_physical_readers
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hD : 0 < D) (hT : 0 < T)
    (hclSlack : cl < 2*T*Real.exp (-12*T))
    (hcuSlack :
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hTeq : ∀n,(M n).data.T=T)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (Htest : ∀ᶠn in atTop,(M n).data.d≤(M n).xs ∧
      ((M n).alpha.val.val (M n).xs<cl*(M n).xs ∨
        cu*(M n).xs<(M n).alpha.val.val (M n).xs)) :
    Tendsto (fun n=>(M n).data.g (M n).xs/(M n).xs^2)
      atTop (𝓝 0) := by
  have HsD : ∀ᶠn in atTop,(M n).data.s≤(M n).data.d := by
    filter_upwards [hsRatio.eventually (eventually_le_nhds zero_lt_one)] with n hn
    simpa only [one_mul] using (div_le_iff₀ (M n).data.hd).mp hn
  have Hsmall : ∀eta : ℝ,0<eta→∀ᶠn in atTop,
      (M n).data.g (M n).xs/(M n).xs^2<eta := by
    intro eta heta
    by_contra Hnone
    have Hfreq : ∃ᶠn in atTop,eta≤(M n).data.g (M n).xs/(M n).xs^2 := by
      simpa only [Filter.Frequently,not_le] using Hnone
    obtain ⟨phi,hphi,Hphi⟩ :=
      extraction_of_frequently_atTop (Hfreq.and_eventually (HsD.and Htest))
    exact no_actual_high_wall_strong_bad_sequence_from_physical_readers
      hm hdelta hmargin hcl hcu hAz hC0 hD hT heta hclSlack hcuSlack
      (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) (fun n=>M (phi n))
      (fun n=>hTeq (phi n)) (hdlim.comp hphi.tendsto_atTop)
      (hsRatio.comp hphi.tendsto_atTop) (fun n=>(Hphi n).2.1)
      (fun n=>(Hphi n).2.2.1) (fun n=>(Hphi n).1) (fun n=>(Hphi n).2.2.2)
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  filter_upwards [Hsmall eta heta] with n hn
  have hf : 0≤(M n).data.g (M n).xs/(M n).xs^2 :=
    div_nonneg (laplaceComparisonStrength_pos (M n).data.d
      (sq_pos_of_pos (M n).data.hd) (M n).xs).le (sq_nonneg _)
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hf] using hn

theorem eventually_actual_high_wall_bad_test_strength_lt_uniform_from_physical_readers
    {m delta cl cu Az C0 Ct D Bclock T eta : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hD : 0 < D) (hT : 0 < T) (heta : 0 < eta)
    (hclSlack : cl < 2*T*Real.exp (-12*T))
    (hcuSlack :
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (d s : ℕ→ℝ)
    (hdlim : Tendsto d atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>s n/d n) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀M : ActualHighWallOverlapMinimum (n+1)
        m delta cl cu Az C0 Ct D Bclock,
      M.data.T=T → M.data.d=d n → M.data.s=s n → M.data.d≤M.xs →
      (M.alpha.val.val M.xs<cl*M.xs ∨ cu*M.xs<M.alpha.val.val M.xs) →
      M.data.g M.xs/M.xs^2<eta := by
  classical
  by_contra Hnone
  have Hfreq : ∃ᶠn in atTop,∃M : ActualHighWallOverlapMinimum (n+1)
        m delta cl cu Az C0 Ct D Bclock,
      M.data.T=T ∧ M.data.d=d n ∧ M.data.s=s n ∧ M.data.d≤M.xs ∧
      (M.alpha.val.val M.xs<cl*M.xs ∨ cu*M.xs<M.alpha.val.val M.xs) ∧
      eta≤M.data.g M.xs/M.xs^2 := by
    have Hneg : ∃ᶠn in atTop,¬∀M : ActualHighWallOverlapMinimum (n+1)
          m delta cl cu Az C0 Ct D Bclock,
        M.data.T=T → M.data.d=d n → M.data.s=s n → M.data.d≤M.xs →
        (M.alpha.val.val M.xs<cl*M.xs ∨ cu*M.xs<M.alpha.val.val M.xs) →
        M.data.g M.xs/M.xs^2<eta := by
      simpa only [Filter.Frequently,not_not] using Hnone
    apply Hneg.mono
    intro n hn
    push Not at hn
    exact hn
  obtain ⟨phi,hphi,Hphi⟩ := extraction_of_frequently_atTop Hfreq
  choose M hTeq hd hs hxsD hbad hstrong using Hphi
  have hdlimM : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0) := by
    apply (hdlim.comp hphi.tendsto_atTop).congr'
    exact Eventually.of_forall (fun n=>(hd n).symm)
  have hsRatioM : Tendsto (fun n=>(M n).data.s/(M n).data.d)
      atTop (𝓝 0) := by
    apply (hsRatio.comp hphi.tendsto_atTop).congr'
    exact Eventually.of_forall (fun n=>by simp only [hd n,hs n,Function.comp_apply])
  have Hweak := actual_high_wall_bad_test_strength_tendsto_zero_from_physical_readers
    hm hdelta hmargin hcl hcu hAz hC0 hD hT hclSlack hcuSlack
    phi hphi.tendsto_atTop M hTeq hdlimM hsRatioM
    (Eventually.of_forall (fun n=>⟨hxsD n,hbad n⟩))
  obtain ⟨n,hn⟩ := (Hweak.eventually (gt_mem_nhds heta)).exists
  exact (not_lt_of_ge (hstrong n)) hn

end OAI.SKFluctuations.LaplaceWindowFormalization
