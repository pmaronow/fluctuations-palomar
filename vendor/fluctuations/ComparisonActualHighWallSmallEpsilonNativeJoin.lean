module

public import ComparisonActualHighWallFixedWallFirstChildFailureFromPhysicalReaders
public import ComparisonActualHighWallSelectedBadAllMassChild
public import ComparisonNativeActualConcreteWallRawHistory
public import ComparisonNativeActualWallFinitePropagation
public import ComparisonActualHighWallOriginsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 36000000

theorem exists_uniform_small_epsilon_native_radius
    (T delta : ℝ) (hT : 0 < T) :
    ∃ c0 rho : ℝ, 0 < c0 ∧ c0 ≤ 1 ∧ c0^2 < T/4 ∧
      (((actualPropagationDepth delta:ℕ):ℝ)+2)*c0^2 ≤ rho ∧
      rho ≤ 5*T/8 := by
  let den : ℝ := ((actualPropagationDepth delta:ℕ):ℝ)+2
  have hden : 0 < den := by dsimp [den]; positivity
  have hden2 : 2 ≤ den := by
    dsimp [den]
    have H : 0 ≤ ((actualPropagationDepth delta:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  let c0 : ℝ := min (1/2) (Real.sqrt (T/(4*den)))
  let rho : ℝ := T/2
  have hc0 : 0 < c0 := by
    dsimp [c0]
    exact lt_min (by norm_num) (Real.sqrt_pos.2 (by positivity))
  have hc01 : c0 ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have Hsq : c0^2 ≤ T/(4*den) := by
    have H := pow_le_pow_left₀ hc0.le (min_le_right (1/2:ℝ) (Real.sqrt (T/(4*den)))) 2
    simpa only [Real.sq_sqrt (by positivity : 0 ≤ T/(4*den))] using H
  have Hbudget : den*c0^2 ≤ T/4 := by
    calc
      den*c0^2 ≤ den*(T/(4*den)) := mul_le_mul_of_nonneg_left Hsq hden.le
      _ = T/4 := by field_simp [ne_of_gt hden]
  have hc0Temp : c0^2 < T/4 := by
    have Htwo := mul_le_mul_of_nonneg_right hden2 (sq_nonneg c0)
    linarith only [Htwo,Hbudget,hT]
  refine ⟨c0,rho,hc0,hc01,hc0Temp,?_,?_⟩
  · have Hquarter : T/4 ≤ T/2 := by linarith only [hT]
    simpa only [den,rho] using Hbudget.trans Hquarter
  · change T/2 ≤ 5*T/8
    linarith only [hT]

theorem exists_concrete_fixed_wall_small_epsilon_native_exclusion
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu C0 c0 rho : ℝ,
        0 < m → m < 1/300 → 0 < cl → 0 < cu → 0 < C0 →
        ∀ hc0 : 0 < c0, c0 ≤ 1 → c0^2 < (beta:ℝ)^2/4 →
        (((actualPropagationDepth (m/10000):ℕ):ℝ)+2)*c0^2 ≤ rho →
        rho ≤ 5*(beta:ℝ)^2/8 →
        cl ≤ lower → upper ≤ cu →
        cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
        ∀ P : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1)
          m (m/10000) cl cu 2 C0 1 1 ((beta:ℝ)^2),
        (∀ n, (P n).data.T = (beta:ℝ)^2) →
        (∀ᶠ n in atTop, (P n).data.E = wallHighError m (dim n+1)) →
        (∀ᶠ n in atTop, (P n).data.d = wallHighD m (dim n+1)) →
        (∀ᶠ n in atTop, (P n).data.s = wallHighMass m (dim n+1)) →
        (∀ n, (P n).xs ≤ 1) →
        (∀ᶠ n in atTop, (P n).data.epsilon < (beta:ℝ)^2/4) →
        (∀ n, (P n).data.d ≤ (P n).xs) →
        (∀ n, (P n).alpha.val.val (P n).xs < cl*(P n).xs ∨
          cu*(P n).xs < (P n).alpha.val.val (P n).xs) → False := by
  classical
  obtain ⟨lowerF, upperF, hlowerF, hupperF, Hfirst⟩ :=
    ActualHighWallOverlapMinimum.exists_concrete_fixed_wall_first_child_pressure_failure_from_physical_readers
      hbeta hTemp
  obtain ⟨lowerP, upperP, hlowerP, hupperP, Hprop⟩ :=
    NativeOverlapMinimum.exists_actual_wall_history_finite_propagation hbeta hTemp
  refine ⟨min lowerF lowerP, max upperF upperP,
    lt_min hlowerF hlowerP, hupperF.trans_le (le_max_left _ _), ?_⟩
  intro m cl cu C0 c0 rho hm hmmax hcl hcu hC0 hc0 hc01 hc0Temp
    hbudget hrho hclBounds hcuBounds hclTemp hcuTemp dim hdim P hT hE hd hs
    hunit heps hdxs hbad
  let T : ℝ := (beta:ℝ)^2
  let delta : ℝ := m/10000
  have hTpos : 0 < T := zero_lt_one.trans hTemp
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hmsmall : m ≤ (1:ℝ)/120 := by linarith
  have hroom : delta < 3*m := by dsimp [delta]; linarith
  have hmargin : delta/4 < 3*m-99*delta := by dsimp [delta]; linarith
  have hcapmargin : 100*delta < (1:ℝ)/3+m := by dsimp [delta]; linarith
  have hgapmargin : 0 < 9*m-298*delta := by dsimp [delta]; linarith
  have hclF : cl ≤ lowerF := hclBounds.trans (min_le_left _ _)
  have hclP : cl ≤ lowerP := hclBounds.trans (min_le_right _ _)
  have hcuF : upperF ≤ cu := (le_max_left _ _).trans hcuBounds
  have hcuP : upperP ≤ cu := (le_max_right _ _).trans hcuBounds
  have hclTempF : cl < 2*T*Real.exp (-12*T) := by
    have hp : 0 < T*Real.exp (-12*T) := by positivity
    dsimp only [T] at hclTemp ⊢
    linarith
  have hHtest : ∀ᶠ n in atTop, (P n).data.d ≤ (P n).xs ∧
      ((P n).alpha.val.val (P n).xs < cl*(P n).xs ∨
        cu*(P n).xs < (P n).alpha.val.val (P n).xs) :=
    Eventually.of_forall (fun n => ⟨hdxs n, hbad n⟩)
  have Hfailure := Hfirst m cl cu 2 C0 c0 hm hmmax hcl hcu (by norm_num) hC0
    hc0 hc01 hc0Temp hclF hcuF hclTempF hcuTemp dim hdim P hT hE hd hs
    hunit hHtest

  have HN : Tendsto (fun n => ((dim n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have HDlim : Tendsto (fun n => (P n).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-15*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hd] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighD
    congr 1
    ring
  have HSratio : Tendsto (fun n => (P n).data.s/(P n).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ) < 10) hm)).comp HN
    apply H.congr'
    filter_upwards [hs, hd] with n hns hnd
    simp only [Function.comp_apply]
    rw [hns, hnd]
    unfold wallHighMass wallHighD
    rw [←Real.rpow_sub (by positivity : (0:ℝ) < ((dim n+1:ℕ):ℝ))]
    congr 1
    ring
  have Hweak : Tendsto (fun n => (P n).data.g (P n).xs/(P n).xs^2)
      atTop (𝓝 0) :=
    actual_high_wall_bad_test_strength_tendsto_zero_from_physical_readers
      hm hdelta (by dsimp [delta]; linarith) hcl hcu (by norm_num) hC0
      zero_lt_one hTpos hclTempF hcuTemp dim hdim P hT HDlim HSratio hHtest
  have Htarget : ∀ᶠ n in atTop,
      comparisonConditionalScale (P n).data.N delta (P n).data.E
        ((P n).data.d^2) ≤ (P n).xs := by
    filter_upwards [hE,hd] with n hnE hnd
    have H := concrete_wall_conditional_scale_le_d hm.le (P n).data.hn
    rw [←hnE, ←hnd] at H
    exact H.trans (hdxs n)
  have Hroom : ∀ᶠ n in atTop,
      (c0*(P n).xs)^2 ≤ (P n).data.b (P n).alpha 0 := by
    filter_upwards [heps] with n hnE
    have He : (P n).data.epsilon ≤ (P n).data.T/4 := by
      rw [hT n]
      exact hnE.le
    have Hmatrix := (P n).data.changed_low_matrix_lower_of_small_epsilon
      (P n).alpha He (P n).data.hs.1
    have Hchild : (c0*(P n).xs)^2 ≤ c0^2 := by
      have Hmul : 0 ≤ c0*(P n).xs := mul_nonneg hc0.le (P n).hxs.le
      have Hbound : c0*(P n).xs ≤ c0 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hunit n) hc0.le
      exact pow_le_pow_left₀ Hmul Hbound 2
    rw [hT n] at Hmatrix
    have hc0TempT : c0^2 < T/4 := hc0Temp
    linarith only [Hmatrix,Hchild,hc0TempT,hTpos]
  have Hweak1 := Hweak.eventually (eventually_le_nhds zero_lt_one)
  have Hselect := hdim.eventually
    (ActualHighWallOverlapMinimum.eventually_exists_selected_bad_all_mass_child
      (Az := 2) (Ct := 1) (D := 1) (Bclock := T)
      hm hdelta hroom hcl (by
        simpa only [mul_one, (P 0).alpha.property.2.1] using
          ((P 0).regular 1 ⟨(P 0).hz.2,le_rfl⟩).1)
      (by
        simpa only [mul_one, (P 0).alpha.property.2.1] using
          ((P 0).regular 1 ⟨(P 0).hz.2,le_rfl⟩).2)
      (by norm_num) (by norm_num) hC0 hc0 hmargin)
  have Hchild : ∀ᶠ n in atTop,
      ∃ Q : NativeOverlapMinimum (dim n+1) m delta cl cu 2 C0 1 1 T,
        Q.context.d = c0*(P n).xs ∧
        Q.context.E = actualChildErrorBudget (dim n+1) delta c0
          (P n).data.d ((P n).data.d^2) (P n).xs ∧
        (P n).data.N^(delta/4)*(P n).data.E ≤ Q.context.E ∧
        Q.xs ∈ Icc (comparisonConditionalScale Q.context.N delta Q.context.E Q.lam) 1 ∧
        Q.z = min (2*Q.xs) 1 ∧
        (Q.alpha.val.val Q.xs < cl*Q.xs ∨ cu*Q.xs < Q.alpha.val.val Q.xs) ∧
        Q.b = (P n).data.b (P n).alpha ∧ Q.h = (P n).data.h (P n).alpha := by
    filter_upwards [Hfailure,Hweak1,Htarget,Hroom,Hselect,heps]
      with n hnF hnW hnTarget hnRoom hnSelect hnE
    have hchild1 : c0*(P n).xs ≤ 1 := by
      have H := mul_le_mul_of_nonneg_left (hunit n) hc0.le
      have Hc : c0*(P n).xs ≤ c0 := by simpa only [mul_one] using H
      exact Hc.trans hc01
    have hw : (P n).data.g (P n).xs ≤ (P n).xs^2 :=
      (div_le_one₀ (sq_pos_of_pos (P n).hxs)).mp hnW
    have hfailAll : (P n).data.N^(20*delta)*actualChildErrorBudget
        (dim n+1) delta c0 (P n).data.d ((P n).data.d^2) (P n).xs <
          (P n).macroAllMassChildSweepCost hc0 := by
      have He : (P n).data.epsilon < (P n).data.T/4 := by
        simpa only [hT n] using hnE
      rw [ActualHighWallOverlapMinimum.macroFixedMarginChildSweepCost,
        ite_eq_left He] at hnF
      simpa only [ActualHighWallData.N,delta] using hnF
    have H := hnSelect (P n) hchild1 hchild1 hnTarget hw hnRoom hfailAll
    simpa only [ActualHighWallData.N] using H
  obtain ⟨n0,Hn0⟩ := eventually_atTop.mp Hchild
  let shift := fun n : ℕ => n+n0
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_right hij n0
  let dim0 := fun n => dim (shift n)
  let P0 := fun n => P (shift n)
  have hdim0 : Tendsto dim0 atTop atTop := hdim.comp hshift.tendsto_atTop
  choose Q hQd hQE hQgrow hQtest hQz hQbad hQb hQh using
    fun n => Hn0 (shift n) (by dsimp [shift]; omega)
  have Hraw : ActualWeakSelectedHistoryChain c0 Q Q := .root
  let G : ActualNativeWallHistory Q T c0 :=
    Hraw.concrete_wall_raw_history hm hmsmall hcl (by norm_num) hC0 hc0 hc01
      hTpos dim0 hdim0 P0 Q Q
      (Eventually.of_forall (fun n => hT (shift n)))
      (hshift.tendsto_atTop.eventually hE)
      (hshift.tendsto_atTop.eventually hd)
      (hshift.tendsto_atTop.eventually hs)
      (fun n => (P0 n).xs) (fun n => (P0 n).hxs)
      (Eventually.of_forall (fun n => hunit (shift n)))
      (hshift.tendsto_atTop.eventually Htarget)
      (Eventually.of_forall (fun n => (P0 n).hzxs))
      (Hweak.comp hshift.tendsto_atTop)
      (Eventually.of_forall hQd)
      (Eventually.of_forall hQE)
      (Eventually.of_forall (fun n u => congrFun (hQb n) u))
      (Eventually.of_forall (fun n u => congrFun (hQh n) u))
  have Hlimits := G.concrete_wall_limits hmmax hdim0
    (hshift.tendsto_atTop.eventually hd)
    (hshift.tendsto_atTop.eventually hs)
  have HDsquare : Tendsto (fun n => (G.wall n).data.d^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] using Hlimits.2.pow 2
  have Hbase : ∀ᶠ n in atTop, rho ≤ (Q n).b 0 := by
    filter_upwards [G.root_matrix_lower_of_small_epsilon
      ((hshift.tendsto_atTop.eventually heps).mono (fun _ hn => hn.le))
      (HDsquare.eventually (eventually_le_nhds (by positivity : (0:ℝ) < 3*T/8)))]
      with n hn
    exact hrho.trans hn
  have HrootCap : ∀ᶠ n in atTop, (Q n).context.d ≤ c0 := by
    apply Eventually.of_forall
    intro n
    rw [hQd n]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hunit (shift n)) hc0.le
  have HrootUnit : ∀ n, (Q n).xs ≤ 1 := fun n => (hQtest n).2
  have HrootTarget : ∀ᶠ n in atTop,
      comparisonConditionalScale (Q n).context.N delta (Q n).context.E (Q n).lam ≤
        (Q n).xs := Eventually.of_forall (fun n => (hQtest n).1)
  have HrootBad : ∀ᶠ n in atTop,
      ¬(cl*(Q n).xs ≤ (Q n).alpha.val.val (Q n).xs ∧
        (Q n).alpha.val.val (Q n).xs ≤ cu*(Q n).xs) := by
    apply Eventually.of_forall
    intro n Hband
    rcases hQbad n with hlo | hhi
    · exact (not_lt_of_ge Hband.1) hlo
    · exact (not_lt_of_ge Hband.2) hhi
  exact Hprop m delta cl cu 2 C0 1 1 c0 rho hm hdelta hroom hcl hcu
    (by norm_num) hC0 (by norm_num) (by norm_num) hc0 hc01 hc01
    (by simpa only [delta,T] using hbudget) hmargin hcapmargin hgapmargin
    hclP hcuP hclTemp hcuTemp dim0 hdim0 Q G Hlimits.1 Hlimits.2 Hbase
    HrootCap HrootUnit HrootTarget HrootBad

end OAI.SKFluctuations.LaplaceWindowFormalization
