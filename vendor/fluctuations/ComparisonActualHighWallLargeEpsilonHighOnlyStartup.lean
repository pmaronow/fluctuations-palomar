module

public import ComparisonActualHighWallFixedWallFirstChildFailureFromPhysicalReaders
public import ComparisonActualHighWallFixedWallFirstHighOnlyBadChild
public import ComparisonActualHighOnlyFixedWallHistory
public import ComparisonActualHighWallOriginsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 36000000
namespace ActualHighWallOverlapMinimum

theorem exists_concrete_fixed_wall_large_epsilon_bad_child_startup
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu C0 c0 : ℝ,
        0 < m → m < 1/300 → 0 < cl → 0 < cu → cl≤cu → 0 < C0 →
        ∀ hc0 : 0 < c0, c0≤1 → c0^2 < (beta:ℝ)^2/4 →
        cl≤lower → upper≤cu →
        cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ→ℕ, Tendsto dim atTop atTop →
        ∀ P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
          m (m/10000) cl cu 2 C0 1 1 ((beta:ℝ)^2),
        (∀ n, (P n).data.T=(beta:ℝ)^2) →
        (∀ᶠ n in atTop, (P n).data.E=wallHighError m (dim n+1)) →
        (∀ᶠ n in atTop, (P n).data.d=wallHighD m (dim n+1)) →
        (∀ᶠ n in atTop, (P n).data.s=wallHighMass m (dim n+1)) →
        (∀ n, (P n).xs≤1) →
        (∀ᶠ n in atTop, (beta:ℝ)^2/4≤(P n).data.epsilon) →
        (∀ n, (P n).data.d≤(P n).xs) →
        (∀ n, (P n).alpha.val.val (P n).xs<cl*(P n).xs ∨
          cu*(P n).xs<(P n).alpha.val.val (P n).xs) →
        ∃ N : ℕ,
          ∃ Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim (n+N)+1)
            m (m/10000) cl cu 2 C0 1 1 ((beta:ℝ)^2),
          ∃ G : ActualHighOnlyOverlapMinimum.ActualFixedWallHighOnlyHistory
            Q ((beta:ℝ)^2) c0,
          G.root=Q ∧ (∀ n, G.wall n=P (n+N)) ∧
          (∀ n, (Q n).xs≤1) ∧
          (∀ᶠ n in atTop, comparisonConditionalScale (Q n).context.N
            (m/10000) (Q n).context.E (Q n).lam≤(Q n).xs) ∧
          (∀ᶠ n in atTop, ¬(cl*(Q n).xs≤(Q n).alpha.val.val (Q n).xs ∧
            (Q n).alpha.val.val (Q n).xs≤cu*(Q n).xs)) := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hfirst⟩ :=
    exists_concrete_fixed_wall_first_child_pressure_failure_from_physical_readers hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu C0 c0 hm hmmax hcl hcu hclcu hC0 hc0 hc01 hc0Temp
    hclBound hcuBound hclSlack hcuSlack dim hdim P hT hE hd hs hunit heps hdxs hbad
  let T : ℝ := (beta:ℝ)^2
  have hTpos : 0 < T := zero_lt_one.trans hTemp
  have hdelta : 0 < m/10000 := by positivity
  have hmsmall : m≤(1:ℝ)/120 := by linarith
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith
  have Htest : ∀ᶠ n in atTop, (P n).data.d≤(P n).xs ∧
      ((P n).alpha.val.val (P n).xs<cl*(P n).xs ∨
        cu*(P n).xs<(P n).alpha.val.val (P n).xs) :=
    Eventually.of_forall (fun n=>⟨hdxs n, hbad n⟩)
  have Hfailure := Hfirst m cl cu 2 C0 c0 hm hmmax hcl hcu (by norm_num)
    hC0 hc0 hc01 hc0Temp hclBound hcuBound hclSlack hcuSlack
    dim hdim P hT hE hd hs hunit Htest
  have HN : Tendsto (fun n=>((dim n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have HDlim : Tendsto (fun n=>(P n).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-15*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hd] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighD
    congr 1
    ring
  have HSlim : Tendsto (fun n=>(P n).data.s) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-5*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [hs] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighMass
    congr 1
    ring
  have HSratio : Tendsto (fun n=>(P n).data.s/(P n).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<10) hm)).comp HN
    apply H.congr'
    filter_upwards [hs, hd] with n hns hnd
    simp only [Function.comp_apply]
    rw [hns, hnd]
    unfold wallHighMass wallHighD
    rw [←Real.rpow_sub (by positivity : (0:ℝ)<((dim n+1:ℕ):ℝ))]
    congr 1
    ring
  have Hweak := actual_high_wall_bad_test_strength_tendsto_zero_from_physical_readers
    hm hdelta (by linarith) hcl hcu (by norm_num) hC0 zero_lt_one hTpos
    hclSlack hcuSlack dim hdim P hT HDlim HSratio Htest
  have Htarget : ∀ᶠ n in atTop, comparisonConditionalScale (P n).data.N
      (m/10000) (P n).data.E ((P n).data.d^2)≤(P n).xs := by
    filter_upwards [hE, hd] with n hnE hnd
    have H := concrete_wall_conditional_scale_le_d hm.le (P n).data.hn
    rw [←hnE, ←hnd] at H
    exact H.trans (hdxs n)
  have Hratio : Tendsto (fun n=>(P n).data.s/comparisonLowerScale
      (P n).data.N (P n).data.E (P n).data.d) atTop (𝓝 0) := by
    apply ((concrete_wall_omission_ratio_tendsto_zero hm).comp
      ((tendsto_add_atTop_nat 1).comp hdim)).congr'
    filter_upwards [hE, hd, hs] with n hnE hnd hns
    simp only [Function.comp_apply, hnE, hnd, hns, ActualHighWallData.N]
  have HchildRatio := actual_wall_omission_ratio_inherits_child_cutoff
    hm hdelta hC0 hc0 (by linarith) dim hdim P (fun n=>(P n).xs)
    (fun n=>(P n).hxs) Htarget Hweak Hratio
  have HmassRatio := HchildRatio.eventually (eventually_le_nhds zero_lt_one)
  have Hs4 := HSlim.eventually (eventually_le_nhds (show (0:ℝ)<1/4 by norm_num))
  have HDsq : Tendsto (fun n=>(P n).data.d^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0)] using HDlim.pow 2
  have HDreserve := HDsq.eventually (eventually_le_nhds
    (show (0:ℝ)<T/4-c0^2 by dsimp [T];linarith))
  have Hreserve : ∀ᶠ n in atTop, (P n).data.d^2+(c0*(P n).xs)^2≤(P n).data.epsilon := by
    filter_upwards [HDreserve, heps] with n hnd hne
    have Hchild := pow_le_pow_left₀ (mul_nonneg hc0.le (P n).hxs.le)
      (show c0*(P n).xs≤c0 from by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hunit n) hc0.le) 2
    dsimp only [T] at hnd
    linarith only [hnd, Hchild, hne]
  have Hweak1 := Hweak.eventually (eventually_le_nhds zero_lt_one)
  have Hselect := hdim.eventually
    (eventually_exists_selected_bad_fixed_wall_high_only_child
      (Az:=2) (Ct:=1) (D:=1) (Bclock:=T) hm hdelta
      (by linarith) hcl hcu hclcu (by norm_num) (by norm_num) hC0 hc0 hmargin)
  have Hchild : ∀ᶠ n in atTop,
      ∃ Q : ActualHighOnlyOverlapMinimum (dim n+1) m (m/10000) cl cu 2 C0 1 1 T,
        Q.context.d=c0*(P n).xs ∧
        Q.context.E=actualChildErrorBudget (dim n+1) (m/10000) c0
          (P n).data.d ((P n).data.d^2) (P n).xs ∧
        (P n).data.N^((m/10000)/4)*(P n).data.E≤Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N (m/10000) Q.context.E Q.lam) 1 ∧
        (Q.alpha.val.val Q.xs<cl*Q.xs ∨ cu*Q.xs<Q.alpha.val.val Q.xs) ∧
        Q.data.s=(P n).data.s ∧ Q.b=(P n).data.b (P n).alpha ∧
        Q.h=(P n).data.h (P n).alpha := by
    filter_upwards [Hfailure, Hweak1, Htarget, HmassRatio, Hs4, Hreserve, Hselect, heps]
      with n hnF hnW hnTarget hnMass hnS4 hnReserve hnSelect hnE
    have hchild1 : c0*(P n).xs≤1 := by
      have H : c0*(P n).xs≤c0 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hunit n) hc0.le
      exact H.trans hc01
    have hw : laplaceComparisonStrength (P n).data.d ((P n).data.d^2)
        (P n).xs≤(P n).xs^2 := (div_le_one₀ (sq_pos_of_pos (P n).hxs)).mp hnW
    have hcut : 0 < actualChildCutoff (dim n+1) (m/10000) c0
        (P n).data.d ((P n).data.d^2) (P n).xs :=
      (actual_child_cutoff_pos_le_radius (P n).data.hN hc0
        (sq_pos_of_pos (P n).data.hd) (P n).hxs).1
    have hmass := (div_le_one₀ hcut).mp hnMass
    have hfailHigh : (P n).data.N^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (P n).data.d ((P n).data.d^2) (P n).xs <
          (P n).macroHighOnlyChildSweepCost hc0 := by
      have He : ¬(P n).data.epsilon<(P n).data.T/4 := by
        rw [hT n]
        exact not_lt_of_ge hnE
      rw [macroFixedMarginChildSweepCost, ite_eq_right He] at hnF
      exact hnF
    exact hnSelect (P n) hnReserve hchild1 hchild1 hnS4 hmass hnTarget hw hfailHigh
  obtain ⟨N, hN⟩ := eventually_atTop.mp Hchild
  let shift : ℕ→ℕ := fun n=>n+N
  have hshift : StrictMono shift := fun i j hij=>Nat.add_lt_add_right hij N
  choose Q hQd hQE hQgrow hQtest hQbad hQs hQb hQh using
    fun n=>hN (shift n) (by dsimp [shift];omega)
  let G : ActualHighOnlyOverlapMinimum.ActualFixedWallHighOnlyHistory Q T c0 := {
    wall := fun n=>P (shift n)
    root := Q
    history := .root
    temperature := Eventually.of_forall (fun n=>hT (shift n))
    error := hshift.tendsto_atTop.eventually hE
    radius := hshift.tendsto_atTop.eventually hd
    omission := hshift.tendsto_atTop.eventually hs
    same_mass := Eventually.of_forall hQs
    wall_unit := Eventually.of_forall (fun n=>hunit (shift n))
    wall_target := hshift.tendsto_atTop.eventually Htarget
    wall_weak := Hweak.comp hshift.tendsto_atTop
    first_radius := Eventually.of_forall hQd
    first_error := Eventually.of_forall hQE
    bare := Eventually.of_forall (fun n u=>congrFun (hQb n) u)
    field := Eventually.of_forall (fun n u=>congrFun (hQh n) u)
    hT := hTpos }
  have HQbad : ∀ᶠ n in atTop, ¬(cl*(Q n).xs≤(Q n).alpha.val.val (Q n).xs ∧
      (Q n).alpha.val.val (Q n).xs≤cu*(Q n).xs) := by
    apply Eventually.of_forall
    intro n hn
    rcases hQbad n with hlo | hhi
    · exact (not_lt_of_ge hn.1) hlo
    · exact (not_lt_of_ge hn.2) hhi
  exact ⟨N, Q, G, rfl, (fun n=>rfl), (fun n=>(hQtest n).2),
    Eventually.of_forall (fun n=>(hQtest n).1), HQbad⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
