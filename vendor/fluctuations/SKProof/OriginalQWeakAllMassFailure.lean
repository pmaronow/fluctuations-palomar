module

public import SKProof.OriginalQAllMassFirstChildBudgetExact
public import SKProof.OriginalQAllMassZeroMassContextProfileJoin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum

theorem eventually_weak_shrinking_all_mass_first_child_failure_original_q
    {m delta cl cu Az C0 T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hTpos : 0 < T)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 1 1 T)
    (hT : ∀ᶠn in atTop, (Q n).data.T = T)
    (heps : ∀ᶠn in atTop, (Q n).data.epsilon ≤ T/4)
    (hunit : ∀ᶠn in atTop, (Q n).xs ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (Q n).data.N delta
        (Q n).data.E (Q n).lam ≤ (Q n).xs)
    (hxs0 : Tendsto (fun n => (Q n).xs) atTop (𝓝 0))
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (Q n).data.d (Q n).lam (Q n).xs/(Q n).xs^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n => (Q n).data.s/(Q n).xs)
      atTop (𝓝 0))
    (hr : Tendsto (fun n => (Q n).data.rmin/(Q n).xs)
      atTop (𝓝 0))
    (hsCut : Tendsto (fun n => (Q n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (Q n).data.d (Q n).lam (Q n).xs) atTop (𝓝 0))
    (hbad : ∀ᶠn in atTop,
      ¬(cl*(Q n).xs ≤ (Q n).alpha.val.val (Q n).xs ∧
        (Q n).alpha.val.val (Q n).xs ≤ cu*(Q n).xs)) :
    ∀ᶠn in atTop,
      ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (Q n).data.d (Q n).lam (Q n).xs <
        (Q n).allMassChildSweepCost hc0 := by
  classical
  have HchildSmall : Tendsto (fun n => (c0*(Q n).xs)^2)
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      using (hxs0.const_mul c0).pow 2
  have Hroom : ∀ᶠn in atTop,
      (c0*(Q n).xs)^2 ≤ (Q n).changedBare 0 := by
    filter_upwards [hT,heps,HchildSmall.eventually
      (eventually_le_nhds (div_pos hTpos (by norm_num : (0:ℝ)<8)))]
      with n hnT hnE hnSmall
    have He : (Q n).data.epsilon ≤ (Q n).data.T/4 := by
      simpa only [hnT] using hnE
    have Hs : (c0*(Q n).xs)^2 ≤ (Q n).data.T/8 := by
      simpa only [hnT] using hnSmall
    change (c0*(Q n).xs)^2 ≤
      (Q n).data.T/8 at Hs
    exact (Q n).all_mass_child_room_of_small_epsilon hc0 He Hs
  by_contra Hnone
  have Hfreq : ∃ᶠn in atTop,
      (Q n).allMassChildSweepCost hc0 ≤
      ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (Q n).data.d (Q n).lam (Q n).xs := by
    simpa only [Filter.Frequently,not_le] using Hnone
  obtain ⟨phi,hphi,Hphi⟩ :=
    extraction_of_frequently_atTop (Hfreq.and_eventually Hroom)
  let dim0 := fun n => dim (phi n)
  let P := fun n => Q (phi n)
  have hdim0 : Tendsto dim0 atTop atTop :=
    hdim.comp hphi.tendsto_atTop
  have hxs0' : Tendsto (fun n => (P n).xs) atTop (𝓝 0) :=
    hxs0.comp hphi.tendsto_atTop
  have hroom0 n : (c0*(P n).xs)^2 ≤ (P n).changedBare 0 :=
    (Hphi n).2
  choose a ha using fun n =>
    (P n).exists_all_mass_child_budget_exact_original_q hc0 (hroom0 n)
  have hcontext n : (a n).context =
      (P n).data.thetaZeroShiftedParentData
        (P n).lam (P n).hlam (P n).hld := by
    rcases ha n with ⟨H,_,_,_,_,_,_,_,_⟩
    exact H
  have hR n : (a n).R = (P n).data.wallRadius (P n).alpha := by
    rcases ha n with ⟨_,_,H,_,_,_,_,_,_⟩
    exact H
  have hD n : (a n).childRadius = c0*(P n).xs := by
    rcases ha n with ⟨_,_,_,H,_,_,_,_,_⟩
    exact H
  have hL n : (a n).childLam = (c0*(P n).xs)^2 := by
    rcases ha n with ⟨_,_,_,_,H,_,_,_,_⟩
    exact H
  have hE n : (a n).childData.E = actualChildErrorBudget
      (dim0 n+1) delta c0 (P n).data.d (P n).lam (P n).xs := by
    rcases ha n with ⟨_,_,_,_,_,H,_,_,_⟩
    exact H
  have hchild : ∀ᶠn in atTop,
      (a n).childRadius = c0*(P n).xs ∧
      (a n).childLam = (c0*(P n).xs)^2 ∧
      (a n).err ≤ ((dim0 n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim0 n+1) delta c0
          (P n).data.d (P n).lam (P n).xs := by
    apply Eventually.of_forall
    intro n
    rcases ha n with ⟨_,_,_,_,_,_,_,_,Herr⟩
    refine ⟨hD n,hL n,?_⟩
    rw [Herr]
    exact (Hphi n).1
  obtain ⟨C,hC,hAzC,Hmin⟩ :=
    eventually_exists_theta_zero_successful_all_mass_child_minimum_original_q
      hm hdelta hcl hcu hAz hC0 hc0 hc01 hmargin
      dim0 hdim0 P a hxs0' hcontext hR hchild
      (Eventually.of_forall hE)
      (hphi.tendsto_atTop.eventually htarget)
      ((hphi.tendsto_atTop.eventually hT).mono
        (fun _ hn => hn.le))
      (hweak.comp hphi.tendsto_atTop)
      (hs.comp hphi.tendsto_atTop)
      (hr.comp hphi.tendsto_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.mp Hmin
  let shift := fun n : ℕ => n+N
  have hshift : StrictMono shift :=
    fun i j hij => Nat.add_lt_add_right hij N
  have Htail n := hN (shift n) (by dsimp [shift]; omega)
  choose V hVE hVd hVzero hVb hVh hVlam hValpha hVxs hVz hVR
    using Htail
  let dim1 := fun n => dim0 (shift n)
  let P1 := fun n => P (shift n)
  let a1 := fun n => a (shift n)
  have hdim1 : Tendsto dim1 atTop atTop :=
    hdim0.comp hshift.tendsto_atTop
  have hxs1 : Tendsto (fun n => (P1 n).xs) atTop (𝓝 0) :=
    hxs0'.comp hshift.tendsto_atTop
  have hVE1 n : (V n).context.E = actualChildErrorBudget
      (dim1 n+1) delta c0 (P1 n).data.d (P1 n).lam (P1 n).xs :=
    (hVE n).trans (hE (shift n))
  have hVd1 n : (V n).context.d = c0*(P1 n).xs :=
    (hVd n).trans (hD (shift n))
  have hV1 n : (V n).R = (a1 n).Z ∧
      (V n).xs = (P1 n).xs ∧
      (V n).lam = (c0*(P1 n).xs)^2 :=
    ⟨hVR n,hVxs n,(hVlam n).trans (hL (shift n))⟩
  have Hprofile := theta_zero_zero_mass_child_context_profile_join_original_q
    hm hdelta hroom hcl hcu hAz hC0 hTpos hc0 hc01 hC hAzC
    hmargin hcapmargin hgapmargin hclmargin hcumargin
    dim1 hdim1 P1 a1 V hxs1
    (hshift.tendsto_atTop.eventually
      (hphi.tendsto_atTop.eventually hT))
    (hshift.tendsto_atTop.eventually
      (hphi.tendsto_atTop.eventually hunit))
    (hshift.tendsto_atTop.eventually
      (hphi.tendsto_atTop.eventually htarget))
    ((hweak.comp hphi.tendsto_atTop).comp hshift.tendsto_atTop)
    ((hs.comp hphi.tendsto_atTop).comp hshift.tendsto_atTop)
    ((hr.comp hphi.tendsto_atTop).comp hshift.tendsto_atTop)
    ((hsCut.comp hphi.tendsto_atTop).comp hshift.tendsto_atTop)
    (fun n => hcontext (shift n)) (fun n => hR (shift n))
    (hshift.tendsto_atTop.eventually hchild)
    hVE1 hVd1 hVzero hVb hVh hV1
  obtain ⟨psi,hpsi,kappa,hklo,hkup,Hparent,Hstrict⟩ := Hprofile
  have Hbad1 := hpsi.tendsto_atTop.eventually
    (hshift.tendsto_atTop.eventually
      (hphi.tendsto_atTop.eventually hbad))
  obtain ⟨n,hn⟩ := (Hstrict.and Hbad1).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
