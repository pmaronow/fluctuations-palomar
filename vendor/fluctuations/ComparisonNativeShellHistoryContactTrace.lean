module

public import ComparisonNativeSingleCutContactTrace
public import ComparisonFiniteHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 7000000
section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

include hc hk hkc hm hM in
theorem inherited_shell_history_exists_clock_cut
    (α : inverseIntegralConstraints 0 0 k M)
    (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm)
    (b h : ℝ → ℝ) (hb : ∀u,b u=historyMatrixClock T epsilon shell ts u)
    (hh : ∀u,h u=historyFieldClock ts u)
    {a z : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1) :
    ∃s∈Icc a z,∀l r,a ≤ l → l ≤ r → r ≤ z → (r < s ∨ s ≤ l) →
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun t=>b (α.val.val t)) (Icc l r) ∧
        LipschitzOnWith Kh (fun t=>h (α.val.val t)) (Icc l r) := by
  have hbranch {l r : ℝ} (hal : a ≤ l) (hlr : l ≤ r) (hrz : r ≤ z)
      (hs : α.val.val r < shell ∨ shell ≤ α.val.val l) :
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun t=>b (α.val.val t)) (Icc l r) ∧
        LipschitzOnWith Kh (fun t=>h (α.val.val t)) (Icc l r) := by
    obtain ⟨Kb,hKb⟩:=historyMatrixClock_inverse_lipschitz hc hk hkc hm hM
      α T epsilon shell ts (ha.trans hal) hlr (hrz.trans hz) hs
    obtain ⟨Kh,hKh⟩:=historyFieldClock_inverse_lipschitz hc hk hkc hm hM
      α ts (ha.trans hal) hlr (hrz.trans hz)
    exact ⟨Kb,Kh,by simpa only [hb] using hKb,by simpa only [hh] using hKh⟩
  by_cases hlow : α.val.val z < shell
  · refine ⟨a,⟨le_rfl,haz⟩,?_⟩
    intro l r hal hlr hrz _
    exact hbranch hal hlr hrz (Or.inl ((α.val.property.2 hrz).trans_lt hlow))
  by_cases hhigh : shell ≤ α.val.val a
  · refine ⟨a,⟨le_rfl,haz⟩,?_⟩
    intro l r hal hlr hrz _
    exact hbranch hal hlr hrz (Or.inr (hhigh.trans (α.val.property.2 hal)))
  have hashell : α.val.val a < shell := lt_of_not_ge hhigh
  have hshellz : shell ≤ α.val.val z := le_of_not_gt hlow
  have hsh : shell∈Icc (0:ℝ) 1 :=
    ⟨(α.val.property.1 a).1.trans hashell.le,hshellz.trans (α.val.property.1 z).2⟩
  let s:=comparisonSweepQuantile hc hk hkc hm hM α shell
  have hs01 : s∈Icc (0:ℝ) 1 := comparisonSweepQuantile_bounds hc hk hkc hm hM α shell
  have hspec : α.val.val s=shell := comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hsh
  have has : a ≤ s := by
    by_contra hno
    have he:=α.val.property.2 (le_of_not_ge hno)
    change α.val.val s ≤ α.val.val a at he
    rw [hspec] at he
    exact hashell.not_ge he
  have hsz : s ≤ z := by
    by_contra hno
    have he:=inverseConstraint_strictMonoOn hc hk hkc α.property ⟨ha.trans haz,hz⟩ hs01
      (lt_of_not_ge hno)
    rw [hspec] at he
    exact he.not_ge hshellz
  refine ⟨s,⟨has,hsz⟩,?_⟩
  intro l r hal hlr hrz hside
  apply hbranch hal hlr hrz
  rcases hside with hleft|hright
  · have he:=inverseConstraint_strictMonoOn hc hk hkc α.property
      ⟨(ha.trans hal).trans hlr,hrz.trans hz⟩ hs01 hleft
    exact Or.inl (by simpa only [hspec] using he)
  · have he:=α.val.property.2 hright
    exact Or.inr (by simpa only [hspec] using he)

theorem comparisonPhysicalShellHistoryContactTrace_eventually
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1 → H r=0 →
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm)
    (hbclock : ∀u,b u=historyMatrixClock T epsilon shell ts u)
    (hhclock : ∀u,h u=historyFieldClock ts u)
    (w : ℝ → ℝ) (hw : Measurable w) (K : ℝ) (hK : 0 ≤ K)
    (hwb : ∀r,‖w r‖ ≤ K) (hw0 : ∀r,0 ≤ w r)
    {ε : ℝ} (hε : 0 < ε) :
    let A := {r | r∈Ioo a z ∧ H r=0}
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      ((9*Real.log N)/F)*(∫r in A,deriv α.val.val r*w r)+ε := by
  obtain ⟨s,hs,hlocal⟩:=inherited_shell_history_exists_clock_cut hc hk hkc hm hM α
    T epsilon shell ts b h hbclock hhclock ha.le haz hz
  exact comparisonPhysicalSingleCutContactTrace_eventually hc hk hkc hm hM hN hlog hd hnd
    hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero as mesh ho hend hmesh hmesh0 hlim
    ha haz hz s hs.1 hs.2 hlocal w hw K hK hwb hw0 hε
end
end OAI.SKFluctuations.LaplaceWindowFormalization
