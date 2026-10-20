module

public import SKProof.OriginalQNativePropagationStep
public import SKProof.OriginalQNativeFirstRootHistory
public import SKProof.Restore.ComparisonActualHighWallThetaZeroFiniteNativeChain
public import SKProof.Restore.ComparisonActualHighWallThetaZeroSelectedBadAllMassChild

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum

theorem exists_low_gap_first_root_finite_contradiction_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu c0 : ℝ, 0 < m → m < 1/300 →
      0 < cl → 0 < cu → cl ≤ lower → upper ≤ cu →
      cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
      (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3:ℝ)^2/
        (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
      ∀ hc0 : 0 < c0, c0 ≤ 1 → c0^2 < (beta:ℝ)^2/4 →
      (((actualPropagationDepth (m/10000):ℕ):ℝ)+2)*c0^2 ≤ (beta:ℝ)^2/2 →
      ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu 2 1 1 1 ((beta:ℝ)^2),
      (∀ᶠ n in atTop, (Q n).data.T = (beta:ℝ)^2) →
      (∀ᶠ n in atTop, (Q n).xs ≤ 1) →
      (∀ᶠ n in atTop, comparisonConditionalScale (Q n).data.N
        (m/10000) (Q n).data.E (Q n).lam ≤ (Q n).xs) →
      Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
        (Q n).lam (Q n).xs/(Q n).xs^2) atTop (𝓝 0) →
      Tendsto (fun n => (Q n).data.s) atTop (𝓝 0) →
      Tendsto (fun n => (Q n).data.s/
        actualChildCutoff (dim n+1) (m/10000) c0
          (Q n).data.d (Q n).lam (Q n).xs) atTop (𝓝 0) →
      (∀ᶠ n in atTop, (Q n).data.epsilon ≤ (beta:ℝ)^2/4) →
      (∀ᶠ n in atTop,
        ((dim n+1:ℕ):ℝ)^(20*(m/10000))*
          actualChildErrorBudget (dim n+1) (m/10000) c0
            (Q n).data.d (Q n).lam (Q n).xs <
        (Q n).allMassChildSweepCost hc0) → False := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hstep⟩ :=
    NativeOverlapMinimum.exists_irregular_child_step_original_q hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu c0 hm hmmax hcl hcu hclBounds hcuBounds
    hclTemp hcuTemp hc0 hc01 _hc0Temp hbudget dim hdim Q
    hWallT hunit htarget hweak hs0 hsCut heps hcost
  have hTpos : 0 < (beta:ℝ)^2 := zero_lt_one.trans hTemp
  have hdelta : 0 < m/10000 := by positivity
  have hroom : m/10000 < 3*m := by linarith only [hm]
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith only [hm]
  have hcapmargin : 100*(m/10000) < (1:ℝ)/3+m := by linarith only [hm]
  have hgapmargin : 0 < 9*m-298*(m/10000) := by linarith only [hm]
  have hcl1 : cl ≤ 1 := by
    simpa only [mul_one, (Q 0).alpha.property.2.1] using
      ((Q 0).regular 1 ⟨(Q 0).hz.2, le_rfl⟩).1
  have hcu1 : 1 ≤ cu := by
    simpa only [mul_one, (Q 0).alpha.property.2.1] using
      ((Q 0).regular 1 ⟨(Q 0).hz.2, le_rfl⟩).2
  have hdepth : 6 ≤ (actualPropagationDepth (m/10000):ℝ) := by
    have H := actual_propagation_depth_budget hdelta
    have hdelta1 : m/10000 ≤ 1 := by linarith only [hmmax]
    have Hmul := mul_le_mul_of_nonneg_left hdelta1
      (Nat.cast_nonneg (actualPropagationDepth (m/10000)) :
        (0:ℝ) ≤ (actualPropagationDepth (m/10000):ℝ))
    linarith only [H, Hmul]
  have hc0T16 : c0^2 ≤ (beta:ℝ)^2/16 := by
    have Hmul := mul_le_mul_of_nonneg_right
      (show (8:ℝ) ≤ (actualPropagationDepth (m/10000):ℝ)+2 by
        linarith only [hdepth]) (sq_nonneg c0)
    linarith only [Hmul, hbudget]
  have Hselect := hdim.eventually
    (eventually_exists_selected_bad_theta_zero_all_mass_child
      (D := 1) (Bclock := (beta:ℝ)^2)
      hm hdelta hroom hcl hcl1 hcu1 le_rfl le_rfl zero_lt_one hc0 hmargin)
  have Hweak := hweak.eventually (eventually_le_nhds zero_lt_one)
  have Hroot : ∀ᶠ n in atTop,
      ∃ root : NativeOverlapMinimum (dim n+1)
        m (m/10000) cl cu 2 1 1 1 ((beta:ℝ)^2),
        root.context.d = c0*(Q n).xs ∧
        root.context.E = actualChildErrorBudget (dim n+1) (m/10000) c0
          (Q n).data.d (Q n).lam (Q n).xs ∧
        (Q n).data.N^((m/10000)/4)*(Q n).data.E ≤ root.context.E ∧
        root.xs ∈ Icc (comparisonConditionalScale root.context.N (m/10000)
          root.context.E root.lam) 1 ∧
        root.z = min (2*root.xs) 1 ∧
        ¬(cl*root.xs ≤ root.alpha.val.val root.xs ∧
          root.alpha.val.val root.xs ≤ cu*root.xs) ∧
        root.b = (Q n).changedBare ∧ root.h = (Q n).changedField := by
    filter_upwards [Hselect, hWallT, heps, hunit, htarget, Hweak, hcost]
      with n hnSelect hnT hnEps hnUnit hnTarget hnWeak hnCost
    have hchildCap : c0*(Q n).xs ≤ c0 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnUnit hc0.le
    have hchild1 : c0*(Q n).xs ≤ 1 := hchildCap.trans hc01
    have hchildT : (c0*(Q n).xs)^2 ≤ (Q n).data.T/8 := by
      rw [hnT]
      calc
        (c0*(Q n).xs)^2 ≤ c0^2 :=
          pow_le_pow_left₀ (mul_pos hc0 (Q n).hxs).le hchildCap 2
        _ ≤ (beta:ℝ)^2/16 := hc0T16
        _ ≤ (beta:ℝ)^2/8 := by linarith only [hTpos]
    have hepsPoint : (Q n).data.epsilon ≤ (Q n).data.T/4 := by
      simpa only [hnT] using hnEps
    have hmatrix := (Q n).all_mass_child_room_of_small_epsilon
      hc0 hepsPoint hchildT
    have hstrength : laplaceComparisonStrength (Q n).data.d
        (Q n).lam (Q n).xs ≤ (Q n).xs^2 :=
      (div_le_one₀ (sq_pos_of_pos (Q n).hxs)).mp hnWeak
    obtain ⟨root, hD, hE, hGrow, hXs, hZ, hBad, hBare, hField⟩ :=
      hnSelect (Q n) hchild1 hchild1 hnTarget hstrength hmatrix hnCost
    refine ⟨root, hD, hE, hGrow, hXs, hZ, ?_, hBare, hField⟩
    rcases hBad with hlow | hhigh
    · exact fun h => not_lt_of_ge h.1 hlow
    · exact fun h => not_lt_of_ge h.2 hhigh
  obtain ⟨n0, Hn0⟩ := eventually_atTop.mp Hroot
  let shift : ℕ → ℕ := fun n => n+n0
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_right hij n0
  have hshiftlim : Tendsto shift atTop atTop := hshift.tendsto_atTop
  have Htail (n : ℕ) : ∃ root : NativeOverlapMinimum (dim (shift n)+1)
      m (m/10000) cl cu 2 1 1 1 ((beta:ℝ)^2),
      root.context.d = c0*(Q (shift n)).xs ∧
      root.context.E = actualChildErrorBudget (dim (shift n)+1) (m/10000) c0
        (Q (shift n)).data.d (Q (shift n)).lam (Q (shift n)).xs ∧
      (Q (shift n)).data.N^((m/10000)/4)*(Q (shift n)).data.E ≤ root.context.E ∧
      root.xs ∈ Icc (comparisonConditionalScale root.context.N (m/10000)
        root.context.E root.lam) 1 ∧
      root.z = min (2*root.xs) 1 ∧
      ¬(cl*root.xs ≤ root.alpha.val.val root.xs ∧
        root.alpha.val.val root.xs ≤ cu*root.xs) ∧
      root.b = (Q (shift n)).changedBare ∧
      root.h = (Q (shift n)).changedField :=
    Hn0 (shift n) (by dsimp [shift]; omega)
  choose root hD hE _hGrow hXs _hZ hBad hBare hField using Htail
  let dim1 : ℕ → ℕ := fun n => dim (shift n)
  let Qwall := fun n => Q (shift n)
  let G : OriginalQNativeRootHistory root ((beta:ℝ)^2) c0 :=
    first_native_root_history_original_q Qwall root
      (hshiftlim.eventually hWallT) (hshiftlim.eventually hunit)
      (hshiftlim.eventually htarget) (hweak.comp hshiftlim)
      (hs0.comp hshiftlim) (hsCut.comp hshiftlim)
      (Eventually.of_forall hD) (Eventually.of_forall hE)
      (Eventually.of_forall (fun n u => congrFun (hBare n) u))
      (Eventually.of_forall (fun n u => congrFun (hField n) u)) hTpos
  have Hfirst : ∀ᶠ n in atTop,
      (root n).context.d ≤ c0 ∧ (beta:ℝ)^2/2 ≤ (root n).b 0 := by
    filter_upwards [hshiftlim.eventually hWallT, hshiftlim.eventually heps,
      hshiftlim.eventually hunit] with n hnT hnEps hnUnit
    have hlow := (Qwall n).data.theta_zero_changed_low_matrix
      (Qwall n).lam (Qwall n).hlam (Qwall n).hld (Qwall n).alpha
      (Qwall n).data.hs.1
    change (Qwall n).changedBare 0 =
      (Qwall n).data.T-(Qwall n).data.epsilon at hlow
    constructor
    · rw [hD n]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnUnit hc0.le
    · rw [hBare n, hlow, hnT]
      linarith only [hnEps, hTpos]
  apply theta_zero_finite_native_chain_of_one_step
    hm hdelta zero_lt_one hc0 dim1 (hdim.comp hshiftlim) root
    (Hfirst.mono (fun _ h => h.1)) (Hfirst.mono (fun _ h => h.2)) hbudget
    (fun n => (hXs n).2) (Eventually.of_forall (fun n => (hXs n).1))
    (Eventually.of_forall hBad)
  intro phi hphi k P Hgrowth Hunit Htarget Hroom Hbad
  let Gphi := G.comp_original_q phi hphi
  let GP : OriginalQNativeRootHistory P ((beta:ℝ)^2) c0 := {
    wall := Gphi.wall
    root := Gphi.root
    history := Hgrowth.weak_history
    hTemp := Gphi.hTemp
    hunit := Gphi.hunit
    htarget := Gphi.htarget
    hweak := Gphi.hweak
    hsZero := Gphi.hsZero
    hsCut := Gphi.hsCut
    hcut := Gphi.hcut
    hb := Gphi.hb
    hh := Gphi.hh
    hT := Gphi.hT
  }
  obtain ⟨HweakP, Hnext⟩ := Hstep m (m/10000) cl cu 2 1 1 1 c0
    hm hdelta hroom hcl hcu le_rfl zero_lt_one le_rfl le_rfl
    hc0 hc01 hc01 hmargin hcapmargin hgapmargin
    hclBounds hcuBounds hclTemp hcuTemp
    (fun n => dim1 (phi n)) ((hdim.comp hshiftlim).comp hphi.tendsto_atTop)
    P GP Hunit Htarget Hroom Hbad
  refine ⟨HweakP, ?_⟩
  filter_upwards [Hnext] with n hn
  rcases hn with ⟨child, hD, hE, hGrow, hXs, _hZ, hBad, hBare, hField⟩
  exact ⟨child, hD, hE, hGrow, hXs, hBad, hBare, hField⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
