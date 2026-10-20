module

public import ComparisonActualHighWallLargeEpsilonHighOnlyStartup
public import ComparisonActualHighOnlyFixedWallFinitePropagation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 36000000

theorem exists_uniform_large_epsilon_high_only_radius
    (T delta : ℝ) (hT : 0 < T) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0≤1 ∧ c0^2<T/4 ∧
      (((actualPropagationDepth delta:ℕ):ℝ)+2)*c0^2≤T/8 := by
  let den : ℝ := ((actualPropagationDepth delta:ℕ):ℝ)+2
  have hden : 0 < den := by dsimp [den];positivity
  have hden2 : 2≤den := by
    dsimp [den]
    have H : 0≤((actualPropagationDepth delta:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  let c0 : ℝ := min (1/2) (Real.sqrt (T/(16*den)))
  have hc0 : 0<c0 := by
    dsimp [c0]
    exact lt_min (by norm_num) (Real.sqrt_pos.2 (by positivity))
  have hc01 : c0≤1 := (min_le_left _ _).trans (by norm_num)
  have Hsq : c0^2≤T/(16*den) := by
    have H := pow_le_pow_left₀ hc0.le
      (min_le_right (1/2:ℝ) (Real.sqrt (T/(16*den)))) 2
    simpa only [Real.sq_sqrt (by positivity : 0≤T/(16*den))] using H
  have Hbudget : den*c0^2≤T/16 := by
    calc
      den*c0^2≤den*(T/(16*den)) := mul_le_mul_of_nonneg_left Hsq hden.le
      _ = T/16 := by field_simp [ne_of_gt hden]
  have hc0Temp : c0^2<T/4 := by
    have Htwo := mul_le_mul_of_nonneg_right hden2 (sq_nonneg c0)
    linarith only [Htwo, Hbudget, hT]
  refine ⟨c0, hc0, hc01, hc0Temp, ?_⟩
  have Hsixteen : T/16≤T/8 := by linarith only [hT]
  simpa only [den] using Hbudget.trans Hsixteen

theorem exists_concrete_fixed_wall_large_epsilon_high_only_exclusion
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu C0 c0 margin : ℝ,
        0 < m → m < 1/300 → 0 < cl → 0 < cu → 0 < C0 →
        ∀ hc0 : 0 < c0, c0≤1 → c0^2<(beta:ℝ)^2/4 →
        (((actualPropagationDepth (m/10000):ℕ):ℝ)+2)*c0^2≤ margin →
        margin≤(beta:ℝ)^2/8 → cl≤lower → upper≤cu →
        cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
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
          cu*(P n).xs<(P n).alpha.val.val (P n).xs) → False := by
  classical
  obtain ⟨lowerF, upperF, hlowerF, hupperF, Hfirst⟩ :=
    ActualHighWallOverlapMinimum.exists_concrete_fixed_wall_large_epsilon_bad_child_startup
      hbeta hTemp
  obtain ⟨lowerP, upperP, hlowerP, hupperP, Hprop⟩ :=
    ActualHighOnlyOverlapMinimum.exists_fixed_wall_finite_high_only_propagation hbeta hTemp
  refine ⟨min lowerF lowerP, max upperF upperP,
    lt_min hlowerF hlowerP, hupperF.trans_le (le_max_left _ _), ?_⟩
  intro m cl cu C0 c0 margin hm hmmax hcl hcu hC0 hc0 hc01 hc0Temp
    hbudget hmarginT hclBounds hcuBounds hclTemp hcuTemp dim hdim P hT hE hd hs
    hunit heps hdxs hbad
  have hmsmall : m≤(1:ℝ)/120 := by linarith
  have hclF : cl≤lowerF := hclBounds.trans (min_le_left _ _)
  have hcuF : upperF≤cu := (le_max_left _ _).trans hcuBounds
  have hclP : cl≤lowerP := hclBounds.trans (min_le_right _ _)
  have hcuP : upperP≤cu := (le_max_right _ _).trans hcuBounds
  have hclcu : cl≤cu := by
    have H := (P 0).regular 1 ⟨(P 0).hz.2, le_rfl⟩
    simpa only [(P 0).alpha.property.2.1, mul_one] using H.1.trans H.2
  have hclTempF : cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) := by
    have H : 0 < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) := by positivity
    linarith only [H, hclTemp]
  obtain ⟨N, Q, G, hGroot, hGwall, hQunit, hQtarget, hQbad⟩ :=
    Hfirst m cl cu C0 c0 hm hmmax hcl hcu hclcu hC0 hc0 hc01 hc0Temp
      hclF hcuF hclTempF hcuTemp dim hdim P hT hE hd hs hunit heps hdxs hbad
  let shift : ℕ→ℕ := fun n=>n+N
  have hshift : StrictMono shift := fun i j hij=>Nat.add_lt_add_right hij N
  have hGwallShift : ∀ n, G.wall n=P (shift n) := hGwall
  have hdimShift : Tendsto (fun n=>dim (shift n)) atTop atTop :=
    hdim.comp hshift.tendsto_atTop
  have hGeps : ∀ᶠ n in atTop, (beta:ℝ)^2/4≤(G.wall n).data.epsilon := by
    filter_upwards [hshift.tendsto_atTop.eventually heps] with n hn
    rw [hGwallShift n]
    exact hn
  exact Hprop m cl cu 2 C0 1 1 ((beta:ℝ)^2) c0 margin hm hmsmall hcl hcu hclcu
    (by norm_num) (by norm_num) hC0 le_rfl hc0 hc01 hc01 le_rfl
    hbudget hmarginT hclP hcuP hclTemp hcuTemp (fun n=>dim (shift n))
    hdimShift Q G hGroot hGeps hQunit hQtarget hQbad

end OAI.SKFluctuations.LaplaceWindowFormalization
