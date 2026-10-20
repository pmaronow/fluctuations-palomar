module

public import SKProof.OriginalQStoppingOnly
public import ComparisonOriginalQReducedPhysicalExclusionsDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter PositiveLaplaceAssembly
open scoped Topology NNReal

namespace OriginalQPhysicalReducedDraft
open OriginalQFixedTStoppingDraft

theorem macroscopicRatioVanishing_of_wall_powers
    {T m cl cu Az C0 Ct D Bclock : ℝ} (hmmax : m < 1/300) :
    MacroscopicRatioVanishing T m cl cu Az C0 Ct D Bclock := by
  intro dim hdim Q hQ eta heta phi hphi hxs
  have hDlim : Tendsto (wallHighD m) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop
      (by linarith : 0 < (1 : ℝ)/6-15*m)).comp
      tendsto_natCast_atTop_atTop using 1
    funext n
    dsimp only [wallHighD, Function.comp_apply]
    congr 1
    ring
  have hindex : Tendsto (fun n => dim (phi n)+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (hdim.tendsto_atTop.comp hphi.tendsto_atTop)
  have hbound : Tendsto (fun n => (wallHighD m (dim (phi n)+1))^2 / eta^2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_pow (by decide : 2 ≠ 0), zero_div] using
      ((hDlim.comp hindex).pow 2).div_const (eta^2)
  apply squeeze_zero (g := fun n => (wallHighD m (dim (phi n)+1))^2 / eta^2)
  · intro n
    exact div_nonneg
      (laplaceComparisonStrength_pos (Q (phi n)).data.d
        (Q (phi n)).hlam (Q (phi n)).xs).le (sq_nonneg _)
  · intro n
    have hstrength : laplaceComparisonStrength (Q (phi n)).data.d
        (Q (phi n)).lam (Q (phi n)).xs ≤
        (wallHighD m (dim (phi n)+1))^2 := by
      have hd := (hQ (phi n)).2.2.1
      simpa only [hd] using
        (laplaceComparisonStrength_le (Q (phi n)).data.d
          (Q (phi n)).hlam.le (Q (phi n)).xs).trans (Q (phi n)).hld
    have hden : eta^2 ≤ (Q (phi n)).xs^2 := by
      nlinarith [hxs n, (Q (phi n)).hxs]
    calc
      _ ≤ (wallHighD m (dim (phi n)+1))^2 / (Q (phi n)).xs^2 :=
        div_le_div_of_nonneg_right hstrength (sq_nonneg _)
      _ ≤ (wallHighD m (dim (phi n)+1))^2 / eta^2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos heta) hden
  · exact hbound

end OriginalQPhysicalReducedDraft

namespace OriginalQLocalSharpReductionDraft
open OriginalQFixedTStoppingDraft

theorem concrete_selected_bad_is_retained
    {T m cl cu : ℝ} {k : ℕ} (hp : ActualConcreteHighWallNumeric m (k+1))
    (epsilon : ℝ) (hepsilon : epsilon ∈ Ioo (0 : ℝ) T)
    (heps0 : upperInitialEpsilon m (k+1) ≤ epsilon)
    (lam : ℝ)
    (hlam : lam ∈ Ioo (((k+1 : ℕ) : ℝ)^(-(10 : ℝ)))
      ((wallHighD m (k+1))^2))
    (Q : ActualThetaZeroOverlapMinimum (k+1) m (m/10000) cl cu 2 1 1 1 T)
    (hdata : Q.data = actualConcreteHighWallData T m (k+1) hp epsilon 0
      hepsilon heps0 (by norm_num))
    (hQlam : Q.lam = lam)
    (hxs : Q.xs ∈ Icc
      (comparisonConditionalScale Q.data.N (m/10000) Q.data.E lam) 1)
    (hbad : Q.alpha.val.val Q.xs < cl*Q.xs ∨
      cu*Q.xs < Q.alpha.val.val Q.xs) :
    RetainedBadQ T k Q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hxs.2, hbad⟩
  · rw [hdata]; rfl
  · rw [hdata]; rfl
  · rw [hdata]; rfl
  · rw [hdata]; rfl
  · rw [hdata]; rfl
  · rw [hdata]; rfl
  · simpa only [hdata, actualConcreteHighWallData] using heps0
  · simpa only [hdata, hQlam, actualConcreteHighWallData] using hlam
  · simpa only [hQlam] using hxs.1

theorem eventually_stoppingGateOnly_of_physical_exclusions
    {T m cl cu : ℝ} (H : PhysicalExclusions T m cl cu 2 1 1 1 T) :
    ∀ᶠ n : ℕ in atTop,
      ∀ hp : ActualConcreteHighWallNumeric m n,
      ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        StoppingGateOnly
          (actualConcreteHighWallData T m n hp epsilon 0
            hepsilon heps0 (by norm_num)) m cl cu := by
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp (eventually_no_fixed_T_retained_bad_q H)
  filter_upwards [eventually_ge_atTop (k0+1)] with n hn
  rcases n with _ | k
  · omega
  · intro hp epsilon hepsilon heps0
    refine ⟨?_⟩
    intro lam hlam _hunresolved _hscale Q hdata hQlam hxs hbad
    apply hk0 k (by omega) Q
    apply concrete_selected_bad_is_retained hp epsilon hepsilon heps0 lam hlam
      Q hdata hQlam ?_ hbad
    simpa only [hdata] using hxs

end OriginalQLocalSharpReductionDraft

open OriginalQPhysicalReducedDraft OriginalQLocalSharpReductionDraft

def ActualOriginalQPhysicalExclusionInputs : Prop :=
  ∀ beta : ℝ, 1 < beta →
    ∀ m : ℝ, 0 < m → m < 1/300 →
      ∃ cl cu : ℝ, 0 < cl ∧ cl ≤ 1 ∧ 1 ≤ cu ∧
        RemainingPhysicalInputs (beta^2) m cl cu 2 1 1 1 (beta^2)

theorem actualOriginalQStoppingInputs_of_physical_exclusions :
    ActualOriginalQPhysicalExclusionInputs → ActualOriginalQStoppingInputs := by
  intro H beta hbeta m hm hmmax
  obtain ⟨cl, cu, hcl, hcl1, hcu1, Hphysical⟩ := H beta hbeta m hm hmmax
  refine ⟨cl, cu, hcl, hcl1, hcu1, ?_⟩
  exact eventually_stoppingGateOnly_of_physical_exclusions
    (physical_exclusions_of_reduced (macroscopicRatioVanishing_of_wall_powers hmmax)
      Hphysical)

theorem main_fluctuation_statement_of_physical_exclusions :
    ActualOriginalQPhysicalExclusionInputs → OAI.SKFluctuations.MainFluctuationStatement := by
  intro H
  exact main_fluctuation_statement_of_stopping
    (actualOriginalQStoppingInputs_of_physical_exclusions H)

end OAI.SKFluctuations.LaplaceWindowFormalization

