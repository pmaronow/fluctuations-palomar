module

public import ComparisonConcreteRegularMeanAlongDraft
public import ComparisonActualHighWallSmallEpsilonNativeJoin
public import ComparisonActualHighWallLargeEpsilonHighOnlyJoin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Cavity PositiveLaplaceAssembly
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 48000000

theorem exists_concrete_positive_wall_mean_from_physical_branches
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < ((beta : ℝ)^2))
    {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300) :
    ∃ Cw : ℝ,1 ≤ Cw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ hp : ActualConcreteHighWallNumeric m n,
      ∀ epsilon : ℝ,∀ hepsilon : epsilon∈Ioo (0:ℝ) ((beta : ℝ)^2),
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        concretePositiveThetaMeanAtNumeric ((beta : ℝ)^2) Cw m n hp epsilon hepsilon heps0 := by
  let T := ((beta : ℝ)^2)
  have hT : 0 < T := zero_lt_one.trans hTemp
  obtain ⟨lowerS,upperS,hlowerS,hupperS,Hsmall⟩ :=
    exists_concrete_fixed_wall_small_epsilon_native_exclusion hbeta hTemp
  obtain ⟨lowerL,upperL,hlowerL,hupperL,Hlarge⟩ :=
    exists_concrete_fixed_wall_large_epsilon_high_only_exclusion hbeta hTemp
  obtain ⟨cl,cu,hcl,hcl1,hclS,hclL,hclTemp,hcu,hcu1,hcuS,hcuL,hcuTemp⟩ :=
    exists_common_original_wall_profile_margins hT hlowerS hupperS hlowerL hupperL
  obtain ⟨c0,hc0,hc01,hc0Temp,hbudget⟩ :=
    exists_uniform_large_epsilon_high_only_radius T (m/10000) hT
  have hsmall : ∀ dim : ℕ→ℕ,Tendsto dim atTop atTop →
      ∀ x : (j : ℕ)→OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j,selectedBadSmallEpsilon (dim j) (x j)) → False := by
    intro dim hdim x heps
    exact Hsmall m cl cu 1 c0 (T/8) hm hmmax hcl hcu zero_lt_one hc0 hc01
      hc0Temp hbudget (by linarith only [hT]) hclS hcuS hclTemp hcuTemp dim hdim
      (fun j=>(x j).P) (fun j=>(x j).hT)
      (Eventually.of_forall (fun j=>(x j).hE))
      (Eventually.of_forall (fun j=>(x j).hd))
      (Eventually.of_forall (fun j=>(x j).hs))
      (fun j=>(x j).hunit) (Eventually.of_forall heps)
      (fun j=>(x j).hdxs) (fun j=>(x j).hbad)
  have hlarge : ∀ dim : ℕ→ℕ,Tendsto dim atTop atTop →
      ∀ x : (j : ℕ)→OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j,selectedBadLargeEpsilon (dim j) (x j)) → False := by
    intro dim hdim x heps
    exact Hlarge m cl cu 1 c0 (T/8) hm hmmax hcl hcu zero_lt_one hc0 hc01
      hc0Temp hbudget le_rfl hclL hcuL hclTemp hcuTemp dim hdim
      (fun j=>(x j).P) (fun j=>(x j).hT)
      (Eventually.of_forall (fun j=>(x j).hE))
      (Eventually.of_forall (fun j=>(x j).hd))
      (Eventually.of_forall (fun j=>(x j).hs))
      (fun j=>(x j).hunit) (Eventually.of_forall heps)
      (fun j=>(x j).hdxs) (fun j=>(x j).hbad)
  exact eventually_concrete_positive_wall_mean_all_sizes_of_physical_exclusions
    hT hm hmmax hcl hcu hcl1 hcu1 hsmall hlarge

theorem exists_concrete_high_wall_inputs_from_original_sharp_and_physical_branches
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < ((beta : ℝ)^2))
    {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300)
    (hsharp : ∀ᶠ n : ℕ in atTop,
      ∀ hp : ActualConcreteHighWallNumeric m n,
      ∀ epsilon : ℝ,∀ hepsilon : epsilon∈Ioo (0:ℝ) ((beta : ℝ)^2),
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        concreteSharpCostAtNumeric ((beta : ℝ)^2) m n hp epsilon hepsilon heps0) :
    ∃ Cw : ℝ,1 ≤ Cw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ hp : ConcreteHighWallGeometry m n,
      ∀ epsilon : ℝ,∀ hepsilon : epsilon∈Ioo (0:ℝ) ((beta : ℝ)^2),
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        concreteHighWallPhysicalInputs ((beta : ℝ)^2) Cw m n hp epsilon := by
  obtain ⟨Cw,hCw,Hmean⟩ := exists_concrete_positive_wall_mean_from_physical_branches
    hbeta hTemp hm hmmax
  exact ⟨Cw,hCw,eventually_concrete_high_wall_physical_inputs_of_numeric_fields
    hm hmmax hsharp Hmean⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
