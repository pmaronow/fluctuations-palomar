module

public import ComparisonSignedCavityInheritedGWordScalarRate
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyInheritedScalarFourRawScale

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
open Filter Set
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_G_word_scalar_raw_bound_high_only
    (r : ℕ) (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D₀ : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(as : List PositiveMass),MassOrdered 0 as →
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        ∀(B T : ClockTree (Spin n×Bool) as) (base : NativeGeneratedTest B)
          (P : NativeGeneratedTest T) (star U : ℕ) (spine : NativeProjectionSpine base star P)
          (D : NativeObservedDiagram B),3 ≤ D.marks.length → 0 < U →
          (spine.graftDiagram D).tree.leaves ≤ r →
          (nativeObservedTargetMetadata D base.target).2=false →
          U ≤ (nativeObservedTargetMetadata D base.target).1 →
          let v:=M.R (partitionPoint 0 as (nativeObservedTargetMetadata D base.target).1)
          M.xs ≤ v → M.z ≤ v →
          |nativeObservedGScalar (spine.graftDiagram D) base.target U K| *
            (M.xs+partitionPoint 0 as (nativeObservedErrorIndex D)) ≤ Cg*v := by
  classical
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_scalar_four_raw_scale_bound_high_only
    (D:=D₀) r Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [HG] with n hn
  intro M hs0 hsxs hsource hxs as ho
  dsimp only
  intro B T base P star U spine D hk hU hleaves hdiag hhigh hxv hzv
  let E:=spine.graftDiagram D
  obtain ⟨f,e,c,tail,he⟩:=native_observed_three_marks E (by
    change 3 ≤ (spine.graftDiagram D).marks.length
    rw [spine.graft_marks_length_all]
    omega)
  have HT : nativeObservedTargetMetadata E base.target=nativeObservedTargetMetadata D base.target:=
    spine.graft_target_metadata D hk
  have Hindex : E.tree.splitIndex (E.embed base.target) c=
      (nativeObservedTargetMetadata D base.target).1 := by
    simpa only [nativeObservedTargetMetadata,he] using congrArg Prod.fst HT
  have Hdiag : decide (E.embed base.target=c)=false := by
    have H:=(congrArg Prod.snd HT).trans hdiag
    simpa only [nativeObservedTargetMetadata,he] using H
  have HE : E.tree.splitIndex e f=nativeObservedErrorIndex D := by
    have H : nativeObservedErrorIndex E=nativeObservedErrorIndex D:=spine.graft_error_index D (by omega)
    simpa only [nativeObservedErrorIndex,he] using H
  have Hκ:=hn M hs0 hsxs hsource hxs as ho E.tree U hU hleaves (E.embed base.target) c e f
    (of_decide_eq_false Hdiag) (by simpa only [Hindex] using hhigh)
    (by simpa only [Hindex] using hxv) (by simpa only [Hindex] using hzv)
  have Hhalf (κ : ℝ) : |(1/2:ℝ)*κ| ≤ |κ| := by
    rw [abs_mul]
    norm_num
    linarith only [abs_nonneg κ]
  have Hraw : 0 ≤ M.xs+partitionPoint 0 as (E.tree.splitIndex e f):=
    add_nonneg M.hxs.le (partitionPoint_mem as ho _).1
  change |nativeObservedGScalar E base.target U _| *
    (M.xs+partitionPoint 0 as (nativeObservedErrorIndex D)) ≤ _
  simp only [nativeObservedGScalar,he]
  rw [←HE]
  exact (mul_le_mul_of_nonneg_right (Hhalf _) Hraw).trans (by simpa only [Hindex] using Hκ)

end OAI.SKFluctuations.Cavity
