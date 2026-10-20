module

public import ComparisonSignedCavityInheritedTripleGScalarRate
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyInheritedGWordScalarRate

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

theorem eventually_actual_minimum_inherited_triple_G_scalar_raw_bound_high_only
    (rBound : ℕ) (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
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
          (p : MarkedPlacement B),p∈B.markedAttach 0 →
        ∀(r : MarkedPlacement p.tree),r∈p.tree.markedAttach 0 →
        ∀(z : MarkedPlacement r.tree),z∈r.tree.markedAttach 0 →
          let D:=(((NativeObservedDiagram.identity B).observe p).observe r).observe z
          0 < U → (spine.graftDiagram D).tree.leaves ≤ rBound →
          p.embed base.target ≠ p.mark → U ≤ p.tree.splitIndex (p.embed base.target) p.mark →
          let v:=M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed base.target) p.mark))
          M.xs ≤ v → M.z ≤ v →
          |nativeObservedGScalar (spine.graftDiagram D) base.target U K| *
            (M.xs+partitionPoint 0 as (z.tree.splitIndex (z.embed r.mark) z.mark)) ≤ Cg*v := by
  classical
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_G_word_scalar_raw_bound_high_only
    (D₀:=D₀) rBound Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [HG] with n hn
  intro M hs0 hsxs hsource hxs as ho
  dsimp only
  intro B T base P star U spine p hp r hr z hz hU hleaves hac hhigh hxv hzv
  let D:=(((NativeObservedDiagram.identity B).observe p).observe r).observe z
  have Hindex : (nativeObservedTargetMetadata D base.target).1=
      p.tree.splitIndex (p.embed base.target) p.mark := by
    simp only [nativeObservedTargetMetadata,D,NativeObservedDiagram.observe,NativeObservedDiagram.identity,
      List.map_cons,List.map_nil,id_eq,(r.tree.markedAttach_embed_preserves 0 z hz).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2]
  have Hdiag : (nativeObservedTargetMetadata D base.target).2=false := by
    simp only [nativeObservedTargetMetadata,D,NativeObservedDiagram.observe,NativeObservedDiagram.identity,
      List.map_cons,List.map_nil,id_eq,(r.tree.markedAttach_embed_preserves 0 z hz).1.eq_iff,
      (p.tree.markedAttach_embed_preserves 0 r hr).1.eq_iff,decide_eq_false hac]
  have H:=hn M hs0 hsxs hsource hxs as ho B T base P star U spine D
    (by simp [D,NativeObservedDiagram.observe,NativeObservedDiagram.identity]) hU hleaves Hdiag
    (by simpa only [Hindex] using hhigh) (by simpa only [Hindex] using hxv)
    (by simpa only [Hindex] using hzv)
  rw [Hindex] at H
  simpa only [nativeObservedErrorIndex,D,NativeObservedDiagram.observe,NativeObservedDiagram.identity,
    List.map_cons,List.map_nil] using H

end OAI.SKFluctuations.Cavity
