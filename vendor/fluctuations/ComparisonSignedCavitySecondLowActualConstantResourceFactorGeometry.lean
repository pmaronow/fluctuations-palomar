module

public import ComparisonSignedCavitySecondLowGeneratedFullB0Geometry
public import ComparisonSignedCavityActualConstantResourceLowForks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}
set_option maxHeartbeats 16000000

theorem NativeActualResourceGenerated.constant_resource_markedStar
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    {mark : NativeResourceMark} (hm : mark∈P.resources) :
    ∃j,j<k ∧ mark=.markedStar j := by
  rw [hP.resource_word,List.nil_append] at hm
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hm
  exact ⟨j,List.mem_range.mp hj,rfl⟩

theorem NativeActualResourceGenerated.constant_resource_not_initial
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P) :
    NativeResourceMark.initial∉P.resources := by
  intro hm
  obtain ⟨j,_,H⟩:=hP.constant_resource_markedStar hm
  cases H

theorem NativeActualResourceGenerated.constant_live_factor_markedStar
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (e : Fin P.live.factors.length) :
    ∃j,j<k ∧ (P.live.factors.get e).1=.markedStar j := by
  apply hP.constant_resource_markedStar
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨P.live.factors.get e,List.get_mem _ e,rfl⟩

theorem NativeActualResourceGenerated.constant_frozen_factor_markedStar
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource S as i star) (hF : F∈P.frozen)
    (e : Fin F.monomial.factors.length) :
    ∃j,j<k ∧ (F.monomial.factors.get e).1=.markedStar j := by
  apply hP.constant_resource_markedStar
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨F,hF,?_⟩
  exact List.mem_map.mpr ⟨F.monomial.factors.get e,List.get_mem _ e,rfl⟩

theorem NativeActualResourceGenerated.constant_live_factor_cut_star
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (e : Fin P.live.factors.length) :
    (P.live.factors.get e).1.cut i star=star := by
  obtain ⟨j,_,H⟩:=hP.constant_live_factor_markedStar e
  rw [H]
  rfl

theorem NativeActualResourceGenerated.constant_live_factor_split_star
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (e : Fin P.live.factors.length) :
    T.splitIndex (P.live.factors.get e).2.1 (P.live.factors.get e).2.2=star := by
  exact (P.live.cuts _ (List.get_mem _ e)).trans (hP.constant_live_factor_cut_star e)

theorem NativeActualResourceGenerated.constant_frozen_factor_cut_star
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource S as i star) (hF : F∈P.frozen)
    (e : Fin F.monomial.factors.length) :
    (F.monomial.factors.get e).1.cut i star=star := by
  obtain ⟨j,_,H⟩:=hP.constant_frozen_factor_markedStar F hF e
  rw [H]
  rfl

theorem NativeActualResourceGenerated.constant_frozen_factor_split_star
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource S as i star) (hF : F∈P.frozen)
    (e : Fin F.monomial.factors.length) :
    F.tree.splitIndex (F.monomial.factors.get e).2.1 (F.monomial.factors.get e).2.2=star := by
  exact (F.monomial.cuts _ (List.get_mem _ e)).trans (hP.constant_frozen_factor_cut_star F hF e)

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators

theorem native_actual_constant_resource_initial_factors_eq_empty
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P) :
    nativeActualResourceInitialFactors P.live=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have H:(P.live.factors.get e).1=.initial:=(Finset.mem_filter.mp he).2
  obtain ⟨j,_,Hj⟩:=hP.constant_live_factor_markedStar e
  rw [H] at Hj
  cases Hj

theorem native_actual_constant_resource_canonical_source_mass_eq_star
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (hi : i ≤ star) (hs : star<as.length) (e : Fin P.live.factors.length) :
    (nativeActualResourceCanonicalShape P.live hi hs).sourceLowMass e=partitionPoint 0 as star := by
  rw [native_actual_resource_canonical_source_mass_eq_tag_cut,hP.constant_live_factor_cut_star]

theorem native_actual_constant_resource_canonical_factor_split_star
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (hi : i ≤ star) (hs : star<as.length) (e : Fin P.live.factors.length) :
    T.splitIndex ((nativeActualResourceCanonicalShape P.live hi hs).i e)
      ((nativeActualResourceCanonicalShape P.live hi hs).j e)=star := by
  dsimp only [nativeActualResourceCanonicalShape]
  rw [T.splitIndex_symm]
  exact hP.constant_live_factor_split_star e

theorem native_actual_constant_resource_canonical_source_mass
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (hi : i ≤ star) (hs : star<as.length) (Cmass x W : ℝ)
    (Hstar : partitionPoint 0 as star ≤ Cmass*W) (e : Fin P.live.factors.length) :
    (nativeActualResourceCanonicalShape P.live hi hs).sourceLowMass e ≤
      Cmass*sourceFactorScale x W (nativeActualResourceInitialFactors P.live) e := by
  rw [native_actual_constant_resource_canonical_source_mass_eq_star hP hi hs,
    native_actual_constant_resource_initial_factors_eq_empty hP]
  simpa only [sourceFactorScale,Finset.notMem_empty,ite_false] using Hstar

theorem native_actual_constant_resource_canonical_source_radius_gate
    {n i star U : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (hi : i ≤ star) (hs : star<as.length) (bound : ℝ)
    (Hstar : M.R (partitionPoint 0 as star) ≤ bound) (e : Fin P.live.factors.length) :
    M.R ((nativeActualResourceCanonicalShape P.live hi hs).sourceLowMass e) ≤ bound := by
  rw [native_actual_constant_resource_canonical_source_mass_eq_star hP hi hs]
  exact Hstar

theorem native_actual_constant_resource_canonical_scale
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P) (x W : ℝ) :
    sourceMonomialScale x W (nativeActualResourceInitialFactors P.live)=W^P.live.factors.length := by
  rw [native_actual_constant_resource_initial_factors_eq_empty hP]
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,one_mul]

theorem native_actual_constant_resource_frozen_initial_factors_eq_empty
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource (Spin n×Bool) as i star) (hF : F∈P.frozen) :
    nativeActualResourceInitialFactors F.monomial=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have H:(F.monomial.factors.get e).1=.initial:=(Finset.mem_filter.mp he).2
  obtain ⟨j,_,Hj⟩:=hP.constant_frozen_factor_markedStar F hF e
  rw [H] at Hj
  cases Hj

theorem native_actual_constant_resource_frozen_canonical_source_mass_eq_star
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource (Spin n×Bool) as i star) (hF : F∈P.frozen)
    (hi : i ≤ star) (hs : star<as.length) (e : Fin F.monomial.factors.length) :
    (nativeActualResourceCanonicalShape F.monomial hi hs).sourceLowMass e=partitionPoint 0 as star := by
  rw [native_actual_resource_canonical_source_mass_eq_tag_cut,hP.constant_frozen_factor_cut_star F hF]

theorem native_actual_constant_resource_frozen_canonical_source_mass
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource (Spin n×Bool) as i star) (hF : F∈P.frozen)
    (hi : i ≤ star) (hs : star<as.length) (Cmass x W : ℝ)
    (Hstar : partitionPoint 0 as star ≤ Cmass*W) (e : Fin F.monomial.factors.length) :
    (nativeActualResourceCanonicalShape F.monomial hi hs).sourceLowMass e ≤
      Cmass*sourceFactorScale x W (nativeActualResourceInitialFactors F.monomial) e := by
  rw [native_actual_constant_resource_frozen_canonical_source_mass_eq_star hP F hF hi hs,
    native_actual_constant_resource_frozen_initial_factors_eq_empty hP F hF]
  simpa only [sourceFactorScale,Finset.notMem_empty,ite_false] using Hstar

theorem native_actual_constant_resource_frozen_canonical_source_radius_gate
    {n i star U : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource (Spin n×Bool) as i star) (hF : F∈P.frozen)
    (hi : i ≤ star) (hs : star<as.length) (bound : ℝ)
    (Hstar : M.R (partitionPoint 0 as star) ≤ bound) (e : Fin F.monomial.factors.length) :
    M.R ((nativeActualResourceCanonicalShape F.monomial hi hs).sourceLowMass e) ≤ bound := by
  rw [native_actual_constant_resource_frozen_canonical_source_mass_eq_star hP F hF hi hs]
  exact Hstar

theorem native_actual_constant_resource_frozen_canonical_scale
    {n i star U : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (F : NativeFrozenResource (Spin n×Bool) as i star) (hF : F∈P.frozen) (x W : ℝ) :
    sourceMonomialScale x W (nativeActualResourceInitialFactors F.monomial)=W^F.monomial.factors.length := by
  rw [native_actual_constant_resource_frozen_initial_factors_eq_empty hP F hF]
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,one_mul]

end OAI.SKFluctuations.Cavity
