module

public import CavityAttachedTree

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
open GaussianCalculus
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

namespace ClockTree

 noncomputable def MarkedPlacement.hit {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (s : T.Slot) : ℝ := by
  classical
  exact if p.mark = p.embed s then 1 else 0

 theorem MarkedPlacement.hit_fresh {as : List PositiveMass} (T : ClockTree S as)
    (c : ℝ) (s : T.Slot) : (MarkedPlacement.fresh T c).hit s = 0 := by
  classical
  simp [MarkedPlacement.hit,MarkedPlacement.fresh]

 theorem markedAttach_hit {as : List PositiveMass} (T : ClockTree S as) (a : ℝ)
    (s : T.Slot) : ((T.markedAttach a).map fun p => p.coeff*p.hit s).sum = 1 := by
  classical
  induction T generalizing a with
  | leaf => cases s; simp [markedAttach,MarkedPlacement.hit,MarkedPlacement.coincide,
      MarkedPlacement.fresh]
  | step b T ih =>
    simp only [markedAttach,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
      MarkedPlacement.hit_fresh,mul_zero,zero_add]
    exact ih b.val s
  | fork T U ihT ihU =>
    cases s with
    | inl s =>
      simpa only [markedAttach,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
        List.map_map,Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.left,
        MarkedPlacement.right,MarkedPlacement.hit,Sum.map_inl,id_eq,Sum.inr_ne_inl,
        Sum.inl.injEq,ite_false,mul_zero,List.map_const',List.sum_replicate,nsmul_zero,
        zero_add,add_zero] using ihT a s
    | inr s =>
      simpa only [markedAttach,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
        List.map_map,Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.left,
        MarkedPlacement.right,MarkedPlacement.hit,Sum.map_inr,id_eq,Sum.inr_ne_inl,
        Sum.inl_ne_inr,Sum.inr.injEq,ite_false,mul_zero,List.map_const',List.sum_replicate,
        nsmul_zero,zero_add,add_zero] using ihU a s

 theorem markedAttach_mass {as : List PositiveMass} (T : ClockTree S as) (a : ℝ) :
    ((T.markedAttach a).map fun p => p.coeff).sum = a := by
  induction T generalizing a with
  | leaf => simp [markedAttach,MarkedPlacement.coincide,MarkedPlacement.fresh]
  | step b T ih =>
    simpa only [markedAttach,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,MarkedPlacement.step,
      MarkedPlacement.fresh,ih] using sub_add_cancel a b.val
  | fork T U ihT ihU =>
    simp only [markedAttach,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,ihT,ihU]
    ring

 theorem markedAttach_disorderPreserves_actual {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    p.tree.disorderExpect w φ v q (fun σ => P (p.restrict σ)) x =
      T.disorderExpect w φ v q P x := by
  let e := finiteJetEquiv ι
  have H := T.markedAttach_rootPreserves hw (reindexFeature e φ) ho p hp
    (fun i => q 0 (e i)-v (e i)) (fun j i => q (j+1) (e i)-q j (e i))
    P ((coordinateEquiv e).symm x)
  rw [p.tree.rootExpect_eq_disorderExpect hw (reindexFeature e φ) ho
      (fun σ => P (p.restrict σ)) (fun i => v (e i)) (fun j i => q j (e i)),
    T.rootExpect_eq_disorderExpect hw (reindexFeature e φ) ho P
      (fun i => v (e i)) (fun j i => q j (e i)),
    p.tree.disorderExpect_reindex e w φ v q,T.disorderExpect_reindex e w φ v q,
    ContinuousLinearEquiv.apply_symm_apply] at H
  exact H

 theorem markedAttach_disorder_tested_hit {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    ((T.markedAttach a).map fun p => p.coeff*p.hit s*
      p.tree.disorderExpect w φ v q (fun σ => P (p.restrict σ)) x).sum =
        T.disorderExpect w φ v q P x := by
  have he : ((T.markedAttach a).map fun p => p.coeff*p.hit s*
      p.tree.disorderExpect w φ v q (fun σ => P (p.restrict σ)) x).sum =
      ((T.markedAttach a).map fun p => p.coeff*p.hit s*T.disorderExpect w φ v q P x).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [T.markedAttach_disorderPreserves_actual hw φ ho p hp v q P x]
  rw [he,List.sum_map_mul_right,T.markedAttach_hit,one_mul]

 theorem markedAttach_disorder_zero_diagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    ((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        r.tree.disorderExpect w φ v q (fun σ => P (p.restrict (r.restrict σ))) x).sum).sum = 0 := by
  have hi (p : MarkedPlacement T) :
      ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        r.tree.disorderExpect w φ v q (fun σ => P (p.restrict (r.restrict σ))) x).sum =
      p.tree.disorderExpect w φ v q (fun σ => P (p.restrict σ)) x :=
    p.tree.markedAttach_disorder_tested_hit hw φ ho v q p.mark (fun σ => P (p.restrict σ)) x
  simp_rw [hi]
  have he : ((T.markedAttach 0).map fun p => p.coeff*
      p.tree.disorderExpect w φ v q (fun σ => P (p.restrict σ)) x).sum =
      ((T.markedAttach 0).map fun p => p.coeff*T.disorderExpect w φ v q P x).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [T.markedAttach_disorderPreserves_actual hw φ ho p hp v q P x]
  rw [he,List.sum_map_mul_right,T.markedAttach_mass,zero_mul]

 def disorderOffDiagonalProfileJet (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (E : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
    ((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*(1-r.hit p.mark)*
        r.tree.disorderExpect w φ v q (profilePairTest P E p r) x).sum).sum/2

 theorem marked_profile_diagonal_actual (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} {T : ClockTree S as} (p : MarkedPlacement T)
    (r : MarkedPlacement p.tree) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) {E : ℕ → S → S → ℝ} {d : ℝ}
    (hE : ∀ σ, E as.length σ σ = d) (x : ι → ℝ) :
    r.hit p.mark*r.tree.disorderExpect w φ v q (profilePairTest P E p r) x =
      d*r.hit p.mark*r.tree.disorderExpect w φ v q
        (fun σ => P (p.restrict (r.restrict σ))) x := by
  classical
  by_cases h : r.mark = r.embed p.mark
  · have hs (σ : r.tree.Assignment) : p.spin (r.restrict σ) = r.spin σ := by
      rw [p.spin_at,r.restrict_at,←h,←r.spin_at]
    have hj : r.tree.splitIndex (r.embed p.mark) r.mark = as.length := by
      rw [←h,r.tree.splitIndex_self]
    simp only [MarkedPlacement.hit,ite_eq_left h,one_mul,mul_one]
    change (∑ σ, r.tree.disorderWeight w φ v q σ x *
      (P (p.restrict (r.restrict σ))*E
        (r.tree.splitIndex (r.embed p.mark) r.mark) (p.spin (r.restrict σ)) (r.spin σ))) =
      d*(∑ σ, r.tree.disorderWeight w φ v q σ x*P (p.restrict (r.restrict σ)))
    simp only [hj,hs,hE,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  · simp only [MarkedPlacement.hit,ite_eq_right h,zero_mul,mul_zero]

 theorem disorderProfileJets_one_eq_offDiagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) {E : ℕ → S → S → ℝ} {d : ℝ}
    (hE : ∀ σ, E as.length σ σ = d) (x : ι → ℝ) :
    disorderProfileJets w φ v q x [E] T P =
      T.disorderOffDiagonalProfileJet w φ v q P E x := by
  have ht (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      r.coeff*r.tree.disorderExpect w φ v q (profilePairTest P E p r) x =
      r.coeff*(1-r.hit p.mark)*r.tree.disorderExpect w φ v q (profilePairTest P E p r) x+
        d*(r.coeff*r.hit p.mark*r.tree.disorderExpect w φ v q
          (fun σ => P (p.restrict (r.restrict σ))) x) := by
    calc
      _ = r.coeff*(1-r.hit p.mark)*r.tree.disorderExpect w φ v q (profilePairTest P E p r) x+
        r.coeff*(r.hit p.mark*r.tree.disorderExpect w φ v q (profilePairTest P E p r) x) := by ring
      _ = _ := by
        rw [marked_profile_diagonal_actual w φ p r v q P hE x]
        ring
  simp only [disorderProfileJets]
  simp_rw [ht,List.sum_map_add,List.sum_map_mul_left,mul_add]
  rw [List.sum_map_add]
  have he : ((T.markedAttach 0).map fun p => p.coeff*(d*
      ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        r.tree.disorderExpect w φ v q (fun σ => P (p.restrict (r.restrict σ))) x).sum)).sum =
      d*((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*r.hit p.mark*
        r.tree.disorderExpect w φ v q (fun σ => P (p.restrict (r.restrict σ))) x).sum).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    ring
  rw [he,T.markedAttach_disorder_zero_diagonal hw φ ho v q P x,mul_zero,add_zero]
  rfl

end ClockTree
end OAI.SKFluctuations.Hierarchy
