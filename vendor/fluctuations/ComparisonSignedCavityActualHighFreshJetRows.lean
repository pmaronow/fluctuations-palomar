module

public import ComparisonSignedCavityActualHighFreshJetTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem native_high_fresh_full_covariance_signed_row_sum {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (aFresh aRow : ℝ) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (D : ℕ→ι→ℝ) (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ)
    (H : ℕ→Bool→ℝ) :
    ((nativeHighMarkedRows (nativeFreshAtSlot T aFresh s star).tree
        ((nativeFreshAtSlot T aFresh s star).embed s) star aRow).map
      (fun p=>p.coeff*H
        (p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed s)) p.mark)
        (decide (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed s)))*
        disorderProfileJets w φ v q x [ReplicaTree.coordinateProfile φ D] p.tree
          (fun σ=>Q ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
            (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))))).sum=
    ((nativeHighMarkedRows T s star aRow).map
      (fun (r : MarkedPlacement T)=>r.coeff*H (r.tree.splitIndex (r.embed s) r.mark)
        (decide (r.mark=r.embed s))*
        (let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
        disorderProfileJets w φ v q x [ReplicaTree.coordinateProfile φ D] g.tree
          (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ))))).sum := by
  have HR:=native_high_fresh_full_row_interchange T s star hstar aFresh aRow hw φ ho
  apply congrArg List.sum
  apply (show ∀{l₁ l₂ : List ℝ},List.Forall₂ Eq l₁ l₂→l₁=l₂ from
    fun h=>by simpa only [List.forall₂_eq_eq_eq] using h)
  apply List.rel_map (fun p r h=>?_) HR
  have Hlaw:=h.covariance_eq hw ho v q hq hq0 D Q x
  have Hhit : decide (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed s))=
      decide (r.mark=r.embed s) :=
    congrArg (fun P:Prop=>@decide P (Classical.propDecidable P)) (propext (h.2.1 s).2)
  rw [h.1,(h.2.1 s).1,Hhit,Hlaw]

theorem native_high_fresh_full_observed_covariance_signed_row_sum {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (aFresh aRow : ℝ) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (D : ℕ→ι→ℝ) (Q : T.Assignment→S→S→ℝ) (u x : ι→ℝ)
    (H : ℕ→Bool→ℝ) :
    ((nativeHighMarkedRows (nativeFreshAtSlot T aFresh s star).tree
        ((nativeFreshAtSlot T aFresh s star).embed s) star aRow).map
      (fun p=>p.coeff*H
        (p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed s)) p.mark)
        (decide (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed s)))*
        nativeMarkedProfileRow w φ p.tree v q [ReplicaTree.coordinateProfile φ D]
          (fun σ=>Q ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
            (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))) (fun σ=>φ σ u) x)).sum=
    ((nativeHighMarkedRows T s star aRow).map
      (fun (r : MarkedPlacement T)=>r.coeff*H (r.tree.splitIndex (r.embed s) r.mark)
        (decide (r.mark=r.embed s))*
        (let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
        nativeMarkedProfileRow w φ g.tree v q [ReplicaTree.coordinateProfile φ D]
          (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) (fun σ=>φ σ u) x))).sum := by
  have HR:=native_high_fresh_full_row_interchange T s star hstar aFresh aRow hw φ ho
  apply congrArg List.sum
  apply (show ∀{l₁ l₂ : List ℝ},List.Forall₂ Eq l₁ l₂→l₁=l₂ from
    fun h=>by simpa only [List.forall₂_eq_eq_eq] using h)
  apply List.rel_map (fun p r h=>?_) HR
  have Hlaw:=h.observed_covariance_eq hw ho v q hq hq0 D Q u x
  have Hhit : decide (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed s))=
      decide (r.mark=r.embed s) :=
    congrArg (fun P:Prop=>@decide P (Classical.propDecidable P)) (propext (h.2.1 s).2)
  rw [h.1,(h.2.1 s).1,Hhit,Hlaw]

end OAI.SKFluctuations.Hierarchy.ClockTree
