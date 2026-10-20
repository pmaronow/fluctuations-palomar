module

public import ComparisonSignedCavityStarFieldTestFold
public import ComparisonSignedCavityHighMarkedRows
public import Mathlib.Data.List.Forall2

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype ι] [Fintype S] [Nonempty S] in
theorem nativeFreshAtSlot_zero_eq_fresh_full {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) (s : T.Slot) :
    ∃c : ℝ,nativeFreshAtSlot T a s 0=MarkedPlacement.fresh T c := by
  cases T with
  | leaf=>exact ⟨a-1,rfl⟩
  | step b T=>exact ⟨a-b.val,rfl⟩
  | fork T V=>exact ⟨-a,rfl⟩

def NativeHighFreshFullRowRelation {as : List PositiveMass}
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (aFresh : ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T aFresh s star).tree)
    (r : MarkedPlacement T) : Prop :=
  p.coeff=r.coeff ∧
    (∀c:T.Slot,
      p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed c)) p.mark=
        r.tree.splitIndex (r.embed c) r.mark ∧
      (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed c) ↔ r.mark=r.embed c)) ∧
    ∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→T.Assignment→S→S→ℝ) (x : ι→ℝ),
      nativeStarFieldTestMean w φ p.tree
        ((p.embed ((nativeFreshAtSlot T aFresh s star).embed s))) star q
        (fun y σ=>J y ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
          (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))) x=
      let h:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
      nativeStarFieldTestMean w φ h.tree
        ((h.embed (r.embed s))) star q
        (fun y σ=>J y (r.restrict (h.restrict σ))
          (r.spin (h.restrict σ)) (h.spin σ)) x

omit [Nonempty S] in
theorem native_fresh_marked_full_row_joint_law {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (c aFresh : ℝ)
    (r : MarkedPlacement T) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→T.Assignment→S→S→ℝ) (x : ι→ℝ) :
    let p:=r.left (single (S:=S) as)
    nativeStarFieldTestMean w φ p.tree
      ((p.embed ((MarkedPlacement.fresh T c).embed s))) 0 q
      (fun y σ=>J y ((MarkedPlacement.fresh T c).restrict (p.restrict σ))
        (p.spin σ) ((MarkedPlacement.fresh T c).spin (p.restrict σ))) x=
    let h:=nativeFreshAtSlot r.tree aFresh (r.embed s) 0
    nativeStarFieldTestMean w φ h.tree
      ((h.embed (r.embed s))) 0 q
      (fun y σ=>J y (r.restrict (h.restrict σ))
        (r.spin (h.restrict σ)) (h.spin σ)) x := by
  obtain ⟨d,hd⟩:=nativeFreshAtSlot_zero_eq_fresh_full r.tree aFresh (r.embed s)
  dsimp only
  rw [nativeStarFieldTestMean_zero,nativeStarFieldTestMean_zero,hd]
  rfl

omit [Nonempty S] in
theorem native_high_fresh_full_row_interchange {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (aFresh aRow : ℝ) {w : S→ℝ} (_hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a₀ : ℝ} (ho : MassOrdered a₀ as) :
    List.Forall₂ (NativeHighFreshFullRowRelation w φ T s star aFresh)
      (nativeHighMarkedRows (nativeFreshAtSlot T aFresh s star).tree
        ((nativeFreshAtSlot T aFresh s star).embed s) star aRow)
      (nativeHighMarkedRows T s star aRow) := by
  clear _hw
  induction T generalizing star aFresh aRow a₀ with
  | leaf =>
    have hz:star=0:=by simpa using hstar
    subst star
    exact List.Forall₂.nil
  | @step b as T ih =>
    cases star with
    | zero =>
      simp only [nativeFreshAtSlot,nativeHighMarkedRows,MarkedPlacement.fresh,
        MarkedPlacement.left]
      rw [List.forall₂_map_left_iff]
      apply List.forall₂_same.mpr
      intro r hr
      refine ⟨rfl,?_,?_⟩
      · intro c
        exact ⟨rfl,Sum.inl.inj_iff⟩
      · exact native_fresh_marked_full_row_joint_law (T.step b) s (aFresh-b.val) aFresh r w φ
    | succ star =>
      simp only [nativeFreshAtSlot,nativeHighMarkedRows,MarkedPlacement.step]
      apply List.rel_map (fun p r H=>?_) (ih s star (by simpa using hstar) b.val b.val ho.2.2)
      rcases H with ⟨hc,hm,Hlaw⟩
      refine ⟨hc,?_,?_⟩
      · intro c
        exact ⟨congrArg (1+·) (hm c).1,(hm c).2⟩
      · intro q J x
        change shiftedMean _ b.val _ _ x=shiftedMean _ b.val _ _ x
        congr 1
        funext y
        exact Hlaw (fun k=>q (k+1)) J y
  | @fork as T V ihT ihV =>
    cases star with
    | zero =>
      simp only [nativeFreshAtSlot,nativeHighMarkedRows,MarkedPlacement.fresh,
        MarkedPlacement.left]
      rw [List.forall₂_map_left_iff]
      apply List.forall₂_same.mpr
      intro r hr
      refine ⟨rfl,?_,?_⟩
      · intro c
        exact ⟨rfl,Sum.inl.inj_iff⟩
      · exact native_fresh_marked_full_row_joint_law (T.fork V) s (-aFresh) aFresh r w φ
    | succ star =>
      cases s with
      | inl s =>
        simp only [nativeFreshAtSlot,nativeHighMarkedRows]
        apply List.rel_map (fun p r H=>?_) (ihT s (star+1) hstar aFresh aRow ho)
        rcases H with ⟨hc,hm,Hlaw⟩
        refine ⟨hc,?_,?_⟩
        · intro c
          cases c with
          | inl c => exact ⟨(hm c).1,by simpa only [nativeFreshAtSlot,MarkedPlacement.left,Sum.map_inl,Sum.inl.injEq] using (hm c).2⟩
          | inr c => exact ⟨rfl,by simp only [nativeFreshAtSlot,MarkedPlacement.left,Sum.map_inr,Sum.inl_ne_inr]⟩
        · intro q J x
          change (∑τ,V.weight w φ q τ x*_)=∑τ,V.weight w φ q τ x*_
          apply Finset.sum_congr rfl
          intro τ _
          congr 1
          have HH:=Hlaw q (fun y σ u v=>J y (σ,τ) u v) x
          dsimp only [nativeFreshAtSlot]
          simpa only [nativeFreshAtSlot,MarkedPlacement.left,Sum.map_inl] using HH
      | inr s =>
        simp only [nativeFreshAtSlot,nativeHighMarkedRows]
        apply List.rel_map (fun p r H=>?_) (ihV s (star+1) hstar aFresh aRow ho)
        rcases H with ⟨hc,hm,Hlaw⟩
        refine ⟨hc,?_,?_⟩
        · intro c
          cases c with
          | inl c => exact ⟨rfl,by simp only [nativeFreshAtSlot,MarkedPlacement.right,Sum.map_inl,Sum.inr_ne_inl]⟩
          | inr c => exact ⟨(hm c).1,by simpa only [nativeFreshAtSlot,MarkedPlacement.right,Sum.map_inr,Sum.inr.injEq] using (hm c).2⟩
        · intro q J x
          change (∑σ,T.weight w φ q σ x*_)=∑σ,T.weight w φ q σ x*_
          apply Finset.sum_congr rfl
          intro σ _
          congr 1
          have HH:=Hlaw q (fun y τ u v=>J y (σ,τ) u v) x
          dsimp only [nativeFreshAtSlot]
          simpa only [nativeFreshAtSlot,MarkedPlacement.right,Sum.map_inr] using HH

omit [Nonempty S] in
theorem native_high_fresh_full_signed_row_sum {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (aFresh aRow : ℝ) {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a₀ : ℝ} (ho : MassOrdered a₀ as)
    (q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→T.Assignment→S→S→ℝ) (x : ι→ℝ)
    (H : (T.Slot→ℕ)→(T.Slot→Bool)→ℝ) :
    ((nativeHighMarkedRows (nativeFreshAtSlot T aFresh s star).tree
        ((nativeFreshAtSlot T aFresh s star).embed s) star aRow).map
      (fun p=>p.coeff *
        H (fun c=>p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed c)) p.mark)
          (fun c=>decide (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed c))) *
        nativeStarFieldTestMean w φ p.tree
          ((p.embed ((nativeFreshAtSlot T aFresh s star).embed s))) star q
          (fun y σ=>J y ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
            (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))) x)).sum=
    ((nativeHighMarkedRows T s star aRow).map
      (fun (r : MarkedPlacement T)=>r.coeff *
        H (fun c=>r.tree.splitIndex (r.embed c) r.mark) (fun c=>decide (r.mark=r.embed c)) *
        (let h : MarkedPlacement r.tree:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
        nativeStarFieldTestMean w φ h.tree
          ((h.embed (r.embed s))) star q
          (fun y σ=>J y (r.restrict (h.restrict σ))
            (r.spin (h.restrict σ)) (h.spin σ)) x))).sum := by
  have HR:=native_high_fresh_full_row_interchange T s star hstar aFresh aRow hw φ ho
  apply congrArg List.sum
  apply (show ∀{l₁ l₂ : List ℝ},List.Forall₂ Eq l₁ l₂ → l₁=l₂ from
    fun h=>by simpa only [List.forall₂_eq_eq_eq] using h)
  apply List.rel_map (fun p r h=>?_) HR
  rcases h with ⟨hc,hm,Hlaw⟩
  have hs : (fun c=>p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed c)) p.mark)=
        (fun c=>r.tree.splitIndex (r.embed c) r.mark):=funext fun c=>(hm c).1
  have hd : (fun c=>decide (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed c)))=
        (fun c=>decide (r.mark=r.embed c)):=by
    funext c
    exact congrArg (fun P:Prop=>@decide P (Classical.propDecidable P)) (propext (hm c).2)
  rw [hc,hs,hd,Hlaw q J x]

theorem NativeHighFreshFullRowRelation.expect_eq {as : List PositiveMass}
    {w : S→ℝ} {φ : S→(ι→ℝ)→L[ℝ]ℝ} {T : ClockTree S as}
    {s : T.Slot} {star : ℕ} {aFresh : ℝ}
    {p : MarkedPlacement (nativeFreshAtSlot T aFresh s star).tree} {r : MarkedPlacement T}
    (h : NativeHighFreshFullRowRelation w φ T s star aFresh p r)
    (hw : ∀σ,0<w σ) {a₀ : ℝ} (ho : MassOrdered a₀ as)
    (q : ℕ→ι→ℝ≥0) (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ) :
    p.tree.expect w φ q (fun σ=>Q
      ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
      (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))) x=
    let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
    g.tree.expect w φ q (fun σ=>Q (r.restrict (g.restrict σ))
      (r.spin (g.restrict σ)) (g.spin σ)) x := by
  have H:=h.2.2 q (fun _ σ u v=>Q σ u v) x
  simpa only [native_star_field_test_field_independent (hw:=hw) (φ:=φ) (ho:=ho)] using H

theorem NativeHighFreshFullRowRelation.disorder_eq {as : List PositiveMass}
    {w : S→ℝ} {φ : S→(ι→ℝ)→L[ℝ]ℝ} {T : ClockTree S as}
    {s : T.Slot} {star : ℕ} {aFresh : ℝ}
    {p : MarkedPlacement (nativeFreshAtSlot T aFresh s star).tree} {r : MarkedPlacement T}
    (h : NativeHighFreshFullRowRelation w φ T s star aFresh p r)
    (hw : ∀σ,0<w σ) {a₀ : ℝ} (ho : MassOrdered a₀ as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ) :
    p.tree.disorderExpect w φ v q (fun σ=>Q
      ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
      (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))) x=
    let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
    g.tree.disorderExpect w φ v q (fun σ=>Q (r.restrict (g.restrict σ))
      (r.spin (g.restrict σ)) (g.spin σ)) x := by
  dsimp only
  rw [p.tree.disorderExpect_integral hw φ ho,
    (nativeFreshAtSlot r.tree aFresh (r.embed s) star).tree.disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  apply integral_congr_ae
  exact Eventually.of_forall fun y=>h.expect_eq hw ho _ Q (x+y)

theorem native_high_fresh_full_disorder_signed_row_sum {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (aFresh aRow : ℝ) {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a₀ : ℝ} (ho : MassOrdered a₀ as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ)
    (H : (T.Slot→ℕ)→(T.Slot→Bool)→ℝ) :
    ((nativeHighMarkedRows (nativeFreshAtSlot T aFresh s star).tree
        ((nativeFreshAtSlot T aFresh s star).embed s) star aRow).map
      (fun p=>p.coeff *
        H (fun c=>p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed c)) p.mark)
          (fun c=>decide (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed c))) *
        p.tree.disorderExpect w φ v q
          (fun σ=>Q ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
            (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))) x)).sum=
    ((nativeHighMarkedRows T s star aRow).map
      (fun (r : MarkedPlacement T)=>r.coeff *
        H (fun c=>r.tree.splitIndex (r.embed c) r.mark) (fun c=>decide (r.mark=r.embed c)) *
        (let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
        g.tree.disorderExpect w φ v q
          (fun σ=>Q (r.restrict (g.restrict σ))
            (r.spin (g.restrict σ)) (g.spin σ)) x))).sum := by
  have HR:=native_high_fresh_full_row_interchange T s star hstar aFresh aRow hw φ ho
  apply congrArg List.sum
  apply (show ∀{l₁ l₂ : List ℝ},List.Forall₂ Eq l₁ l₂ → l₁=l₂ from
    fun h=>by simpa only [List.forall₂_eq_eq_eq] using h)
  apply List.rel_map (fun p r h=>?_) HR
  have Hlaw:=h.disorder_eq hw ho v q Q x
  rcases h with ⟨hc,hm,_⟩
  have hs : (fun c=>p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed c)) p.mark)=
        (fun c=>r.tree.splitIndex (r.embed c) r.mark):=funext fun c=>(hm c).1
  have hd : (fun c=>decide (p.mark=p.embed ((nativeFreshAtSlot T aFresh s star).embed c)))=
        (fun c=>decide (r.mark=r.embed c)):=by
    funext c
    exact congrArg (fun P:Prop=>@decide P (Classical.propDecidable P)) (propext (hm c).2)
  rw [hc,hs,hd,Hlaw]

end OAI.SKFluctuations.Hierarchy.ClockTree
