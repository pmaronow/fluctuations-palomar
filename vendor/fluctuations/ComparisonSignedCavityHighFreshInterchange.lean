module

public import ComparisonSignedCavityForestFullFreshRestTransport
public import ComparisonSignedCavityStarFieldTestFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B ι : Type}

theorem nativeFreshAtSlot_zero_eq_fresh {as : List PositiveMass}
    (T : ClockTree (S×B) as) (a : ℝ) (s : T.Slot) :
    ∃ c : ℝ,nativeFreshAtSlot T a s 0=MarkedPlacement.fresh T c := by
  cases T with
  | leaf => exact ⟨a-1,rfl⟩
  | step b T => exact ⟨a-b.val,rfl⟩
  | fork T V => exact ⟨-a,rfl⟩

variable [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem native_fresh_high_marked_interchange {as : List PositiveMass}
    (T : ClockTree (S×B) as) (s : T.Slot) (c aRow : ℝ)
    (p : MarkedPlacement (MarkedPlacement.fresh T c).tree)
    (hp : p∈(MarkedPlacement.fresh T c).tree.markedAttach aRow)
    (hh : 0 < p.tree.splitIndex (p.embed ((MarkedPlacement.fresh T c).embed s)) p.mark)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) :
    ∃ r : MarkedPlacement T,r∈T.markedAttach aRow ∧ p.coeff=r.coeff ∧
      p.tree.splitIndex (p.embed ((MarkedPlacement.fresh T c).embed s)) p.mark=
        r.tree.splitIndex (r.embed s) r.mark ∧
      ∀(q : ℕ→ι→ℝ≥0) (Q : T.cavityLeft.Assignment→S→S→ℝ) (x : ι→ℝ),
      p.tree.cavityLeft.expect w φ q
        (fun σ=>Q ((MarkedPlacement.fresh T c).restRestrict (p.restRestrict σ))
          (p.restSpin σ) ((MarkedPlacement.fresh T c).restSpin (p.restRestrict σ))) x=
      (MarkedPlacement.fresh r.tree c).tree.cavityLeft.expect w φ q
        (fun σ=>Q (r.restRestrict ((MarkedPlacement.fresh r.tree c).restRestrict σ))
          (r.restSpin ((MarkedPlacement.fresh r.tree c).restRestrict σ))
          ((MarkedPlacement.fresh r.tree c).restSpin σ)) x := by
  change p∈(T.fork (single as)).markedAttach aRow at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp only [MarkedPlacement.fresh,splitIndex,Sum.elim_inl,Sum.elim_inr] at hh
    omega
  · rcases List.mem_append.mp hp with hleft | hright
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hleft
      refine ⟨r,hr,rfl,rfl,?_⟩
      intro q Q x
      apply congrArg (fun F=>
        (r.tree.cavityLeft.fork (single (S:=S×B) as).cavityLeft).expect w φ q F x)
      funext σ
      have HR := MarkedPlacement.restRestrict_left r (single (S:=S×B) as) σ
      have HS := MarkedPlacement.restSpin_left r (single (S:=S×B) as) σ
      have HF := MarkedPlacement.restRestrict_fresh r.tree c σ
      rw [HR,HS,HF]
      rw [MarkedPlacement.restRestrict_fresh]
      rfl
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hright
      simp only [MarkedPlacement.right,MarkedPlacement.fresh,splitIndex,
        Sum.map_inl,Sum.elim_inl,Sum.elim_inr] at hh
      omega

omit [Nonempty S] in
theorem native_fresh_high_marked_zero_field_interchange {as : List PositiveMass}
    (T : ClockTree (S×B) as) (s : T.Slot) (c aFresh aRow : ℝ)
    (p : MarkedPlacement (MarkedPlacement.fresh T c).tree)
    (hp : p∈(MarkedPlacement.fresh T c).tree.markedAttach aRow)
    (hh : 0 < p.tree.splitIndex (p.embed ((MarkedPlacement.fresh T c).embed s)) p.mark)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) :
    ∃ r : MarkedPlacement T,r∈T.markedAttach aRow ∧ p.coeff=r.coeff ∧
      p.tree.splitIndex (p.embed ((MarkedPlacement.fresh T c).embed s)) p.mark=
        r.tree.splitIndex (r.embed s) r.mark ∧
      ∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→T.cavityLeft.Assignment→S→S→ℝ) (x : ι→ℝ),
      nativeStarFieldTestMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed ((MarkedPlacement.fresh T c).embed s))) 0 q
        (fun y σ=>J y ((MarkedPlacement.fresh T c).restRestrict (p.restRestrict σ))
          (p.restSpin σ) ((MarkedPlacement.fresh T c).restSpin (p.restRestrict σ))) x=
      let h:=nativeFreshAtSlot r.tree aFresh (r.embed s) 0
      nativeStarFieldTestMean w φ h.tree.cavityLeft
        (h.tree.cavityLeftSlot (h.embed (r.embed s))) 0 q
        (fun y σ=>J y (r.restRestrict (h.restRestrict σ))
          (r.restSpin (h.restRestrict σ)) (h.restSpin σ)) x := by
  obtain ⟨r,hr,hcoeff,hsplit,Hlaw⟩ := native_fresh_high_marked_interchange T s c aRow p hp hh w φ
  refine ⟨r,hr,hcoeff,hsplit,?_⟩
  intro q J x
  obtain ⟨d,hd⟩ := nativeFreshAtSlot_zero_eq_fresh r.tree aFresh (r.embed s)
  dsimp only
  rw [nativeStarFieldTestMean_zero,nativeStarFieldTestMean_zero,hd]
  exact Hlaw q (J x) x

variable [Fintype B] [Nonempty B]

omit [Fintype S] [Nonempty S] [Fintype B] [Nonempty B] in
theorem nativeFreshAtSlot_marked_left_restRestrict {as : List PositiveMass}
    {T : ClockTree (S×B) as} (r : MarkedPlacement T) (V : ClockTree (S×B) as)
    (a : ℝ) (s : T.Slot) (j : ℕ)
    (σ : (nativeFreshAtSlot (r.left V).tree a ((r.left V).embed (Sum.inl s)) (j+1)).tree.cavityLeft.Assignment) :
    (nativeFreshAtSlot (r.left V).tree a ((r.left V).embed (Sum.inl s)) (j+1)).restRestrict σ=
      ((nativeFreshAtSlot r.tree a (r.embed s) (j+1)).restRestrict σ.1,σ.2) := by
  exact MarkedPlacement.restRestrict_left (nativeFreshAtSlot r.tree a (r.embed s) (j+1)) V σ

omit [Fintype S] [Nonempty S] [Fintype B] [Nonempty B] in
theorem nativeFreshAtSlot_marked_left_restSpin {as : List PositiveMass}
    {T : ClockTree (S×B) as} (r : MarkedPlacement T) (V : ClockTree (S×B) as)
    (a : ℝ) (s : T.Slot) (j : ℕ)
    (σ : (nativeFreshAtSlot (r.left V).tree a ((r.left V).embed (Sum.inl s)) (j+1)).tree.cavityLeft.Assignment) :
    (nativeFreshAtSlot (r.left V).tree a ((r.left V).embed (Sum.inl s)) (j+1)).restSpin σ=
      (nativeFreshAtSlot r.tree a (r.embed s) (j+1)).restSpin σ.1 := rfl

omit [Fintype S] [Nonempty S] [Fintype B] [Nonempty B] in
theorem nativeFreshAtSlot_marked_right_restRestrict {as : List PositiveMass}
    {V : ClockTree (S×B) as} (r : MarkedPlacement V) (T : ClockTree (S×B) as)
    (a : ℝ) (s : V.Slot) (j : ℕ)
    (σ : (nativeFreshAtSlot (r.right T).tree a ((r.right T).embed (Sum.inr s)) (j+1)).tree.cavityLeft.Assignment) :
    (nativeFreshAtSlot (r.right T).tree a ((r.right T).embed (Sum.inr s)) (j+1)).restRestrict σ=
      (σ.1,(nativeFreshAtSlot r.tree a (r.embed s) (j+1)).restRestrict σ.2) := by
  exact MarkedPlacement.restRestrict_right T (nativeFreshAtSlot r.tree a (r.embed s) (j+1)) σ

omit [Fintype S] [Nonempty S] [Fintype B] [Nonempty B] in
theorem nativeFreshAtSlot_marked_right_restSpin {as : List PositiveMass}
    {V : ClockTree (S×B) as} (r : MarkedPlacement V) (T : ClockTree (S×B) as)
    (a : ℝ) (s : V.Slot) (j : ℕ)
    (σ : (nativeFreshAtSlot (r.right T).tree a ((r.right T).embed (Sum.inr s)) (j+1)).tree.cavityLeft.Assignment) :
    (nativeFreshAtSlot (r.right T).tree a ((r.right T).embed (Sum.inr s)) (j+1)).restSpin σ=
      (nativeFreshAtSlot r.tree a (r.embed s) (j+1)).restSpin σ.2 := rfl

theorem native_high_fresh_interchange {as : List PositiveMass}
    (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (aFresh aRow : ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T aFresh s star).tree)
    (hp : p∈(nativeFreshAtSlot T aFresh s star).tree.markedAttach aRow)
    (hh : star < p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed s)) p.mark)
    {w : S→ℝ} (_hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) :
    ∃ r : MarkedPlacement T,r∈T.markedAttach aRow ∧ p.coeff=r.coeff ∧
      p.tree.splitIndex (p.embed ((nativeFreshAtSlot T aFresh s star).embed s)) p.mark=
        r.tree.splitIndex (r.embed s) r.mark ∧
      ∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→T.cavityLeft.Assignment→S→S→ℝ) (x : ι→ℝ),
      nativeStarFieldTestMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed ((nativeFreshAtSlot T aFresh s star).embed s))) star q
        (fun y σ=>J y ((nativeFreshAtSlot T aFresh s star).restRestrict (p.restRestrict σ))
          (p.restSpin σ) ((nativeFreshAtSlot T aFresh s star).restSpin (p.restRestrict σ))) x=
      let h:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
      nativeStarFieldTestMean w φ h.tree.cavityLeft
        (h.tree.cavityLeftSlot (h.embed (r.embed s))) star q
        (fun y σ=>J y (r.restRestrict (h.restRestrict σ))
          (r.restSpin (h.restRestrict σ)) (h.restSpin σ)) x := by
  clear _hw
  induction T generalizing star aFresh aRow a₀ with
  | leaf =>
    have H := p.tree.splitIndex_le_clockLength
      (p.embed ((nativeFreshAtSlot .leaf aFresh s star).embed s)) p.mark
    simp only [List.length_nil] at H
    omega
  | @step b as T ih =>
    cases star with
    | zero =>
      exact native_fresh_high_marked_zero_field_interchange (T.step b) s (aFresh-b.val)
        aFresh aRow p hp hh w φ
    | succ star =>
      let g:=nativeFreshAtSlot T b.val s star
      change p∈(g.tree.step b).markedAttach aRow at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [MarkedPlacement.fresh,splitIndex,Sum.elim_inl,Sum.elim_inr] at hh
        omega
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
        have hh' : star < v.tree.splitIndex (v.embed (g.embed s)) v.mark := by
          change star+1 < 1+v.tree.splitIndex (v.embed (g.embed s)) v.mark at hh
          omega
        obtain ⟨r,hr,hcoeff,hsplit,Hlaw⟩ := ih s star (by simpa using hstar) b.val b.val v hv hh' ho.2.2
        refine ⟨r.step b,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩),hcoeff,?_,?_⟩
        · exact congrArg (1+·) hsplit
        · intro q J x
          change shiftedMean _ b.val _ _ x=shiftedMean _ b.val _ _ x
          congr 1
          funext y
          exact Hlaw (fun k=>q (k+1)) J y
  | @fork as T V ihT ihV =>
    cases star with
    | zero =>
      exact native_fresh_high_marked_zero_field_interchange (T.fork V) s (-aFresh)
        aFresh aRow p hp hh w φ
    | succ star =>
      cases s with
      | inl s =>
        let g:=nativeFreshAtSlot T aFresh s (star+1)
        change p∈(g.tree.fork V).markedAttach aRow at hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only [MarkedPlacement.fresh,splitIndex,Sum.elim_inl,Sum.elim_inr] at hh
          omega
        · rcases List.mem_append.mp hp with hleft | hright
          · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hleft
            have hh' : star+1 < v.tree.splitIndex (v.embed (g.embed s)) v.mark := hh
            obtain ⟨r,hr,hcoeff,hsplit,Hlaw⟩ := ihT s (star+1) hstar aFresh aRow v hv hh' ho
            refine ⟨r.left V,List.mem_cons_of_mem _ (List.mem_append_left _
              (List.mem_map.mpr ⟨r,hr,rfl⟩)),hcoeff,hsplit,?_⟩
            intro q J x
            change (∑τ,V.cavityLeft.weight w φ q τ x*_)=∑τ,V.cavityLeft.weight w φ q τ x*_
            apply Finset.sum_congr rfl
            intro τ _
            congr 1
            have HH:=Hlaw q (fun y σ u v=>J y (σ,τ) u v) x
            dsimp only [nativeFreshAtSlot]
            simpa only [nativeFreshAtSlot_marked_left_restRestrict,nativeFreshAtSlot_marked_left_restSpin,
              MarkedPlacement.restRestrict_left,MarkedPlacement.restSpin_left] using HH
          · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hright
            dsimp only [nativeFreshAtSlot] at hh
            simp only [MarkedPlacement.right,MarkedPlacement.left,splitIndex,
              Sum.map_inl,Sum.elim_inl,Sum.elim_inr] at hh
            omega
      | inr s =>
        let g:=nativeFreshAtSlot V aFresh s (star+1)
        change p∈(T.fork g.tree).markedAttach aRow at hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only [MarkedPlacement.fresh,splitIndex,Sum.elim_inl,Sum.elim_inr] at hh
          omega
        · rcases List.mem_append.mp hp with hleft | hright
          · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hleft
            dsimp only [nativeFreshAtSlot] at hh
            simp only [MarkedPlacement.right,MarkedPlacement.left,splitIndex,
              Sum.map_inr,Sum.elim_inl,Sum.elim_inr] at hh
            omega
          · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hright
            have hh' : star+1 < v.tree.splitIndex (v.embed (g.embed s)) v.mark := hh
            obtain ⟨r,hr,hcoeff,hsplit,Hlaw⟩ := ihV s (star+1) hstar aFresh aRow v hv hh' ho
            refine ⟨r.right T,List.mem_cons_of_mem _ (List.mem_append_right _
              (List.mem_map.mpr ⟨r,hr,rfl⟩)),hcoeff,hsplit,?_⟩
            intro q J x
            change (∑σ,T.cavityLeft.weight w φ q σ x*_)=∑σ,T.cavityLeft.weight w φ q σ x*_
            apply Finset.sum_congr rfl
            intro σ _
            congr 1
            have HH:=Hlaw q (fun y τ u v=>J y (σ,τ) u v) x
            dsimp only [nativeFreshAtSlot]
            simpa only [nativeFreshAtSlot_marked_right_restRestrict,nativeFreshAtSlot_marked_right_restSpin,
              MarkedPlacement.restRestrict_right,MarkedPlacement.restSpin_right] using HH

end OAI.SKFluctuations.Hierarchy.ClockTree
