module

public import ComparisonSignedCavityActualMarkedExchange

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_single_pair_whole_exchange {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement (single (S := S) as)) (hp : p∈(single as).markedAttach a)
    (q : ℕ → ι → ℝ≥0) (Q : S → S → ℝ) (x : ι → ℝ) :
    p.tree.expect w φ q (fun σ=>
      Q (p.tree.atSlot σ
          (p.embed (singleSlot as)))
        (p.tree.atSlot σ p.mark)) x=
    p.tree.expect w φ q (fun σ=>
      Q (p.tree.atSlot σ p.mark)
        (p.tree.atSlot σ
          (p.embed (singleSlot as)))) x := by
  induction as generalizing a x q with
  | nil =>
    rcases List.mem_cons.mp hp with rfl|hp
    · rfl
    · obtain rfl:=List.mem_singleton.mp hp
      exact identical_fork_expect_swap w φ leaf q Q x
  | cons m as ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact identical_fork_expect_swap w φ (single (S := S) (m::as)) q
        (fun σ τ=>Q
          ((single (S := S) (m::as)).atSlot σ
            (singleSlot (m::as)))
          ((single (S := S) (m::as)).atSlot τ
            (singleSlot (m::as)))) x
    · obtain ⟨z,hz,hpz⟩:=List.mem_map.mp hp
      subst p
      change (z.tree.step m).expect w φ q
        (fun σ=>Q (z.tree.atSlot σ
          (z.embed (singleSlot as)))
          (z.tree.atSlot σ z.mark)) x=
        (z.tree.step m).expect w φ q (fun σ=>
          Q (z.tree.atSlot σ z.mark)
            (z.tree.atSlot σ
              (z.embed (singleSlot as)))) x
      rw [expect_step hw φ m z.tree ho.2.2 q,
        expect_step hw φ m z.tree ho.2.2 q]
      congr 1
      funext y
      exact ih ho.2.2 z hz (fun j=>q (j+1)) y

theorem native_single_whole_exchange
    (as : List PositiveMass) {w : S → ℝ} (hw : ∀σ,0<w σ)
    (φ : S → (ι → ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement (single (S:=S) as)) (hp : p∈(single as).markedAttach a)
    (q : ℕ → ι → ℝ≥0)
    (Q : (single (S:=S) as).Assignment → S → ℝ) (x : ι → ℝ) :
    p.tree.expect w φ q (fun σ=>Q (p.restrict σ) (p.spin σ)) x=
    p.tree.expect w φ q (fun σ=>Q
      (nativeReplaceAtSlot (single (S:=S) as)
        (singleSlot as)
        (p.restrict σ) (p.spin σ))
      ((single (S:=S) as).atSlot (p.restrict σ)
        (singleSlot as))) x := by
  let C:=fun u:S=>assignmentOfSlots (single (S:=S) as) (fun _=>u)
  have hAll : ∀c : (single (S:=S) as).Slot,
      c=singleSlot as := by
    intro c
    exact native_single_slot_eq as c
  have hOld : ∀σ,p.restrict σ=C
      ((single (S:=S) as).atSlot (p.restrict σ)
        (singleSlot as)) := by
    intro σ
    apply (single (S:=S) as).assignment_ext
    intro c
    rw [atSlot_assignmentOfSlots,hAll c]
  have hNew : ∀σ,nativeReplaceAtSlot (single (S:=S) as)
      (singleSlot as) (p.restrict σ) (p.spin σ)=
      C (p.spin σ) := by
    intro σ
    apply (single (S:=S) as).assignment_ext
    intro c
    rw [nativeReplaceAtSlot_at,atSlot_assignmentOfSlots,ite_eq_left (hAll c)]
  have H:=native_single_pair_whole_exchange hw φ as ho p hp q (fun u v=>Q (C u) v) x
  simp_rw [p.restrict_at] at hOld
  simp_rw [hNew]
  simp_rw [p.restrict_at]
  simp_rw [hOld]
  simpa only [←p.spin_at] using H

theorem native_target_singleton_whole_exchange
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (k : ℕ)
    (h : ∀c : T.Slot,k≤T.splitIndex s c → c=s)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (hh : k≤p.tree.splitIndex (p.embed s) p.mark)
    (q : ℕ → ι → ℝ≥0) (Q : T.Assignment → S → ℝ) (x : ι → ℝ) :
    p.tree.expect w φ q (fun σ=>Q (p.restrict σ) (p.spin σ)) x=
    p.tree.expect w φ q (fun σ=>Q
      (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
      (T.atSlot (p.restrict σ) s)) x := by
  induction T generalizing a k q x with
  | leaf=>
    cases s
    simpa only [single,singleSlot,cavityLeftSlot,cavityLeft,atSlot,nativeReplaceAtSlot] using
      native_single_whole_exchange [] hw φ ho p hp q Q x
  | @step b tail T ih=>
    cases k with
    | zero=>
      have hT:=native_eq_single_of_slots_singleton (T.step b) s (fun c=>h c (Nat.zero_le _))
      have hT0 : T=single tail := by injection hT with hT0
      subst T
      have hs:=native_single_slot_eq (b::tail) s
      subst s
      exact native_single_whole_exchange (b::tail) hw φ ho p hp q Q x
    | succ k=>
      rcases List.mem_cons.mp hp with rfl | hp
      · change k+1≤0 at hh
        omega
      · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
        have hi : ∀c:T.Slot,k≤T.splitIndex s c → c=s := by
          intro c hc
          exact h c (by change k+1≤1+T.splitIndex s c;omega)
        have hh' : k≤r.tree.splitIndex (r.embed s) r.mark := by
          change k+1≤1+r.tree.splitIndex (r.embed s) r.mark at hh
          omega
        change (r.tree.step b).expect w φ q
          (fun σ=>Q (r.restrict σ) (r.spin σ)) x=
          (r.tree.step b).expect w φ q (fun σ=>Q
            (nativeReplaceAtSlot T s (r.restrict σ) (r.spin σ))
            (T.atSlot (r.restrict σ) s)) x
        rw [expect_step hw φ b _ ho.2.2,expect_step hw φ b _ ho.2.2]
        congr 1
        funext y
        exact ih s k hi ho.2.2 r hr hh' (fun j=>q (j+1)) Q y
  | @fork tail T V ihT ihV=>
    cases k with
    | zero=>
      have H:Sum.inl (nativeFirstSlot T)=Sum.inr (nativeFirstSlot V):=
        (h _ (Nat.zero_le _)).trans (h _ (Nat.zero_le _)).symm
      exact (Sum.inl_ne_inr H).elim
    | succ k=>
      rcases List.mem_cons.mp hp with rfl | hp
      · change k+1≤0 at hh
        omega
      · rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
          cases s with
          | inr s=>change k+1≤0 at hh;omega
          | inl s=>
            have hi : ∀c:T.Slot,k+1≤T.splitIndex s c → c=s := by
              intro c hc
              exact Sum.inl.inj (h (Sum.inl c) hc)
            have hh' : k+1≤r.tree.splitIndex (r.embed s) r.mark:=hh
            dsimp only [MarkedPlacement.left]
            change (r.tree.fork V).expect w φ q
              (fun σ=>Q (r.restrict σ.1,σ.2) (r.spin σ.1)) x=
              (r.tree.fork V).expect w φ q (fun σ=>Q
                (nativeReplaceAtSlot T s (r.restrict σ.1)
                  (r.spin σ.1),σ.2)
                (T.atSlot (r.restrict σ.1) s)) x
            rw [expect_fork,expect_fork]
            conv_lhs=>rw [native_expect_nested_commute]
            conv_rhs=>rw [native_expect_nested_commute]
            congr 1
            funext τ
            exact ihT s (k+1) hi ho r hr hh' q (fun σ u=>Q (σ,τ) u) x
        · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
          cases s with
          | inl s=>change k+1≤0 at hh;omega
          | inr s=>
            have hi : ∀c:V.Slot,k+1≤V.splitIndex s c → c=s := by
              intro c hc
              exact Sum.inr.inj (h (Sum.inr c) hc)
            have hh' : k+1≤r.tree.splitIndex (r.embed s) r.mark:=hh
            dsimp only [MarkedPlacement.right]
            change (T.fork r.tree).expect w φ q
              (fun σ=>Q (σ.1,r.restrict σ.2) (r.spin σ.2)) x=
              (T.fork r.tree).expect w φ q (fun σ=>Q
                (σ.1,nativeReplaceAtSlot V s (r.restrict σ.2)
                  (r.spin σ.2))
                (V.atSlot (r.restrict σ.2) s)) x
            rw [expect_fork,expect_fork]
            congr 1
            funext τ
            exact ihV s (k+1) hi ho r hr hh' q (fun σ u=>Q (τ,σ) u) x

theorem native_target_singleton_whole_disorder_exchange
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (k : ℕ)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c → c=s)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (Q : T.Assignment→S→ℝ) (x : ι→ℝ) :
    p.tree.disorderExpect w φ v q (fun σ=>Q (p.restrict σ) (p.spin σ)) x=
      p.tree.disorderExpect w φ v q (fun σ=>Q
        (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) x := by
  rw [p.tree.disorderExpect_integral hw φ ho,p.tree.disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun y=>
    native_target_singleton_whole_exchange T s k h hw φ ho p hp hh _ Q (x+y)

end OAI.SKFluctuations.Hierarchy.ClockTree
