module

public import ComparisonSignedCavityTransientForkCost
public import CavityPhysicalJetBounds
public import SKFluctuationsOAI.Probability.SKFluctuations.CavityGraphParity

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeSmallCutRowClock (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U V : ℕ) (l s t : ℝ) (b h K : ℕ → ℝ) : ℕ → FullCoordinate n → ℝ :=
  cutFullVariance n q V s t (relocatedClock U l b)
    (relocatedClock U l h) (relocatedClock U l K)

theorem nativeSmallCutRowClock_one (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U V : ℕ) (l t : ℝ) (b h K : ℕ → ℝ) :
    nativeSmallCutRowClock n q U V l 1 t b h K=cutFullVariance n q U l t b h K := by
  funext j
  simp only [nativeSmallCutRowClock,cutFullVariance,relocatedClock_one]

theorem nativeSmallCutRowClock_nonneg (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U V : ℕ) {l s t : ℝ} (hl : l∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1)
    (ht : t∈Icc (0:ℝ) 1) (b h K : ℕ → ℝ)
    (hq : ∀ j i,0 ≤ q j i) (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j)
    (hK : ∀ j,0 ≤ K j) (j : ℕ) (i : FullCoordinate n) :
    0 ≤ nativeSmallCutRowClock n q U V l s t b h K j i :=
  cutFullVariance_nonneg n q V hs ht hq (relocatedClock_nonneg U hl.1 hb)
    (relocatedClock_nonneg U hl.1 hh) (relocatedClock_nonneg U hl.1 hK) j i

theorem nativeSmallCutRowClock_monotone (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U V : ℕ) {l s t : ℝ} (hl : l∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1)
    (ht : t∈Icc (0:ℝ) 1) (b h K : ℕ → ℝ)
    (hq : ∀ i,Monotone (fun j => q j i)) (hb : ∀ j,0 ≤ b j)
    (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (i : FullCoordinate n) :
    Monotone (fun j => nativeSmallCutRowClock n q U V l s t b h K j i) :=
  cutFullVariance_monotone n q V hs ht hq (relocatedClock_nonneg U hl.1 hb)
    (relocatedClock_nonneg U hl.1 hh) (relocatedClock_nonneg U hl.1 hK)
    (relocatedClock_monotone U hl hbm hb) (relocatedClock_monotone U hl hhm hh)
    (relocatedClock_monotone U hl hKm hK) i

theorem native_cut_nonnegative_test_le_endpoint (n : ℕ)
    (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (hP : ∀ σ,0 ≤ P σ) (x : FullCoordinate n → ℝ)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ j<U,|K j|+|h j|+|b j| ≤ M)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K) P x ≤
      Real.exp (ClockTree.jetVariation T.leaves 1*M)*
        T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 t b h K) P x := by
  let F := fun s => cutLowJet n q U b h K T P x 0 s t
  let D := fun s => cutLowJet n q U b h K T P x 1 s t
  let C := ClockTree.jetVariation T.leaves 1*M
  have hC : 0 ≤ C := mul_nonneg (ClockTree.jetVariation_nonneg _ _) hM
  have hF (s : ℝ) : 0 ≤ F s := by
    rw [show F s=cutLowJet n q U b h K T P x 0 s t from rfl,
      cutLowJet_zero n q U b h K T ho P x]
    exact Finset.sum_nonneg (fun σ _ => mul_nonneg
      ((T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0
        (cutFullVariance n q U s t b h K) x).1 σ) (hP σ))
  have hD (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : |D s| ≤ C*F s := by
    rw [show D s=cutLowJet n q U b h K T P x 1 s t from rfl,
      cutLowJet_eq_profileJets n q U b h K T ho P x hq0 hq hb hh hK
        hbm hhm hKm 1 hs ht]
    have H := T.disorderProfileJets_relative_abs_le (fullWeight_pos n) (fullFeature n) ho
      (List.replicate 1 (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K)))
      (le_refl _) P hM (fun A hA j σ τ => by
        rw [(List.mem_replicate.mp hA).2]
        exact cutLSlope_coordinateProfile_abs_le n U b h K ht hM hbound j σ τ)
      0 (cutFullVariance n q U s t b h K) x
    have h_abs : (fun σ => |P σ|)=P := funext (fun σ => abs_of_nonneg (hP σ))
    rw [h_abs] at H
    simpa only [List.length_replicate,pow_one,F,C,
      cutLowJet_zero n q U b h K T ho P x,mul_assoc,mul_comm M,mul_left_comm M] using H
  have hcont : Continuous F := cutLowJet_continuous_l n q U b h K T P x 0 t
  have hd (s : ℝ) (hs : s∈Ioo (0:ℝ) 1) : HasDerivAt F (D s) s :=
    cutLowJet_hasDerivAt_l n q U hs ht b h K hq0 hq hb hh hK hbm hhm hKm T ho P x 0
  have hweighted : MonotoneOn (fun s => F s*Real.exp (C*s)) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1)
      (hcont.mul (by fun_prop)).continuousOn
      (f' := fun s => (D s+C*F s)*Real.exp (C*s))
    · intro s hs
      rw [interior_Icc] at hs
      have he := ((hasDerivAt_id s).const_mul C).exp
      convert ((hd s hs).mul he).hasDerivWithinAt using 1 <;> try rfl
      simp only [id_eq]
      ring
    · intro s hs
      rw [interior_Icc] at hs
      have H := neg_le_of_abs_le (hD s ⟨hs.1.le,hs.2.le⟩)
      exact mul_nonneg (by linarith) (Real.exp_nonneg _)
  have H := hweighted hl (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) hl.2
  have hexp : 1 ≤ Real.exp (C*l) := Real.one_le_exp (mul_nonneg hC hl.1)
  have H1 := mul_le_mul_of_nonneg_left hexp (hF l)
  have H2 : F l ≤ F 1*Real.exp C := by
    have HH : F l*1 ≤ F 1*Real.exp C := H1.trans (by simpa only [mul_one] using H)
    simpa only [mul_one] using HH
  simpa only [F,C,cutLowJet_zero n q U b h K T ho P x,mul_comm] using H2

theorem native_small_cut_graph_restore (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U V : ℕ) (hV0 : 0<V) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hV : V≤as.length) (s : T.Slot) (es : List T.Slot)
    (hes : Odd (blockDegree T V s es)) (P : T.cavityLeft.Assignment → ℝ)
    (x : FullCoordinate n → ℝ) (hs : ∀ i,x (.inl (.inr i))=0) (hr : ∀ i,x (.inr i)=0)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ => P (T.cavityAssignment σ).1*siteMonomial T σ es) x =
      ∫ r in (0:ℝ)..1,cutLowJet n q V (relocatedClock U l b) (relocatedClock U l h)
        (relocatedClock U l K) T (fun σ => P (T.cavityAssignment σ).1*siteMonomial T σ es)
        x 1 r t := by
  let b' := relocatedClock U l b
  let h' := relocatedClock U l h
  let K' := relocatedClock U l K
  let J := fun σ => P (T.cavityAssignment σ).1*siteMonomial T σ es
  have hb' := relocatedClock_nonneg U hl.1 hb
  have hh' := relocatedClock_nonneg U hl.1 hh
  have hK' := relocatedClock_nonneg U hl.1 hK
  have hbm' := relocatedClock_monotone U hl hbm hb
  have hhm' := relocatedClock_monotone U hl hhm hh
  have hKm' := relocatedClock_monotone U hl hKm hK
  have H := first_jet_remainder (fun r => cutLowJet n q V b' h' K' T J x 0 r t)
    (fun r => cutLowJet n q V b' h' K' T J x 1 r t)
    (cutLowJet_continuous_l n q V b' h' K' T J x 0 t)
    (cutLowJet_continuous_l n q V b' h' K' T J x 1 t)
    (fun r hr => cutLowJet_hasDerivAt_l n q V hr ht b' h' K' hq0 hq hb' hh' hK'
      hbm' hhm' hKm' T ho J x 0)
  rw [cutLowJet_zero n q V b' h' K' T ho J x,
    cutLowJet_zero n q V b' h' K' T ho J x,
    cutDisorderExpect_graph_odd n q V hV0 t b' h' K' T hV s es hes P x hs hr,
    zero_add] at H
  have hclock : cutFullVariance n q V 1 t b' h' K' = cutFullVariance n q U l t b h K :=
    nativeSmallCutRowClock_one n q U V l t b h K
  rw [hclock] at H
  exact H

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

theorem native_same_cut_membership {as : List PositiveMass} (T : ClockTree S as)
    (V : ℕ) (s a b : T.Slot) (hab : V ≤ T.splitIndex a b) :
    (V ≤ T.splitIndex s a) ↔ (V ≤ T.splitIndex s b) := by
  induction T generalizing V with
  | leaf => rfl
  | step m T ih =>
    cases V with
    | zero => simp
    | succ V =>
      simp only [splitIndex,Nat.add_comm 1,Nat.succ_le_succ_iff] at hab ⊢
      exact ih V s a b hab
  | fork T W ihT ihW =>
    cases V with
    | zero => simp
    | succ V =>
      cases a <;> cases b <;> cases s <;>
        simp only [splitIndex,Sum.elim_inl,Sum.elim_inr] at hab ⊢
      all_goals first | exact ihT (V+1) _ _ _ hab | exact ihW (V+1) _ _ _ hab | omega

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_inside_edge_graph_degree_even {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (V : ℕ) (s : T.Slot) (edges : List (T.Slot×T.Slot))
    (hedges : ∀ e∈edges,V ≤ T.splitIndex e.1 e.2) :
    Even (blockDegree T V s (edges.flatMap (fun e => [e.1,e.2]))) := by
  induction edges with
  | nil => exact ⟨0,rfl⟩
  | cons e edges ih =>
    simp only [List.flatMap_cons,blockDegree_append]
    exact (blockDegree_pair_even T V s e.1 e.2
      (T.native_same_cut_membership V s e.1 e.2 (hedges e List.mem_cons_self))).add
      (ih (fun d hd => hedges d (List.mem_cons_of_mem e hd)))

theorem native_old_initial_pair_degree_odd {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (V : ℕ) (hV : V≤as.length) (a b : T.Slot)
    (hab : T.splitIndex a b<V) (edges : List (T.Slot×T.Slot))
    (hedges : ∀ e∈edges,V ≤ T.splitIndex e.1 e.2) :
    Odd (blockDegree T V a ([a,b]++edges.flatMap (fun e => [e.1,e.2]))) := by
  rw [blockDegree_append]
  have he := native_inside_edge_graph_degree_even T V a edges hedges
  have hp : blockDegree T V a [a,b]=1 := by
    simp only [blockDegree,T.splitIndex_self,if_pos hV,if_neg (not_le.mpr hab)]
  rw [hp]
  exact odd_one.add_even he

theorem native_small_cut_nonnegative_test_le_original (n : ℕ)
    (q : ℕ → RestCoordinate n → ℝ) (U V : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (hP : ∀ σ,0 ≤ P σ) (x : FullCoordinate n → ℝ)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ j<V,|K j|+|h j|+|b j| ≤ M)
    {l s t : ℝ} (hl : l∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1)
    (ht : t∈Icc (0:ℝ) 1) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (nativeSmallCutRowClock n q U V l s t b h K) P x ≤
      Real.exp (ClockTree.jetVariation T.leaves 1*M)*
        T.disorderExpect (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U l t b h K) P x := by
  have hbound' (j : ℕ) (hj : j<V) :
      |relocatedClock U l K j|+|relocatedClock U l h j|+|relocatedClock U l b j| ≤ M := by
    have hK' := relocatedClock_nonneg U hl.1 hK j
    have hh' := relocatedClock_nonneg U hl.1 hh j
    have hb' := relocatedClock_nonneg U hl.1 hb j
    rw [abs_of_nonneg hK',abs_of_nonneg hh',abs_of_nonneg hb']
    apply (add_le_add (add_le_add (relocatedClock_le U hl.2 hK j)
      (relocatedClock_le U hl.2 hh j)) (relocatedClock_le U hl.2 hb j)).trans
    simpa only [abs_of_nonneg (hK j),abs_of_nonneg (hh j),abs_of_nonneg (hb j)] using hbound j hj
  have H := native_cut_nonnegative_test_le_endpoint n q V (relocatedClock U l b)
    (relocatedClock U l h) (relocatedClock U l K) T ho P hP x hq0 hq
    (relocatedClock_nonneg U hl.1 hb) (relocatedClock_nonneg U hl.1 hh)
    (relocatedClock_nonneg U hl.1 hK) (relocatedClock_monotone U hl hbm hb)
    (relocatedClock_monotone U hl hhm hh) (relocatedClock_monotone U hl hKm hK)
    hM hbound' hs ht
  change T.disorderExpect _ _ _ (nativeSmallCutRowClock n q U V l s t b h K) P x ≤
    _*T.disorderExpect _ _ _ (nativeSmallCutRowClock n q U V l 1 t b h K) P x at H
  rw [nativeSmallCutRowClock_one] at H
  exact H

end OAI.SKFluctuations.Cavity
