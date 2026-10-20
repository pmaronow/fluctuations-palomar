module

public import ComparisonSignedCavityActualFullMarkedExchange
public import ComparisonSignedCavityActualFiniteProfileMarginal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem native_target_singleton_whole_profile_exchange_strict
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (k : ℕ)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (v : ι→ℝ) (Ds : List (ℕ→ι→ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hDs : ∀D∈Ds,∀j i,|D j i| ≤ B) (Q : T.Assignment→S→ℝ) (x : ι→ℝ)
    (q : ℕ→ι→ℝ) {epsilon : ℝ} (he : 0 < epsilon)
    (hq : strictCumulativeClock v q epsilon) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ))=
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) := by
  induction Ds using List.reverseRecOn generalizing q epsilon with
  | nil=>exact native_target_singleton_whole_disorder_exchange T s k h hw φ ho p hp hh v q Q x
  | append_singleton Ds D ih=>
    have hD : ∀j i,|D j i| ≤ B:=hDs D (by simp)
    have hOld : ∀E∈Ds,∀j i,|E j i| ≤ B:=fun E hE=>hDs E (by simp [hE])
    let radius:=epsilon/(2*(2*B+1))
    have hrpos : 0 < radius:=by dsimp [radius];positivity
    have hpert (t : ℝ) (ht : t∈Ioo (-radius) radius) :
        strictCumulativeClock v (fun j i=>q j i+t*D j i) (epsilon/2) := by
      apply strictCumulativeClock_perturb he hB hq hD
      have htabs : |t| ≤ radius:=(abs_le).2 ⟨ht.1.le,ht.2.le⟩
      have HH:=mul_le_mul_of_nonneg_right htabs (by positivity : 0 ≤ 2*B+1)
      have hrad : radius*(2*B+1)=epsilon/2:=by dsimp [radius];field_simp
      rwa [hrad] at HH
    have hmono : ∀t∈Ioo (-radius) radius,∀i,Monotone (fun j=>q j i+t*D j i) := by
      intro t ht i
      exact (hpert t ht).monotone (by positivity) i
    have hroot : ∀t∈Ioo (-radius) radius,∀i,v i ≤ q 0 i+t*D 0 i := by
      intro t ht i
      have H:=(hpert t ht).1 i
      linarith
    have hzero : (0:ℝ)∈Ioo (-radius) radius:=by constructor <;> linarith
    have HL:=hasDerivAt_finiteProfileJets hw φ ho v q D hmono hroot
      (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree (fun σ=>Q (p.restrict σ) (p.spin σ)) x hzero
    have HR:=hasDerivAt_finiteProfileJets hw φ ho v q D hmono hroot
      (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) x hzero
    have HF : (fun t=>disorderProfileJets w φ v (fun j i=>q j i+t*D j i) x
        (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree (fun σ=>Q (p.restrict σ) (p.spin σ)))=ᶠ[𝓝 (0:ℝ)]
      (fun t=>disorderProfileJets w φ v (fun j i=>q j i+t*D j i) x
        (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
        (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
          (T.atSlot (p.restrict σ) s))) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with t ht
      exact ih hOld _ (by positivity) (hpert t ht)
    have H:=HF.deriv_eq
    rw [HL.deriv,HR.deriv] at H
    simpa only [List.map_append,List.map_singleton,zero_mul,add_zero] using H

theorem native_target_singleton_whole_profile_exchange_bounded
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (k : ℕ)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (Ds : List (ℕ→ι→ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hDs : ∀D∈Ds,∀j i,|D j i| ≤ B) (Q : T.Assignment→S→ℝ) (x : ι→ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ))=
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) := by
  let qr:=fun e : ℝ=>fun j i=>q j i+e*(j+1:ℕ)
  have HE : EqOn
      (fun e=>disorderProfileJets w φ v (qr e) x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
        (fun σ=>Q (p.restrict σ) (p.spin σ)))
      (fun e=>disorderProfileJets w φ v (qr e) x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
        (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
          (T.atSlot (p.restrict σ) s))) (Ioi (0:ℝ)) := by
    intro e he
    exact native_target_singleton_whole_profile_exchange_strict T s k h hw φ ho p hp hh
      v Ds hB hDs Q x (qr e) he (strictCumulativeClock_regularize hq hq0 he.le)
  have hc (j : ℕ) : Continuous (fun e=>qr e j):=by dsimp [qr];fun_prop
  have HL:=disorderProfileJets_continuous hw φ ho v qr hc (fun _=>x) continuous_const
    (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree (fun σ=>Q (p.restrict σ) (p.spin σ))
  have HR:=disorderProfileJets_continuous hw φ ho v qr hc (fun _=>x) continuous_const
    (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
    (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
      (T.atSlot (p.restrict σ) s))
  have h0 : (0:ℝ)∈closure (Ioi (0:ℝ)):=by
    simpa only [closure_Ioi,mem_Ici] using (le_rfl : (0:ℝ) ≤ 0)
  have H:=HE.closure HL HR h0
  simpa only [qr,zero_mul,add_zero] using H

omit [Nonempty ι] in
theorem exists_profile_directions_finite_bound (d : ℕ) (Ds : List (ℕ→ι→ℝ)) :
    ∃B : ℝ,0 ≤ B ∧ ∀A∈Ds,∀j,j ≤ d→∀i,|A j i| ≤ B := by
  induction Ds with
  | nil=>exact ⟨0,le_rfl,by simp⟩
  | cons D Ds ih=>
    obtain ⟨B,hB,hDs⟩:=ih
    obtain ⟨C,hC,hD⟩:=exists_single_direction_finite_bound d D
    refine ⟨B+C,add_nonneg hB hC,?_⟩
    intro A hA j hj i
    rcases List.mem_cons.mp hA with rfl|hA
    · exact (hD A (by simp) j hj i).trans (le_add_of_nonneg_left hB)
    · exact (hDs A hA j hj i).trans (le_add_of_nonneg_right hC)

theorem native_target_singleton_whole_profile_exchange
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (k : ℕ)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (Ds : List (ℕ→ι→ℝ))
    (Q : T.Assignment→S→ℝ) (x : ι→ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ))=
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) := by
  obtain ⟨B,hB,hDs⟩:=exists_profile_directions_finite_bound as.length Ds
  rw [disorderProfileJets_eq_clipDirections w φ v q x Ds p.tree _,
    disorderProfileJets_eq_clipDirections w φ v q x Ds p.tree _]
  exact native_target_singleton_whole_profile_exchange_bounded T s k h hw φ ho p hp hh
    v q hq hq0 (Ds.map (clipDirection as.length)) hB
    (clipDirection_bounded as.length Ds hB hDs) Q x

end OAI.SKFluctuations.Hierarchy.ClockTree
