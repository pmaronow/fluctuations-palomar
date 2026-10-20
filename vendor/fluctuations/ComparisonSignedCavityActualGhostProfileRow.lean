module

public import ComparisonSignedCavityActualGhostRowMarginal

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

def nativeMarkedProfileRow (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (Ks : List (ℕ→S→S→ℝ)) (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*disorderProfileJets w φ v q x Ks p.tree
    (fun σ=>P (p.restrict σ)*B (p.spin σ)))).sum

theorem nativeMarkedProfileRow_hasDerivAt
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q D : ℕ→ι→ℝ) {l r : ℝ}
    (hq : ∀s∈Ioo l r,∀i,Monotone (fun j=>q j i+s*D j i))
    (hq0 : ∀s∈Ioo l r,∀i,v i≤q 0 i+s*D 0 i)
    (Ks : List (ℕ→S→S→ℝ)) (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ)
    {t : ℝ} (ht : t∈Ioo l r) :
    HasDerivAt (fun s=>nativeMarkedProfileRow w φ T v (fun j i=>q j i+s*D j i) Ks P B x)
      (nativeMarkedProfileRow w φ T v (fun j i=>q j i+t*D j i)
        (Ks++[ReplicaTree.coordinateProfile φ D]) P B x) t := by
  exact hasDerivAt_listSum (T.markedAttach 0) _ _ (fun p hp=>
    (hasDerivAt_finiteProfileJets hw φ ho v q D hq hq0 Ks p.tree
      (fun σ=>P (p.restrict σ)*B (p.spin σ)) x ht).const_mul p.coeff)

theorem native_marked_profile_row_marginal_strict
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (v : ι→ℝ) (Ds : List (ℕ→ι→ℝ)) {B : ℝ} (hB : 0≤B)
    (hDs : ∀D∈Ds,∀j i,|D j i|≤B)
    (P : T.Assignment→ℝ) (u x : ι→ℝ)
    (q : ℕ→ι→ℝ) {epsilon : ℝ} (he : 0<epsilon)
    (hq : strictCumulativeClock v q epsilon) :
    nativeMarkedProfileRow w φ p.tree v q (Ds.map (ReplicaTree.coordinateProfile φ))
      (fun σ=>P (p.restrict σ)) (fun σ=>φ σ u) x=
    nativeMarkedProfileRow w φ T v q (Ds.map (ReplicaTree.coordinateProfile φ))
      P (fun σ=>φ σ u) x := by
  induction Ds using List.reverseRecOn generalizing q epsilon with
  | nil=>exact native_marked_disorder_row_marginal hw φ T ho p hp v q P u x
  | append_singleton Ds D ih=>
    have hD : ∀j i,|D j i|≤B:=hDs D (by simp)
    have hOld : ∀E∈Ds,∀j i,|E j i|≤B:=fun E hE=>hDs E (by simp [hE])
    let radius:=epsilon/(2*(2*B+1))
    have hrpos : 0<radius:=by dsimp [radius];positivity
    have hpert (s : ℝ) (hs : s∈Ioo (-radius) radius) :
        strictCumulativeClock v (fun j i=>q j i+s*D j i) (epsilon/2) := by
      apply strictCumulativeClock_perturb he hB hq hD
      have hsabs : |s|≤radius:=(abs_le).2 ⟨hs.1.le,hs.2.le⟩
      have HH:=mul_le_mul_of_nonneg_right hsabs (by positivity : 0≤2*B+1)
      have hrad : radius*(2*B+1)=epsilon/2:=by dsimp [radius];field_simp
      rwa [hrad] at HH
    have hmono : ∀s∈Ioo (-radius) radius,∀i,Monotone (fun j=>q j i+s*D j i) := by
      intro s hs i
      exact (hpert s hs).monotone (by positivity) i
    have hroot : ∀s∈Ioo (-radius) radius,∀i,v i≤q 0 i+s*D 0 i := by
      intro s hs i
      have H:=(hpert s hs).1 i
      linarith
    have hzero : (0:ℝ)∈Ioo (-radius) radius:=by constructor <;> linarith
    have HL:=nativeMarkedProfileRow_hasDerivAt hw φ p.tree ho v q D hmono hroot
      (Ds.map (ReplicaTree.coordinateProfile φ)) (fun σ=>P (p.restrict σ)) (fun σ=>φ σ u) x hzero
    have HR:=nativeMarkedProfileRow_hasDerivAt hw φ T ho v q D hmono hroot
      (Ds.map (ReplicaTree.coordinateProfile φ)) P (fun σ=>φ σ u) x hzero
    have HF : (fun s=>nativeMarkedProfileRow w φ p.tree v (fun j i=>q j i+s*D j i)
        (Ds.map (ReplicaTree.coordinateProfile φ)) (fun σ=>P (p.restrict σ)) (fun σ=>φ σ u) x)=ᶠ[𝓝 (0:ℝ)]
      (fun s=>nativeMarkedProfileRow w φ T v (fun j i=>q j i+s*D j i)
        (Ds.map (ReplicaTree.coordinateProfile φ)) P (fun σ=>φ σ u) x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      exact ih hOld _ (by positivity) (hpert s hs)
    have H:=HF.deriv_eq
    rw [HL.deriv,HR.deriv] at H
    simpa only [List.map_append,List.map_singleton,zero_mul,add_zero] using H

theorem nativeMarkedProfileRow_continuous
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℝ→ℕ→ι→ℝ) (hq : ∀j,Continuous (fun t=>q t j))
    (Ks : List (ℕ→S→S→ℝ)) (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ) :
    Continuous (fun t=>nativeMarkedProfileRow w φ T v (q t) Ks P B x) := by
  apply continuous_listSum
  intro p hp
  exact (disorderProfileJets_continuous hw φ ho v q hq (fun _=>x) continuous_const Ks p.tree
    (fun σ=>P (p.restrict σ)*B (p.spin σ))).const_mul p.coeff

theorem native_marked_profile_row_marginal
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i≤q 0 i) (Ds : List (ℕ→ι→ℝ))
    {B : ℝ} (hB : 0≤B) (hDs : ∀D∈Ds,∀j i,|D j i|≤B)
    (P : T.Assignment→ℝ) (u x : ι→ℝ) :
    nativeMarkedProfileRow w φ p.tree v q (Ds.map (ReplicaTree.coordinateProfile φ))
      (fun σ=>P (p.restrict σ)) (fun σ=>φ σ u) x=
    nativeMarkedProfileRow w φ T v q (Ds.map (ReplicaTree.coordinateProfile φ))
      P (fun σ=>φ σ u) x := by
  let qr:=fun e : ℝ=>fun j i=>q j i+e*(j+1:ℕ)
  have HE : EqOn
      (fun e=>nativeMarkedProfileRow w φ p.tree v (qr e) (Ds.map (ReplicaTree.coordinateProfile φ))
        (fun σ=>P (p.restrict σ)) (fun σ=>φ σ u) x)
      (fun e=>nativeMarkedProfileRow w φ T v (qr e) (Ds.map (ReplicaTree.coordinateProfile φ))
        P (fun σ=>φ σ u) x) (Ioi (0:ℝ)) := by
    intro e he
    exact native_marked_profile_row_marginal_strict hw φ T ho p hp v Ds hB hDs P u x
      (qr e) he (strictCumulativeClock_regularize hq hq0 he.le)
  have hc (j : ℕ) : Continuous (fun e=>qr e j):=by dsimp [qr];fun_prop
  have HL:=nativeMarkedProfileRow_continuous hw φ p.tree ho v qr hc
    (Ds.map (ReplicaTree.coordinateProfile φ)) (fun σ=>P (p.restrict σ)) (fun σ=>φ σ u) x
  have HR:=nativeMarkedProfileRow_continuous hw φ T ho v qr hc
    (Ds.map (ReplicaTree.coordinateProfile φ)) P (fun σ=>φ σ u) x
  have h0 : (0:ℝ)∈closure (Ioi (0:ℝ)):=by
    simpa only [closure_Ioi,mem_Ici] using (le_rfl : (0:ℝ)≤0)
  have H:=HE.closure HL HR h0
  simpa only [qr,zero_mul,add_zero] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
