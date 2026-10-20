module

public import ComparisonSignedCavityInitialInsertionWordAtom
public import ComparisonSignedCavityInitialTransientLowSourceLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 28000000

 theorem native_initial_LOW_jet_eq_terminal_word_sum
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (i star U k : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hq0 : ∀j x,0≤q j x) (hq : ∀x,Monotone (fun j=>q j x))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (P : T.Assignment→ℝ) (x : FullCoordinate n→ℝ)
    {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    nativeTransientLowErrorPartJet n q i star U b h K T P x .initial k l t=
      ((nativeInitialInsertionWords T (k+1)).map fun g=>g.coefficient*
        g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
          (g.test (nativeInitialTerminalLowDirections n U i k b h K t) P) x).sum := by
  let law:=cutFullVariance n q U l t b h K
  let A:=nativeTransientLowErrorPartDirection n U i star b h K .initial
  let Ds:=List.replicate k (cutLSlope n U t b h K)++[A]
  have Hlaw x : Monotone (fun j=>law j x):=cutFullVariance_monotone n q U hl ht hq hb hh hK hbm hhm hKm x
  have Hzero x : (0:ℝ)≤law 0 x:=cutFullVariance_nonneg n q U hl ht hq0 hb hh hK 0 x
  have Hoff:=native_profileJets_allOffDiagonal_without_budget (fullWeight_pos n) (fullFeature n)
    (fun z=>(fullAmplitude n z)^2) (by
      intro σ z
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ z)
    T ho 0 law Hlaw Hzero Ds P x
  unfold nativeTransientLowErrorPartJet
  rw [←native_transient_low_part_direction_profile]
  simp only [Ds,List.map_append,List.map_replicate,List.map_cons,List.map_nil] at Hoff
  rw [Hoff]
  have Hmask : ReplicaTree.coordinateProfile (fullFeature n) A=
      (fun j σ τ=>if j=i then ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) j σ τ else 0):=
    native_transient_low_part_direction_profile n U i star b h K .initial
  rw [Hmask]
  have HDlist : List.ofFn (nativeInitialTerminalLowDirections n U i k b h K t)=
      List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))++
        [fun j σ τ=>if j=i then ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) j σ τ else 0]:=by
    rw [List.ofFn_succ']
    simp only [nativeInitialTerminalLowDirections,Fin.lastCases_castSucc,Fin.lastCases_last,List.ofFn_const,
      List.concat_eq_append]
  rw [←HDlist,native_initial_insertion_word_exact_ofFn]

end OAI.SKFluctuations.Cavity
