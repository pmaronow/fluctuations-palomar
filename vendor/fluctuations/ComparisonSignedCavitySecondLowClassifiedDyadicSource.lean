module

public import ComparisonSignedCavitySecondLowInheritedClassifiedIndexedLayerRate
public import ComparisonSignedCavitySecondLowInheritedClassifiedCovarianceRate
public import ComparisonSignedCavityActualDyadicShiftedReadout
public import ComparisonSignedCavitySecondLowExteriorIndexedTelescope

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {pre mid tail : List PositiveMass}
variable {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {f c z : T.Slot}
variable {v₀ : RestCoordinate n→ℝ} {q₀ : ℕ→RestCoordinate n→ℝ} {x₀ : RestCoordinate n→ℝ}

def nativeSecondLowClassifiedCompleteCFold
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v₀ q₀ x₀)
    (U : ℕ) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let Q:=fun sf sc sz=>restLowKernel n U b h (T.splitIndex f c) sf sc*
    restLowKernel n U b h (T.splitIndex c z) sc sz-
    (if T.splitIndex f c<U then K (T.splitIndex f c) else 0)*
      (if T.splitIndex c z<U then K (T.splitIndex c z) else 0)
  ∫r,nativeExteriorCompleteCFold E.source.Ei E.source.Es E.source.D (restWeight n) (restFeature n)
    E.source.target (U-(pre.length+mid.length))
    (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))
    (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
    (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
    (fun η ζ δ=>P (E.source.read η ζ δ)) E.outsideF E.outsideZ Q
    (exteriorForestIRoot r,exteriorForestStarRoot r)
    ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0

theorem native_second_low_classified_complete_c_fold_eq_dyadic_layers_sub_covariance
    (E : NativeSecondLowClassifiedRetainedWholeCSource n pre mid tail T f c z v₀ q₀ x₀)
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ)
    (hstar : pre.length+mid.length < U) (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (a : ℝ) (ha : 0 < a) (H : NativeDyadicRetainedReadout a ha (pre++(mid++tail)) U) :
    nativeSecondLowClassifiedCompleteCFold E U q b h K P=
      (∑j∈Finset.range (nativeDyadicCutDepth a),nativeSecondLowClassifiedIndexedLayer E ho U
        (nativeDyadicSourceRetainedIndex a ha (pre++(mid++tail)) U j)
        (nativeDyadicMassCut a ha j).val (nativeDyadicMassCut a ha (j+1)).val q b h K P)-
        (a/2)*nativeSecondLowClassifiedRetainedCovariance E U U q b h K P := by
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let cum:=cumulativeIncrements (q 0) (fun k=>q (k+1))
  let aStar:=partitionPoint 0 as star
  let Q:=fun sf sc sz=>restLowKernel n U b h (T.splitIndex f c) sf sc*
    restLowKernel n U b h (T.splitIndex c z) sc sz-
    (if T.splitIndex f c<U then K (T.splitIndex f c) else 0)*
      (if T.splitIndex c z<U then K (T.splitIndex c z) else 0)
  have HD:=H.shifted_two_level ho pre mid tail rfl hstar hU cum
  have hblock : ∀d:E.source.D.Slot,U-star ≤ E.source.D.splitIndex E.source.target d := by
    intro d
    have Hhigh:=E.source.occupied_high hstar hU hT.cavityLeft d
    have HS:=E.source.embed_splits E.source.target d
    rw [E.source.embed_target] at HS
    dsimp only [star]
    omega
  have HoTail : MassOrdered aStar tail := by
    have HO : MassOrdered 0 ((pre++mid)++tail):=by simpa only [List.append_assoc] using ho
    have HH:=HO.suffix_end
    have Hp:=native_partitionPoint_append_shift 0 (pre++mid) tail 0
    simp only [Nat.add_zero,partitionPoint,partitionValues_zero,id_eq,List.length_append,List.append_assoc] at Hp
    change aStar=partitionEnd 0 (pre++mid) at Hp
    rw [Hp]
    exact HH
  let :=nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho 0 q 0
  have HI:=native_exterior_incoming_complete_c_fold_eq_grouped_indexed_layers_sub_covariance
    E.source.Ei E.source.Es E.source.D E.source.target (restWeight_pos n) (restFeature n)
    (U-star) ho.suffix_end HoTail hblock
    (fun j=>cum (pre.length+j)) (fun j=>cum (pre.length+(mid.length+j)))
    (fun η ζ δ=>P (E.source.read η ζ δ)) E.outsideF E.outsideZ Q
    (fun j=>(nativeDyadicMassCut a ha j).val) (nativeDyadicCutDepth a)
    (nativeDyadicShiftedRetainedIndex a ha as U star)
    HD.first_virtual HD.last_mass HD.first_index
    (fun j hj=>HD.index_le j (Nat.le_of_lt hj))
    (by intro j hj hdepth;simpa only [Nat.add_assoc] using HD.prefix_mass j hj (Nat.le_of_lt hdepth))
    (by intro j hj hdepth;simpa only [Nat.add_assoc] using HD.source_prefix_mass j hj (Nat.le_of_lt hdepth))
    (fun j _=>HD.cut_monotone (Nat.le_succ j))
    (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
    (fun r=>(exteriorForestIRoot r,exteriorForestStarRoot r))
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  rw [HD.source_mass] at HI
  rw [native_second_low_classified_covariance_eq_literal_target_clone E ho U U]
  exact HI

end OAI.SKFluctuations.Cavity
