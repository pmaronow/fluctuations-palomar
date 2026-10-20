module

public import ComparisonSignedCavityActualSharpSourceCutReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum Set Filter
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 10000000

def nativeDyadicMassCut (a : ℝ) (ha : 0 < a) (j : ℕ) : PositiveMass :=
  ⟨min ((2:ℝ)^j*(a/2)) 1,lt_min (by positivity) zero_lt_one⟩

theorem nativeDyadicMassCut_zero {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (nativeDyadicMassCut a ha 0).val=a/2 := by
  simp only [nativeDyadicMassCut,pow_zero,one_mul]
  exact min_eq_left (by linarith)

theorem nativeDyadicMassCut_one {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (nativeDyadicMassCut a ha 1).val=a := by
  simp only [nativeDyadicMassCut,pow_one]
  rw [show 2*(a/2)=a by ring,min_eq_left ha1]

theorem nativeDyadicMassCut_le_one {a : ℝ} (ha : 0 < a) (j : ℕ) :
    (nativeDyadicMassCut a ha j).val ≤ 1 := min_le_right _ _

theorem nativeDyadicMassCut_monotone {a : ℝ} (ha : 0 < a) :
    Monotone (fun j=>(nativeDyadicMassCut a ha j).val) := by
  intro i j hij
  exact min_le_min (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) (by positivity)) le_rfl

theorem nativeDyadicMassCut_comparable {a : ℝ} (ha : 0 < a) (j : ℕ) :
    (nativeDyadicMassCut a ha (j+1)).val ≤ 2*(nativeDyadicMassCut a ha j).val := by
  dsimp only [nativeDyadicMassCut]
  by_cases H : (2:ℝ)^j*(a/2) ≤ 1
  · rw [min_eq_left H]
    calc
      _ ≤ (2:ℝ)^(j+1)*(a/2):=min_le_left _ _
      _=2*((2:ℝ)^j*(a/2)):=by rw [pow_succ];ring
  · rw [min_eq_right (le_of_not_ge H)]
    exact (min_le_right _ _).trans (by norm_num)

theorem nativeDyadicMassCut_terminal {a : ℝ} (ha : 0 < a) (q : ℕ)
    (hreach : 1 ≤ (2:ℝ)^q*(a/2)) :
    (nativeDyadicMassCut a ha q).val=1 := min_eq_right hreach

def nativeDyadicMassCutNodes (a : ℝ) (ha : 0 < a) (q : ℕ) : List PositiveMass :=
  List.ofFn (fun j : Fin (q+1)=>nativeDyadicMassCut a ha j.val)

theorem nativeDyadicMassCutNodes_mem {a : ℝ} (ha : 0 < a) (q j : ℕ) (hj : j ≤ q) :
    nativeDyadicMassCut a ha j∈nativeDyadicMassCutNodes a ha q := by
  exact List.mem_ofFn.mpr ⟨⟨j,by omega⟩,rfl⟩

theorem nativeDyadicMassCutNodes_le_one {a : ℝ} (ha : 0 < a) (q : ℕ) :
    ∀u∈nativeDyadicMassCutNodes a ha q,u.val ≤ 1 := by
  intro u hu
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hu
  exact nativeDyadicMassCut_le_one ha j.val

theorem nativeDyadicMassCutNodes_length {a : ℝ} (ha : 0 < a) (q : ℕ) :
    (nativeDyadicMassCutNodes a ha q).length=q+1 := by simp [nativeDyadicMassCutNodes]

theorem nativeDyadicMassCutNodes_exists_common_net {a : ℝ} (ha : 0 < a) (q L : ℕ)
    (extra : List PositiveMass) (hextra : ∀u∈extra,u.val ≤ 1) :
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧
      (∀j ≤ q,nativeDyadicMassCut a ha j∈us) ∧
      (∀u∈extra,u∈us) ∧ (∀u∈uniformMasses L,u∈us) := by
  let us:=nativeDyadicMassCutNodes a ha q++extra++uniformMasses L
  refine ⟨us,?_,?_,?_,?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with hu|hu
    · rcases List.mem_append.mp hu with hu|hu
      · exact nativeDyadicMassCutNodes_le_one ha q u hu
      · exact hextra u hu
    · exact (uniformMasses_ordered L).members_le_one u hu
  · intro j hj
    exact List.mem_append_left _ (List.mem_append_left _ (nativeDyadicMassCutNodes_mem ha q j hj))
  · intro u hu
    exact List.mem_append_left _ (List.mem_append_right _ hu)
  · intro u hu
    exact List.mem_append_right _ hu

end OAI.SKFluctuations.LaplaceWindowFormalization
