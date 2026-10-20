module

public import SKBarriers2.Corner.FrozenRowsNoise4

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

abbrev AffineRowParameter := ℝ × ((Vec3 →L[ℝ] Vec3) × (Vec3 × Vec3))
abbrev AffineRowParameters := Fin 12 → AffineRowParameter

def affineRowCoordinate (i : Fin 12) : AffineGaussianCoordinate AffineRowParameters Vec3 where
  logMass := (ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.proj i)
  mean := (ContinuousLinearMap.fst ℝ (Vec3 →L[ℝ] Vec3) _).comp
    ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.proj i))
  shift := (ContinuousLinearMap.fst ℝ Vec3 Vec3).comp
    ((ContinuousLinearMap.snd ℝ (Vec3 →L[ℝ] Vec3) _).comp
      ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.proj i)))
  noise := (ContinuousLinearMap.snd ℝ Vec3 Vec3).comp
    ((ContinuousLinearMap.snd ℝ (Vec3 →L[ℝ] Vec3) _).comp
      ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.proj i)))

def affineRowCoordinates : (n : ℕ) → n ≤ 12 → List
    (AffineGaussianCoordinate AffineRowParameters Vec3)
  | 0, _ => []
  | n + 1, hn => affineRowCoordinate ⟨n, by omega⟩ :: affineRowCoordinates n (by omega)

def completedRowParameters {ι : Type*} (l : List ι) (m : ι → ℝ) (v : ι → Vec3)
    (Q : QuadraticTerminal) : AffineRowParameters :=
  match l with
  | [] => 0
  | j :: l => fun i => if i.val = l.length then
      let A := riccatiRecursion (l.map (fun j => (m j, v j))) Q
      (Real.log (m j), (quadraticMeanLinear A (m j) (v j),
        (quadraticNoiseConstant A (m j) (v j),
          (Real.sqrt (A.precision (m j) (v j))⁻¹) • v j)))
    else completedRowParameters l m v Q i

theorem completedRowParameters_coordinates {ι : Type*} (l : List ι)
    (hl : l.length ≤ 12) (m : ι → ℝ) (v : ι → Vec3) (Q : QuadraticTerminal)
    (hm : ∀ j ∈ l, 0 < m j) (p : AffineRowParameters)
    (hp : ∀ i : Fin 12, i.val < l.length → p i = completedRowParameters l m v Q i) :
    CompletedSquareCoordinates p Q (affineRowCoordinates l.length hl)
      (l.map (fun j => (m j, v j))) := by
  induction l with
  | nil => trivial
  | cons j l ih =>
    simp only [List.length_cons] at hl hp
    have hlt : l.length ≤ 12 := by omega
    have hp' (i : Fin 12) (hi : i.val < l.length) :
        p i = completedRowParameters l m v Q i := by
      have H := hp i (Nat.lt_succ_of_lt hi)
      simpa only [completedRowParameters, ite_eq_right (by omega : i.val ≠ l.length)] using H
    have hhead := hp ⟨l.length, by omega⟩ (by simp)
    simp only [completedRowParameters, ite_true] at hhead
    refine ⟨ih hlt (fun i hi => hm i (List.mem_cons_of_mem _ hi)) hp', ?_, ?_, ?_, ?_⟩
    · change Real.exp ((p ⟨l.length, by omega⟩).1) = m j
      rw [hhead]
      exact Real.exp_log (hm j List.mem_cons_self)
    · change (p ⟨l.length, by omega⟩).2.1 = _
      rw [hhead]
    · change (p ⟨l.length, by omega⟩).2.2.1 = _
      rw [hhead]
    · change (p ⟨l.length, by omega⟩).2.2.2 = _
      rw [hhead]

theorem completedRowParameters_contDiffAt {P ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (l : List ι) (m : ι → P → ℝ) (v : ι → P → Vec3)
    (Q : P → QuadraticTerminal) {p : P}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hv : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun q => v j q i) p)
    (hQ : QuadraticFamilyContDiffAt Q p)
    (hA : RiccatiAdmissible (l.map (fun j => (m j p, v j p))) (Q p)) :
    ContDiffAt ℝ ∞
      (fun q => completedRowParameters l (fun j => m j q) (fun j => v j q) (Q q)) p := by
  induction l with
  | nil => exact contDiffAt_const
  | cons j l ih =>
    have hmt := fun i hi => hm i (List.mem_cons_of_mem _ hi)
    have hvt := fun i hi => hv i (List.mem_cons_of_mem _ hi)
    have ht := ih hmt hvt hA.1
    have hR := riccatiRecursion_coefficients_contDiffAt l m v Q hmt hvt hQ hA.1
    have hmj := hm j List.mem_cons_self
    have hvj := hv j List.mem_cons_self
    have hAlinear := hR.meanLinear hmj hvj hA.2.2
    have hb := contDiffAt_pi.mpr (hR.noiseConstant hmj hvj hA.2.2)
    have hn := contDiffAt_pi.mpr (hR.noiseDirection hmj hvj hA.2.2)
    apply contDiffAt_pi.mpr
    intro i
    by_cases hi : i.val = l.length
    · simp only [completedRowParameters, ite_eq_left hi]
      exact (hmj.log hA.2.1).prodMk (hAlinear.prodMk (hb.prodMk hn))
    · simp only [completedRowParameters, ite_eq_right hi]
      exact (contDiffAt_apply ℝ AffineRowParameter i _).comp p ht

end SKBarriers2.Corner
