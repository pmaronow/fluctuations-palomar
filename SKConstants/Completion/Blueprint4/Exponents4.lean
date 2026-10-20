module

public import SKConstants.Completion.Blueprint.Exponents
public import SKConstants.OptimizedRate

@[expose] public section
noncomputable section
open Filter
open scoped Topology

namespace SKConstants.Blueprint4
open SKConstants.Blueprint

def CoarseExponents4 (p : Parameters) : Prop :=
  0 < p.b ∧ p.b < p.f ∧ p.b / 4 < p.a ∧ 0 < p.kb ∧ p.kb < p.z ∧ p.z < p.a ∧
    p.z < p.b / 2 ∧ p.z < 2 * p.gamma ∧ 2 * p.gamma < p.sb ∧ p.gamma + p.b / 4 < p.sb ∧
    p.b / 2 < p.sb ∧ 2 * p.z - p.a < p.sb ∧ 2 * p.z - 2 * p.gamma < p.sb ∧
    2 * p.z - p.b < p.sb ∧ p.a < 1 - p.sb

def CoarseCommon (p : Parameters) : Prop :=
  0 < p.b ∧ p.b < p.f ∧ 0 < p.z ∧ 0 < p.gamma ∧ 0 < p.kb ∧ p.kb < p.z ∧
    p.kb < 2 * p.gamma ∧ p.kb < p.a ∧ p.kb < p.b ∧ 2 * p.gamma < p.sb ∧
    p.b / 2 < p.sb ∧ p.a < 1 - p.sb

theorem common_of_coarseExponents {p : Parameters} (h : CoarseExponents p) : CoarseCommon p := by
  obtain ⟨hb0, hbf, hz0, hγ0, hkb0, hkbz, hkbγ, hkba, hkbb, hzsb, hγsb, hasb⟩ := h
  exact ⟨hb0, hbf, hz0, hγ0, hkb0, hkbz, hkbγ, hkba, hkbb, by linarith, by linarith, hasb⟩

theorem common_of_coarseExponents4 {p : Parameters} (h : CoarseExponents4 p) : CoarseCommon p := by
  obtain ⟨hb0, hbf, hba, hkb0, hkbz, hza, hzb, hzγ, hγsb, -, hbsb, -, -, -, hasb⟩ := h
  exact ⟨hb0, hbf, by linarith, by linarith, hkb0, hkbz, by linarith, by linarith,
    by linarith, hγsb, hbsb, hasb⟩

def Admissible4 (c sseq : ℝ) (p : Parameters) : Prop :=
  FineExponents p ∧ CoarseExponents4 p ∧ BoundaryExponents p ∧ SequenceExponents p sseq ∧
    CoverageExponents p sseq ∧ 0 < c ∧ c < p.q

def familySequence (ε : ℝ) : ℝ := 1 / 4 - 4 * ε

theorem family_admissible4 {c ε : ℝ} (hε : 0 < ε) (hε80 : ε < 1 / 80) (hc : 0 < c)
    (hcq : c < 1 / 4 - 10 * ε) : Admissible4 c (familySequence ε) (family ε) := by
  unfold Admissible4 FineExponents CoarseExponents4 BoundaryExponents SequenceExponents
    CoverageExponents family familySequence
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hc, ?_⟩ <;> linarith

def g4Epsilon (c : ℝ) : ℝ := (1 / 4 - c) / 20

def g4Parameters (c : ℝ) : Parameters := family (g4Epsilon c)

theorem g4_admissible4 {c : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) :
    Admissible4 c (familySequence (g4Epsilon c)) (g4Parameters c) :=
  family_admissible4 (by unfold g4Epsilon; linarith) (by unfold g4Epsilon; linarith) hc
    (by unfold g4Epsilon; linarith)

theorem optimized_admissible4 {c : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) :
    Admissible4 c (familySequence (optimizedEpsilon c)) (optimizedParameters c) := by
  obtain ⟨hpos, hsmall, hgap⟩ := optimizedEpsilon_margins c hc hc4
  exact family_admissible4 hpos (by linarith) hc (by linarith)

theorem g4Parameters_one_fifth :
    (g4Parameters (1 / 5)).q = 9 / 40 ∧ (g4Parameters (1 / 5)).d = 1 / 800 ∧
      (g4Parameters (1 / 5)).kb = 91 / 400 ∧ (g4Parameters (1 / 5)).sb = 19 / 80 ∧
      familySequence (g4Epsilon (1 / 5)) = 6 / 25 := by
  unfold g4Parameters g4Epsilon family familySequence
  norm_num

theorem g0_admissible4 : Admissible4 (1 / 20) g0Sequence g0Parameters := by
  obtain ⟨hfe, -, hbe, hse, hcov, hc, hcq⟩ := g0_admissible
  refine ⟨hfe, ?_, hbe, hse, hcov, hc, hcq⟩
  unfold CoarseExponents4 g0Parameters
  norm_num

theorem admissible4_of_feasible {c : ℝ} {p : Parameters} (h : Feasible c p)
    (hfa : p.f / 4 < p.a) :
    Admissible4 c ((p.sb + p.e) / 2) p := by
  unfold Feasible at h
  obtain ⟨ha0, hf0, hkf0, hD0, hu0, hd0, he0, hzP0, hb0, hz0, hγ0, hkb0, hsb0, hr0, huF0,
    hsF0, hq0, hg0, hc0, hkfa, hkff, hkf1, haf, hkba, hza, hkbz, hkbb, hzb, hzγ, h2za,
    h2zγ, hzsb, hbsb, hγsb, hγbsb, hasb, hbf, huD, hukf, heud, he1, hrb, hqu, hur, hsF,
    hsFq, hqkb, hqD, hqzP, hzP, hqe, hsbe, hre, hag, hgsb, hgq, hgr, hcq, hqh⟩ := h
  unfold Admissible4 FineExponents CoarseExponents4 BoundaryExponents SequenceExponents
    CoverageExponents
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hc0, hcq⟩ <;> linarith

end SKConstants.Blueprint4
