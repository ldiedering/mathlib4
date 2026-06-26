module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Measures having no atoms
-/

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

def IsAtom (s : Set α) (μ : Measure α) :=
  0 < μ s ∧ ∀ t ⊆ s, MeasurableSet t → μ t = 0 ∨ μ t = μ s

/-- Measure `μ` *has no atoms* if for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class NoAtoms (μ : Measure α) : Prop where
  no_atoms : ∀ s, MeasurableSet s → ¬ IsAtom s μ

export MeasureTheory.NoAtoms (no_atoms)

theorem no_atoms_iff :
    NoAtoms μ
      ↔ ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s := by
  constructor
  · intro na s meas_s hs
    have := na.no_atoms
    unfold IsAtom at this
    push Not at this
    rcases this s meas_s hs with ⟨t, ts, meas_t, ht, ht'⟩
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot] at ht
    use t, ts, meas_t, ht, lt_of_le_of_ne (measure_mono ts) ht'
  · intro h
    apply NoAtoms.mk
    intro s meas_s
    unfold IsAtom
    push Not
    intro hs
    rcases h s meas_s hs with ⟨t, ts, meas_t, ht, ht'⟩
    use t, ts, meas_t, ht.ne', ht'.ne

theorem NoAtoms.mk' {μ : Measure α}
  (h : ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s) :
    NoAtoms μ := by
  rw [no_atoms_iff]
  intro s meas_s hs
  rcases h _ meas_s hs with ⟨t, hst, ht, hts⟩
  rcases exists_measurable_superset μ t with ⟨u, htu, hu, hut⟩
  use u ∩ s
  use inter_subset_right
  use hu.inter meas_s
  have : μ (u ∩ s) = μ t := by
    apply le_antisymm
    · rw [← hut]
      apply measure_mono inter_subset_left
    · calc _
        _ = μ (u ∩ t) := by
          congr
          symm
          rwa [inter_eq_right]
        _ ≤ μ (u ∩ s) := by gcongr
  rw [this]
  use ht, hts


variable [na : NoAtoms μ]

theorem exists_measurable_subset_lt {s : Set α} (meas_s : MeasurableSet s) (hs : 0 < μ s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s := no_atoms_iff.mp na s meas_s hs

--TODO: do we really need `MeasurableSingletonClass α`
instance instNullSingletonClassOfNoAtoms [MeasurableSingletonClass α] : NullSingletonClass μ where
  measure_singleton := by
    intro x
    by_contra! hx
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot] at hx
    rcases exists_measurable_subset_lt (measurableSet_singleton _) hx with ⟨t, htx, _, ht, ht'⟩
    rw [subset_singleton_iff_eq] at htx
    rcases htx with h | h
    · rw [h] at ht
      simp at ht
    · rw [h] at ht'
      simp at ht'

instance Measure.restrict.instNoAtoms (s : Set α) :
    NoAtoms (μ.restrict s) := by
  apply NoAtoms.mk'
  intro t meas_t ht
  rw [Measure.restrict_apply meas_t] at *
  /-
  refine ⟨fun x => ?_⟩
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
  apply measure_mono_null hxt
  rw [Measure.restrict_apply ht1]
  apply measure_mono_null inter_subset_left ht2
  -/
  sorry

end MeasureTheory
