import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Acyclic


namespace SimpleGraph


variable {V : Type*} {G : SimpleGraph V}

def InInterval (G : SimpleGraph V) (x y : V) : Set V :=
  {v | G.dist x v + G.dist v y = G.dist x y}

def IsMedian : Prop :=
  G.Connected ∧ ∀ v1 v2 v3 : V, ∃! m,
    m ∈ InInterval V G v1 v2 ∩ InInterval V G v2 v3 ∩ InInterval V G v1 v3

lemma unique_path
    (hG : G.IsAcyclic) (x y : V)
    (p q : G.Walk x y)
    (hp : p.IsPath) (hq : q.IsPath) :
    p = q := by
  obtain ⟨r, hr⟩ := hG.existsUnique_path x y
  exact (hr p hp).trans (hr q hq).symm

lemma path_intersection
    (hG : G.IsTree)
    {x y : V}
    (p q : G.Walk x y)
    (hp : p.IsPath)
    (hq : q.IsPath) :
    p.support = q.support := by
  have h := unique_path hG.isAcyclic x y p q hp hq
  rw [h]

lemma tripod
    (hG : G.IsTree)
    (x y z : V) :
    ∃ m : V,
      m ∈ (hG.existsUnique_path x y).choose.support ∧
      m ∈ (hG.existsUnique_path y z).choose.support ∧
      m ∈ (hG.existsUnique_path x z).choose.support := by
  sorry


-- Median theorem.
theorem existsUnique_median
    (hG : G.IsTree)
    (x y z : V) :
    ∃! m : V,
      m ∈ InInterval G x y ∩
          InInterval G y z ∩
          InInterval G x z := by
  sorry


theorem IsTree.isMedianGraph
    (hG : G.IsTree) :
    G.Connected ∧
      ∀ x y z : V,
        ∃! m : V,
          m ∈ InInterval G x y ∩
              InInterval G y z ∩
              InInterval G x z := by
  constructor
  · exact hG.connected
  · intro x y z
    exact existsUnique_median hG x y z


end SimpleGraph
