import Mathlib

variable (V : Type*) (G : SimpleGraph V)

-- Definition of graph intervals

def InInterval (x y : V) : Set V :=
  {z | G.dist x z + G.dist z y = G.dist x y}

-- Definition of a median graph

def IsMedian : Prop :=
  G.Connected ∧
    ∀ v1 v2 v3 : V, ∃! m,
      m ∈ InInterval V G v1 v2 ∩
          InInterval V G v2 v3 ∩
          InInterval V G v1 v3

-- Symmetry of graph intervals

theorem InInterval_symm (x y : V) :
    InInterval V G x y = InInterval V G y x := by
  unfold InInterval
  apply Set.ext
  intro z
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h1
    rw [add_comm,
      G.dist_comm (u := z) (v := x),
      G.dist_comm (u := y) (v := z),
      G.dist_comm (u := y) (v := x)]
    exact h1
  · intro h2
    rw [add_comm,
      G.dist_comm (u := z) (v := y),
      G.dist_comm (u := x) (v := z),
      G.dist_comm (u := x) (v := y)]
    exact h2

-- Endpoints belong to their intervals

theorem left_mem_InInterval (x y : V) :
    x ∈ InInterval V G x y := by
  simp [InInterval]

theorem right_mem_InInterval (x y : V) :
    y ∈ InInterval V G x y := by
  simp [InInterval]

-- Unique paths in a tree

theorem tree_path_unique
    {a b : V}
    (hG : G.IsTree)
    (p q : G.Walk a b)
    (hp : p.IsPath)
    (hq : q.IsPath) :
    p = q := by
  obtain ⟨r, hr, huniq⟩ :=
    hG.existsUnique_path a b
  exact (huniq p hp).trans (huniq q hq).symm

-- Shortest paths in a tree

theorem tree_shortest_path
    (hG : G.IsTree)
    (a b : V) :
    ∃ p : G.Walk a b,
      p.IsPath ∧ p.length = G.dist a b := by
  exact hG.connected.exists_path_of_dist a b

-- Shortest paths from a common starting vertex

theorem common_starting_paths
    (hG : G.IsTree)
    (a b c : V) :
    ∃ p : G.Walk a b,
      ∃ q : G.Walk a c,
        p.IsPath ∧ q.IsPath ∧
        p.length = G.dist a b ∧
        q.length = G.dist a c := by
  obtain ⟨p, hp, hplen⟩ :=
    hG.connected.exists_path_of_dist a b
  obtain ⟨q, hq, hqlen⟩ :=
    hG.connected.exists_path_of_dist a c
  exact ⟨p, q, hp, hq, hplen, hqlen⟩

-- Existence of the median

theorem tripod_lemma
    (hG : G.IsTree)
    (a b c : V) :
    ∃ m : V,
      m ∈ InInterval V G a b ∩
          InInterval V G b c ∩
          InInterval V G a c := by
  sorry

-- Uniqueness of the median

theorem median_unique
    (hG : G.IsTree)
    (a b c m n : V)
    (hm :
      m ∈ InInterval V G a b ∩
          InInterval V G b c ∩
          InInterval V G a c)
    (hn :
      n ∈ InInterval V G a b ∩
          InInterval V G b c ∩
          InInterval V G a c) :
    m = n := by
  sorry

-- Main theorem: every tree is a median graph

theorem tree_is_median :
    G.IsTree → IsMedian V G := by
  intro hG
  constructor
  · exact hG.connected
  · intro a b c
    obtain ⟨m, hm⟩ :=
      tripod_lemma V G hG a b c
    refine ⟨m, hm, ?_⟩
    intro n hn
    exact (median_unique V G hG a b c m n hm hn).symm
