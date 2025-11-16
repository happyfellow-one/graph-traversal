import Mathlib
open Std

section

variable {α : Type}

theorem List.diff_not_mem_left
  [BEq α]
  [LawfulBEq α]
  (l1 l2 : List α)
  (x : α)
  (h : x ∉ l1) : x ∉ l1.diff l2 := by
  rw [List.diff_eq_foldl]
  cases l2 with
  | nil => simp; trivial
  | cons head tail =>
    simp
    rw [<-List.diff_eq_foldl]
    apply (List.diff_not_mem_left (l1.erase head) tail x ?_)
    grind

theorem List.diff_commutes
  [BEq α]
  [LawfulBEq α]
  (l1 l2 l3 : List α)
  : (l1.diff l2).diff l3 = (l1.diff l3).diff l2 := by
  calc (l1.diff l2).diff l3 = l1.diff (l2 ++ l3) := by rw [List.diff_append]
       _ = l1.diff (l3 ++ l2) := by rw [List.Perm.diff_left]; grind
       _ = (l1.diff l3).diff l2 := by rw [<-List.diff_append]

theorem List.diff_length
  [BEq α]
  [LawfulBEq α]
  (l1 l2 : List α)
  (x : α)
  (xmem : x ∈ l1)
  (xnotmem : x ∉ l2) :
  (l1.diff (x :: l2)).length < (l1.diff l2).length := by
  have h : l1.diff (x :: l2) = (l1.diff l2).diff [x] := by
    calc l1.diff (x :: l2) = l1.diff ([x] ++ l2) := by simp
        _ = (l1.diff [x]).diff l2 := by rw [List.diff_append]
        _ = (l1.diff l2).diff [x] := by rw [List.diff_commutes]
  rw [h]
  have hdiffmem : x ∈ l1.diff l2 := by apply List.mem_diff_of_mem <;> grind
  simp
  rw [List.length_erase]; simp [hdiffmem]
  grind
end

theorem Array.foldl_0_len
  (l : Array α)
  (init : β)
  (f : β → α → β)
  : Array.foldl f init l 0 0 = init := by
  cases h : l.toList with
  | nil =>
    have : l = [].toArray := by grind
    simp [this]
  | cons head tail =>
    have : l = (head :: tail).toArray := by grind
    simp [this, foldl, foldlM, Id.run, foldlM.loop, pure]

theorem Array.getElem_splits
  (l : Array α)
  (i : ℕ)
  (_ : i < l.size)
  : ∃ l1 l2, l = l1 ++ #[l[i]] ++ l2 ∧ l1.size = i ∧ l2.size = l.size - i - 1 := by
  exists (l.extract 0 i)
  exists (l.extract (i+1) l.size)
  refine ⟨ ?heq, ?hlen1, ?hlen2⟩
  case heq => simp; grind
  case hlen1 => simp; omega
  case hlen2 => simp; trivial

theorem Array.foldl_monoid
  [Monoid α]
  (l : Array α)
  (m m' : α)
  : Array.foldl (· * ·) (m * m') l = m * (Array.foldl (· * ·) m' l) := by
  cases h : l.toList with
  | nil =>
    rw [Array.toList_eq_nil_iff] at h
    rw [h]
    simp
  | cons head tail =>
    have h : l = (head :: tail).toArray := by
      suffices l.toList.toArray = (head :: tail).toArray by simp at this; trivial
      congr
    have ih : Array.foldl (· * ·) (m * m' * head) tail.toArray
              = m * (Array.foldl (· * ·) (m' * head) tail.toArray) := by
      rw [mul_assoc]
      apply (Array.foldl_monoid tail.toArray m (m' * head))
    simp [h]
    simp at ih
    apply ih

section

variable {α : Type} [BEq α] [Hashable α]

def Std.HashSet.toFinset [DecidableEq α] (a : HashSet α) : Finset α := a.toList.toFinset

def Std.HashSet.mem_toFinset
    [DecidableEq α] [BEq α] [LawfulBEq α] [Hashable α]
    {s : HashSet α} {x : α} :
    x ∈ HashSet.toFinset s ↔ x ∈ s := by
    unfold toFinset; simp

theorem HashSet.toFinset_toList_insert
    [DecidableEq α]
    [LawfulBEq α]
    (a : HashSet α) (x : α) (h : x ∉ a) :
    List.Perm ( (a.toFinset ∪ {x}).toList ) (x :: a.toFinset.toList) := by
  have h : x ∉ a.toFinset := by
    rw [a.mem_toFinset]; trivial
  simpa using (Finset.toList_insert (s := a.toFinset) (a := x) h)

theorem HashSet.toFinset_insert
    [DecidableEq α]
    [LawfulBEq α]
    (a : HashSet α)
    (x : α) :
    (a.insert x).toFinset = insert x a.toFinset := by
  apply Finset.ext
  intro y
  apply Iff.intro
  · intro h
    rw [HashSet.mem_toFinset, HashSet.mem_insert] at h
    simp at h
    cases h with
    | inl h => rw [h]; grind
    | inr h =>
      rw [Finset.mem_insert]
      right; rw [HashSet.mem_toFinset]; trivial
  · intro h
    rw [Finset.mem_insert] at h
    cases h with
    | inl h => rw [h, HashSet.mem_toFinset]; grind
    | inr h =>
      rw [HashSet.mem_toFinset, HashSet.mem_insert]
      right; rw [HashSet.mem_toFinset] at h; trivial

def HashSet.diff (a b : HashSet α) : HashSet α :=
  a.fold (fun acc x => acc.erase x) b

def HashSet.attach
  [LawfulBEq α]
  (a : HashSet α) :
  HashSet { x // x ∈ a } :=
  a.toArray.attach.map (fun ⟨x, xmem⟩ =>
    ⟨x, by rw [HashSet.mem_toArray] at xmem; trivial⟩)
  |> HashSet.ofArray

theorem HashSet.size_not_empty
  (a : HashSet α)
  (hnotempty : ¬a.isEmpty = true)
  : a.size > 0 := by
  if h : a.size > 0
  then assumption
  else
    have : a.size = 0 := by grind
    have : a.isEmpty = true := by rw [HashSet.isEmpty_eq_size_eq_zero, this]; simp
    trivial

theorem HashSet.subset_sizes
  [LawfulBEq α]
  (a b : HashSet α)
  (subset : ∀ x ∈ a, x ∈ b)
  : a.size <= b.size :=  by
  if hempty : a.isEmpty
  then
    have : HashSet.size a = 0 := by
      apply LawfulBEq.eq_of_beq
      simpa [<-HashSet.isEmpty_eq_size_eq_zero]
    grind
  else
    have : a.size > 0 := by apply HashSet.size_not_empty; grind
    have : a.toArray.size > 0 := by
      rw [HashSet.size_toArray]
      apply HashSet.size_not_empty
      assumption
    let x : α := a.toArray[0]
    have hxina : x ∈ a := by
      rw [<-HashSet.mem_toArray]
      grind
    have hxinb : x ∈ b := by
      apply subset; trivial
    have : ¬b.isEmpty = true := by
      simp
      rw [HashSet.isEmpty_eq_false_iff_exists_mem]
      exists x
    have : b.size > 0 := by apply HashSet.size_not_empty; grind
    let a' : HashSet α := a.erase x
    let b' : HashSet α := b.erase x
    have ha : a'.size = a.size - 1 := by
      rw [HashSet.size_erase]
      simp; intros; trivial
    have hb : b'.size = b.size - 1 := by
      rw [HashSet.size_erase]
      simp; intros; trivial
    have ih : a'.size <= b'.size := by
      apply (HashSet.subset_sizes a' b' ?_)
      intros x' x'memb
      grind
    have ha : a'.size + 1 = a.size := by
      symm
      apply Nat.eq_add_of_sub_eq
      · grind
      · grind
    have hb : b'.size + 1 = b.size := by
      symm
      apply Nat.eq_add_of_sub_eq
      · grind
      · grind
    grind
termination_by a.size
decreasing_by
  suffices (a.erase x).size = a.size - 1 by grind
  have : (a.erase x).size = if x ∈ a then a.size - 1 else a.size := by
    apply HashSet.size_erase
  simp [hxina] at this; assumption

-- set_option pp.all true

def HashSet.mem_of_big_union
  (x : α)
  (s : Array (HashSet α))
  (h : x ∈ s.foldl (· ∪ ·) ∅)
  : ∃ (i : ℕ) (_ : i < s.size), x ∈ s[i] := by
  let union : HashSet α := s.foldl (· ∪ ·) ∅
  have : ∃ (i : ℕ) (_ : i < s.size), x ∈ s[i] := by
    suffices ∃ (i : ℕ) (_ : i < s.size), s.size ≤ s.size → x ∈ s[i] by simpa using this
    apply Array.foldl_induction
      (as := s)
      (motive := λ n set =>
        x ∈ s.foldl (· ∪ ·) ∅ 0 n →
          ∃ (i : ℕ) (_ : i < n), (hb : n ≤ s.size) → x ∈ s[i]'?_)
      (init := ∅)
      (f := (· ∪ ·))
      (h0 := ?h0)
      (hf := ?hf)
    rotate_right
    · omega
    · assumption
    · intro inEmpty
      rw [Array.foldl_0_len] at inEmpty
      simp at inEmpty
    · intro i b ih hinfold
      if hlast : x ∈ s[i]
      then
        exists i
        have : (i : ℕ) < i + 1 := by omega
        exists this
        intro hb
        simpa using hlast
      else
        let mid : HashSet α := s[i]
        have : ∃ (s1 s2: Array _), s = s1 ++ #[mid] ++ s2 := by
          simpa using (Array.getElem_splits s i)
        obtain ⟨s1, s2, s1s2eq⟩ := this
        have hinfold' : x ∈ s.foldl (· ∪ ·) ∅ 0 i := by
          have hsize : s.size = (s1 ++ #[mid] ++ s2).size := by rw (occs := .pos [1]) [s1s2eq]
          have i' : Fin (s1 ++ #[mid] ++ s2).size := Fin.cast hsize i
          simp_rw [s1s2eq] at hinfold
          rw [Array.foldl_append'] at hinfold
          rw [Array.foldl_append'] at hinfold
          simp at hinfold
          sorry
        have : ∃ (i' : ℕ) (hilen : i' < i), ∀ (hb : i ≤ s.size), x ∈ s[i'] := by
          sorry
        obtain ⟨ i', hilen, xi ⟩ := this
        exists i'
        have : (i' : ℕ) < i + 1 := by omega
        exists this
        intro hb
        have hilen' : i' < i := by omega
        grind
  assumption

end

variable {V : Type} [DecidableEq V] [LawfulBEq V] [EquivBEq V] [Hashable V] [LawfulHashable V]

structure FinGraph
  (V : Type)
  [BEq V]
  [LawfulBEq V]
  [EquivBEq V]
  [Hashable V]
  [LawfulHashable V] where
  nodes : HashSet V
  -- TODO Change to hashmap?
  edges : V → HashSet V
  edgesInNodes : ∀ v w, w ∈ edges v → w ∈ nodes

example : FinGraph ℕ :=
  { nodes := ∅
    edges := (fun _ => ∅),
    edgesInNodes := (by intros; trivial) }

namespace FinGraph

def reachability'
  (g : FinGraph V)
  (v : V)
  (_vInNodes : v ∈ g.nodes)
  (visited : HashSet V)
  : HashSet V :=
  if visited.contains v
  then visited
  else
    let visited' := visited.insert v
    g.edges v
    |> HashSet.attach
    |> HashSet.fold (fun acc ⟨w, wmem⟩  =>
      have wInNodes : w ∈ g.nodes := by apply g.edgesInNodes; exact wmem
      acc ∪ reachability' g w wInNodes visited')
      ∅
termination_by (g.nodes.toFinset \ visited.toFinset).card
decreasing_by
  have h : v ∉ visited := by grind
  rw [HashSet.toFinset_insert]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  apply And.intro
  · rw [Finset.subset_iff]
    intros x xmem
    rw [Finset.mem_sdiff] at *
    have ⟨xmem, xnotmem⟩ := xmem
    rw [Finset.mem_insert] at xnotmem
    apply And.intro
    · exact xmem
    · intro xin
      grind
  · intro heq
    have : v ∈ g.nodes.toFinset \ visited.toFinset := by
      rw [Finset.mem_sdiff]
      apply And.intro
      · rw [HashSet.mem_toFinset]; trivial
      · rw [HashSet.mem_toFinset]; trivial
    grind

def reachability'_p
  (g : FinGraph V)
  (v : V)
  (_vInNodes : v ∈ g.nodes)
  (visited : List V)
  : List V :=
  if hinv : v ∈ visited
  then visited
  else
    let visited' := v :: visited
    let a :=
      g.edges v
      |> HashSet.toList
      |> List.attach
    a.flatMap (fun ⟨w, wmem⟩  =>
      have wmem' : w ∈ g.edges v := by simp at wmem; trivial
      have wInNodes : w ∈ g.nodes := by apply g.edgesInNodes; exact wmem'
      reachability'_p g w wInNodes visited')
termination_by (List.diff g.nodes.toList visited).length
decreasing_by apply List.diff_length <;> grind

theorem reachability'_p_equiv
  (g : FinGraph V)
  (v : V)
  (vInNodes : v ∈ g.nodes)
  (visited : HashSet V)
  (visitedInNodes : ∀ w ∈ visited, w ∈ g.nodes) :
  (reachability' g v vInNodes visited visitedInNodes).toList.toFinset
  = reachability'_p g v vInNodes visited.toList.toFinset (by simp; grind) := by
  fun_induction reachability' g v vInNodes visited visitedInNodes
  · expose_names
    have : v_1 ∈ visited_1 := by grind
    unfold reachability'_p; simp; intros
    trivial
  · expose_names
    have : v_1 ∉ visited_1 := by grind
    unfold reachability'_p; simp [*]
    sorry


/-- Returns the set of nodes reachable from [v]. -/
def reachability (g : FinGraph V) (v : V) (vInNodes : v ∈ g.nodes) : HashSet V :=
  reachability' g v vInNodes ∅ (by grind)

inductive Reachable (g : FinGraph V) : V → V → Prop where
| self : Reachable g x x
| step : Reachable g x y → z ∈ g.edges y → Reachable g x z

theorem reachability'_sound
  (g : FinGraph V)
  (start : V)
  (startInNodes : start ∈ g.nodes)
  (visited : HashSet V)
  (visitedInNodes : ∀ v ∈ visited, v ∈ g.nodes)
  (visitedReachable : ∀ stop ∈ visited, Reachable g start stop)
  : ∀ stop ∈ reachability' g start startInNodes visited visitedInNodes, Reachable g start stop := by
  intro stop stopReachability
  unfold reachability' at stopReachability
  if startVisited : start ∈ visited
  then
    simp [startVisited] at stopReachability
    simpa using (visitedReachable stop stopReachability)
  else
    simp [startVisited] at stopReachability
    let visited' : HashSet V := visited.insert start
    have visitedInNodes' : ∀ w ∈ visited', w ∈ g.nodes := by
      intros w wmem
      simp [visited'] at wmem
      cases wmem <;> repeat grind
    let s : Array (HashSet V) := (g.edges start).toArray.attach.map (λ ⟨w, wmem⟩  =>
      have wmem' : w ∈ g.edges start := by rw [HashSet.mem_toArray] at wmem; trivial
      have wInNodes : w ∈ g.nodes := by apply g.edgesInNodes; exact wmem'
      reachability' g w wInNodes visited' visitedInNodes')
    have : ∃ (i : ℕ) (_ : i < s.size), stop ∈ s[i] := by
      apply HashSet.mem_of_big_union
      simp [s]
      apply stopReachability
    obtain ⟨ i, hilen, simem ⟩ := this
    simp [s] at simem
    have : i < (g.edges start).toArray.size := by
      unfold s at hilen
      rw [Array.size_map] at hilen
      rw [Array.size_attach] at hilen
      assumption
    let mid : V := (g.edges start).toArray[i]
    have ih : Reachable g mid stop := by
      apply (reachability'_sound g (g.edges start).toArray[i] ?_ visited' visitedInNodes' ?_)
      assumption
      intros stop stopInVisited'
      unfold visited' at stopInVisited'
      if heq : start = stop
      then
        rw [heq] at *
        sorry
      else
        sorry
    assumption
    sorry

theorem reachability_sound
  (g : FinGraph V)
  (start : V)
  (startInNodes : start ∈ g.nodes)
  (stop : V)
  (stopReachable : stop ∈ reachability g start startInNodes)
  : Reachable g start stop := by
  sorry

theorem reachability_complete
  (g : FinGraph V)
  (start : V)
  (startInNodes : start ∈ g.nodes)
  (stop : V)
  (stopReachable : Reachable g start stop)
  : stop ∈ reachability g start startInNodes := by sorry

end FinGraph
