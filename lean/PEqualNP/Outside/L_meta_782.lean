import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private def unitVec {n : ℕ} (a : Fin n) : Fin n → Bool :=
  fun b => decide (b = a)

private def U (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a : Fin n => wval C (unitVec a) w = true)

private lemma foldl_extend_length (gs : List Gate) (init : List Bool) :
    (gs.foldl extend init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g rest ih =>
    simp [extend, ih]
    omega

private lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases hlt : i < w.length
  · simp [List.getD, List.getElem?_append_left hlt, Nat.ne_of_lt hlt]
  · rw [List.getD, List.getElem?_append_right (by omega)]
    by_cases heq : i = w.length
    · simp [heq]
    · have h1 : w.length ≤ i := by omega
      have h2 : [b].length ≤ i - w.length := by simp; omega
      simp [heq, List.getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]

private lemma foldl_extend_getD_lt (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (gs.foldl extend init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hi' : i < (extend init g).length := by
      simp only [extend, List.length_append, List.length_singleton]
      omega
    rw [ih (extend init g) hi']
    simp only [extend, getD_snoc, Nat.ne_of_lt hi, ↓reduceIte]

private lemma wires_eq_foldl {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    C.wires (List.ofFn x) = C.gates.foldl extend (List.ofFn x) := rfl

private lemma wires_length {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.size := by
  rw [wires_eq_foldl, foldl_extend_length, List.length_ofFn, Circuit.size]

private lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : w < n) :
    wval C x w = x ⟨w, hw⟩ := by
  unfold wval
  rw [wires_eq_foldl]
  have hlen : w < (List.ofFn x).length := by simpa using hw
  rw [foldl_extend_getD_lt _ _ _ hlen]
  rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]

private lemma wval_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.size ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by rw [wires_length]; exact hw
  simp [List.getD, List.getElem?_eq_none hlen]

private lemma wval_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin C.size) :
    wval C x (n + j.val) =
      (C.gates[j.val]'(j.isLt)).op.eval
        ((C.gates[j.val]'(j.isLt)).inputs.map
          (fun u => if u < n + j.val then wval C x u else false)) := by
  have hdrop : C.gates.drop j.val = (C.gates[j.val]'(j.isLt)) :: C.gates.drop (j.val + 1) :=
    List.drop_eq_getElem_cons j.isLt
  let pre := (C.gates.take j.val).foldl extend (List.ofFn x)
  have hpre_len : pre.length = n + j.val := by
    have hjle : j.val ≤ C.gates.length := Nat.le_of_lt j.isLt
    simp only [pre, foldl_extend_length, List.length_ofFn, List.length_take, Nat.min_eq_left hjle]
  have hwires_pre : C.wires (List.ofFn x) = (C.gates.drop j.val).foldl extend pre := by
    rw [wires_eq_foldl, ← List.foldl_append, List.take_append_drop]
  have hpre_getD : ∀ u : ℕ, pre.getD u false = if u < n + j.val then wval C x u else false := by
    intro u
    by_cases hu : u < n + j.val
    · simp only [hu, ↓reduceIte]
      unfold wval
      rw [hwires_pre, foldl_extend_getD_lt (C.gates.drop j.val) pre u (by omega)]
    · simp only [hu, ↓reduceIte]
      have hge : pre.length ≤ u := by omega
      simp [List.getD, List.getElem?_eq_none hge]
  have hwires_step :
      C.wires (List.ofFn x) =
        (C.gates.drop (j.val + 1)).foldl extend (extend pre (C.gates[j.val]'(j.isLt))) := by
    rw [hwires_pre, hdrop, List.foldl_cons]
  show (C.wires (List.ofFn x)).getD (n + j.val) false = _
  rw [hwires_step]
  have hlt : n + j.val < (extend pre (C.gates[j.val]'(j.isLt))).length := by
    simp only [extend, List.length_append, List.length_singleton, hpre_len]
    omega
  rw [foldl_extend_getD_lt _ _ _ hlt]
  simp only [extend, getD_snoc, hpre_len, ↓reduceIte]
  congr 1
  exact List.map_congr_left (fun u _ => hpre_getD u)

private lemma wval_gate_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin C.size)
    (hop : (C.gates[j.val]'(j.isLt)).op = GateOp.and) :
    wval C x (n + j.val) = true ↔
      ∀ u ∈ (C.gates[j.val]'(j.isLt)).inputs, u < n + j.val ∧ wval C x u = true := by
  rw [wval_gate, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h u hu
    have h1 := h _ ⟨u, hu, rfl⟩
    by_cases hlt : u < n + j.val
    · simp only [hlt, ↓reduceIte] at h1
      exact ⟨hlt, h1⟩
    · simp only [hlt, ↓reduceIte] at h1
      exact absurd h1 (by decide)
  · intro h b hb
    rcases hb with ⟨u, hu, rfl⟩
    obtain ⟨hlt, huval⟩ := h u hu
    simp only [hlt, ↓reduceIte]
    exact huval

private lemma wval_gate_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin C.size)
    (hop : (C.gates[j.val]'(j.isLt)).op = GateOp.or) :
    wval C x (n + j.val) = true ↔
      ∃ u ∈ (C.gates[j.val]'(j.isLt)).inputs, u < n + j.val ∧ wval C x u = true := by
  rw [wval_gate, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · intro h
    rcases h with ⟨_, ⟨u, hu, rfl⟩, h1⟩
    by_cases hlt : u < n + j.val
    · simp only [hlt, ↓reduceIte] at h1
      exact ⟨u, hu, hlt, h1⟩
    · simp only [hlt, ↓reduceIte] at h1
      exact absurd h1 (by decide)
  · intro h
    rcases h with ⟨u, hu, hlt, huval⟩
    exact ⟨true, ⟨u, hu, by simp only [hlt, ↓reduceIte, huval]⟩, rfl⟩

private lemma wval_mono {n : ℕ} (C : Circuit)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    {x y : Fin n → Bool} (hxy : ∀ a : Fin n, x a = true → y a = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases h1 : w < n
    · rw [wval_input C x h1] at hx
      rw [wval_input C y h1]
      exact hxy ⟨w, h1⟩ hx
    · by_cases h2 : w < n + C.size
      · let j : Fin C.size := ⟨w - n, by omega⟩
        have hwj : w = n + j.val := by simp [j]; omega
        rw [hwj] at hx ⊢
        rcases (hgates _ (List.getElem_mem j.isLt)).1 with hop | hop
        · rw [wval_gate_and C x j hop] at hx
          rw [wval_gate_and C y j hop]
          intro u hu
          obtain ⟨hlt, huval⟩ := hx u hu
          exact ⟨hlt, ih u (by omega) huval⟩
        · rw [wval_gate_or C x j hop] at hx
          rw [wval_gate_or C y j hop]
          obtain ⟨u, hu, hlt, huval⟩ := hx
          exact ⟨u, hu, hlt, ih u (by omega) huval⟩
      · rw [wval_oob C x (by omega)] at hx
        exact absurd hx (by decide)

private lemma U_card_le_one_of_lt (C : Circuit) (n w : ℕ) (hw : w < n) :
    (U C n w).card ≤ 1 := by
  have hsub : U C n w ⊆ ({⟨w, hw⟩} : Finset (Fin n)) := by
    intro a ha
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, wval_input C _ hw,
      unitVec, decide_eq_true_eq] at ha
    simp [ha.symm]
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma U_eq_empty_of_ge (C : Circuit) (n w : ℕ) (hw : n + C.size ≤ w) :
    U C n w = ∅ := by
  ext a
  simp [U, wval_oob C _ hw]

private def privGates (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter (fun j : Fin C.size => U C n (n + j.val) ⊆ Si ∧ 2 ≤ (U C n (n + j.val)).card)

private def validInputs (C : Circuit) (n : ℕ) (j : Fin C.size) : Finset ℕ :=
  ((C.gates[j.val]'(j.isLt)).inputs.toFinset).filter (fun u => u < n + j.val)

private lemma mem_validInputs (C : Circuit) (n : ℕ) (j : Fin C.size) (u : ℕ) :
    u ∈ validInputs C n j ↔ u ∈ (C.gates[j.val]'(j.isLt)).inputs ∧ u < n + j.val := by
  simp [validInputs]

private lemma card_validInputs_le (C : Circuit) (n : ℕ) (j : Fin C.size)
    (hlen : (C.gates[j.val]'(j.isLt)).inputs.length = 2) :
    (validInputs C n j).card ≤ 2 := by
  calc (validInputs C n j).card
      ≤ (C.gates[j.val]'(j.isLt)).inputs.toFinset.card := Finset.card_filter_le _ _
    _ ≤ (C.gates[j.val]'(j.isLt)).inputs.length := List.toFinset_card_le _
    _ = 2 := hlen

private def privStep (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (a b : Fin C.size) : Prop :=
  a ∈ privGates C n Si ∧ b ∈ privGates C n Si ∧ n + b.val ∈ validInputs C n a

private def lab (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (Q : Finset (Fin C.size)) (w : ℕ) :
    Bool :=
  if h : n ≤ w ∧ w < n + C.size then
    let j : Fin C.size := ⟨w - n, by omega⟩
    if j ∈ Q then
      let g := C.gates[j.val]'(show j.val < C.gates.length from j.isLt)
      let childVal (u : ℕ) : Bool := if hu : u < w then lab C n Si Q u else false
      match g.op with
      | GateOp.and => g.inputs.all childVal
      | GateOp.or => g.inputs.any childVal
      | _ => false
    else
      decide (¬ U C n w ⊆ Si)
  else
    decide (¬ U C n w ⊆ Si)
termination_by w

private lemma lab_not_mem (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (Q : Finset (Fin C.size))
    (w : ℕ) (hnot : ∀ j ∈ Q, w ≠ n + j.val) :
    lab C n Si Q w = decide (¬ U C n w ⊆ Si) := by
  rw [lab]
  by_cases h1 : n ≤ w ∧ w < n + C.size
  · simp only [h1, and_self, ↓reduceDIte]
    have hnot' : (⟨w - n, by omega⟩ : Fin C.size) ∉ Q := fun hq => hnot _ hq (by dsimp; omega)
    simp only [hnot', ↓reduceIte]
  · simp only [h1, ↓reduceDIte]

private lemma lab_mem_and (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (Q : Finset (Fin C.size))
    (j : Fin C.size) (hjQ : j ∈ Q) (hop : (C.gates[j.val]'(j.isLt)).op = GateOp.and) :
    lab C n Si Q (n + j.val) = true ↔
      ∀ u ∈ (C.gates[j.val]'(j.isLt)).inputs, u < n + j.val ∧ lab C n Si Q u = true := by
  have h1 : n ≤ n + j.val ∧ n + j.val < n + C.size :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.isLt n⟩
  have hlab_eq : lab C n Si Q (n + j.val) =
      (C.gates[j.val]'(show j.val < C.gates.length from j.isLt)).inputs.all
        (fun u => if hu : u < n + j.val then lab C n Si Q u else false) := by
    rw [lab]
    simp only [h1, and_self, ↓reduceDIte, Nat.add_sub_cancel_left, hjQ, ↓reduceIte]
    have hop' : (C.gates[j.val]'(show j.val < C.gates.length from j.isLt)).op = GateOp.and := hop
    rw [hop']
  rw [hlab_eq, List.all_eq_true]
  constructor
  · intro h u hu
    have h2 := h u hu
    by_cases hlt : u < n + j.val
    · simp only [hlt, ↓reduceDIte] at h2
      exact ⟨hlt, h2⟩
    · simp only [hlt, ↓reduceDIte] at h2
      exact absurd h2 (by decide)
  · intro h u hu
    obtain ⟨hlt, hlu⟩ := h u hu
    simp only [hlt, ↓reduceDIte]
    exact hlu

private lemma lab_mem_or (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (Q : Finset (Fin C.size))
    (j : Fin C.size) (hjQ : j ∈ Q) (hop : (C.gates[j.val]'(j.isLt)).op = GateOp.or) :
    lab C n Si Q (n + j.val) = true ↔
      ∃ u ∈ (C.gates[j.val]'(j.isLt)).inputs, u < n + j.val ∧ lab C n Si Q u = true := by
  have h1 : n ≤ n + j.val ∧ n + j.val < n + C.size :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.isLt n⟩
  have hlab_eq : lab C n Si Q (n + j.val) =
      (C.gates[j.val]'(show j.val < C.gates.length from j.isLt)).inputs.any
        (fun u => if hu : u < n + j.val then lab C n Si Q u else false) := by
    rw [lab]
    simp only [h1, and_self, ↓reduceDIte, Nat.add_sub_cancel_left, hjQ, ↓reduceIte]
    have hop' : (C.gates[j.val]'(show j.val < C.gates.length from j.isLt)).op = GateOp.or := hop
    rw [hop']
  rw [hlab_eq, List.any_eq_true]
  constructor
  · intro h
    rcases h with ⟨u, hu, h2⟩
    by_cases hlt : u < n + j.val
    · simp only [hlt, ↓reduceDIte] at h2
      exact ⟨u, hu, hlt, h2⟩
    · simp only [hlt, ↓reduceDIte] at h2
      exact absurd h2 (by decide)
  · intro h
    rcases h with ⟨u, hu, hlt, hlu⟩
    exact ⟨u, hu, by simp only [hlt, ↓reduceDIte]; exact hlu⟩

private lemma per_index_bound {n k : ℕ} (C : Circuit) (Si : Finset (Fin n)) (oi ci : ℕ)
    (h2 : 2 ≤ (U C n oi).card)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hsub : U C n oi ⊆ Si)
    (hzero : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ Si, x q = false) → wval C x oi = false)
    (hck : ci ≤ k)
    (hcU : ci + 1 ≤ (U C n oi).card) :
    ci ≤ (privGates C n Si).card := by
  classical
  have hoi_ge : n ≤ oi := by
    by_contra hlt
    have hle1 := U_card_le_one_of_lt C n oi (by omega)
    omega
  have hoi_lt : oi < n + C.size := by
    by_contra hge
    have hemp := U_eq_empty_of_ge C n oi (by omega)
    rw [hemp] at h2
    simp at h2
  let r : Fin C.size := ⟨oi - n, by omega⟩
  have hr_eq : n + r.val = oi := by simp [r]; omega
  have hrP : r ∈ privGates C n Si := by
    simp only [privGates, Finset.mem_filter, Finset.mem_univ, true_and, hr_eq]
    exact ⟨hsub, h2⟩
  let Q : Finset (Fin C.size) :=
    Finset.univ.filter (fun j : Fin C.size => Relation.ReflTransGen (privStep C n Si) r j)
  have hrQ : r ∈ Q := by
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  have hQsub : Q ⊆ privGates C n Si := by
    intro j hj
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    cases hj with
    | refl => exact hrP
    | tail _ hstep => exact hstep.2.1
  let AllIn : Finset ℕ := Q.biUnion (validInputs C n)
  let Qwires : Finset ℕ := Q.image (fun j : Fin C.size => n + j.val)
  let E : Finset ℕ := AllIn \ Qwires
  have hQwires_card : Qwires.card = Q.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    exact Fin.ext (Nat.add_left_cancel hab)
  have hr_mem_Qwires : n + r.val ∈ Qwires := Finset.mem_image_of_mem _ hrQ
  have hQwires_erase_sub : Qwires.erase (n + r.val) ⊆ AllIn := by
    intro w hw
    rw [Finset.mem_erase] at hw
    rcases hw with ⟨hne, hwQ⟩
    rw [Finset.mem_image] at hwQ
    rcases hwQ with ⟨j, hjQ, rfl⟩
    have hjr : j ≠ r := fun h => hne (by rw [h])
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and] at hjQ
    cases hjQ with
    | refl => exact absurd rfl hjr
    | tail hreach hstep =>
      refine Finset.mem_biUnion.mpr ⟨_, ?_, hstep.2.2⟩
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hreach
  have hAllIn_card : AllIn.card ≤ 2 * Q.card := by
    calc AllIn.card
        ≤ ∑ j ∈ Q, (validInputs C n j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Q, 2 := Finset.sum_le_sum (fun j _ =>
            card_validInputs_le C n j (hgates _ (List.getElem_mem j.isLt)).2)
      _ = Q.card * 2 := by simp
      _ = 2 * Q.card := Nat.mul_comm _ _
  have hE_card : E.card ≤ Q.card + 1 := by
    have hdisj : Disjoint E (Qwires.erase (n + r.val)) := by
      rw [Finset.disjoint_left]
      intro w hwE hwQ
      rw [Finset.mem_sdiff] at hwE
      exact hwE.2 (Finset.mem_of_mem_erase hwQ)
    have hunion_sub : E ∪ Qwires.erase (n + r.val) ⊆ AllIn := by
      intro w hw
      rw [Finset.mem_union] at hw
      rcases hw with hwE | hwQ
      · exact (Finset.mem_sdiff.mp hwE).1
      · exact hQwires_erase_sub hwQ
    have hle : E.card + (Qwires.erase (n + r.val)).card ≤ AllIn.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hunion_sub
    have herase : (Qwires.erase (n + r.val)).card = Q.card - 1 := by
      rw [Finset.card_erase_of_mem hr_mem_Qwires, hQwires_card]
    have hQpos : 1 ≤ Q.card := Finset.card_pos.mpr ⟨r, hrQ⟩
    omega
  have hchild_mem : ∀ j ∈ Q, ∀ u ∈ (C.gates[j.val]'(j.isLt)).inputs, u < n + j.val →
      u ∈ E ∪ Qwires := by
    intro j hjQ u hu hlt
    have hAll : u ∈ AllIn :=
      Finset.mem_biUnion.mpr ⟨j, hjQ, (mem_validInputs C n j u).mpr ⟨hu, hlt⟩⟩
    by_cases hq : u ∈ Qwires
    · exact Finset.mem_union_right _ hq
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hAll, hq⟩)
  have hnot_Qwires : ∀ w, w ∉ Qwires → ∀ j ∈ Q, w ≠ n + j.val := by
    intro w hnot j hjQ hw
    exact hnot (Finset.mem_image.mpr ⟨j, hjQ, hw.symm⟩)
  have hQleP : Q.card ≤ (privGates C n Si).card := Finset.card_le_card hQsub
  cases hlab_r : lab C n Si Q (n + r.val) with
  | true =>
    let Etrue : Finset ℕ := E.filter (fun w => lab C n Si Q w = true)
    have hpick : ∀ w ∈ Etrue, ∃ q : Fin n, q ∈ U C n w ∧ q ∉ Si := by
      intro w hw
      rw [Finset.mem_filter] at hw
      rcases hw with ⟨hwE, hwlab⟩
      have hnotQ : w ∉ Qwires := (Finset.mem_sdiff.mp hwE).2
      rw [lab_not_mem C n Si Q w (hnot_Qwires w hnotQ)] at hwlab
      exact Finset.not_subset.mp (of_decide_eq_true hwlab)
    let X : Finset (Fin n) := Etrue.attach.image (fun w => (hpick w.1 w.2).choose)
    let x : Fin n → Bool := fun q => decide (q ∈ X)
    have hX_disj : ∀ q ∈ Si, x q = false := by
      intro q hqSi
      simp only [x, decide_eq_false_iff_not]
      intro hqX
      rw [Finset.mem_image] at hqX
      rcases hqX with ⟨w, _, hwq⟩
      exact (hpick w.1 w.2).choose_spec.2 (hwq ▸ hqSi)
    have hX_card : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ Q.card + 1 := by
      have hfilt : Finset.univ.filter (fun q : Fin n => x q = true) = X := by
        ext q
        simp [x]
      rw [hfilt]
      calc X.card
          ≤ Etrue.attach.card := Finset.card_image_le
        _ = Etrue.card := Finset.card_attach
        _ ≤ E.card := Finset.card_filter_le _ _
        _ ≤ Q.card + 1 := hE_card
    have htrue : ∀ w, w ∈ E ∪ Qwires → lab C n Si Q w = true → wval C x w = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hlab
        by_cases hwQ : w ∈ Qwires
        · rcases Finset.mem_image.mp hwQ with ⟨j, hjQ, rfl⟩
          rcases (hgates _ (List.getElem_mem j.isLt)).1 with hop | hop
          · rw [lab_mem_and C n Si Q j hjQ hop] at hlab
            rw [wval_gate_and C x j hop]
            intro u hu
            obtain ⟨hlt, hlu⟩ := hlab u hu
            exact ⟨hlt, ih u hlt (hchild_mem j hjQ u hu hlt) hlu⟩
          · rw [lab_mem_or C n Si Q j hjQ hop] at hlab
            rw [wval_gate_or C x j hop]
            obtain ⟨u, hu, hlt, hlu⟩ := hlab
            exact ⟨u, hu, hlt, ih u hlt (hchild_mem j hjQ u hu hlt) hlu⟩
        · have hwE : w ∈ E := by
            rcases Finset.mem_union.mp hw with h | h
            · exact h
            · exact absurd h hwQ
          have hwEt : w ∈ Etrue := Finset.mem_filter.mpr ⟨hwE, hlab⟩
          let q := (hpick w hwEt).choose
          have hqU : q ∈ U C n w := (hpick w hwEt).choose_spec.1
          have hqX : q ∈ X := Finset.mem_image.mpr ⟨⟨w, hwEt⟩, Finset.mem_attach _ _, rfl⟩
          have hqw : wval C (unitVec q) w = true := (Finset.mem_filter.mp hqU).2
          apply wval_mono C hgates _ w hqw
          intro b hb
          have hbq : b = q := of_decide_eq_true hb
          simp [x, hbq, hqX]
    have hwoi : wval C x oi = true := by
      rw [← hr_eq]
      exact htrue (n + r.val) (Finset.mem_union_right _ hr_mem_Qwires) hlab_r
    have hgt : k < (Finset.univ.filter (fun q : Fin n => x q = true)).card := by
      by_contra hle
      have hfalse := hzero x (by omega) hX_disj
      rw [hwoi] at hfalse
      exact absurd hfalse (by decide)
    omega
  | false =>
    have hfalse_U_le_one : ∀ e ∈ E, lab C n Si Q e = false → (U C n e).card ≤ 1 := by
      intro e heE helab
      have heAll : e ∈ AllIn := (Finset.mem_sdiff.mp heE).1
      have heNotQ : e ∉ Qwires := (Finset.mem_sdiff.mp heE).2
      rw [lab_not_mem C n Si Q e (hnot_Qwires e heNotQ)] at helab
      have heSub : U C n e ⊆ Si := by
        by_contra h
        have htr : decide (¬ U C n e ⊆ Si) = true := decide_eq_true h
        rw [helab] at htr
        exact absurd htr (by decide)
      by_cases hlt : e < n
      · exact U_card_le_one_of_lt C n e hlt
      · by_cases hlt2 : e < n + C.size
        · let j' : Fin C.size := ⟨e - n, by omega⟩
          have hej' : n + j'.val = e := by simp [j']; omega
          have hj'notP : j' ∉ privGates C n Si := by
            intro hj'P
            rcases Finset.mem_biUnion.mp heAll with ⟨j, hjQ, hev⟩
            have hjP : j ∈ privGates C n Si := hQsub hjQ
            have hstep : privStep C n Si j j' := ⟨hjP, hj'P, hej'.symm ▸ hev⟩
            have hreach : Relation.ReflTransGen (privStep C n Si) r j :=
              (Finset.mem_filter.mp hjQ).2
            have hj'Q : j' ∈ Q :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.tail hreach hstep⟩
            exact heNotQ (Finset.mem_image.mpr ⟨j', hj'Q, hej'⟩)
          simp only [privGates, Finset.mem_filter, Finset.mem_univ, true_and, hej'] at hj'notP
          have hnot2 : ¬ 2 ≤ (U C n e).card := fun h2e => hj'notP ⟨heSub, h2e⟩
          omega
        · rw [U_eq_empty_of_ge C n e (by omega)]
          simp
    have hexit : ∀ w, w ∈ E ∪ Qwires → ∀ a : Fin n,
        wval C (unitVec a) w = true → lab C n Si Q w = false →
        ∃ e ∈ E, wval C (unitVec a) e = true ∧ lab C n Si Q e = false := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw a hwval hlab
        by_cases hwQ : w ∈ Qwires
        · rcases Finset.mem_image.mp hwQ with ⟨j, hjQ, rfl⟩
          rcases (hgates _ (List.getElem_mem j.isLt)).1 with hop | hop
          · rw [wval_gate_and C (unitVec a) j hop] at hwval
            have hnot : ¬ ∀ u ∈ (C.gates[j.val]'(j.isLt)).inputs,
                u < n + j.val ∧ lab C n Si Q u = true := by
              intro hall
              have htr := (lab_mem_and C n Si Q j hjQ hop).mpr hall
              rw [hlab] at htr
              exact absurd htr (by decide)
            have hex : ∃ u ∈ (C.gates[j.val]'(j.isLt)).inputs,
                ¬ (u < n + j.val ∧ lab C n Si Q u = true) := by
              by_contra hno
              apply hnot
              intro u hu
              by_contra hbad
              exact hno ⟨u, hu, hbad⟩
            rcases hex with ⟨u, hu, hbad⟩
            obtain ⟨hlt, huval⟩ := hwval u hu
            have hulab : lab C n Si Q u = false := by
              cases hl : lab C n Si Q u
              · rfl
              · exact absurd ⟨hlt, hl⟩ hbad
            exact ih u hlt (hchild_mem j hjQ u hu hlt) a huval hulab
          · rw [wval_gate_or C (unitVec a) j hop] at hwval
            obtain ⟨u, hu, hlt, huval⟩ := hwval
            have hulab : lab C n Si Q u = false := by
              cases hl : lab C n Si Q u
              · rfl
              · have htr := (lab_mem_or C n Si Q j hjQ hop).mpr ⟨u, hu, hlt, hl⟩
                rw [hlab] at htr
                exact absurd htr (by decide)
            exact ih u hlt (hchild_mem j hjQ u hu hlt) a huval hulab
        · have hwE : w ∈ E := by
            rcases Finset.mem_union.mp hw with h | h
            · exact h
            · exact absurd h hwQ
          exact ⟨w, hwE, hwval, hlab⟩
    have hhex : ∀ a ∈ U C n oi, ∃ e ∈ E, a ∈ U C n e ∧ lab C n Si Q e = false := by
      intro a ha
      have haw : wval C (unitVec a) (n + r.val) = true := by
        rw [hr_eq]
        exact (Finset.mem_filter.mp ha).2
      obtain ⟨e, heE, hew, helab⟩ :=
        hexit (n + r.val) (Finset.mem_union_right _ hr_mem_Qwires) a haw hlab_r
      exact ⟨e, heE, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hew⟩, helab⟩
    let f : Fin n → ℕ := fun a => if h : a ∈ U C n oi then (hhex a h).choose else 0
    have hcard_le : (U C n oi).card ≤ E.card := by
      apply Finset.card_le_card_of_injOn f
      · intro a ha
        simp only [Finset.mem_coe] at ha ⊢
        simp only [f, ha, ↓reduceDIte]
        exact (hhex a ha).choose_spec.1
      · intro a1 ha1 a2 ha2 heq
        simp only [Finset.mem_coe] at ha1 ha2
        simp only [f, ha1, ha2, ↓reduceDIte] at heq
        set e := (hhex a1 ha1).choose
        have heE : e ∈ E := (hhex a1 ha1).choose_spec.1
        have ha1e : a1 ∈ U C n e := (hhex a1 ha1).choose_spec.2.1
        have helab : lab C n Si Q e = false := (hhex a1 ha1).choose_spec.2.2
        have ha2e : a2 ∈ U C n e := heq ▸ (hhex a2 ha2).choose_spec.2.1
        have hle1 : (U C n e).card ≤ 1 := hfalse_U_le_one e heE helab
        exact Finset.card_le_one.mp hle1 a1 ha1e a2 ha2e
    omega

private theorem main :
    ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) →
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) →
      (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
      (∀ i : Fin m, c i ≤ k) →
      (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) →
      ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hinter h2 hgates hsub hzero hck hcU
  have hdisj : ∀ i j : Fin m, i ≠ j → Disjoint (privGates C n (S i)) (privGates C n (S j)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro g hgi hgj
    simp only [privGates, Finset.mem_filter, Finset.mem_univ, true_and] at hgi hgj
    have hsub_ij : U C n (n + g.val) ⊆ S i ∩ S j := Finset.subset_inter hgi.1 hgj.1
    have hle1 : (S i ∩ S j).card ≤ 1 := hinter i j hij
    have hle2 : (U C n (n + g.val)).card ≤ (S i ∩ S j).card := Finset.card_le_card hsub_ij
    omega
  have hper : ∀ i : Fin m, c i ≤ (privGates C n (S i)).card := by
    intro i
    apply per_index_bound C (S i) (o i) (c i) (h2 i) hgates
    · intro p hp
      exact hsub i p (Finset.mem_filter.mp hp).2
    · exact hzero i
    · exact hck i
    · exact hcU i
  calc ∑ i : Fin m, c i
      ≤ ∑ i : Fin m, (privGates C n (S i)).card := Finset.sum_le_sum (fun i _ => hper i)
    _ = (Finset.univ.biUnion (fun i : Fin m => privGates C n (S i))).card := by
          rw [Finset.card_biUnion]
          intro i _ j _ hij
          exact hdisj i j hij
    _ ≤ (Finset.univ : Finset (Fin C.size)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = C.size := by simp

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  exact PEqualNP.Outside.L_meta_782.main
