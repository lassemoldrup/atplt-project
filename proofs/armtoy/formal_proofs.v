From Coq Require Import Lists.ListSet Arith.

Open Scope bool_scope.

Definition Thread := nat.
Definition Location := nat.

Inductive EventType :=
| W
| R
| F.

Definition eventtype_eqb (t1 t2 : EventType) :=
    match t1, t2 with
    | W, W => true
    | R, R => true
    | F, F => true
    | _, _ => false
    end.

Lemma eventtype_eqb_eq:
    forall (t1 t2 : EventType),
    eventtype_eqb t1 t2 = true <-> t1 = t2.
Proof.
  intros.
  destruct t1, t2;
  split; intro;
  try reflexivity;
  simpl in H; inversion H.
Qed.

Lemma eventtype_eq_dec:
    forall (t1 t2 : EventType),
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  intros.
  destruct t1, t2;
  try (left; reflexivity);
  right; intro H; inversion H.
Qed.

Record Event := {
    id : nat;
    thread : Thread;
    type : EventType;
    loc : Location;
}.

Definition event_eqb (e1 e2 : Event) : bool :=
    (id e1 =? id e2)
    && (thread e1 =? thread e2)
    && (eventtype_eqb (type e1) (type e2))
    && (loc e1 =? loc e2).

Lemma event_eqb_eq:
    forall (e1 e2 : Event),
    event_eqb e1 e2 = true <-> e1 = e2.
Proof.
  split; intro; unfold event_eqb in *;
  destruct e1 as (id1, thread1, type1, loc1);
  destruct e2 as (id2, thread2, type2, loc2).
  - simpl in H.
    repeat rewrite Bool.andb_true_iff in H.
    repeat rewrite Nat.eqb_eq in H.
    rewrite eventtype_eqb_eq in H.
    destruct H as [[[H1 H2] H3] H4]. subst.
    reflexivity.
  - rewrite H. simpl.
    repeat rewrite Bool.andb_true_iff.
    repeat rewrite Nat.eqb_eq.
    rewrite eventtype_eqb_eq.
    split; try split; try split; reflexivity.
Qed.

Lemma event_eqb_refl (e : Event):
    event_eqb e e = true.
Proof.
    rewrite event_eqb_eq. reflexivity.
Qed. 

Lemma Event_eq_dec: forall (x y : Event), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x, y.
  destruct (Nat.eq_dec id0 id1);
  destruct (Nat.eq_dec thread0 thread1);
  destruct (eventtype_eq_dec type0 type1);
  destruct (Nat.eq_dec loc0 loc1); subst;
  try (left; reflexivity);
  right; intro H; inversion H; auto.
Qed.

Definition Edge := (Event * Event)%type.

Lemma Edge_eq_dec: forall (x y : Edge), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x as (v1, v2), y as (w1, w2).
  destruct (Event_eq_dec v1 w1); destruct (Event_eq_dec v2 w2);
    try rewrite e; try rewrite e0;
    try (left;
    reflexivity);
    right;
    injection; auto.
Qed.

Definition cartesian (events1 events2 : set Event) :=
  List.flat_map (fun e1 =>
    List.map (fun e2 => (e1, e2)) events2
  ) events1.

Definition event_union := set_union Event_eq_dec.

Infix "∈" := set_In (at level 72, left associativity).
Infix "×" := cartesian (at level 71, left associativity).
Infix "∪'" := event_union (at level 71, left associativity).

Infix "\in" := set_In (at level 72, left associativity, only parsing).
Infix "\cross" := cartesian (at level 71, left associativity, only parsing).
Infix "\e_cup" := event_union (at level 71, left associativity, only parsing).

Definition event_proj_loc (x : Location) :=
    List.filter (fun e => loc e =? x).

Definition event_proj_thr (i : Thread) :=
    List.filter (fun e => thread e =? i).

Definition event_proj_type (t : EventType) :=
    List.filter (fun e => eventtype_eqb (type e) t).

Lemma event_proj_type_correct:
  forall (events : set Event) (t : EventType) (e : Event),
  e \in (event_proj_type t events) <-> e \in events /\ (type e) = t.
Proof.
  intros.
  split; intros.
  - apply List.filter_In in H as [H1 H2].
    apply eventtype_eqb_eq in H2.
    split; assumption.
  - apply List.filter_In.
    rewrite eventtype_eqb_eq.
    exact H.
Qed.

Lemma event_proj_type_disjoint:
  forall (events : set Event) (t1 t2 : EventType) (e : Event),
  t1 <> t2 -> ~(e \in (event_proj_type t1 events)) \/ ~(e \in (event_proj_type t2 events)).
Proof.
  intros.
  destruct (eventtype_eq_dec (type e) t1) as [H0 | H0].
  - right.
    intro.
    apply event_proj_type_correct in H1 as [_ H1].
    rewrite H0 in H1.
    contradiction.
  - left.
    intro.
    apply event_proj_type_correct in H1 as [_ H1].
    contradiction.
Qed.

Lemma cartesian_correct:
  forall (events1 events2 : set Event) e1 e2,
  e1 \in events1 /\ e2 \in events2 <-> (e1, e2) \in events1 \cross events2.
Proof.
  intros.
  split.
  - intros [H1 H2].
    unfold cartesian.
    apply List.in_flat_map.
    exists (e1).
    split. exact H1.
    apply List.in_map_iff.
    exists e2.
    split; auto.
  - intro.
    apply List.in_flat_map in H as [e1' [H1 H2]].
    apply List.in_map_iff in H2 as [e2' [H3 H4]].
    inversion H3.
    subst.
    split; assumption.
Qed.

Definition edge_union := set_union Edge_eq_dec.

Definition edge_inter := set_inter Edge_eq_dec.

Definition edge_diff := set_diff Edge_eq_dec.

Definition edge_in (x y : Event) (edges : set Edge) := set_In (x, y) edges.

Infix "∪" := edge_union (at level 71, left associativity).
Infix "∩" := edge_inter (at level 71, left associativity).
Infix "\" := edge_diff (at level 71, left associativity).

Infix "\cup" := edge_union (at level 71, left associativity, only parsing).
Infix "\cap" := edge_inter (at level 71, left associativity, only parsing).
Infix "\diff" := edge_diff (at level 71, left associativity, only parsing).

Definition subset [A : Type] (s1 s2 : set A) :=
  forall e, e \in s1 -> e\in s2.

Infix "⊆" := subset (at level 72).

Infix "\subset" := subset (at level 72, only parsing).

Definition equiv [A : Type] (s1 s2 : set A) :=
  s1 \subset s2 /\ s2 \subset s1.

Infix "≡" := equiv (at level 72).

Infix "\equiv" := equiv (at level 72, only parsing).

Lemma in_equiv:
  forall [A : Type] (s1 s2 : set A) (e : A),
  s1 \equiv s2 -> (e \in s1 <-> e\in s2).
Proof.
  intros.
  destruct H.
  unfold subset in H, H0.
  split; intros.
  - apply H. exact H1.
  - apply H0. exact H1.
Qed.

Lemma union_subset_left:
  forall (edges1 edges2 : set Edge),
  edges1 \subset edges1 \cup edges2.
Proof.
  intros.
  unfold subset.
  intros.
  apply set_union_intro.
  left. exact H.
Qed.

Lemma union_subset_right:
  forall (edges1 edges2 : set Edge),
  edges2 \subset edges1 \cup edges2.
Proof.
  unfold subset.
  intros.
  apply set_union_intro.
  right. exact H.
Qed.

Lemma union_both_right:
  forall (edges1 edges2 edges3 : set Edge),
  edges1 \subset edges2 ->
  edges1 \cup edges3 \subset edges2 \cup edges3.
Proof.
  unfold subset.
  intros.
  - apply set_union_elim in H0 as [H0 | H0].
    + apply set_union_intro1. apply H. exact H0.
    + apply set_union_intro2. exact H0.
Qed. 

Lemma diff_subset:
  forall (edges1 edges2 : set Edge),
  edges1 \diff edges2 \subset edges1.
Proof.
  unfold subset.
  intros.
  apply set_diff_elim1 in H.
  exact H.
Qed.

Lemma union_commutes:
    forall edges1 edges2,
    edges1 \cup edges2 \equiv edges2 \cup edges1.
intros.
  split; unfold subset; intros;
  apply set_union_elim in H;
  apply set_union_intro;
  apply or_comm; exact H.
Qed.

Definition identity (s : set Event) : set Edge :=
    List.map (fun e => (e, e)) s.

Definition inverse :=
    @List.map Edge Edge (fun e => (snd e, fst e)).

Definition composition (edges1 edges2 : set Edge) :=
    List.flat_map (fun e1 =>
        List.map (fun e2 => (fst e1, snd e2))
            (List.filter (fun e2 => event_eqb (snd e1) (fst e2)) edges2)
    ) edges1.

Definition proj (predicate : Event -> bool) :=
    List.filter (
        fun (e : Edge) =>
        let (v1, v2) := e in
        (predicate v1) && (predicate v2)
    ).

Definition proj_loc (x : Location) :=
    proj (fun e => loc e =? x).

Definition proj_thr (i : Thread) :=
    proj (fun e => thread e =? i).

Definition external (edges po : set Edge) :=
    edge_diff edges po.

Lemma identity_correct (s : set Event):
    forall (e1 e2 : Event), (e1, e2) \in (identity s) <-> e1 = e2 /\ e1 \in s.
Proof.
    intros.
    unfold identity.
    rewrite List.in_map_iff.
    split.
    - intro.
      destruct H as [e [H1 H2]].
      inversion H1. subst.
      auto.
    - intro.
      exists (e1). destruct H.
      subst. auto.
Qed.

Lemma inverse_correct (edges : set Edge):
    forall (e1 e2 : Event), (e1, e2) \in edges <-> (e2, e1) \in inverse edges.
Proof.
    intros.
    unfold inverse.
    rewrite List.in_map_iff.
    split.
    - intro.
      exists (e1, e2).
      auto.
    - intro.
      destruct H as [e [H1 H2]].
      destruct e. simpl in H1.
      inversion H1. subst. exact H2.
Qed.

Lemma composition_correct (edges1 edges2 : set Edge):
    forall (e1 e2 : Event),
    (e1, e2) \in composition edges1 edges2 <-> exists e3, (e1, e3) \in edges1 /\ (e3, e2) \in edges2.
Proof.
    intros.
    unfold composition.
    rewrite List.in_flat_map.
    split; intro.
    - destruct H as [edge1 [H1 H2]].
      rewrite List.in_map_iff in H2.
      destruct H2 as [edge2 [H3 H4]].
      rewrite List.filter_In in H4.
      destruct H4 as [H5 H6].
      rewrite event_eqb_eq in H6.
      destruct edge1, edge2. inversion H3.
      simpl in *. subst.
      eauto.
    - destruct H as [e3 [H1 H2]].
      exists (e1, e3).
      split. exact H1.
      apply List.in_map_iff.
      exists (e3, e2).
      split. auto.
      apply List.filter_In.
      split. apply H2.
      simpl.
      apply event_eqb_refl.
Qed.

Lemma proj_correct:
    forall (edges : set Edge) (predicate : Event -> bool) (e1 e2 : Event),
    (e1, e2) \in edges -> (e1, e2) \in (proj predicate edges) <-> predicate e1 && predicate e2 = true.
Proof.
    intros.
    unfold set_In, proj.
    rewrite List.filter_In.
    split; intro.
    - destruct H0. exact H1.
    - split. exact H. exact H0.
Qed.

Lemma proj_subset:
    forall (edges : set Edge) (predicate : Event -> bool),
    proj predicate edges \subset edges.
Proof.
    intros.
    unfold proj.
    unfold subset.
    intro.
    apply List.filter_In.
Qed.

Lemma proj_of_subset:
  forall (edges1 edges2 : set Edge) (predicate : Event -> bool),
  edges1 \subset edges2 -> proj predicate edges1 \subset proj predicate edges2.
Proof.
  intros.
  unfold subset.
  intros.
  apply List.filter_In in H0 as [H1 H2].
  apply List.filter_In.
  split.
  - apply H. exact H1.
  - exact H2.
Qed.

Lemma proj_union:
    forall (edges1 edges2 : set Edge) predicate,
    proj predicate (edges1 \cup edges2) \equiv proj predicate edges1 \cup proj predicate edges2.
Proof.
  intros.
  unfold equiv.
  split; unfold subset; intros; destruct e as [e1 e2].
  - apply List.filter_In in H as [H1 H2].
    apply set_union_elim in H1 as [H1 | H1].
    + apply union_subset_left.
      rewrite proj_correct; assumption.
    + apply union_subset_right.
      rewrite proj_correct; assumption.
  - apply set_union_elim in H as [H | H];
    apply List.filter_In;
    apply List.filter_In in H;
    destruct H as [H1 H2];
    split; try exact H2.
    + eapply union_subset_left.
      apply H1.
    + eapply union_subset_right.
      apply H1.
Qed.

Lemma proj_loc_correct:
    forall (edges : set Edge) (x : Location) (e1 e2 : Event),
    (e1, e2) \in edges -> (e1, e2) \in (proj_loc x edges) <-> loc e1 = x /\ loc e2 = x.
Proof.
    intros.
    unfold proj_loc.
    rewrite proj_correct.
    - rewrite Bool.andb_true_iff.
      repeat rewrite Nat.eqb_eq.
      split; intro; auto.
    - exact H.
Qed.

Lemma proj_thr_correct:
    forall (edges : set Edge) (i : Thread) (e1 e2 : Event),
    (e1, e2) \in edges -> (e1, e2) \in (proj_thr i edges) <-> thread e1 = i /\ thread e2 = i.
Proof.
    intros.
    unfold proj_thr.
    rewrite proj_correct.
    - rewrite Bool.andb_true_iff.
      repeat rewrite Nat.eqb_eq.
      split; intro; auto.
    - exact H.
Qed.

Definition partial (edges : set Edge) :=
    (forall a, (a, a) \in edges)
    /\ (forall a b c, (a, b) \in edges -> (b, c) \in edges -> (a, c) \in edges)
    /\ (forall a b, (a, b) \in edges -> (b, a) \in edges -> a = b).

Definition total (E : set Event) (edges : set Edge) :=
    partial edges /\ forall a b,
    set_In a E -> set_In b E -> (a, b) \in edges \/ (b, a) \in edges.

Definition acyclic (edges : set Edge) : Prop.
Admitted.

Definition pairwise_same_loc (edges : set Edge) :=
  forall e, e \in edges -> (loc (fst e) = loc (snd e)).

Definition in_universe (edges : set Edge) (events : set Event) :=
  forall e, e \in edges -> fst e \in events /\ snd e \in events.

Lemma acyclic_if_subset:
    forall edges1 edges2,
    acyclic edges2 ->
    edges1 \subset edges2 ->
    acyclic edges1.
Admitted.

Lemma acyclic_per_loc:
    forall (edges : set Edge),
    pairwise_same_loc edges ->
    acyclic edges <-> forall x, acyclic (proj_loc x edges).
Admitted.

Lemma pairwise_same_loc_union:
    forall edges1 edges2,
    pairwise_same_loc edges1 ->
    pairwise_same_loc edges2 ->
    pairwise_same_loc (edges1 \cup edges2).
Proof.
  intros.
  unfold pairwise_same_loc.
  intros.
  apply set_union_elim in H1.
  destruct (H1).
  - apply H in H2. exact H2.
  - apply H0 in H2. exact H2.
Qed.

Lemma pairwise_same_loc_diff:
    forall edges1 edges2,
    pairwise_same_loc edges1 ->
    pairwise_same_loc (edges1 \diff edges2).
Proof.
  intros.
  unfold pairwise_same_loc.
  intros.
  apply set_diff_elim1 in H0.
  apply H in H0. exact H0.
Qed.

Lemma pairwise_same_loc_inverse:
    forall edges,
    pairwise_same_loc edges ->
    pairwise_same_loc (inverse edges).
Proof.
  intros.
  unfold pairwise_same_loc.
  intros.
  destruct e as [e1 e2].
  apply inverse_correct in H0.
  apply H in H0.
  simpl in *.
  rewrite H0. reflexivity.
Qed.

Lemma pairwise_same_loc_composition:
    forall edges1 edges2,
    pairwise_same_loc edges1 ->
    pairwise_same_loc edges2 ->
    pairwise_same_loc (composition edges1 edges2).
Proof.
  intros.
  unfold pairwise_same_loc.
  intros.
  destruct e as [e1 e2].
  rewrite composition_correct in H1.
  destruct H1 as [e3 [H2 H3]].
  apply H in H2.
  apply H0 in H3.
  simpl in *.
  rewrite H2, H3. reflexivity.
Qed.

Record Trace := {
    E_set : set Event;
    po_edges : set Edge;
    rf_edges : set Edge;
    mo_edges : set Edge;
    dob_edges : set Edge;
}.

Section Traces.

Variable t : Trace.

Definition E := E_set t.
Definition Reads := event_proj_type R E.
Definition Writes := event_proj_type W E.
Definition Fences := event_proj_type F E.

Definition po := po_edges t.
Definition rf := rf_edges t.
Definition mo := mo_edges t.
Definition dob := dob_edges t.

Definition fr :=
    composition (inverse rf) mo.

Definition rfe :=
    rf \diff po.

Definition fre :=
    fr \diff po.

Definition moe :=
    mo \diff po.

Lemma rfe_is_subset:
  rfe \subset rf.
Proof. apply diff_subset. Qed.

Lemma fre_is_subset:
  fre \subset fr.
Proof. apply diff_subset. Qed.

Lemma moe_is_subset:
  moe \subset mo.
Proof. apply diff_subset. Qed.

Record partial_trace := {
  po_total_per_loc : forall i, total (event_proj_thr i E) (proj_thr i po);
  rf_total : total (event_proj_type R E) (inverse rf);
  rf_same_loc : pairwise_same_loc rf;
  mo_same_loc : pairwise_same_loc mo;
  po_in_universe : in_universe po E;
  rf_in_universe : in_universe rf E;
  mo_in_universe : in_universe mo E;
  fr_in_universe : in_universe fr E;
}.
    

Lemma fr_same_loc:
  partial_trace -> pairwise_same_loc fr.
Proof.
  intros.
  apply pairwise_same_loc_composition.
  - apply pairwise_same_loc_inverse.
    exact (rf_same_loc H).
  - exact (mo_same_loc H).
Qed.

Definition sc_per_location :=
    forall (x : Location),
    acyclic (proj_loc x po \cup proj_loc x rf \cup proj_loc x mo \cup proj_loc x fr).

Definition external_coherence :=
    acyclic (dob \cup rfe \cup moe \cup fre).

Definition armtoy_consistent :=
    sc_per_location /\ external_coherence.

Definition c11_relaxed := sc_per_location.

Definition sc :=
  acyclic (po \cup rf \cup mo \cup fr).

Lemma empty_dob_is_relaxed:
  dob = empty_set _ ->  
  partial_trace ->
  c11_relaxed <-> armtoy_consistent.
Proof.
  intros.
  unfold c11_relaxed, armtoy_consistent.
  split; intro.
  - split. assumption.
    unfold external_coherence.
    apply acyclic_per_loc.
    + repeat apply pairwise_same_loc_union;
      try (apply pairwise_same_loc_diff).
      * rewrite H.
        unfold pairwise_same_loc.
        intros.
        inversion H2.
      * exact (rf_same_loc H0).
      * apply (mo_same_loc H0).
      * apply (fr_same_loc H0).
    + intro.
      eapply acyclic_if_subset.
      * apply (H1 x).
      * unfold subset. intros.
        repeat (apply proj_union in H2;
         apply set_union_elim in H2;
         destruct H2 as [H2 | H2]).
        --rewrite H in H2. inversion H2.
        --do 2(apply set_union_intro1).
          apply set_union_intro2.
          eapply proj_of_subset.
          ++apply diff_subset.
          ++apply H2.
        --apply set_union_intro1.
          apply set_union_intro2.
          eapply proj_of_subset.
          ++apply diff_subset.
          ++apply H2.
        --apply set_union_intro2.
          eapply proj_of_subset.
          ++apply diff_subset.
          ++apply H2.
  - destruct H1 as [H1 _].
    exact H1.
Qed.

Lemma po_dob_is_sc:
  dob = po ->  
  partial_trace ->
  sc <-> armtoy_consistent.
Proof.
  intros.
  unfold sc, armtoy_consistent, sc_per_location, external_coherence.
  split.
  - intros.
    rewrite H.
    split.
    + intros.
      eapply acyclic_if_subset. apply H1.
      unfold subset. intros.
      repeat (apply set_union_elim in H2;
       destruct H2 as [H2 | H2]);
      [do 3 apply set_union_intro1 | do 2 apply set_union_intro1 | apply set_union_intro1 | ];
      try (apply set_union_intro2);
      eapply proj_subset;
      exact H2.
    + eapply acyclic_if_subset. apply H1.
      unfold subset. intros.
      repeat (apply set_union_elim in H2;
       destruct H2 as [H2 | H2]);
       [do 3 apply set_union_intro1 | do 2 apply set_union_intro1 | apply set_union_intro1 | ];
       try (apply set_union_intro2);
       try (exact H2);
       try (eapply diff_subset);
       exact H2.
  - intros [_ H1].
    eapply acyclic_if_subset. apply H1.
    unfold subset. intros.
    rewrite H.
    repeat (apply set_union_elim in H2;
     destruct H2 as [H2 | H2]);
    destruct (List.In_dec Edge_eq_dec e po) as [H3 | H3];
    try (do 3 apply set_union_intro1; exact H3);
    try contradiction;
    [do 2 apply set_union_intro1 | apply set_union_intro1 | ];
    apply set_union_intro2;
    apply set_diff_intro; assumption.
Qed.

Definition ppo :=
  po \cap ((Reads \cross (Reads \e_cup Writes \e_cup Fences))
    \cup (Fences \cross (Reads \e_cup Writes \e_cup Fences))
    \cup (Writes \cross (Writes \e_cup Fences))).

Lemma ppo_rewrite:
  partial_trace ->
  ppo \equiv po \diff (Writes \cross Reads).
Proof.
  unfold ppo.
  split; unfold subset; intros; destruct e as [e1 e2].
  - apply set_inter_elim in H0 as [H1 H2].
    apply set_diff_intro; try exact H1.
    intro.
    apply cartesian_correct in H0 as [H3 H4].
    repeat apply set_union_elim in H2 as [H2 | H2];
    apply cartesian_correct in H2 as [H5 H6];
    repeat apply set_union_elim in H6 as [H6 | H6].
    + destruct (event_proj_type_disjoint E R W e1) as [H7 | H7]; auto.
      intro. inversion H0.
    + destruct (event_proj_type_disjoint E R W e1) as [H7 | H7]; auto.
      intro. inversion H0.
    + destruct (event_proj_type_disjoint E R W e1) as [H7 | H7]; auto.
      intro. inversion H0.
    + destruct (event_proj_type_disjoint E F W e1) as [H7 | H7]; auto.
      intro. inversion H0.
    + destruct (event_proj_type_disjoint E F W e1) as [H7 | H7]; auto.
      intro. inversion H0.
    + destruct (event_proj_type_disjoint E F W e1) as [H7 | H7]; auto.
      intro. inversion H0.
    + destruct (event_proj_type_disjoint E W R e2) as [H7 | H7]; auto.
      intro. inversion H0.
    + destruct (event_proj_type_disjoint E F R e2) as [H7 | H7]; auto.
      intro. inversion H0.
  - apply set_diff_elim1 in H0 as H1.
    apply set_diff_elim2 in H0 as H2.
    apply set_inter_intro. exact H1.
    apply (po_in_universe H) in H1 as [H3 H4].
    simpl in H3, H4.
    destruct (type e1) eqn:EQ1; destruct (type e2) eqn:EQ2;
    assert (e1 \in event_proj_type (type e1) E) as H5; try (apply event_proj_type_correct; auto);
    assert (e2 \in event_proj_type (type e2) E) as H6; try (apply event_proj_type_correct; auto);
    rewrite EQ1 in H5; rewrite EQ2 in H6.
    + apply set_union_intro2.
      apply cartesian_correct.
      split.
      * auto.
      * apply set_union_intro1. auto.
    + exfalso. apply H2.
      apply cartesian_correct.
      split; auto.
    + apply set_union_intro2.
      apply cartesian_correct.
      split. auto.
      apply set_union_intro2.
      auto.
    + do 2 apply set_union_intro1.
      apply cartesian_correct.
      split. auto.
      apply set_union_intro1.
      apply set_union_intro2.
      auto.
    + do 2 apply set_union_intro1.
      apply cartesian_correct.
      split. auto.
      do 2 apply set_union_intro1.
      auto.
    + do 2 apply set_union_intro1.
      apply cartesian_correct.
      split. auto.
      apply set_union_intro2.
      auto.
    + apply set_union_intro1.
      apply set_union_intro2.
      apply cartesian_correct.
      split. auto.
      apply set_union_intro1.
      apply set_union_intro2.
      auto.
    + apply set_union_intro1.
      apply set_union_intro2.
      apply cartesian_correct.
      split. auto.
      do 2 apply set_union_intro1.
      auto.
    + apply set_union_intro1.
      apply set_union_intro2.
      apply cartesian_correct.
      split. auto.
      apply set_union_intro2.
      auto.
Qed.

Definition tso_consistent := sc_per_location /\ acyclic (ppo \cup rfe \cup moe \cup fre).

Lemma ppo_dob_is_tso:
  dob = (po \diff (Writes \cross Reads)) ->  
  partial_trace ->
  tso_consistent <-> armtoy_consistent.
Proof.
  intros.
  pose proof (ppo_rewrite H0) as H1.
  unfold tso_consistent, armtoy_consistent.
  split; intros [H2 H3].
  - split. exact H2.
    unfold external_coherence.
    eapply acyclic_if_subset. exact H3.
    repeat apply union_both_right.
    rewrite H.
    unfold equiv in H1. destruct H1. auto.
  - split. exact H2.
    unfold external_coherence in H3.
    eapply acyclic_if_subset. exact H3.
    repeat apply union_both_right.
    rewrite H.
    unfold equiv in H1. destruct H1. auto.
Qed.

End Traces.