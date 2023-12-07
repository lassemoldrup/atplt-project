From Coq Require Import Arith Decidable.
Require Import Hahn.

Open Scope bool_scope.

Notation "P +++e Q" := (set_union P Q) (at level 50, left associativity, only parsing).

Notation "P --- Q" := (minus_rel P Q) (at level 50, left associativity, only parsing).

Notation "P &&& Q" := (inter_rel P Q) (at level 50, left associativity, only parsing).

Notation "P \times Q" := (cross_rel P Q) (at level 50, left associativity, only parsing).

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

Definition event_proj_loc (x : Location) (events : Event -> Prop) :=
    set_inter events (fun e => loc e = x).

Definition event_proj_thr (i : Thread) (events : Event -> Prop) :=
  set_inter events (fun e => thread e = i).

Definition event_proj_type (t : EventType) (events : Event -> Prop) :=
  set_inter events (fun e => type e = t).

Lemma proj_loc_dec:
  forall (events : Event -> Prop) x,
  (forall e, decidable (events e)) -> forall e, decidable (event_proj_loc x events e).
Proof.
  intros.
  destruct (H e); destruct (Nat.eq_dec (loc e) x).
  - left.
    split; auto.
  - right.
    intro.
    destruct H1.
    contradiction.
  - right.
    intro.
    destruct H1.
    contradiction.
  - right.
    intro.
    destruct H1.
    contradiction.
Qed.

Lemma event_proj_type_disjoint:
  forall (events : Event -> Prop) (t1 t2 : EventType) (e : Event),
  t1 <> t2 -> ~(event_proj_type t1 events e) \/ ~(event_proj_type t2 events e).
Proof.
  intros.
  destruct (eventtype_eq_dec (type e) t1) as [H0 | H0].
  - right.
    intro.
    destruct H1 as [_ H1].
    rewrite H0 in H1.
    contradiction.
  - left.
    intro.
    destruct H1 as [_ H1].
    contradiction.
Qed.

Notation EventRel := (relation Event).

Definition proj_loc (x : Location) :=
  restr_rel (fun e => loc e = x).

Definition proj_thr (i : Thread) :=
  restr_rel (fun e => thread e = i).

Definition external (edges po : EventRel) :=
  edges --- po.

Definition pairwise_same_loc (edges : EventRel) :=
  forall e1 e2, edges e1 e2 -> loc e1 = loc e2.

Definition in_universe (events : Event -> Prop) (edges : EventRel) :=
  forall e1 e2, edges e1 e2 -> events e1 /\ events e2.

Lemma proj_loc_inclusion:
  forall (r1 r2 : EventRel) x,
  r1 <<= r2 -> proj_loc x r1 <<= proj_loc x r2.
Proof.
  intros.
  apply restr_rel_mori.
  - apply set_subset_refl.
  - exact H.
Qed.

Lemma proj_loc_union:
  forall x r1 r2 e1 e2,
  (proj_loc x r1 +++ proj_loc x r2) e1 e2 ->
  loc e1 = x /\ loc e2 = x.
Proof.
  intros.
  unfold proj_loc, restr_rel in H.
  destruct H; destruct H as [_ H]; exact H.
Qed. 

Lemma pairwise_same_loc_proj_loc:
  forall x edges,
  pairwise_same_loc (proj_loc x edges).
Proof.
  intros.
  intros e1 e2 H.
  destruct H as [H1 [H2 H3]].
  rewrite H2, H3. reflexivity.
Qed.

Lemma pairwise_same_loc_trans:
  forall edges,
  pairwise_same_loc edges ->
  pairwise_same_loc (clos_trans edges).
Proof.
  intros.
  unfold pairwise_same_loc. intros.
  induction H0.
  - intros.
    apply H.
    apply H0.
  - rewrite IHclos_trans1, IHclos_trans2. reflexivity.
Qed.

Lemma pairwise_same_loc_proj_loc_inclusion:
  forall edges x e1 e2,
  pairwise_same_loc edges ->
  loc e1 = x ->
  edges e1 e2 -> proj_loc x edges e1 e2.
Proof.
  intros.
  unfold proj_loc, restr_rel.
  split.
  - exact H1.
  - unfold pairwise_same_loc in H.
    apply H in H1.
    split.
    + exact H0.
    + rewrite <- H1. exact H0.
Qed.

Lemma pairwise_same_loc_proj_loc_clos_trans_inclusion:
  forall edges x e1 e2,
  pairwise_same_loc edges ->
  loc e1 = x ->
  clos_trans edges e1 e2 -> clos_trans (proj_loc x edges) e1 e2.
Proof.
  intros.
  induction H1.
  - apply t_step.
    apply pairwise_same_loc_proj_loc_inclusion; auto.
  - eapply t_trans.
    + apply IHclos_trans1.
      exact H0.
    + pose proof (pairwise_same_loc_trans edges H).
      unfold pairwise_same_loc in H1.
      apply H1 in H1_.
      apply H1 in H1_0.
      apply IHclos_trans2.
      rewrite <- H1_, <- H0. reflexivity.
Qed.

Lemma pairwise_same_loc_proj_loc_clos_trans_distrib:
  forall edges x,
  pairwise_same_loc edges ->
  proj_loc x (clos_trans edges) <--> clos_trans (proj_loc x edges).
Proof.
  intros.
  split; intros.
  - unfold inclusion. intros e1 e2 H0.
    unfold proj_loc, restr_rel in H0.
    destruct H0 as [H1 [H2 H3]].
    induction H1.
    + apply t_step.
      unfold proj_loc, restr_rel.
      auto.
    + pose proof (pairwise_same_loc_trans edges H).
      apply H0 in H1_0.
      rewrite H3 in H1_0.
      specialize (IHclos_trans1 H2 H1_0).
      specialize (IHclos_trans2 H1_0 H3).
      eapply t_trans.
      apply IHclos_trans1. apply IHclos_trans2.
  - unfold inclusion. intros e1 e2 H0.
    unfold proj_loc, restr_rel.
    split.
    + eapply inclusion_t_t.
      * apply inclusion_restr.
      * apply H0.
    + apply clos_trans_restrD in H0.
      exact H0.
Qed.

Lemma acyclic_per_loc:
  forall (edges : EventRel),
  pairwise_same_loc edges ->
  acyclic edges <-> forall x, acyclic (proj_loc x edges).
Proof.
  intros.
  split; intros.
  - eapply inclusion_acyclic.
    apply inclusion_restr.
    exact H0.
  - unfold acyclic, irreflexive. intros e H1.
    specialize (H0 (loc e)).
    unfold acyclic, irreflexive in H0.
    apply (H0 e).
    apply (pairwise_same_loc_proj_loc_clos_trans_distrib _ _ H).
    unfold proj_loc, restr_rel.
    split; auto.
Qed.

Lemma pairwise_same_loc_union:
    forall edges1 edges2,
    pairwise_same_loc edges1 ->
    pairwise_same_loc edges2 ->
    pairwise_same_loc (edges1 +++ edges2).
Proof.
  intros.
  unfold pairwise_same_loc.
  intros.
  destruct H1.
  - exact (H e1 e2 H1).
  - exact (H0 e1 e2 H1).
Qed.

Lemma pairwise_same_loc_diff:
    forall edges1 edges2,
    pairwise_same_loc edges1 ->
    pairwise_same_loc (edges1 --- edges2).
Proof.
  intros.
  unfold pairwise_same_loc.
  intros.
  destruct H0.
  exact (H e1 e2 H0).
Qed.

Lemma pairwise_same_loc_inverse:
    forall edges,
    pairwise_same_loc edges <->
    pairwise_same_loc edges ^{-1}.
Proof.
  intros.
  split; intros.
  - unfold pairwise_same_loc. intros.
    unfold transp in H0.
    symmetry.
    apply H.
    exact H0.
  - unfold pairwise_same_loc. intros.
    assert (edges^{-1} e2 e1). apply H0.
    symmetry.
    apply H.
    exact H1.
Qed.

Lemma pairwise_same_loc_composition:
    forall edges1 edges2,
    pairwise_same_loc edges1 ->
    pairwise_same_loc edges2 ->
    pairwise_same_loc (edges1 ;; edges2).
Proof.
  intros.
  unfold pairwise_same_loc.
  intros.
  destruct H1 as [e3 [H1 H2]].
  apply H in H1.
  apply H0 in H2.
  rewrite H1, H2. reflexivity.
Qed.

Record Execution := {
    E : Event -> Prop;
    po : EventRel;
    rf : EventRel;
    dob : EventRel;
    mo : EventRel;
}.

Section Executions.

Definition Reads exe := event_proj_type R (E exe).
Definition Writes exe := event_proj_type W (E exe).
Definition Fences exe := event_proj_type F (E exe).

Definition fr exe :=
    (rf exe)^{-1} ;; mo exe.

Definition rfe exe :=
    rf exe --- po exe.

Definition fre exe :=
    fr exe --- po exe.

Definition moe exe :=
    mo exe --- po exe.

Lemma rfe_inclusion:
  forall exe,
  rfe exe <<= rf exe.
Proof. intro. apply inclusion_minus_rel. Qed.

Lemma fre_inclusion:
  forall exe,
  fre exe <<= fr exe.
Proof. intro. apply inclusion_minus_rel. Qed.

Lemma moe_inclusion:
  forall exe,
  moe exe <<= mo exe.
Proof. intro. apply inclusion_minus_rel. Qed.

Definition total_function {A : Type} (dom : A -> Prop) (r : relation A) :=
  functional r /\ forall e1, dom e1 -> exists e2, r e1 e2.

Record partial_execution exe := {
  po_total_per_loc : forall i, is_total (event_proj_thr i (E exe)) (proj_thr i (po exe));
  po_no_crossthread : forall e1 e2, thread e1 <> thread e2 -> ~(po exe e1 e2);
  rf_transp_total_func : total_function (event_proj_type R (E exe)) (rf exe)^{-1};
  rf_same_loc : pairwise_same_loc (rf exe);
  mo_same_loc : pairwise_same_loc (mo exe);
  po_in_universe : in_universe (E exe) (po exe);
  rf_in_universe : in_universe (E exe) (rf exe);
  mo_in_universe : in_universe (E exe) (mo exe);
  dob_inclusion : dob exe <<= po exe;
  decidable_E : forall e, decidable ((E exe) e);
  decidable_po : forall e1 e2, decidable ((po exe) e1 e2);
}.

Record total_execution exe := {
  partial_exe : partial_execution exe;
  total_mo : forall x, is_total (event_proj_loc x (E exe)) (proj_loc x (mo exe));
}.

Lemma fr_same_loc:
  forall exe,
  partial_execution exe -> pairwise_same_loc (fr exe).
Proof.
  intros.
  apply pairwise_same_loc_composition.
  - rewrite <- pairwise_same_loc_inverse.
    exact (rf_same_loc exe H).
  - exact (mo_same_loc exe H).
Qed.

Lemma fr_in_universe:
  forall exe,
  partial_execution exe -> in_universe (E exe) (fr exe).
Proof.
  intros.
  intros e1 e2 H0.
  destruct H0 as [e3 [H0 H1]].
  unfold transp in H0.
  split.
  - apply (rf_in_universe _ H e3 e1 H0).
  - apply (mo_in_universe _ H e3 e2 H1).
Qed.

Definition scpl_rel (x : Location) (exe : Execution) :=
  proj_loc x (po exe)
  +++ proj_loc x (rf exe)
  +++ proj_loc x (mo exe)
  +++ proj_loc x (fr exe).

Definition ec_rel (exe : Execution) :=
  dob exe +++ rfe exe +++ moe exe +++ fre exe.

Definition sc_per_location (exe : Execution) :=
    forall (x : Location),
    acyclic (scpl_rel x exe).

Definition external_coherence (exe : Execution) :=
    acyclic (ec_rel exe).

Definition armtoy_consistent (exe : Execution) :=
    sc_per_location exe /\ external_coherence exe.

Definition c11_relaxed (exe : Execution) := sc_per_location exe.

Definition sc (exe : Execution) :=
  acyclic (po exe +++ rf exe +++ mo exe +++ fr exe).

Lemma scpl_same_loc:
  forall x exe,
  pairwise_same_loc (scpl_rel x exe).
Proof.
  intros.
  intros e1 e2 H.
  unfold scpl_rel in H.
  repeat destruct H as [H | H];
  apply pairwise_same_loc_proj_loc in H;
  exact H.
Qed.

Lemma scpl_all_x:
  forall x exe e1 e2,
  scpl_rel x exe e1 e2 -> loc e1 = x /\ loc e2 = x.
Proof.
  intros.
  repeat destruct H; exact H0.
Qed.

Lemma scpl_trans_all_x:
  forall x exe e1 e2,
  clos_trans (scpl_rel x exe) e1 e2 -> loc e1 = x /\ loc e2 = x.
Proof.
  intros.
  induction H.
  - apply scpl_all_x in H. exact H.
  - destruct IHclos_trans1 as [H1 _].
    destruct IHclos_trans2 as [_ H2].
    split; auto.
Qed.

Lemma scpl_rel_in_universe:
  forall x exe,
  partial_execution exe ->
  in_universe (E exe) (scpl_rel x exe).
Proof.
  intros.
  intros e1 e2 H0.
  repeat destruct H0 as [H0 | H0];
  apply inclusion_restr in H0.
  - exact (po_in_universe _ H _ _ H0).
  - exact (rf_in_universe _ H _ _ H0).
  - exact (mo_in_universe _ H _ _ H0).
  - exact (fr_in_universe _ H _ _ H0).
Qed.

Lemma scpl_rel_trans_in_universe:
  forall x exe,
  partial_execution exe ->
  in_universe (E exe) (clos_trans (scpl_rel x exe)).
Proof.
  intros.
  intros e1 e2 H0.
  induction H0.
  - exact (scpl_rel_in_universe _ _ H x0 y H0).
  - split.
    + exact (proj1 IHclos_trans1).
    + exact (proj2 IHclos_trans2).
Qed.

Lemma ec_rel_in_universe:
  forall exe,
  partial_execution exe ->
  in_universe (E exe) (ec_rel exe).
Proof.
  intros.
  intros e1 e2 H0.
  repeat destruct H0 as [H0 | H0].
  - apply (dob_inclusion _ H) in H0. exact (po_in_universe _ H _ _ H0).
  - apply rfe_inclusion in H0. exact (rf_in_universe _ H _ _ H0).
  - apply moe_inclusion in H0. exact (mo_in_universe _ H _ _ H0).
  - apply fre_inclusion in H0. exact (fr_in_universe _ H _ _ H0).
Qed.

Lemma ec_rel_trans_in_universe:
  forall exe,
  partial_execution exe ->
  in_universe (E exe) (clos_trans (ec_rel exe)).
Proof.
  intros.
  intros e1 e2 H0.
  induction H0.
  - exact (ec_rel_in_universe _ H x y H0).
  - split.
    + exact (proj1 IHclos_trans1).
    + exact (proj2 IHclos_trans2).
Qed.

Lemma empty_dob_is_relaxed:
  forall exe,
  dob exe <--> ∅₂ ->  
  partial_execution exe ->
  c11_relaxed exe <-> armtoy_consistent exe.
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
      * exact (rf_same_loc exe H0).
      * apply (mo_same_loc exe H0).
      * apply (fr_same_loc exe H0).
    + intro.
      eapply inclusion_acyclic;
      try apply (H1 x).
      * unfold inclusion. intros e1 e2 H2.
        repeat (apply restr_union in H2;
          destruct H2 as [H2 | H2]).
        --inversion H2. apply H in H3. contradiction.
        --do 2 left. right.
          eapply proj_loc_inclusion.
          ++apply rfe_inclusion.
          ++exact H2.
        --left. right.
          eapply proj_loc_inclusion.
          ++apply moe_inclusion.
          ++exact H2.
        --right.
          eapply proj_loc_inclusion.
          ++apply fre_inclusion.
          ++exact H2.
  - destruct H1 as [H1 _].
    exact H1.
Qed.

Lemma po_dob_is_sc:
  forall exe,
  dob exe <--> po exe ->  
  partial_execution exe ->
  sc exe <-> armtoy_consistent exe.
Proof.
  intros.
  unfold sc, armtoy_consistent, sc_per_location, external_coherence.
  split.
  - intros.
    split.
    + intros.
      eapply inclusion_acyclic; try apply H1.
      repeat apply inclusion_union_mon; apply inclusion_restr.
    + eapply inclusion_acyclic; try apply H1.
      repeat apply inclusion_union_mon; try apply inclusion_minus_rel.
      apply (dob_inclusion _ H0).
  - intros [_ H1].
    unfold ec_rel in H1.
    rewrite H in H1.
    eapply inclusion_acyclic; try apply H1.
    intros e1 e2 H2.
    destruct (decidable_po _ H0 e1 e2).
    + repeat left. exact H3.
    + repeat destruct H2 as [H2 | H2].
      * contradiction.
      * do 2 left. right. unfold rfe, minus_rel. auto.
      * left. right. unfold moe, minus_rel. auto.
      * right. unfold fre, minus_rel. auto.
Qed.

Definition ppo (exe : Execution) :=
  po exe &&& ((Reads exe \times (Reads exe +++e Writes exe +++e Fences exe))
    +++ (Fences exe \times (Reads exe +++e Writes exe +++e Fences exe))
    +++ (Writes exe \times (Writes exe +++e Fences exe))).

Lemma ppo_rewrite:
  forall exe,
  partial_execution exe ->
  ppo exe <--> po exe --- (Writes exe \times Reads exe).
Proof.
  unfold ppo.
  split; unfold inclusion; intros e1 e2 H0.
  - destruct H0.
    unfold minus_rel.
    split; auto.
    intro.
    destruct H2.
    repeat destruct H1 as [H1 | H1].
    + destruct H1.
      destruct (event_proj_type_disjoint (E exe) R W e1) as [H5 | H5]; auto.
      intro. inversion H5.
    + destruct H1.
      destruct (event_proj_type_disjoint (E exe) F W e1) as [H5 | H5]; auto.
      intro. inversion H5.
    + destruct H1.
      destruct H4.
      * destruct (event_proj_type_disjoint (E exe) W R e2) as [H5 | H5]; auto.
        intro. inversion H5.
      * destruct (event_proj_type_disjoint (E exe) F R e2) as [H5 | H5]; auto.
        intro. inversion H5.
  - destruct H0.
    split; auto.
    pose proof (po_in_universe exe H e1 e2 H0) as [H2 H3].
    assert (event_proj_type (type e1) (E exe) e1) as H4; try (split; auto).
    assert (event_proj_type (type e2) (E exe) e2) as H5; try (split; auto).
    destruct (type e1), (type e2).
    + right.
      split; auto.
      left. auto.
    + exfalso.
      apply H1.
      split; auto.
    + right.
      split; auto.
      right. auto.
    + do 2 left.
      split; auto.
      left. right. auto.
    + do 2 left.
      split; auto.
      do 2 left. auto.
    + do 2 left.
      split; auto.
      right. auto.
    + left. right.
      split; auto.
      left. right. auto.
    + left. right.
      split; auto.
      do 2 left. auto.
    + left. right.
      split; auto.
      right. auto.
Qed.

Definition tso_consistent (exe : Execution) :=
  sc_per_location exe /\ acyclic (ppo exe +++ rfe exe +++ moe exe +++ fre exe).

Lemma ppo_dob_is_tso:
  forall exe,
  dob exe <--> (po exe --- (Writes exe \times Reads exe)) ->  
  partial_execution exe ->
  tso_consistent exe <-> armtoy_consistent exe.
Proof.
  intros.
  pose proof (ppo_rewrite exe H0) as H1.
  unfold tso_consistent, armtoy_consistent.
  destruct H1 as [H2 H3].
  split; intros [H4 H5].
  - split. exact H4.
    unfold external_coherence.
    eapply inclusion_acyclic; try exact H5.
    repeat apply inclusion_union_mon; try apply inclusion_refl.
    rewrite H.
    exact H3.
  - split. exact H4.
    unfold external_coherence in H5.
    eapply inclusion_acyclic; try exact H5.
    repeat apply inclusion_union_mon; try apply inclusion_refl.
    rewrite H.
    exact H2.
Qed.

End Executions.

Section Saturation.

Record extended exe exe' := {
  same_E : set_equiv (E exe) (E exe');
  same_po : po exe <--> po exe';
  same_dob : dob exe <--> dob exe';
  same_rf : rf exe <--> rf exe';
  extended_mo : mo exe <<= mo exe';
}.

Lemma fr_extended:
  forall exe exe',
  extended exe exe' ->
  fr exe <<= fr exe'.
Proof.
  intros.
  intros e1 e2 H0.
  destruct H0 as [e3 [H0 H1]].
  exists e3.
  split.
  - unfold transp in *. apply (same_rf _ _ H). exact H0.
  - apply (extended_mo _ _ H). exact H1.
Qed.

Lemma scpl_rel_extended:
  forall x exe exe',
  extended exe exe' ->
  scpl_rel x exe <<= scpl_rel x exe'.
Proof.
  intros.
  intros e1 e2 H0.
  repeat destruct H0 as [H0 | H0].
  - repeat left. eapply proj_loc_inclusion. apply (same_po _ _ H). exact H0.
  - do 2 left. right. eapply proj_loc_inclusion. apply (same_rf _ _ H). exact H0.
  - left. right. eapply proj_loc_inclusion. apply (extended_mo _ _ H). exact H0.
  - right. eapply proj_loc_inclusion. apply (fr_extended _ _ H). apply H0.
Qed.

Lemma ec_rel_extended:
  forall exe exe',
  extended exe exe' ->
  ec_rel exe <<= ec_rel exe'.
Proof.
  intros.
  intros e1 e2 H0.
  repeat destruct H0 as [H0 | H0].
  - repeat left. apply (same_dob _ _ H). exact H0.
  - do 2 left. right.
    split.
    + apply (same_rf _ _ H). apply H0.
    + intro. apply (same_po _ _ H) in H1. destruct H0. contradiction.
  - left. right.
    split.
    + apply (extended_mo _ _ H). apply H0.
    + intro. apply (same_po _ _ H) in H1. destruct H0. contradiction.
  - right.
    split.
    + apply (fr_extended _ _ H). apply H0.
    + intro. apply (same_po _ _ H) in H1. destruct H0. contradiction.
Qed.

Definition can_totally_satisfy P exe :=
  exists exe', extended exe exe' /\ total_execution exe' /\ P exe'.

Definition extend_with_mo e1 e2 exe :=
  {|
    E := E exe;
    po := po exe;
    rf := rf exe;
    dob := dob exe;
    mo := mo exe +++ singl_rel e1 e2;
    |}.

Lemma can_totally_satisfy_equiv:
  forall P1 P2 exe,
  (forall exe', P1 exe' <-> P2 exe') ->
  can_totally_satisfy P1 exe <-> can_totally_satisfy P2 exe.
Proof.
  intros.
  split; intros [exe_t [H0 [H1 H2]]];
  exists exe_t;
  split; auto;
  split; auto;
  apply H; exact H2.
Qed.

Lemma saturation_write_coherence:
  forall exe,
  partial_execution exe ->
  can_totally_satisfy armtoy_consistent exe ->
  forall r w1 w2,
  w1 <> w2 ->
  (rf exe) w1 r ->
  (exists x, clos_trans (scpl_rel x exe) w2 r) ->
  can_totally_satisfy armtoy_consistent (extend_with_mo w2 w1 exe).
Proof.
  intros.
  destruct H0 as [exe_t [Hext [Htotal Harmtoy]]].
  destruct H3 as [x H3].
  exists exe_t.
  split; auto.
  assert (loc r = x) as Rx. eapply (scpl_trans_all_x x exe w2 r H3).
  assert (loc w2 = x) as W2x. eapply (scpl_trans_all_x x exe w2 r H3).
  assert (loc w1 = x) as W1x. {
    rewrite (rf_same_loc _ H w1 r H2).
    exact Rx.
  }
  assert (event_proj_loc x (E exe_t) w1). {
    split; auto.
    apply Hext.
    apply (rf_in_universe exe H _ r H2).
  }
  assert (event_proj_loc x (E exe_t) w2). {
    split; auto.
    apply Hext.
    apply (scpl_rel_trans_in_universe x exe H _ r H3).
  }
  split; try (destruct Hext; assumption).
  intros e1 e2 H5.
  destruct H5.
  - apply (extended_mo _ _ Hext). exact H5.
  - destruct H5 as [H5 H6]. rewrite H5, H6.
    destruct (total_mo exe_t Htotal x w1 H0 w2 H4 H1).
    + exfalso.
      destruct Harmtoy as [Hscpl _].
      apply (Hscpl x r).
      eapply (t_trans _ _ r w2).
      * apply t_step.
        right.
        split; auto.
        exists w1.
        split. apply (same_rf _ _ Hext). exact H2.
        apply H7.
      * eapply inclusion_t_t. apply (scpl_rel_extended _ _ _ Hext).
        exact H3.
    + apply H7.
Qed.

(* Turned out to be redundant (captured by the above pattern) *)
Lemma saturation_read_coherence:
  forall exe,
  partial_execution exe ->
  can_totally_satisfy armtoy_consistent exe ->
  forall r1 r2 w1 w2,
  w1 <> w2 ->
  (exists x, clos_trans (scpl_rel x exe) r1 r2) ->
  (rf exe) w1 r1 -> (rf exe) w2 r2 ->
  can_totally_satisfy armtoy_consistent (extend_with_mo w1 w2 exe).
Proof.
  intros.
  destruct H0 as [exe_t [H0 [H5 H6]]].
  destruct H2 as [x H2].
  exists exe_t.
  split; auto.
  assert (loc r1 = x) as R1x. eapply (scpl_trans_all_x x exe r1 r2 H2).
  assert (loc r2 = x) as R2x. eapply (scpl_trans_all_x x exe r1 r2 H2).
  assert (loc w1 = x) as W1x. {
    rewrite (rf_same_loc _ H w1 r1 H3). exact R1x.
  }
  assert (loc w2 = x) as W2x. {
    rewrite (rf_same_loc _ H w2 r2 H4). exact R2x.
  } 
  assert (event_proj_loc x (E exe_t) w1). {
    split; auto.
    apply H0.
    apply (rf_in_universe exe H _ r1). exact H3.
  }
  assert (event_proj_loc x (E exe_t) w2). {
    split; auto.
    apply H0.
    apply (rf_in_universe exe H _ r2). exact H4.
  }
  split; try (destruct H0; assumption).
  intros e1 e2 H9.
  destruct H9.
  - apply (extended_mo _ _ H0). exact H9.
  - destruct H9 as [H9 H10]. rewrite H9, H10.
    destruct (total_mo exe_t H5 x w1 H7 w2 H8 H1).
    + eapply inclusion_restr. apply H11.
    + exfalso.
      destruct H6 as [H12 H13].
      specialize (H12 x).
      apply (H12 r1).
      eapply t_trans.
      * eapply inclusion_t_t. apply (scpl_rel_extended _ _ _ H0).
        apply H2.
      * eapply t_trans.
        --apply (t_step _ _ _ w1). right.
          split; auto.
          exists w2.
          split. apply (same_rf _ _ H0). exact H4.
          apply H11.
        --apply t_step.
          apply (scpl_rel_extended _ _ _ H0).
          do 2 left. right.
          split; auto.
Qed.

(* Todo: Rewrite some sections *)
Lemma saturation_external_coherence1:
  forall exe x,
  partial_execution exe ->
  can_totally_satisfy armtoy_consistent exe ->
  forall w1 w2,
  w1 <> w2 ->
  loc w1 = x ->
  loc w2 = x ->
  thread w1 <> thread w2 ->
  clos_trans (ec_rel exe) w1 w2 ->
  can_totally_satisfy armtoy_consistent (extend_with_mo w1 w2 exe).
Proof.
  intros.
  destruct H0 as [exe_t [Hext [Htotal Harmtoy]]].
  exists exe_t.
  split; auto.
  assert (event_proj_loc x (E exe_t) w1). {
    split; auto.
    apply Hext.
    apply (ec_rel_trans_in_universe exe H w1 _ H5).
  }
  assert (event_proj_loc x (E exe_t) w2). {
    split; auto.
    apply Hext.
    apply (ec_rel_trans_in_universe exe H _ w2 H5).
  }
  split; try (destruct Hext; assumption).
  intros e1 e2 H7.
  destruct H7.
  - apply (extended_mo _ _ Hext). exact H7.
  - destruct H7 as [H7 H8]. rewrite H7, H8.
    destruct (total_mo exe_t Htotal x w1 H0 w2 H6 H1).
    + apply H9.
    + exfalso.
      destruct Harmtoy as [_ Hec].
      apply (Hec w1).
      apply (t_trans _ _ _ w2).
      * eapply inclusion_t_t. apply (ec_rel_extended _ _ Hext).
        exact H5.
      * apply t_step.
        left. right.
        split.
        --apply H9.
        --intro.
          apply (same_po _ _ Hext) in H10.
          eapply (po_no_crossthread _ H w2 w1).
          ++intro. apply H4. rewrite H11. reflexivity.
          ++exact H10.
Qed.

Lemma saturation_external_coherence2:
  forall exe x,
  partial_execution exe ->
  can_totally_satisfy armtoy_consistent exe ->
  forall r w1 w2,
  w1 <> w2 ->
  loc w1 = x ->
  loc w2 = x ->
  thread r <> thread w2 ->
  (rf exe) w1 r ->
  clos_trans (ec_rel exe) w2 r ->
  can_totally_satisfy armtoy_consistent (extend_with_mo w2 w1 exe).
Proof.
  intros.
  destruct H0 as [exe_t [Hext [Htotal Harmtoy]]].
  exists exe_t.
  split; auto.
  assert (loc r = x) as Rx. erewrite <- (rf_same_loc _ H _ _ H5). exact H2.
  assert (event_proj_loc x (E exe_t) w1). {
    split; auto.
    apply Hext.
    apply (rf_in_universe exe H _ r H5).
  }
  assert (event_proj_loc x (E exe_t) w2). {
    split; auto.
    apply Hext.
    apply (ec_rel_trans_in_universe exe H _ r H6).
  }
  split; try (destruct Hext; assumption).
  intros e1 e2 H8.
  destruct H8.
  - apply (extended_mo _ _ Hext). exact H8.
  - destruct H8 as [H8 H9]. rewrite H8, H9.
    destruct (total_mo exe_t Htotal x w1 H0 w2 H7 H1).
    + exfalso.
      destruct Harmtoy as [_ Hec].
      apply (Hec r).
      eapply (t_trans _ _ r w2).
      * apply t_step.
        right.
        split.
        --exists w1.
          split. apply (same_rf _ _ Hext). exact H5.
          apply H10.
        --intro.
          apply (po_no_crossthread _ H r w2 H4).
          apply (same_po _ _ Hext).
          exact H11.
      * eapply inclusion_t_t. apply (ec_rel_extended _ _ Hext).
        exact H6.
    + apply H10.
Qed.

End Saturation.

Section SoundOneLocSC.

Definition release_acquire (exe : Execution) :=
  forall x,
  acyclic(po exe +++ rf exe +++ proj_loc x (mo exe) +++ proj_loc x (fr exe)).

Lemma one_loc_sc_is_release_acquire:
  forall x exe,
  partial_execution exe ->
  (forall e, E exe e -> loc e = x) ->
  sc exe <-> release_acquire exe.
Proof.
  intros.
  split; intro.
  - intros x' e H2.
    apply (H1 e).
    eapply inclusion_t_t; try apply H2.
    repeat apply inclusion_union_mon;
    try apply inclusion_refl;
    try apply inclusion_restr.
  - specialize (H1 x).
    eapply inclusion_acyclic; try apply H1.
    intros e1 e2 H2.
    repeat destruct H2 as [H2 | H2].
    + repeat left. exact H2.
    + do 2 left. right. exact H2.
    + left. right.
      split. exact H2.
      pose proof (mo_in_universe _ H _ _ H2) as [H3 H4].
      apply H0 in H3, H4.
      auto.
    + right.
      split. exact H2.
      pose proof (fr_in_universe _ H _ _ H2) as [H3 H4].
      apply H0 in H3, H4.
      auto.
Qed.

Lemma one_loc_sc_sound_helper:
  forall x exe (f : Execution -> bool),
  partial_execution exe ->
  (forall e, E exe e -> loc e = x) ->
  (f exe = true <-> can_totally_satisfy release_acquire exe) ->
  (f exe = true <-> can_totally_satisfy sc exe).
Proof.
  intros.
  split.
  - intros.
    apply H1 in H2.
    destruct H2 as [exe_t [H3 [H4 H5]]].
    exists exe_t.
    split; auto.
    split; auto.
    eapply (one_loc_sc_is_release_acquire).
    + exact (partial_exe _ H4).
    + intros.
      apply H0.
      apply (same_E _ _ H3).
      exact H2.
    + exact H5.
  - intros.
    apply H1.
    destruct H2 as [exe_t [H3 [H4 H5]]].
    exists exe_t.
    split; auto.
    split; auto.
    eapply (one_loc_sc_is_release_acquire).
    + exact (partial_exe _ H4).
    + intros.
      apply H0.
      apply (same_E _ _ H3).
      exact H2.
    + exact H5.
Qed.

End SoundOneLocSC.