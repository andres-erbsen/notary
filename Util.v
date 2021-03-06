Require Import Arith.
Require Import Omega.
Require Import NPeano.
Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import VerdiTactics.

Set Implicit Arguments.

Notation member := (in_dec eq_nat_dec).

Ltac do_in_map :=
  match goal with
    | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H; break_exists; break_and
  end.

Ltac do_in_app :=
  match goal with
    | [ H : In _ (_ ++ _) |- _ ] => apply in_app_iff in H
  end.

Lemma filter_app : forall A (f : A -> bool) xs ys,
    filter f (xs ++ ys) = filter f xs ++ filter f ys.
Proof.
  induction xs; intros.
  - auto.
  - simpl. rewrite IHxs. break_if; auto.
Qed.

Section dedup.
  Variable A : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Fixpoint dedup (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => let tail := dedup xs in
                 if in_dec A_eq_dec x xs then
                   tail
                 else
                   x :: tail
    end.

  Lemma dedup_eliminates_duplicates : forall (a : A) b c,
      (dedup (a :: b ++ a :: c) = dedup (b ++ a :: c)).
  Proof.
    intros. simpl in *.
    break_match.
    + auto.
    + exfalso. intuition.
  Qed.

  Lemma dedup_In : forall (x : A) xs,
      In x xs ->
      In x (dedup xs).
  Proof.
    induction xs; intros.
    - simpl in *. intuition.
    - simpl in *. break_if; intuition.
      + subst. auto.
      + subst. simpl. auto.
  Qed.

  Lemma filter_dedup (pred : A -> bool) :
    forall xs (p : A) ys,
      pred p = false ->
      filter pred (dedup (xs ++ ys)) = filter pred (dedup (xs ++ p :: ys)).
  Proof.
    intros. induction xs.
    - simpl. repeat (break_match; simpl; auto; try discriminate).
    - simpl. repeat (break_match; simpl; auto).
      + exfalso. apply n. apply in_app_iff. apply in_app_or in i. intuition.
      + exfalso. apply n. apply in_app_or in i. intuition.
        * simpl in *. intuition. subst. rewrite Heqb in H. discriminate.
      + rewrite IHxs. auto.
      + discriminate.
      + discriminate.
  Qed.

  Lemma dedup_app : forall (xs ys : list A),
      (forall x y, In x xs -> In y ys -> x <> y) ->
      dedup (xs ++ ys) = dedup xs ++ dedup ys.
  Proof.
    intros. induction xs; simpl; auto.
    repeat break_match.
    - apply IHxs.
      intros. apply H; intuition.
    - exfalso. specialize (H a a).
      apply H; intuition.
      do_in_app. intuition.
    - exfalso. apply n. intuition.
    - simpl. f_equal.
      apply IHxs.
      intros. apply H; intuition.
  Qed.

  Lemma in_dedup_was_in :
    forall xs (x : A),
      In x (dedup xs) ->
      In x xs.
  Proof.
    induction xs; intros.
    - simpl in *; intuition.
    - simpl in *. break_if; simpl in *; intuition.
  Qed.

  Lemma NoDup_dedup :
    forall (xs : list A),
      NoDup (dedup xs).
  Proof.
    induction xs.
    - simpl. constructor.
    - simpl. break_if; auto.
      constructor; auto.
      intro.
      apply n.
      eapply in_dedup_was_in; eauto.
  Qed.

  Lemma remove_preserve :
    forall (x y : A) xs,
      x <> y ->
      In y xs ->
      In y (remove A_eq_dec x xs).
  Proof.
    induction xs; intros.
    - intuition.
    - simpl in *.
      concludes.
      intuition; break_if; subst; try congruence; intuition.
  Qed.

  Lemma in_remove :
    forall (x y : A) xs,
      In y (remove A_eq_dec x xs) ->
      In y xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *. break_if; simpl in *; intuition.
  Qed.

  Lemma remove_dedup_comm : forall (x : A) xs,
      remove A_eq_dec x (dedup xs) =
      dedup (remove A_eq_dec x xs).
  Proof.
    induction xs; intros.
    - auto.
    - simpl. repeat (break_match; simpl); auto.
      + exfalso. apply n0. apply remove_preserve; auto.
      + exfalso. apply n. eapply in_remove; eauto.
      + f_equal. auto.
  Qed.

  Lemma remove_partition :
    forall xs (p : A) ys,
      remove A_eq_dec p (xs ++ p :: ys) = remove A_eq_dec p (xs ++ ys).
  Proof.
    induction xs; intros.
    - simpl. break_if; congruence.
    - simpl. break_if.
      + auto.
      + f_equal. auto.
  Qed.

  Lemma remove_not_in : forall (x : A) xs,
      ~ In x xs ->
      remove A_eq_dec x xs = xs.
  Proof.
    intros. induction xs.
    - intuition.
    - simpl. break_match.
      + exfalso. apply H.
        subst. intuition.
      + f_equal. apply IHxs.
        intro Hin.
        apply H. simpl. intuition.
  Qed.

  Lemma dedup_partition :
    forall xs (p : A) ys xs' ys',
      dedup (xs ++ p :: ys) = xs' ++ p :: ys' ->
      remove A_eq_dec p (dedup (xs ++ ys)) = xs' ++ ys'.
  Proof.
    intros.
    f_apply H (remove A_eq_dec p).
    rewrite remove_dedup_comm in *.
    rewrite remove_partition in *.
    rewrite H0.
    rewrite remove_partition.

    apply remove_not_in.
    apply NoDup_remove_2.
    rewrite <- H.
    apply NoDup_dedup.
  Qed.

  Lemma dedup_NoDup_id : forall (xs : list A),
      NoDup xs -> dedup xs = xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl. invc H. concludes. rewrite IHxs.
      break_if; congruence.
  Qed.

  Lemma dedup_not_in_cons :
    forall x xs,
      (~ In x xs) ->
      x :: dedup xs = dedup (x :: xs).
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *. intuition. repeat break_match; intuition.
  Qed.
End dedup.

Lemma filter_fun_ext_eq : forall A f g xs,
                            (forall a : A, In a xs -> f a = g a) ->
                            filter f xs = filter g xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl. rewrite H by intuition. rewrite IHxs by intuition. auto.
Qed.



Lemma NoDup_map_injective : forall A B (f : A -> B) xs,
                              (forall x y, In x xs -> In y xs ->
                                           f x = f y -> x = y) ->
                              NoDup xs -> NoDup (map f xs).
Proof.
  induction xs; intros.
  - constructor.
  - simpl. constructor.
    + intro.
      do_in_map.
      specialize (H a x).
      repeat conclude H intuition.
      subst.
      invc H0. auto.
    + apply IHxs. intuition. inv H0. auto.
Qed.

Lemma NoDup_disjoint_append :
  forall A (l : list A) l',
    NoDup l ->
    NoDup l' ->
    (forall a, In a l -> ~ In a l') ->
    NoDup (l ++ l').
Proof.
  induction l; intros.
  - auto.
  - simpl. constructor.
    + intro. do_in_app. intuition.
      * invc H. auto.
      * apply (H1 a); intuition.
    + invc H. apply IHl; auto.
      intros. apply H1. intuition.
Qed.

Lemma filter_NoDup :
  forall A p (l : list A),
    NoDup l ->
    NoDup (filter p l).
Proof.
  induction l; intros.
  - auto.
  - invc H. simpl. break_if.
    + constructor; auto.
      intro. apply filter_In in H. intuition.
    + auto.
Qed.

    

Lemma filter_true_id : forall A (f : A -> bool) xs,
                         (forall x, In x xs -> f x = true) ->
                         filter f xs = xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl. rewrite H by intuition. rewrite IHxs by intuition. auto.
Qed.

Lemma map_of_map : forall A B C (f : A -> B) (g : B -> C) xs,
                     map g (map f xs) = map (fun x => g (f x)) xs.
Proof.
  induction xs.
  - auto.
  - simpl. f_equal. auto.
Qed.

Lemma filter_except_one : forall A A_eq_dec (f g : A -> bool) x xs,
                            (forall y, In y xs ->
                                       x <> y ->
                                       f y = g y) ->
                            g x = false ->
                            filter f (remove A_eq_dec x xs) = filter g xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl.
    pose proof (A_eq_dec x a).
    intuition; repeat (break_match; simpl); try congruence; subst; intuition; f_equal; intuition;
    rewrite (H a) in * by intuition; congruence.
Qed.

Lemma flat_map_nil : forall A B (f : A -> list B) l,
                       flat_map f l = [] ->
                       l = [] \/ (forall x, In x l -> f x = []).
Proof.
  induction l; intros.
  - intuition.
  - right. simpl in *.
    apply app_eq_nil in H.
    intuition; subst; simpl in *; intuition.
Qed.

Fixpoint remove_first {A : Set} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : list A :=
  match l with
    | [] => []
    | y::tl => if (A_eq_dec x y) then tl else y::(remove_first A_eq_dec x tl)
  end.


Fixpoint subseq {A} (xs ys : list A) : Prop :=
  match xs, ys with
    | [], _ => True
    | x :: xs', y :: ys' => (x = y /\ subseq xs' ys') \/ subseq xs ys'
    | _, _ => False
  end.

Lemma subseq_refl : forall A (l : list A), subseq l l.
Proof.
  induction l; simpl; tauto.
Qed.

Lemma subseq_trans :
  forall A (zs xs ys : list A),
    subseq xs ys ->
    subseq ys zs ->
    subseq xs zs.
Proof.
  induction zs; intros; simpl in *;
  repeat break_match; subst; simpl in *; intuition; subst; eauto;
  right; (eapply IHzs; [|eauto]); simpl; eauto.
Qed.
Lemma subseq_In :
  forall A (ys xs : list A) x,
    subseq xs ys ->
    In x xs ->
    In x ys.
Proof.
  induction ys; intros.
  - destruct xs; simpl in *; intuition.
  - simpl in *. break_match; simpl in *; intuition; subst; intuition eauto;
                right; (eapply IHys; [eauto| intuition]).
Qed.

Theorem subseq_NoDup :
  forall A (ys xs : list A),
    subseq xs ys ->
    NoDup ys ->
    NoDup xs.
Proof.
  induction ys; intros.
  - destruct xs; simpl in *; intuition.
  - simpl in *. invc H0.
    break_match.
    + constructor.
    + intuition.
      subst. constructor.
      * intro. apply H3.
        eapply subseq_In; eauto.
      * eauto.
Qed.

Theorem NoDup_Permutation_NoDup :
  forall A (l l' : list A),
    NoDup l ->
    Permutation l l' ->
    NoDup l'.
Proof.
  intros. induction H0.
  - auto.
  - invc H. constructor; auto.
    intro. apply H3. apply Permutation_in with (l := l'); auto.
    symmetry. auto.
  - invc H. invc H3. constructor.
    * simpl in *. intuition.
    * constructor; simpl in *; intuition.
  - auto.
Qed.

Theorem NoDup_append :
  forall A l (a : A),
    NoDup (l ++ [a]) <-> NoDup (a :: l).
Proof.
  intros.
  split; intro.
  - eapply NoDup_Permutation_NoDup; try eassumption.
    symmetry.
    apply Permutation_cons_append.
  - eapply NoDup_Permutation_NoDup; try eassumption.
    apply Permutation_cons_append.
Qed.

Lemma leb_false_lt : forall m n, leb m n = false -> n < m.
Proof.
  induction m; intros.
  - discriminate.
  - simpl in *. break_match; subst; auto with arith.
Qed.

Lemma leb_true_le : forall m n, leb m n = true -> m <= n.
Proof.
  induction m; intros.
  - auto with arith.
  - simpl in *. break_match; subst; auto with arith.
    discriminate.
Qed.

Lemma ltb_false_le : forall m n, m <? n = false -> n <= m.
Proof.
  induction m; intros; destruct n; try discriminate; auto with arith.
Qed.

Lemma ltb_true_lt : forall m n, m <? n = true -> m < n.
  induction m; intros; destruct n; try discriminate; auto with arith.
Qed.

Ltac do_bool :=
  repeat match goal with
    | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true in H
    | [ H : beq_nat _ _ = false |- _ ] => apply beq_nat_false in H
    | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
    | [ H : negb _ = true |- _ ] => apply Bool.negb_true_iff in H
    | [ H : negb _ = false |- _ ] => apply Bool.negb_false_iff in H
    | [ H : PeanoNat.Nat.ltb _ _ = true |- _ ] => apply ltb_true_lt in H
    | [ H : PeanoNat.Nat.ltb _ _ = false |- _ ] => apply ltb_false_le in H
    | [ H : leb _ _ = true |- _ ] => apply leb_true_le in H
    | [ H : leb _ _ = false |- _ ] => apply leb_false_lt in H
    | [ |- context [ andb _ _ ] ] => apply Bool.andb_true_iff
    | [ |- context [ leb _ _ ] ] => apply leb_correct
    | [ |- context [ _ <> false ] ] => apply Bool.not_false_iff_true
    | [ |- beq_nat _ _ = false ] => apply beq_nat_false_iff
    | [ |- beq_nat _ _ = true ] => apply beq_nat_true_iff
  end.


Lemma NoDup_map_elim :
  forall A B (f : A -> B) xs x y,
    f x = f y ->
    NoDup (map f xs) ->
    In x xs ->
    In y xs ->
    x = y.
Proof.
  induction xs; intros.
  - simpl in *. intuition.
  - simpl in *. invc H0. intuition; subst.
    + auto.
    + exfalso. repeat find_rewrite. apply H5. apply in_map. auto.
    + exfalso. apply H5. rewrite <- H. apply in_map. auto.
Qed.

Lemma subseq_map :
  forall A B (f : A -> B) ys xs,
    subseq xs ys ->
    subseq (map f xs) (map f ys).
Proof.
  induction ys; intros.
  - simpl in *. repeat break_match; try discriminate; auto.
  - simpl in *. repeat break_match; try discriminate; auto.
    simpl in *. find_inversion.
    intuition.
    + subst. auto.
    + right. apply IHys in H0. auto.
Qed.

Lemma subseq_cons_drop :
  forall A xs ys (a : A),
    subseq (a :: xs) ys -> subseq xs ys.
Proof.
  induction ys; intros; simpl in *; intuition; break_match; eauto.
Qed.

Lemma subseq_length :
  forall A (ys xs : list A),
    subseq xs ys ->
    length xs <= length ys.
Proof.
  induction ys; intros; simpl in *; break_match; intuition.
  subst. simpl in *. specialize (IHys l). concludes. auto with *.
Qed.

Lemma subseq_subseq_eq :
  forall A (xs ys : list A),
    subseq xs ys ->
    subseq ys xs ->
    xs = ys.
Proof.
  induction xs; intros.
  - destruct ys; auto; simpl in *; intuition.
  - destruct ys; simpl in *.
    + intuition.
    + intuition.
      * f_equal; eauto.
      * f_equal; eauto using subseq_cons_drop.
      * f_equal; eauto using subseq_cons_drop.
      * exfalso.
        apply subseq_length in H1.
        apply subseq_length in H.
        simpl in *. omega.
Qed.

Lemma subseq_filter :
  forall A (f : A -> bool) xs,
    subseq (filter f xs) xs.
Proof.
  induction xs; intros.
  - simpl. auto.
  - simpl. repeat break_match.
    + discriminate.
    + auto.
    + find_inversion. auto.
    + right. rewrite <- Heql. eauto.
Qed.

Fixpoint take A (n : nat) (xs : list A) : list A :=
  match n with
    | O => []
    | S n' => match xs with
               | [] => []
               | x :: xs' => x :: take n' xs'
             end
  end.

Lemma remove_length_not_in : forall A A_eq_dec (x : A) xs,
                               ~ In x xs ->
                               length (remove A_eq_dec x xs) = length xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl in *. intuition.
    break_if; subst; simpl; intuition.
Qed.

Lemma remove_length_in : forall A A_eq_dec (x : A) xs,
                           In x xs ->
                           NoDup xs ->
                           S (length (remove A_eq_dec x xs)) = length xs.
Proof.
  induction xs; intros.
  - simpl in *. intuition.
  - simpl in *. intuition.
    + subst. break_if; try congruence.
      inv H0.
      rewrite remove_length_not_in; auto.
    + invc H0.
      break_if; subst; intuition.
Qed.


Lemma subset_size_eq :
  forall A xs,
    NoDup xs ->
    forall ys,
      NoDup ys ->
      (forall x : A, In x xs -> In x ys) ->
      length xs = length ys ->
      (forall x, In x ys -> In x xs).
Proof.
  induction xs; intros.
  - destruct ys; try discriminate. auto.
  - simpl in *. inv H. concludes.
    pose proof H1 a (or_introl eq_refl).
    apply in_split in H4. break_exists. subst.
    specialize (IHxs (x0 ++ x1)).


    forward IHxs.
    eapply NoDup_remove_1; eauto.
    concludes. clear H4.


    forward IHxs.
    intros. pose proof H1 x2 (or_intror H4).
    pose proof NoDup_remove_2 x0 x1 a H0.
    apply in_app_or in H5. simpl in *. intuition. subst. congruence.
    concludes. clear H4.

    forward IHxs. rewrite app_length in *. simpl in *. omega.
    concludes.  clear H4.

    apply in_app_or in H3. simpl in *. intuition.
Qed.

Lemma in_take : forall A n (x : A) xs,
                  In x (take n xs) -> In x xs.
Proof.
  induction n; intros.
  - simpl in *. intuition.
  - simpl in *. break_match.
    + simpl in *. intuition.
    + simpl in *. intuition.
Qed.

Lemma take_NoDup : forall A n (xs : list A),
                     NoDup xs ->
                     NoDup (take n xs).
Proof.
  induction n; intros.
  - destruct xs; simpl in *; intuition. constructor.
  - simpl. destruct xs.
    + auto.
    + invc H. constructor; auto.
      intro. apply in_take in H. auto.
Qed.

Lemma remove_NoDup :
  forall A A_eq_dec (x : A) xs,
    NoDup xs ->
    NoDup (remove A_eq_dec x xs).
Proof.
  induction xs; intros.
  - auto.
  - invc H. simpl. break_if.
    + auto.
    + constructor.
      * intro. apply H2. eapply in_remove; eauto.
      * auto.
Qed.

Lemma seq_range :
  forall n a x,
    In x (seq a n) ->
    a <= x < a + n.
Proof.
  induction n; intros.
  - simpl in *. intuition.
  - simpl in *. invc H. intuition.
    apply IHn in H0. omega.
Qed.


Lemma take_length : forall A n (xs : list A),
                      length xs >= n ->
                      length (take n xs) = n.
Proof.
  induction n; intros.
  - auto.
  - simpl. break_match.
    + simpl in *. omega.
    + simpl in *. rewrite IHn by omega. auto.
Qed.


Lemma seq_NoDup : forall n a ,
                    NoDup (seq a n).
Proof.
  induction n; intros; simpl in *.
  - constructor.
  - constructor.
    intro. apply seq_range in H. omega.
    auto.
Qed.

Lemma remove_length_ge : forall A A_eq_dec (x : A) xs,
                           NoDup xs ->
                           length (remove A_eq_dec x xs) >= length xs - 1.
Proof.
  induction xs; intros.
  - auto.
  - inv H. simpl. break_if.
    + rewrite <- minus_n_O.
      subst.
      rewrite remove_length_not_in; auto.
    + simpl. concludes. omega.
Qed.

Lemma remove_length_le :
  forall A (x : A) xs eq_dec,
    length xs >= length (remove eq_dec x xs).
Proof.
  induction xs; intros.
  - auto.
  - simpl in *.
    specialize (IHxs eq_dec).
    break_if; subst; simpl; omega.
Qed.

Lemma remove_length_lt :
  forall A (x : A) xs eq_dec,
    In x xs ->
    length xs > length (remove eq_dec x xs).
Proof.
  induction xs; intros.
  - simpl in *. intuition.
  - simpl in *.
    intuition.
    + subst.
      break_if; try congruence.
      pose proof remove_length_le x xs eq_dec.
      omega.
    + specialize (IHxs eq_dec H0).
      break_if; subst; simpl; omega.
Qed.

Lemma subset_length :
  forall A xs ys,
    (forall a b : A, {a = b} + {a <> b}) ->
    NoDup xs ->
    (forall x : A, In x xs -> In x ys) ->
    length ys >= length xs.
Proof.
  induction xs; intros.
  - simpl. omega.
  - specialize (IHxs (remove X a ys) X).
    invc H.
    concludes.

    forward IHxs.
    intros.
    apply remove_preserve.
    intro. subst. congruence.

    apply H0. intuition.
    concludes.
    pose proof remove_length_lt a ys X.
    forwards.
    apply H0. intuition. concludes.
    simpl. omega.
Qed.

Lemma take_length_ge : forall A n m (xs : list A),
                         length (take n xs) >= m ->
                         length xs >= m.
Proof.
  induction n; intros.
  - simpl in *. omega.
  - simpl in *. break_match.
    + omega.
    + simpl in *.
      destruct m; try omega.
      unfold ge in *.
      apply le_S_n in H.
      apply IHn in H. omega.
Qed.

Fixpoint fin (n : nat) : Type :=
  match n with
    | 0 => False
    | S n' => option (fin n')
  end.

Lemma fin_eq_dec : forall n (a b : fin n), {a = b} + {a <> b}.
Proof.
  induction n.
  - auto.
  - intros. destruct a, b.
    + specialize (IHn f f0). intuition.
      * subst. auto.
      * right. intros. inversion H. auto.
    + right. discriminate.
    + right. discriminate.
    + auto.
Qed.

Fixpoint all_fin (n : nat) : list (fin n) :=
  match n with
    | 0 => []
    | S n' => None :: map (fun x => Some x) (all_fin n')
  end.

Lemma all_fin_all :
  forall n (x : fin n),
    In x (all_fin n).
Proof.
  induction n; intros.
  - solve_by_inversion.
  - simpl in *. destruct x; auto using in_map.
Qed.

Lemma all_fin_NoDup :
  forall n,
    NoDup (all_fin n).
Proof.
  induction n; intros; simpl; constructor.
  - intro. apply in_map_iff in H. firstorder. discriminate.
  - apply NoDup_map_injective; auto. congruence.
Qed.

Lemma or_false :
  forall P : Prop, P -> (P \/ False).
Proof.
  firstorder.
Qed.

Ltac map_crush :=
  repeat match goal with
                   | [ H : context [ map _ (_ ++ _) ] |- _ ] => rewrite map_app in H
                   | [ |- context [ map _ (_ ++ _) ] ] => rewrite map_app
                   | [ H : context [ map _ (map _ _) ] |- _ ] => rewrite map_map in H
                   | [ |- context [ map _ (map _ _) ] ] => rewrite map_map
         end; simpl in *.


Ltac in_crush_finish :=
  repeat match goal with
    | [ |- _ \/ _ ] => try first [solve [apply or_introl; in_crush_finish]|
                                 solve [apply or_intror; in_crush_finish]]
    | [ |- In _ (_ ++ _) ] => apply in_or_app; in_crush_finish
    | [ |- In _ (map _ _) ] => apply in_map_iff; eexists; eauto
  end.
Ltac in_crush_start :=
  intuition; simpl in *;
  repeat
    (match goal with
       | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H; break_exists; break_and
       | [ H : In _ (_ ++ _) |- _ ] => apply in_app_iff in H
     end; intuition; simpl in *); subst.

Ltac in_crush := repeat (in_crush_start; in_crush_finish).

Fixpoint Prefix {A} (l1 : list A) l2 : Prop :=
  match l1, l2 with
    | a :: l1', b :: l2' => a = b /\ Prefix l1' l2'
    | [], _ => True
    | _, _ => False
  end.

Lemma app_Prefix :
  forall A (xs ys zs : list A),
    xs ++ ys = zs ->
    Prefix xs zs.
Proof.
  induction xs; intros; simpl in *.
  - auto.
  - break_match.
    + discriminate.
    + subst. find_inversion. eauto.
Qed.

Fixpoint filterMap {A B} (f : A -> option B) (l : list A) : list B :=
  match l with
    | [] => []
    | x :: xs => match f x with
                   | None => filterMap f xs
                   | Some y => y :: filterMap f xs
                 end
  end.

Lemma app_cons_singleton_inv :
  forall A xs (y : A) zs w,
    xs ++ y :: zs = [w] ->
    xs = [] /\ y = w /\ zs = [].
Proof.
  intros.
  destruct xs.
  - solve_by_inversion.
  - destruct xs; solve_by_inversion.
Qed.

Definition null {A : Type} (xs : list A) : bool :=
  match xs with
    | [] => true
    | _ => false
  end.

Lemma null_sound :
  forall A (l : list A),
    null l = true -> l = [].
Proof.
  destruct l; simpl in *; auto; discriminate.
Qed.

Lemma null_false_neq_nil :
  forall A (l : list A),
    null l = false -> l <> [].
Proof.
  destruct l; simpl in *; auto; discriminate.
Qed.

Lemma map_of_filterMap :
  forall A B C (f : A -> option B) (g : B -> C) l,
    map g (filterMap f l) = filterMap (fun x => match f x with
                                                  | Some y => Some (g y)
                                                  | None => None
                                                end) l.
Proof.
  induction l; intros; simpl in *.
  - auto.
  - repeat break_match; simpl; auto using f_equal.
Qed.

Lemma filterMap_ext :
  forall A B (f g : A -> option B) l,
    (forall x, f x = g x) ->
    filterMap f l = filterMap g l.
Proof.
  induction l; intros; simpl in *.
  - auto.
  - repeat find_higher_order_rewrite; auto.
Qed.

Lemma filterMap_defn :
  forall A B (f : A -> option B) x xs,
    filterMap f (x :: xs) = match f x with
                              | Some y => y :: filterMap f xs
                              | None => filterMap f xs
                            end.
Proof.
  simpl. auto.
Qed.

Lemma app_cons_in :
  forall A (l : list A) xs a ys,
    l = xs ++ a :: ys ->
    In a l.
Proof.
  intros. subst. auto with *.
Qed.
Hint Resolve app_cons_in.

Lemma app_cons_in_rest:
  forall A (l : list A) xs a b ys,
    l = xs ++ a :: ys ->
    In b (xs ++ ys) ->
    In b l.
Proof.
  intros. subst. in_crush.
Qed.
Hint Resolve app_cons_in_rest.

Lemma remove_filter_commute :
  forall A  (l : list A) A_eq_dec f x,
    remove A_eq_dec x (filter f l) = filter f (remove A_eq_dec x l).
Proof.
  induction l; intros; simpl in *; auto.
  repeat (break_if; subst; simpl in *; try congruence).
Qed.

Lemma filter_partition :
  forall A (l1 : list A) f l2 x l1' l2',
    NoDup (l1 ++ x :: l2) ->
    filter f (l1 ++ x :: l2) = (l1' ++ x :: l2') ->
    filter f l1 = l1' /\ filter f l2 = l2'.
Proof.
  induction l1; intros; simpl in *.
  - break_if; simpl in *.
    + invcs H.
      destruct l1'; simpl in *; intuition.
      * solve_by_inversion.
      * find_inversion.
        exfalso.
        match goal with
          | H : filter ?f ?l = _ ++ ?x :: _ |- _ =>
            assert (In x (filter f l)) by (repeat find_rewrite; in_crush)
        end.
        find_apply_lem_hyp filter_In. intuition.
      * find_inversion.
        exfalso.
        match goal with
          | H : filter ?f ?l = _ ++ ?x :: _ |- _ =>
            assert (In x (filter f l)) by (repeat find_rewrite; in_crush)
        end.
        find_apply_lem_hyp filter_In. intuition.
    + exfalso.
      match goal with
        | H : filter ?f ?l = _ ++ ?x :: _ |- _ =>
          assert (In x (filter f l)) by (repeat find_rewrite; in_crush)
      end.
      find_apply_lem_hyp filter_In. intuition. congruence.
  - break_if.
    + invcs H.
      destruct l1'; simpl in *; intuition;
      try solve [
            find_inversion; exfalso;
            match goal with
              | _ : In ?x ?l -> False |- _ =>
                assert (In x l) by in_crush; intuition
            end|
            find_inversion; f_equal;
            find_apply_hyp_hyp; intuition].
    + invcs H. eauto.
Qed.

Lemma map_inverses :
  forall A B (la : list A) (lb : list B)  (f : A -> B) g,
    (forall a, g (f a) = a) ->
    (forall b, f (g b) = b) ->
    lb = map f la ->
    la = map g lb.
Proof.
  destruct la; intros; simpl in *.
  - subst. reflexivity.
  - destruct lb; try congruence.
    simpl in *. find_inversion.
    find_higher_order_rewrite.
    f_equal.
    rewrite map_map.
    erewrite map_ext; [symmetry; apply map_id|].
    simpl in *. auto.
Qed.

Lemma if_sum_bool_fun_comm :
  forall A B C D (b : {A}+{B}) (c1 c2 : C) (f : C -> D),
    f (if b then c1 else c2) = if b then f c1 else f c2.
Proof.
  intros. break_if; auto.
Qed.

Section assoc.
  Variable K V : Type.
  Variable K_eq_dec : forall k k' : K, {k = k'} + {k <> k'}.

  Fixpoint assoc (l : list (K * V)) (k : K) : option V :=
    match l with
      | [] => None
      | (k', v) :: l' =>
        if K_eq_dec k k' then
          Some v
        else
          assoc l' k
    end.

  Definition assoc_default (l : list (K * V)) (k : K) (default : V) : V :=
    match (assoc l k) with
      | Some x => x
      | None => default
    end.

  Fixpoint assoc_set (l : list (K * V)) (k : K) (v : V) : list (K * V) :=
    match l with
      | [] => [(k, v)]
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          (k, v) :: l'
        else
          (k', v') :: (assoc_set l' k v)
    end.

  Fixpoint assoc_del (l : list (K * V)) (k : K) : list (K * V) :=
    match l with
      | [] => []
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          l'
        else
          (k', v') :: (assoc_del l' k)
    end.

  Lemma get_set_same :
    forall k v l,
      assoc (assoc_set l k v) k = Some v.
  Proof.
    induction l; intros; simpl; repeat (break_match; simpl); subst; congruence.
  Qed.

  Lemma get_set_diff :
    forall k k' v l,
      k <> k' ->
      assoc (assoc_set l k v) k' = assoc l k'.
  Proof.
    induction l; intros; simpl; repeat (break_match; simpl); subst; try congruence; auto.
  Qed.

  Lemma not_in_assoc :
    forall k l,
      ~ In k (map (@fst _ _) l) ->
      assoc l k = None.
  Proof.
    intros.
    induction l.
    - auto.
    - simpl in *. repeat break_match; intuition.
      subst. simpl in *. congruence.
  Qed.

  Lemma get_del_same :
    forall k l,
      NoDup (map (@fst _ _) l) ->
      assoc (assoc_del l k) k = None.
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - invc H.
      repeat break_match; subst.
      + simpl in *. apply not_in_assoc. auto.
      + simpl in *. break_if; try congruence.
        auto.
  Qed.

  Lemma get_del_diff :
    forall k k' l,
      k <> k' ->
      assoc (assoc_del l k') k = assoc l k.
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - repeat (break_match; simpl); subst; try congruence.
      auto.
  Qed.
End assoc.

