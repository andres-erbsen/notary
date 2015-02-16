Require Import List.
Require Import String.
Import ListNotations.

Require Import VerdiTactics.
Require Import HandlerMonad.
Require Import Net.
Require Import Util.

Section Notary.

  Inductive Name :=
  | Notary : Name
  | Client : Name.

  Definition all_nodes := [Notary; Client].

  Definition Name_eq_dec : forall a b : Name, {a = b} + {a <> b}.
    decide equality.
  Qed.


  Definition Data := unit.
  Definition init_data (n : Name) : Data := tt.

  Theorem In_Nodes :
    forall (n : Name), (In n all_nodes).
  Proof.
    destruct n; [left|right;left]; auto.
   Qed.

  Theorem NoDup_Nodes : NoDup all_nodes.
  Proof.
    repeat constructor; auto.
    intro. destruct H. discriminate. destruct H.
   Qed. 

  Global Instance Notary_BaseParams : BaseParams :=
    {
      data   := Data ;
      input  := unit ;
      output := string
    }.

  Definition magic : string := "magic".
  Definition staple s : string := magic ++ s.
  Definition Handler (node _:Name) (msg:string) (_:Data)
    : (list string * Data * list (Name * string) * list (@cryptoEvent Name))
    :=
    match node with
    | Notary => ([],   tt, [], [Sign (staple msg)])
    | Client => ([msg], tt, [], [Verify Notary msg])
  end.
  Definition inputHandler (_:Name) (_:unit) (d:Data)
    : (list string * Data * list (Name * string) * list (@cryptoEvent Name))
    := ([], d, [], [])
  .

  Global Instance Notary_MultiParams : MultiParams Notary_BaseParams :=
    {
      name := Name ;
      msg  := string ;
      msg_eq_dec := string_dec ;
      name_eq_dec := Name_eq_dec ;
      nodes := all_nodes;
      all_names_nodes := In_Nodes ;
      no_dup_nodes := NoDup_Nodes ;
      init_handlers := init_data ;
      net_handlers := Handler;
      input_handlers := inputHandler
    }.

  Definition magical s := exists t, s=staple t.
  Lemma magical_staple : forall s, magical (staple s).
    intros; unfold magical, staple. exists s.
  Qed.

  Lemma signed_magic : forall st trace,
    refl_trans_n1_trace step_m step_m_init st trace ->
    forall n s, In (n, Sign s) (nwCrypto st) -> magical s.
    intros until 1.
    remember step_m_init as s0 in H.
    induction H; [subst; unfold step_m_init; simpl; intros; exfalso; auto|].
    inversion H0; subst net net'. {
      unfold net_handlers in *; simpl in *.
      case_eq (pDst p); intro e; rewrite e in *; simpl in *. {
        injection H1; clear H1; intros until n; revert n; subst; simpl in *.
        intros.
        destruct H1.
        - injection H1; clear H1; intros; subst. apply magical_staple.
        - eapply IHrefl_trans_n1_trace; eauto.
      } {
        injection H1; clear H1; intros; subst.
        unfold mark_cevents_src in *; simpl in *. 
        destruct H8; [discriminate|]; eauto.
      }
    } {
      injection H1; clear H1; intros; subst; eauto.
    }
  Qed.

  Goal forall st trace, step_m_star step_m_init st trace ->
    forall (n:Name) (ss:list string), In (n, inr ss) trace ->
    forall s, In s ss -> magical s.
  Proof.
    intros.
    unfold step_m_star in *.
    specialize (refl_trans_1n_n1_trace H); clear H; intro H.
    remember step_m_init as s0 in H.
    induction H; [inversion H0|]; rewrite Heqs0 in *; clear Heqs0.
    destruct (in_app_or _ _ _ H0); try eauto.
    inversion H2. {
      unfold net_handlers in *; simpl in *.
      case_eq (pDst p); intro e; rewrite e in *; clear e; simpl in *; 
        injection H4; clear H4; intros; subst; simpl in *;
        destruct H3; intuition; 
        injection H3; clear H3; intros; subst; simpl in *; [exfalso; auto|].
      eapply signed_magic; [eauto|].
      edestruct H6; [left;eauto|discriminate|].
      replace s with (pBody p) by intuition; eapply H3.
   } { 
    unfold net_handlers in *; subst; simpl in *.
    destruct H3; intuition; discriminate.
   }
  Qed.

End Notary.
