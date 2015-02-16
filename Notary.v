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
    destruct n ; auto.
  Qed.

  Global Instance Notary_BaseParams : BaseParams :=
    {
      data   := Data ;
      input  := unit ;
      output := string
    }.

  Global Instance Notary_MultiParams : MultiParams Notary_BaseParams :=
    {
      name := Name ;
      msg  := string ;
      msg_eq_dec := string_dec ;
      name_eq_dec := Name_eq_dec ;
      nodes :=  ;
      all_names_nodes := In_n_Nodes ;
      no_dup_nodes := nodup ;
      init_handlers := init_data ;
      net_handlers := fun dst src msg s =>
                        runGenHandler_ignore s (NetHandler dst src msg) ;
      input_handlers := fun nm msg s =>
                          runGenHandler_ignore s (InputHandler nm msg)
    }.


End Notary.
