Require Import List.
Require Import DepList.
Import ListNotations.

Require Import Coq.Classes.EquivDec.

Class Params  :=
  {
    state : Type ;
    input : Type ;
    output : Type ;

    name : Type ;
    name_eq_dec : EqDec name eq ;

    v : Type ;
    v_eq_dec : EqDec v eq ;

    kdf : v -> v -> v (* key -> seed -> new key *) ;

    box_keygen : v -> v (* sk -> pk *) ;
    box : v -> v -> v -> v (* sk -> pk -> message -> ciphertext *) ;
    box_open : v -> v -> v -> v (* sk -> pk -> ciphertext -> message *)
  }.


Section Expr.
  Context `{params : Params}.

  Fixpoint funcType
    (argts:list Type)
    (T:Type)
    {struct argts}
    :=
    match argts with
      | nil => T
      | cons t argts' => t -> (funcType argts' T)
    end
  .

  Fixpoint call {T:Type}
    {argts}
    (f:@funcType argts T)
    (args : hlist id argts)
    : T
    .
    inversion args. {
      rewrite <- H in f; apply f.
    } {
      eapply call; [|eauto].
      rewrite <- H in f; apply f.
      unfold id in X; apply X.
    }
  Defined.

  Inductive expr (T:Type) : Type := 
  | Const : T -> expr T
  | External : forall {argts} (f:@funcType argts T) (args:hlist (@expr) argts), expr T
  .

  Implicit Arguments Const [T].
  Implicit Arguments External [T argts].

  Fixpoint eval
    {T:Type}
    (e:@expr T)
    {struct e}
    : T
    .
    refine (match e with
    | Const v => v
    | External f args => call f (hmap eval args)
    end).
  Defined.

  Section Ops.
    Ltac op xs := intros; eapply (@External _ xs); eauto; repeat (econstructor; eauto).

    Definition unop  {T A}     (f:A           -> T) : expr A -> expr T.                     op [A].     Defined.
    Definition binop {T A B}   (f:A -> B      -> T) : expr A -> expr B -> expr T.           op [A;B].   Defined.
    Definition terop {T A B C} (f:A -> B -> C -> T) : expr A -> expr B -> expr C -> expr T. op [A;B;C]. Defined.
  End Ops.

  Example evalOne : eval ((unop S) (Const 0)) = 1. reflexivity. Qed.
  Example evalTwoPlusThree : eval ((binop plus) ((unop S) (Const 1)) (Const 3)) = 5. reflexivity. Qed.


  Definition hIn {A:Type} {B:A->Type} {ls:list A} {t:A} (v:B t) (L:hlist B ls) : Prop :=
    exists (pf_m:@member A t ls), @hget A B t ls L pf_m = v.

  Inductive eIn {T:Type} (v:T) : @expr T -> Prop :=
  | inAtom : eIn v (Const v)
  | inArgs : forall argts f args, (exists e, hIn e args /\ eIn v e) -> eIn v (@External T argts f args)
  .
End Expr.

Class Handlers `(P : Params) :=
  {
    init : name -> v -> state; (* v is random seed *)
    net_handler :   name -> state -> v     -> (state * expr v * list output) ;
    input_handler : name -> state -> input -> (state * expr v * list output)
  }.