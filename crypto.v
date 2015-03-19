Require Import List.
Require Import String.
Require Import DepList.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.DecidableType.
Require Import Coq.FSets.FMapFacts.
Import ListNotations.

Require Import Coq.Classes.EquivDec.

Class Params  :=
  {
    state : Type ;
    input : Type ;
    output : Type ;

    name : Type ;
    name_eq_dec : EqDec name eq ;

    msg : Type ;
    msg_eq_dec : EqDec msg eq ;

    box_sk : Type ;
    box_sk_eq_dec : EqDec box_sk eq ;

    box_pk : Type ;
    box_pk_eq_dec : EqDec box_pk eq ;

    box_ct : Type ;

    box_new : name -> nat -> box_sk ;
    box_keygen : box_sk -> box_pk ;
    box : box_sk -> box_pk -> msg -> box_ct ;
    box_open : box_sk -> box_pk -> box_ct -> option msg
  }.

Module string_as_DT <: DecidableType.
  Definition t := string.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := string_dec.
End string_as_DT.

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

Module Expr (StringMap:FMapInterface.WSfun string_as_DT).
  Definition params := StringMap.t Type.
  Module MapFacts := WFacts_fun string_as_DT StringMap.
  Module MapProperties := WProperties_fun string_as_DT StringMap.
  Import StringMap.
  Import MapFacts.
  Import MapProperties.
  Implicit Arguments empty [elt].
  Implicit Arguments add [elt].

  Definition consistent (l r:params) : Prop :=
    forall p vl vr, MapsTo p vl l -> MapsTo p vr r -> vl = vr.
  Fixpoint consistent' (ms:list params) := match ms with
  | nil => True
  | m::ms' => (forall m', List.In m' ms' -> consistent m m')
              /\
              consistent' ms'
  end.

  Definition merge := fold (@add Type).
  Definition merge' := fold_right merge empty.

  Inductive expr : params -> Type -> Type := 
  | Const : forall {T:Type}, T -> expr empty T
  | Param : forall {T:Type} V n, expr (add n V empty) T
  | External : forall {T: Type}
      {argspecs:list (params * Type)}
      (f:funcType (List.map snd argspecs) T)
      (args:hlist (uncurry (@expr)) argspecs),
    consistent' (List.map fst argspecs) ->
    expr (merge' (List.map fst argspecs)) T
  .

  Fixpoint eval
    {T:Type}
    (e:@expr nil T)
    {struct e}
    : T
    .
    refine (match e with
    | Const x => x
    | Param T n => _
    | @External T' argtypes f argparams args => _
    end).
    intro; auto. (* no variables in expr [] *)
    assert (T = T) by admit; subst.
    assert (argparams = nil) by admit; subst.
    simpl. apply eval, e.
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

End Expr.


Section IND.
  Context `{params : Params}.

  Inductive eIND : forall {V T C:Type}, V -> expr T -> expr C -> Prop :=
  | INDConst : forall {V T C} (v:V) (ctx:expr C) (t:T), eIND v (Const t) ctx
  | INDArgs : forall {V T C} (v:V) (ctx:expr C) argts f args,
          (forall W (e:expr W), hIn e args -> eIND v e ctx)
          -> eIND v (@External T argts f args) ctx
  | INDBoxKey : forall {V C} (v:V) (ctx:expr C) nm idx pk m,
          eIND v (terop box (binop box_new nm idx) pk m) ctx
  | INDBoxMessage : forall {V C} (v:V) (ctx:expr C) nm idx pk m,
          eIND (binop box_new nm idx) ctx ctx ->
          eIND v (terop box (binop box_new nm idx) pk m) ctx
  | INDBoxOpen : forall {V C} (v:V) sk pk sk' pk' m (ctx:expr C),
          eIND v m ctx ->
          eIND v (terop box_open sk pk' (terop box sk' pk m)) ctx
  .
End IND.

Class Handlers `(P : Params) :=
  {
    (* TODO: expr should take in previous state as expr, not evaled
      because we want to track taint across state changes *)
    init : name -> msg -> state; (* v is random seed *)
    net_handler :   name -> state -> msg   -> (state * expr msg * list output) ;
    input_handler : name -> state -> input -> (state * expr msg * list output)
  }.
