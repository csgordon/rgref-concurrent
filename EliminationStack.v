Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Concurrency.
Require Import RGref.DSL.Fields.
Require Import TrieberStack. (* Reuse the node implementation *)

(** Elimination Stack
    We'll roughly follow the paper "A Scalable Lock-free Stack Algorithm"
    by Hendler, Shavit, and Yerushalmi, from SPAA'04. *)
Inductive Op : Set := PUSH | POP.
Inductive  ThreadInfo : Set :=
  | mkTI : nat -> Op -> Node -> nat -> ThreadInfo.
Inductive TIFields : Set := id | op | cell | spin.
Instance ti_ft : FieldTyping ThreadInfo TIFields.
Instance ti_id : FieldType ThreadInfo TIFields id nat :=
{ getF := (fun ti => match ti with mkTI i o c s => i end);
  setF := (fun ti v => match ti with mkTI i o c s => mkTI v o c s end)
}.
Instance ti_op : FieldType ThreadInfo TIFields op Op :=
{ getF := (fun ti => match ti with mkTI i o c s => o end);
  setF := (fun ti v => match ti with mkTI i o c s => mkTI i v c s end)
}.
Instance ti_cell : FieldType ThreadInfo TIFields cell Node :=
{ getF := (fun ti => match ti with mkTI i o c s => c end);
  setF := (fun ti v => match ti with mkTI i o c s => mkTI i o v s end)
}.
Instance ti_spin : FieldType ThreadInfo TIFields spin nat :=
{ getF := (fun ti => match ti with mkTI i o c s => s end);
  setF := (fun ti v => match ti with mkTI i o c s => mkTI i o c v end)
}.

Section Body.
  
  Parameter size : nat.
  Parameter mypid : nat.
  Parameter pid_size : mypid < size.

  (* Each thread may only modify its own entry in the location array *)
  Definition SingleCellHavoc {n c:nat} {T:Set} (pf:c < n) : hrel (Array n T) :=
    fun (a a':Array n T) (h h':heap) => forall (i:fin n), i=(of_nat_lt pf) \/ array_read a i = array_read a' i.
  Lemma precise_single_cell_havoc : forall n c T (rch:ImmediateReachability T) (pf:c<n),
                                      precise_rel (@SingleCellHavoc n c T pf).
  Proof.
    intros. compute -[of_nat_lt]. intros.
    induction (H1 i); eauto.
  Qed. (* SingleCellHavoc is local *)
  Hint Resolve @precise_single_cell_havoc.
  
  Inductive ElimStack : Set :=
  | mkES : option (ref{Node|any}[local_imm,local_imm]) ->
           ref{(Array size (option (ref{ThreadInfo|any}[havoc,local_imm])))|any}[havoc,SingleCellHavoc pid_size] ->
           ref{(Array size nat)|any}[havoc,havoc] ->
           ElimStack.
  Inductive ES_fields : Set := stack | location | collision.
  Instance es_ft : FieldTyping ElimStack ES_fields.
  Instance es_stack : FieldType ElimStack ES_fields stack _ :=
  { getF := fun es => match es with mkES st loc col => st end;
    setF := fun es v => match es with mkES st loc col => mkES v loc col end
  }.
  Instance es_loc : FieldType ElimStack ES_fields location _ :=
  { getF := fun es => match es with mkES st loc col => loc end;
    setF := fun es v => match es with mkES st loc col => mkES st v col end
  }.
  Instance es_col : FieldType ElimStack ES_fields collision _ :=
  { getF := fun es => match es with mkES st loc col => col end;
    setF := fun es v => match es with mkES st loc col => mkES st loc v end
  }.
  Print ImmediateReachability.
  Inductive es_reachability : forall T P R G, ref{T|P}[R,G] -> ElimStack -> Prop :=
  | st_reach : forall st loc col,
                 es_reachability _ _ _ _ st (mkES (Some st) loc col)
  | loc_reach : forall st loc col,
                  es_reachability _ _ _ _ loc (mkES st loc col)
  | col_reach : forall st loc col,
                  es_reachability _ _ _ _ col (mkES st loc col).
  Instance reach_es : ImmediateReachability ElimStack :=
  { imm_reachable_from_in := es_reachability }.
  Print Containment.
  Instance cont_es : Containment ElimStack.
  Admitted. (* TODO *)
  Instance fold_es : rel_fold ElimStack.
  Admitted. (* TODO: This is one of those cases where the result of folding
               isn't necessarily valid; if you weaken guarantees of the
               ES interior pointers, you can't compose the results into
               an ES!  In this case we could parameterize ES by
               relations for the pointer members, and then folding would
               work.  But for recursive strucutures like the M&S queue or
               Heller set, this is important.  Might need to go ahead and
               directly specify a field-specific fold, since we're going
               to access these things field-at-a-time anyways.

               Then in general I could build Allocatable, FullDeref, and
               FieldDeref parameterized typeclasses for different use
               cases, and derive those from instances of rel_fold, Containment,
               etc. as appropriate.  This way I can easily have types
               that for example can be accessed field-at-a-time without
               the ability to be accessed all-at-once (like ElimStack) *)

  (* TODO: More precise rely, guarantee, for arrays, ElimStack. *)
  Definition EliminationStack := ref{ElimStack|any}[havoc,havoc].

  Program Definition alloc_es {Γ} (_:unit) : rgref Γ EliminationStack Γ :=
    locarr <- Alloc (new_array size _ None);
    colarr <- Alloc (new_array size _ 0);
    Alloc (mkES None locarr colarr).

  (* TODO: more precise rely, guarantee, predicate for ThreadInfo operations. *)
  Program Definition TryCollision {Γ} (es:EliminationStack) (him:nat) (p:ref{ThreadInfo|any}[havoc,havoc]) (q:ref{ThreadInfo|any}[havoc,havoc]) : rgref Γ bool Γ :=
    match p~>op with
    | PUSH => (*@field_cas_core _ _ _ _ _ _ _ _ (es~>location) mypid _ _ (Some q) None _ *)
              fCAS((es~>location)→him, Some q, Some p) (* WTF? where is 'him' scoped in the original paper??? globally? *)
    | POP => res <- fCAS((es~>location)→him, Some q, None);
             if res
             then (_ <- {[p ~~> cell ]}:= (q ~> cell);
                   _ <- {[(es~>location)~~>mypid]}:= @None _;
                   rgret true)
             else rgret false
    end.

  (* Paper uses a type 'ProcessInfo' which appears to be intended to be 'ThreadInfo' *)
  Program Definition FinishCollision {Γ} (es:EliminationStack) (p:ref{ThreadInfo|any}[havoc,havoc]) : rgref Γ unit Γ :=
    match (p ~> op) with
    | POP =>
        (*[ @field_read ThreadInfo _ _ _ _ _ _ _ _ _ p cell _ ti_cell ]:= _*)
        (*[ @field_read ThreadInfo _ _ _ _ _ _ _ _ _ p cell _ _ ]:= _*)
        (*[ @field_read _ _ _ _ _ _ _ _ _ _ p cell _ _ ]:= _*)
        _ <- {[ p ~~> cell ]}:= ( ((es ~> location)~>mypid)~>cell );
        {[ (es~>location)~~>mypid ]}:= @None _
    | _ => rgret tt
    end.
  
  Program Definition LesOP {Γ} (es:EliminationStack) (p:ref{ThreadInfo|any}[havoc,havoc]) : rgref Γ unit Γ.
  Admitted.

  Program Definition TryPerformStackOp {Γ} (es:EliminationStack) (p:ref{ThreadInfo|any}[havoc,havoc]) : rgref Γ bool Γ :=
    match (p ~> op) with
    | PUSH => (phead <- (es~>stack);
               _ <- {[ (p~>cell)~~>next ]}:= phead;
               fCAS(es → stack, phead, Some _ ) (* Needs to be &p~>cell, but cell is embedded in ThreadInfo atm. Also need Node fields.
                                                   What should the R,G be for the Node ptr in ThreadInfo? We assign to it here, so
                                                   it can't be local_imm.  Later we set cell field of ThreadInfo to null, so
                                                   it should actually be an option of a ref to a Node.

                                                   OH! Or not... Fig. 3 seems to use EMPTY as value-copying the empty node... Line T11 vs. T15,
                                                   and the ThreadInfo def in Fig. 2 has the Cell inline...
                                                 *)
               )
    | POP => (phead <- es~>stack;
              match phead with
              | None => ( _ <- {[ p ~~> cell ]}:= EMPTY;
                          rgret true)
              | Some hd => (
                    pnext <- hd~>next;
                    IF fCAS(es→stack, phead, pnext)
                    THEN (_ <- {[ p ~~> cell ]}:= phead;
                          rgret true)
                    ELSE (_ <- {[ p ~~> cell ]}:= EMPTY;
                          rgref false)
                    )
               end
    end.
  
  Program Definition StackOp {Γ} (es:EliminationStack) (pInfo:ref{ThreadInfo|any}[havoc,havoc]) : rgref Γ unit Γ :=
    op <- TryPerformStackOp es pInfo;
    if op
    then rgret tt
    else LesOP pInfo.
