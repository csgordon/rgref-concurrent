Require Import Utf8.

Parameter var : Set.
Parameter var_dec : forall (v v':var), {v=v'}+{v<>v'}.

Inductive expr : Set :=
  | evar : var -> expr
  | app : expr -> expr -> expr
  | deref : expr -> expr
  | ref : expr -> expr
  | rgrefl : expr -> expr -> expr
  | enat : nat -> expr
  | ebool : bool -> expr
  | eunit : expr
  | elam : var -> ty -> (var -> expr) -> expr
  | ety : ty -> expr
  | easgn : var -> expr -> expr
  | eproc : var -> ty -> (var -> expr) -> expr
with
  ty : Set :=
  | tynat : ty
  | tybool : ty
  | tyunit : ty
  | typrop : ty
  | tyeq : expr -> expr -> ty
  | tyref : ty -> expr -> expr -> expr -> ty
  | typrod : var -> ty -> (var -> ty) -> ty
  | typroc : ty -> ty -> ty
  | tyheap : ty.

Notation "(λC x ∈ τ . e )" := (eproc x τ e) (at level 80).
Notation "(λ x ∈ τ . e )" := (elam x τ e) (at level 80).
Notation "(Π x ∈ τ → τ' )" := (typrod x τ τ') (at level 80).
Infix "←" := easgn (at level 50).
Notation "! e" := (deref e) (at level 80).
Notation "ref{ τ | P }[ R , G ]" := (tyref τ P R G) (at level 40).

Definition rgnat : nat -> expr := (fun (n:nat) => enat n).
Coercion rgnat : nat >-> expr.
Definition rgbool : bool -> expr := (fun (b:bool) => ebool b).
Coercion rgbool : bool >-> expr.
Definition u2u : unit -> expr := fun _ => eunit.
Coercion u2u : unit >-> expr.
Definition rgvar : var -> expr := fun v => evar v.
Coercion rgvar : var >-> expr.

Section SyntaxTests.
Set Implicit Arguments.
Variable x : var.
Example fabstest : expr := elam x (tynat) (fun x=> app (evar x) (evar x)).
Example tabstest : ty := typrod x (tynat) (fun x=> tyeq (evar x) (evar x)).
End SyntaxTests.

Definition tyenv := list (var * ty).

Reserved Notation "Γ ⊢ e ∈ τ ⊣ Γ'" (at level 50).
Reserved Notation "Γ ⊢ e ∈ τ ⇒ Γ'" (at level 50).
Reserved Notation "⊢ Γ `ctxt`" (at level 50).
Reserved Notation "Γ ⊢ τ `type`" (at level 50).
Reserved Notation "Γ ⊢ τ ↝ τ'" (at level 50).
Reserved Notation "Γ ⊢ e ↝ e' ∈ τ" (at level 50).
Reserved Notation "⊢ Γ ↝ Γ'" (at level 50).

Infix "→C" := (typroc) (at level 40).

Inductive typesplit : tyenv -> ty -> ty -> ty -> Prop :=
  | natsp : forall Γ, typesplit Γ tynat tynat tynat
  | boolsp : forall Γ, typesplit Γ tybool tybool tybool
  | unitsp : forall Γ, typesplit Γ tyunit tyunit tyunit
  | symmsp : forall Γ τ τ' τ'', typesplit Γ τ τ' τ'' -> typesplit Γ τ τ'' τ'
.
Notation "Γ ⊢ τ ≺ τ' ⋇ τ''" := (typesplit Γ τ τ' τ'') (at level 50).

Inductive puretyping : tyenv -> expr -> ty -> tyenv -> Prop :=
  | purenat : forall Γ n, Γ ⊢ (enat n) ∈ tynat ⊣ Γ
  | purebool : forall Γ b, Γ ⊢ (ebool b) ∈ tybool ⊣ Γ
  | pureunit : forall Γ, Γ ⊢ eunit ∈ tyunit ⊣ Γ
  | puredrop : forall x τ Γ, ((x,τ)::Γ)%list ⊢ x ∈ τ ⊣ Γ
  | puresplit : forall x τ τ' τ'' Γ,
                  Γ⊢τ≺τ'⋇τ'' ->
                  ((x,τ)::Γ)%list ⊢ x ∈ τ' ⊣ ((x,τ'')::Γ)%list
(*  | pureabs *)
(*  | pureapp : forall Γ e₁ x τ τ' Γ' e₂ Γ'',
                Γ⊢e₁∈(typrod x τ τ')⊣Γ' ->
                Γ'⊢e₂∈τ⊣Γ'' ->
                Γ⊢(app e₁ e₂)∈(τ' e₁)⊣Γ''*)
  | pureconv : forall Γ e τ τ' Γ', Γ⊢e∈τ⊣Γ' -> tyconv Γ' τ τ' -> Γ⊢e∈τ'⊣Γ'
(*  | purederef : forall Γ e τ P R G Γ',
                  Γ⊢e∈ref{τ|P}[R,G]⊣Γ' ->
                  (* G reflexive -> *)
                  Γ⊢(!e)∈(>>[R,G]>>τ)⊣Γ'*)
with
  impuretyping : tyenv -> expr -> ty -> tyenv -> Prop :=
(*  | impasgn
  | impswap
  | impref *)
  | impproc : forall Γ x τ e τ' Γ',
               (* AllSelfSplittable Γ -> *)
               ((x,τ)::Γ)%list⊢(e x)∈τ'⇒Γ' ->
               Γ⊢eproc x τ e ∈ (typroc τ τ')⇒Γ'
  | impapp : forall Γ Γ₁ Γ₂ e₁ e₂ τ τ',
               Γ⊢e₁∈(τ →C τ')⇒Γ₁ ->
               Γ₁⊢e₂∈τ⇒Γ₂ ->
               Γ⊢(app e₁ e₂)∈τ'⇒Γ₂
  | implift : forall Γ Γ' e τ, Γ⊢e∈τ⊣Γ' -> Γ⊢e∈τ⇒Γ'
with
  tyconv : tyenv -> ty -> ty -> Prop :=
  | tyconv_refl : forall Γ τ, tyconv Γ τ τ
where "Γ ⊢ e ∈ τ ⊣ Γ'" := (puretyping Γ e τ Γ')
and "Γ ⊢ e ∈ τ ⇒ Γ'" := (impuretyping Γ e τ Γ').


Hint Constructors puretyping.
Hint Constructors impuretyping.
Hint Constructors tyconv.
Hint Constructors typesplit.

Ltac typechecker :=
  intros;
  match goal with 
  | [ |- puretyping _ _ _ _ ] => constructor
  | [ |- impuretyping _ _ _ _ ] => try solve[eapply impproc; typechecker];
                                   try solve[eapply impapp; typechecker];
                                   try solve[eapply implift; typechecker]
  | [ |- tyconv _ _ _ ] => constructor
  | [ |- typesplit _ _ _ _ ] => constructor
  | [ |- exists _, _ ] => eexists; typechecker
  | _ => eauto
  end; eauto.

Section TypecheckingTests.
Example n_typing : forall Γ (n:nat), exists Γ', exists τ, Γ⊢n∈τ⊣Γ'.
Proof.
  typechecker.
Qed.

Example b_typing : forall Γ (b:bool), exists Γ', exists τ, Γ⊢b∈τ⊣Γ'.
Proof.
  typechecker.
Qed.

Example var_typing : forall x Γ, exists Γ', exists τ, ((x,tynat)::Γ)%list⊢x∈τ⊣Γ'.
Proof.
  typechecker.
Qed.

Example impure_app : forall x, exists Γ', nil⊢(app (eproc x tynat (fun x=>x)) 3)∈tynat⇒Γ'.
Proof. typechecker.
Qed.
End TypecheckingTests.
