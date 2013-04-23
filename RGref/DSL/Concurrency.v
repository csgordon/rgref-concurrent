Require Import RGref.DSL.DSL.
Require Import RGref.DSL.Fields.


(* CAS Axioms and notations *)
Axiom cas_core : forall Γ T P R G (r : ref{T|P}[R,G]) (e0 : T) (e' : T),
                        (forall h, h[r]=e0 -> G e0 e' h (heap_write r e' h)) ->
                        rgref Γ bool Γ.

Notation "CAS( r , e , e' )" := (cas_core _ _ _ _ _ r e e' _) (at level 70).

Axiom field_cas_core : forall Γ T P R G F FT `{FieldTyping T F} 
                              (r : ref{T|P}[R,G]) (f:F) `{FieldType T F f FT}
                              (fv0 : FT) (fv' : FT),
                              (forall h v, h[r]=v -> getF v = fv0 ->
                                           G v (setF v fv') h (heap_write r (setF v fv') h)) ->
                              rgref Γ bool Γ.

Notation "fCAS( r → f , e , e' )" := (field_cas_core _ _ _ _ _ _ _ _ r f _ e e' _) (at level 70).

