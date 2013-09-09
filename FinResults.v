Require Import Coq.Vectors.Fin.

(** * Some useful results about finite sets *)

Definition fin_beq {n:nat} (x y:Fin.t n) : bool :=
  Fin.rect2 (fun _ _ _ => bool)
            (* F1 F1 *) (fun _ => true)
            (* F1 FS *) (fun _ _ => false)
            (* FS F1 *) (fun _ _ => false)
            (* FS FS *) (fun _ _ _ rec => rec) x y.

Lemma fin_beq_eq : forall n x y, @fin_beq n x y = true <-> x = y.
Proof.
  intros. split; intros.
  Require Import Coq.Program.Equality.
  (* -> *) induction x; dependent induction y; try reflexivity; try inversion H.
           rewrite (IHx y H1). reflexivity.
  (* <- *) induction x. inversion y; subst; simpl; reflexivity.
                        inversion y; subst. unfold fin_beq in *. simpl in *. eapply IHx. reflexivity.
                        unfold fin_beq in *; simpl in *. eapply IHx. reflexivity.
Qed.
Definition fin_lt {n:nat} (x y:Fin.t n) : bool :=
  Fin.rect2 (fun _ _ _ => bool)
            (* F1 F1 *) (fun _ => false)
            (* F1 FS *) (fun _ _ => true)
            (* FS F1 *) (fun _ _ => false)
            (* FS FS *) (fun _ _ _ rec => rec) x y.
Program Lemma proj1_to_nat_comm : forall n (x:t n), proj1_sig (to_nat (FS x)) = S (proj1_sig (to_nat x)).
Proof.
  intros.
 induction x. compute. reflexivity. rewrite IHx. 
 simpl. induction (to_nat x). simpl. reflexivity.
Qed.
Program Lemma fin_lt_nat : forall n (x y:Fin.t n), @fin_lt n x y = true <-> (to_nat x) < to_nat y.
Proof.
  intros. split.
  eapply Fin.rect2 with (a := x) (b := y); intros.
      inversion H. 
      induction f. simpl. auto with arith. rewrite proj1_to_nat_comm. compute. auto with arith.
      inversion H.
      induction f. repeat rewrite proj1_to_nat_comm. auto with arith.
      rewrite proj1_to_nat_comm. rewrite (@proj1_to_nat_comm _ g).
      auto with arith.
  (* <- *)
  eapply Fin.rect2 with (a := x) (b := y); intros; try solve[inversion H].
      compute; auto.
      simpl. apply H. repeat rewrite proj1_to_nat_comm in H0. inversion H0. constructor. subst. auto with arith.
Qed.
Lemma fin_dec : forall n (x y : t n), {x=y}+{not (x=y)}.
  intros. eapply Fin.rect2 with (a := x) (b := y); intros.
  left. reflexivity. right. discriminate.
  right. discriminate. 
  induction H. subst. left; auto.
  right. red in b. red. intros. apply b.
  inversion H.
  assert (projT1 (existT (fun n => t n) n0 f) = projT1 (existT (fun n => t n) n0 g)).
      compute. auto.
  eapply Eqdep_dec.inj_pair2_eq_dec. apply Peano_dec.eq_nat_dec.
  apply H1.
Qed.

