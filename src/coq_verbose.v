Require Import Classical.

Lemma contrapose_prop: forall P Q:Prop, (~ Q -> ~P) -> P -> Q.
Proof.
intros.
apply NNPP;tauto.
Qed.

(* Coq verbose *)

Ltac check_hyp_is h stmt :=
 let Hf:=fresh in 
  assert (Hf: stmt);[exact h|idtac ];clear Hf.


Ltac assume_tac name stmt :=
 match goal with
  |- ?P -> ?Q => intro name;check_hyp_is name stmt
 end.

Ltac Fix name :=
 match goal with
   |- ?P -> ?Q => fail 1 "Not a forall statement"
|  |- forall x, ?P => intro name
end.


Ltac assume_contr_tac name stmt := apply NNPP;hnf;assume_tac name stmt.

Ltac isconj :=
 match goal with
|  |- ?P /\ ?Q => idtac
end.

Ltac letsprove_left stmt :=
 match goal with
 |  |- stmt /\ ?Q => split
 end.

Ltac letsprove_tac stmt :=
 match goal with
 |  |- ?P => hnf;isconj;split;letsprove_tac stmt
 |  |- stmt => idtac
 |  |- stmt \/ ?Q  => left
 |  |- ?P \/ stmt  => right
 end.

Ltac letsprove_tac_error stmt := letsprove_tac stmt  || fail 2 "This is not what should be proven".

Tactic Notation "Assume" "that" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.
Tactic Notation "Assume" simple_intropattern(I) ":" constr(H) :=
 assume_tac I H.

Tactic Notation "Assume" "for" "contradiction" simple_intropattern(I) ":" constr(H) :=
 assume_contr_tac I H.
 
Tactic Notation "Let's" "prove" "that" constr(stmt) := 
 letsprove_tac stmt.

Tactic Notation "Let's" "prove" "it" "is" "contradictory" := 
 exfalso.

Tactic Notation "Let's" "prove" "that" constr(witness) "works" := 
 exists witness.

Tactic Notation "Let's" "prove" "that" constr(witness) "works" "ie" constr(stmt) := 
 exists witness;letsprove_tac stmt.

Tactic Notation "Let's" "prove" "the" "contrapositive" := apply contrapose_prop.
 
Tactic Notation "By" constr(H) "it" "suffices" "to" "prove" "that" constr(stmt) := apply H;letsprove_tac stmt.

Tactic Notation "By" constr(H) "it" "suffices" "to" "prove" "that" constr(stmt1) "and" constr(stmt2) := 
 apply H;[letsprove_tac stmt1|letsprove_tac stmt2].


Example test1 : forall n:nat, n>0 -> True.
Proof.
Fix n.
Assume that H : (n>0).
Assume for contradiction H2 : (~ True).
intuition.
Qed.

Example test2 : forall n:nat, n>0 -> True.
Proof.
Fix n.
Assume H : (n>0).
auto.
Qed.

Example test3 : forall P Q : Prop, ( ~Q -> ~ P) -> P -> Q.
Proof.
intros.
Assume for contradiction H2 : (~ Q).
apply (H H2 H0).
Qed.


Example test_letsprove_1 : forall P Q: Prop, P -> P \/ Q.
Proof.
Fix P.
Fix Q.
Assume H : P.
Let's prove that P.
assumption.
Qed.

Example test_letsprove_2 : forall P Q: Prop, Q -> P \/ Q.
Proof.
Fix P.
Fix Q.
Assume H : Q.
Let's prove that (P \/ Q).
Let's prove that (Q).
assumption.
Qed.

Example test_letsprove_3 : True <-> True.
Proof.
Let's prove that (True -> True).
intuition.
intuition.
Qed.

Example test_letsprove_4 : False -> True.
Proof.
intro H.
Let's prove it is contradictory.
intuition.
Qed.


Example test_letsprove_4b : False -> True.
Proof.
Let's prove the contrapositive.
intuition.
Qed.


Example test_letsprove_5 : exists n:nat, S(n) = 2.
Proof.
Let's prove that 1 works.
trivial.
Qed.

Example test_letsprove_6 : exists n:nat, S(n) = 2.
Proof.
Let's prove that 1 works ie (2=2).
trivial.
Qed.

Example test_by_1 : forall P Q : Prop, (P -> Q) ->  P -> Q.
Proof.
intros.
By H it suffices to prove that P.
assumption.
Qed.

Example test_by_2 : forall P1 P2 Q : Prop, (P1 -> P2 -> Q) ->  P1 -> P2 -> Q.
Proof.
intros.
By H it suffices to prove that P1 and P2.
Let's prove that P1.
assumption.
Let's prove that P2.
assumption.
Qed.

