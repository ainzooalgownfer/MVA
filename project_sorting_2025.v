(* ** The goal of this project is to implement a "certified sorting algorithm". Please refer to the exercises at  https://members.loria.fr/SStratulat/files/node_modules/jscoq/lab5.html. You can use https://x80.org/collacoq/ for editing the Coq code *)

(* We are interested to certify the quicksort algorithm *)

(* A specification of correctness for a general sorting algorithm *)

From Coq Require Import Arith List.

(* A sorting algorithm must rearrange the elements into a list that is totally ordered. *)

Inductive sorted : list nat -> Prop :=
  snil : sorted nil
| s1 : forall x, sorted (x::nil)
| s2 : forall x y l, sorted (y::l) -> x <= y ->
    sorted (x::y::l).


(* an important property about sorted lists *)

Lemma sorted_sorted: forall a l, sorted (a::l) -> sorted l.
Proof.
  induction l; simpl; intros.
  - apply snil.
  - inversion H; subst.
    trivial.
Qed.


(* The sorted list should be a permutation of the input list *)
 
Fixpoint count x l :=
  match l with
    nil => 0
  | hd :: tl => if x =? hd then S (count x tl) else count x tl
  end.

Definition permutation l l' := 
  forall x, (In x l <-> In x l') /\ count x l = count x l'. 


(* some properties about permutation as auxiliary lemmas *)

Lemma permutation_transitive :  forall (l1 l2 l3 : list nat),
  permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
(* FILL IN HERE *) Admitted.


Lemma permutation_sym : forall (l1 l2 : list nat), permutation l1 l2 -> permutation l2 l1.
(* FILL IN HERE *) Admitted.

Lemma permutation_C : forall a l1 l2, permutation l1 l2 -> permutation (a::l1) (a::l2).
(* FILL IN HERE *) Admitted.

(* The specification for a sorting algorithm *)

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall al, permutation (f al) al /\ sorted (f al).


(**** It is time to check an implementation of quicksort ****)

(* extracts the sublist of l with the elements smaller or equal than x *)
Fixpoint LoE x l :=
  match l with
    nil => nil
  | hd :: tl => if Nat.leb hd x then hd :: (LoE x tl) else LoE x tl
  end.

(* some properties about LoE as auxiliary lemmas *)

Lemma len_LoE : forall x l, Nat.le (length (LoE x l)) (length l) .
Proof.
 intros.
 induction l; simpl.
 - auto.
 - case_eq (a <=? x); intro.
 -- simpl. apply le_n_S. assumption.
 -- apply le_S. assumption.
Qed.

Lemma le_LoE : forall x y l,  In x (LoE y l) -> Nat.le x y.
Proof.
 induction l; simpl.
 - intro. contradiction.
 - case_eq (a <=? y); intro.
 -- simpl. intro. apply leb_complete in H. destruct H0.
 --- rewrite H0 in H. assumption.
 --- apply IHl. assumption.
 -- assumption.
Qed.

Lemma lt_LoE_rev : forall x y l,  In x l -> Nat.le x y -> In x (LoE y l).
Proof.
 induction l; simpl.
 - intro; contradiction.
 - intro. case_eq (a <=? y); intro.
 -- intro. simpl. destruct H.
 --- left; assumption.
 --- right. apply IHl; assumption.
 -- intro. destruct H.
 --- apply leb_complete_conv in H0. rewrite H in H0. unfold Nat.le in H1.
     Print Nat.le_lt_trans. apply (Nat.le_lt_trans _ _ _ H1) in H0. contradict H0.
     apply Nat.lt_irrefl.
 --- apply IHl; assumption.
Qed.
      

(* computing the sublist of l with the elements greater than x *)

Fixpoint High x l :=
  match l with
    nil => nil
  | hd :: tl => if Nat.leb hd x then High x tl else hd :: (High x tl)
  end.
 
(* some properties about High as auxiliary lemmas *)

Lemma len_High : forall x l, Nat.le (length (High x l)) (length l) .
Proof.
 induction l; simpl.
 - auto.
 - case_eq (a <=? x); intro.
 -- apply le_S. assumption.
 -- simpl. apply le_n_S. assumption.
Qed.
 

Lemma lt_High : forall x y l,  In x (High y l) -> Nat.lt y x.
Proof.
 induction l; simpl.
 - intro; contradiction.
 - case_eq (a <=? y); intro.
 -- assumption.
 -- simpl. intro. destruct H0.
 --- apply leb_complete_conv in H. rewrite H0 in H. assumption.
 --- apply IHl. assumption.
Qed.
 

Lemma lt_High_rev : forall x y l,  In x l -> Nat.lt y x -> In x (High y l).
Proof.
 induction l; simpl.
 - intro; contradiction.
 - intros. case_eq (a <=? y); intro.
 -- apply IHl.
 --- destruct H.
 ---- unfold Nat.lt in H0. apply leb_complete in H1. rewrite H in H1.
      apply (Nat.le_lt_trans _ _ _ H1) in H0. contradict H0. apply Nat.lt_irrefl.
 ---- assumption.
 --- assumption.
 -- simpl. destruct H.
 --- left; assumption.
 --- right. apply IHl; assumption.
Qed.

From Coq Require Import FunInd.
Require Import Recdef. 
Require Import Wellfounded.

(* The Quicksort algorithm *)

Function QS (l: list nat) {wf (fun (l1: list nat) (l2: list nat) => Nat.lt (length l1) (length l2)) l}  :=
  match l with
    nil => nil
  | hd :: tl => app (QS (LoE hd tl)) (hd :: (QS (High hd tl)))
  end.
intros.
unfold Nat.lt. unfold lt. simpl. assert (H:= len_High hd tl). apply le_n_S. auto.
intros. unfold Nat.lt. unfold lt. assert (H:= len_LoE hd tl). simpl. apply le_n_S.
auto.
apply (wf_inverse_image). apply well_founded_ltof.
Qed.


(* defining the explicit induction schema from the QS definition, to be used in the subsequent proofs *)

Functional Scheme QS_ind := Induction for QS Sort Prop.

Require Export Coq.Lists.List.
Export ListNotations. 

(* a test for QS for sorting the first 10 digits of pi *) 

Example sort_pi: QS [3;1;4;1;5;9;2;6;5;3;5]
                 = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
 repeat (rewrite QS_equation; simpl).
 reflexivity.
Qed.

(* some properties about QS as auxiliary lemmas *)

Lemma QS_in : forall x l, In x l -> In x (QS l).
(* FILL IN HERE *) Admitted.


Lemma QS_in_rev : forall x l,  In x (QS l) -> In x l.
(* FILL IN HERE *) Admitted.

(* some properties about In as auxiliary lemmas *)

Lemma In_LoE : forall x y l, In x (LoE y l) -> In x l.
(* FILL IN HERE *) Admitted.

Lemma In_High : forall x y l, In x (High y l) -> In x l.
(* FILL IN HERE *) Admitted.

(* some properties about 'count' as auxiliary lemmas *)

Lemma count_LoE : forall x y l,  Nat.lt y x -> count x (LoE y l) = 0.
(* FILL IN HERE *) Admitted.

Lemma count_In_zero : forall x l, ~ In x l <-> count x l = 0.
(* FILL IN HERE *) Admitted.

Lemma count_app : forall x l1 l2, count x (app l1 l2) = count x l1 + (count x l2).
(* FILL IN HERE *) Admitted.

Lemma count_LoE_count : forall x l, count  x (LoE x l) = count x l.
(* FILL IN HERE *) Admitted.

Lemma count_LoE_count1 : forall x hd l, (x =? hd) = false -> (x <=? hd) = true -> count x (LoE hd l) = count x l.
(* FILL IN HERE *) Admitted.

Lemma  count_High_count1 : forall x hd l, (x =? hd) = false -> (x <=? hd) = false -> count x (High hd l) = count x l.
(* FILL IN HERE *) Admitted.

(* some important lemmas about QS *) 

Lemma QS_permutation : forall l, permutation (QS l) l.
(* FILL IN HERE *) Admitted.

Lemma QS_is_sorted : forall l, sorted (QS l).
Proof.
 intro.
 functional induction (QS l).
 - constructor.
 - assert (forall x : nat, In x (QS (LoE hd tl)) -> Nat.le x hd).
   {
    intros. apply QS_in_rev in H. apply le_LoE with tl. assumption.
   }
   induction (QS (LoE hd tl)); simpl.
 --- case_eq (QS ((High hd tl))); intro.
 ---- constructor.
 ---- intros. constructor.
 ----- rewrite H0 in IHl1. assumption.
 ----- apply Nat.lt_le_incl. apply lt_High with tl. apply QS_in_rev.
       rewrite H0. simpl; auto.
 --- assert ( sorted (l ++ hd :: (QS (High hd tl)))).
     {
      apply IHl.
      -  apply (sorted_sorted a). assumption.
      - intros. apply H. simpl. right; assumption.
     }
     induction l; simpl.
     + constructor.
       ++ assumption.
       ++ apply H. simpl; auto.
     + constructor.
       ++ assumption.
       ++ inversion IHl0. assumption.
Qed.

(* the main lemma *)

Lemma QS_is_sound : is_a_sorting_algorithm QS.
 unfold is_a_sorting_algorithm.
 intro.
 split.
 - apply QS_permutation.
 - apply QS_is_sorted.
Qed.


(* ** You can now extract OCaml code that implements our sorting algorithm *)

From Coq Require Extraction.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Parameter leb: nat -> nat -> bool.
Extract Inlined Constant Nat.leb => "( <= )".

Recursive Extraction QS.

(** * WOW! *)

(* save the extracted code listed on the right to some file, called code.ml. 

Add at the end of the file 

;; 
assert (qS [3;1;4;1;5;9;2;6;5;3;5] 
          = [1;1;2;3;3;4;5;5;5;6;9]);;

then compile it with 'ocamlc code.ml' and run it with './a.out'

  *)
