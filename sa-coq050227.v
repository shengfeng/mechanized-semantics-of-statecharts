(* Copyright (c), Department of Computer Science and Engineering
 * East China Normal University, Shanghai, China.
 * All rights reserved.
 * Author: Dou Liang
 * Email: ldou@cs.ecnu.edu.cn
 * Description: Mechanized Semantics of UML Statecharts
     and Refinement Relation
*)

Require Export String ListSet List Arith Bool. 
Open Scope nat_scope.
Open Scope type_scope.
Open Scope string_scope.
Open Scope list_scope.

(*==========Definition of Semantic Model of Statecharts==========*)
(* event name *)
Definition event := string.

(* state name *)
Definition sname := string.

(* transition name *)
Definition tname := string.

(* action name*)
Definition action := string.

(* sequence of action *)
Definition seqact := list action.

(* history type *)
Inductive history : Set :=
  | none : history
  | deep : history
  | shallow : history.

(* use natural numbers as identifiers *)
Inductive id : Set := Id : nat -> id.

(* a state represents the current values of all the variables *)
Definition state := id -> nat.

(* definitions for arithmetic expression and boolean expression *)
Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BGt : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp
  | BImp : bexp -> bexp -> bexp.

(* evaluation functions for arithmetic expression and boolean expression *)
Fixpoint aeval (st : state) (e : aexp) {struct e} : nat :=
  match e with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => plus (aeval st a1) (aeval st a2)
  | AMinus a1 a2  => minus (aeval st a1) (aeval st a2)
  | AMult a1 a2 => mult (aeval st a1) (aeval st a2)
  end.

Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint bgt_nat (n m : nat) {struct n} : bool :=
  match m with
  | O => true
  | S m' =>
      match n with
      | O => false
      | S n' => ble_nat m' n'
      end
  end.

Fixpoint beval (st : state)(e : bexp) {struct e} : bool :=
  match e with 
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BGt a1 a2 => bgt_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  | BOr b1 b2 => orb (beval st b1) (beval st b2)
  | BImp b1 b2 => orb (negb (beval st b1)) (beval st b2)
  end.

(* enter sequence of actions and exit sequence of actions *)
Definition entryexit := seqact * seqact.

(* guard condition *)
Definition guard := bexp.

(* transition *) 
Definition trans := 
  tname * nat * set sname * event * guard * seqact * set sname * nat * history.

(* label *)
Definition label := event * guard * seqact * bool.

(* trace *)
Definition trace := list event.


(*==========Syntax of Statecharts==========*)
Inductive sc : Type :=
  | basic_sc : sname -> entryexit -> sc
  | or_sc : sname -> list sc -> nat -> set trans -> entryexit -> sc
  | and_sc : sname -> set sc -> entryexit -> sc.

(*==========Equality Judgement==========*)
Definition event_dec : forall (a b : event), {a = b} + {a <> b}.
  exact string_dec.
Defined.

Definition sname_dec : forall (a b : sname), {a = b} + {a <> b}.
  exact string_dec.
Defined.

Definition tname_dec : forall (a b : tname), {a = b} + {a <> b}.
  repeat decide equality. 
Defined.

Definition action_dec : forall (a b : action), {a = b} + {a <> b}.
  repeat decide equality. 
Defined.

Definition entryexit_dec : forall (a b : entryexit), {a = b} + {a <> b}.
  repeat decide equality.
Defined.

Definition sc_dec : forall (a b : sc), {a = b} + {a <> b}.
  fix 1.
  repeat decide equality.
Defined.

Definition trans_dec : forall (a b : trans), {a = b} + {a <> b}.
  fix 1.    
  repeat decide equality. 
Defined.

Definition set_sname_dec : forall (a b : set sname), {a = b} + {a <> b}.
  repeat decide equality. 
Defined.

Definition set_set_sname_dec : forall (a b : set (set sname)), {a = b} + {a <> b}.
  repeat decide equality. 
Defined.

(*==========Auxiliary Functions==========*)
(* the current configuration of a statechart:
   the set of names of all currently active substates within s *)
Fixpoint conf (s : sc) {struct s} : (set sname) :=
  match s with
 | basic_sc n ee => (n :: nil)
 | or_sc n lsc l ltr ee => 
     set_add sname_dec n ((fix aux (num : nat) (ls : list sc) {struct ls} : (set sname) :=
       match num, ls with
       | 0, x :: l' => conf x
       | S m , x :: l' => aux m l'
       | 0, nil => nil
       | S m, nil => nil
       end) l lsc)
 | and_sc n lsc ee => 
     set_add sname_dec n ((fix aux (l : set sc) : (set sname) :=
       match l with
       | nil => nil
       | p :: tail => set_union sname_dec (conf p) (aux tail)
       end) lsc)
  end.

Fixpoint subconf (s : sc) {struct s} : (set sname) :=
  match s with
 | basic_sc n ee => (n :: nil)
 | or_sc n lsc l ltr ee => 
     (fix aux (num : nat) (ls : list sc) {struct ls} : (set sname) :=
       match num, ls with
       | 0, x :: l' => subconf x
       | S m , x :: l' => aux m l'
       | 0, nil => nil
       | S m, nil => nil
       end) l lsc
 | and_sc n lsc ee => 
     set_add sname_dec n ((fix aux (l : set sc) : (set sname) :=
       match l with
       | nil => nil
       | p :: tail => set_union sname_dec (subconf p) (aux tail)
       end) lsc)
  end.

Fixpoint add_to_states (x : sname) (sst : set (set sname)) : set (set sname) :=
  match sst with
  | nil => nil
  | t :: tail => set_add set_sname_dec (set_add sname_dec x t) (add_to_states x tail)
  end.

Fixpoint product_aux (s : set sname) (ss : set (set sname)): set (set sname) :=
  match ss with
  | nil => nil
  | t :: tail => set_add set_sname_dec (set_union sname_dec s t) (product_aux s tail)
  end.

Fixpoint product (ss1 ss2 : set (set sname)) : set (set sname) :=
  match ss1 with
  | nil => nil
  | t :: tail => set_union set_sname_dec (product_aux t ss2) (product tail ss2)
  end.

(* the set of all potenial configurations of a statechart *)
Fixpoint conf_all (s : sc) {struct s} : set (set sname) :=
  match s with
  | basic_sc n ee => (n :: nil) :: nil
  | or_sc n lsc l ltr ee => 
      set_add set_sname_dec (n :: nil) (add_to_states n ((fix aux (l : list sc) : (set (set sname)) :=
      match l with
      | nil => nil
      | p :: tail => set_union set_sname_dec (conf_all p) (aux tail)
      end) lsc))
  | and_sc n lsc ee =>  
     set_add set_sname_dec (n :: nil) ( add_to_states n ((fix aux (l : set sc) : (set (set sname)) :=
      match l with
      | nil => (nil :: nil)
      | p :: nil => conf_all p
      | a :: b :: tail => product (product (conf_all a) (conf_all b)) (aux tail)
     end) lsc))
end.

(* get enter sequences of action *)
Fixpoint get_enter (s : sc) : seqact :=
  match s with
  | basic_sc n ee => fst ee
  | or_sc n lsc l ltr ee => fst ee
  | and_sc n lsc ee => fst ee
  end.

(* get exit sequences of action *)
Fixpoint get_exit (s : sc) : seqact :=
  match s with
  | basic_sc n ee => snd ee
  | or_sc n lp l ltr ee => snd ee
  | and_sc n lp ee => snd ee
  end.

Fixpoint turn_flat (ltr : list seqact) : list action :=
  match ltr with
  | nil => nil
  | tr :: tail => tr ++ (turn_flat tail)
  end.

(* the bijection for entry *)
Inductive reconstruct_enter : set sc -> list seqact -> Prop :=
  | r1 : forall lsc ltr, 
         (forall s, set_In s lsc -> (exists tr', set_In tr' ltr /\ entry s tr')) ->
         (forall tr', set_In tr' ltr -> (exists s, set_In s lsc /\ entry s tr')) ->
         reconstruct_enter lsc ltr
with entry : sc -> seqact -> Prop :=
  | base_entry : forall n ee, entry (basic_sc n ee) (fst ee)
  | or_entry : forall n lsc l lt ee s tr t, 
               entry (nth l lsc s) tr -> t = (fst ee) ++ tr -> 
               entry (or_sc n lsc l lt ee) t
  | and_entry : forall n lsc ee t lle, reconstruct_enter lsc lle ->
                t = (fst ee) ++ (turn_flat lle) -> entry (and_sc n lsc ee) t.

(* the bijection for exit *)
Inductive reconstruct_exit : set sc -> list seqact -> Prop :=
  | r_exit : forall lsc ltr, 
             (forall s, set_In s lsc -> (exists tr', set_In tr' ltr -> exit s tr')) ->
             (forall tr', set_In tr' ltr -> (exists s, set_In s lsc -> exit s tr')) ->
             reconstruct_exit lsc ltr
with exit : sc -> seqact -> Prop :=
  | base_exit : forall n ee, exit (basic_sc n ee) (snd ee)
  | or_exit : forall n lsc l lt ee s tr t, exit (nth l lsc s) tr -> t = tr ++ (snd ee) -> 
              exit (or_sc n lsc l lt ee) t
  | and_exit : forall n lsc ee t ltr, reconstruct_exit lsc ltr ->
              t = (snd ee) ++ (turn_flat ltr) ->  exit (and_sc n lsc ee) t.


(* substitute sl with sl' in an "or" statechart *)
Fixpoint subst_or (s : sc) (sl : sc) (sl' : sc) {struct s} : sc :=
  match s with 
  | or_sc n lsc l lt ee  => 
     (or_sc n ((fix aux (ls : list sc) : list sc :=
      match ls with
        | nil => nil
        | s :: tail => if (sc_dec s sl) then sl' :: tail else s :: (aux tail)
      end) lsc) l lt ee)
  | _ => s
end.

(* substitute sl with sl' in an "and" statechart *)
Fixpoint subst_and (s : sc) (sl : sc) (sl' : sc) {struct s} : sc :=
  match s with 
  | and_sc n lsc ee => 
     (and_sc n ((fix aux (ls : set sc) : list sc :=
      match ls with
        | nil => nil
        | s :: tail => if (sc_dec s sl) then sl' :: tail else s :: (aux tail)
      end) lsc) ee )
  | _ => s
end.

(* reset to default *)
Fixpoint default (s : sc) : sc :=
  match s with
  | basic_sc n ee => basic_sc n ee
  | or_sc n nil l lt ee => or_sc n nil 0 lt ee
  | or_sc n (t :: stail) l lt ee => or_sc n ((default t) :: stail) 0 lt ee
  | and_sc n lsc ee => 
      and_sc n ((fix aux (l : set sc) : (list sc) :=
      match l with
        | nil => nil
        | p :: tail => (default p) :: aux tail
      end) lsc) ee
  end.

(* use the history type information to determine currently active substates of a state *)
Fixpoint next_stop (h : history) (s : sc) : sc :=
  match s, h with
  | or_sc n lp l lt ee, none => subst_or s (nth 0 lp s) (default (nth 0 lp s))
  | or_sc n lp l lt ee, deep => or_sc n lp l lt ee
  | or_sc n lp l lt ee, shallow => subst_or s (nth l lp s) (default (nth l lp s))
  | _ , _ => s
 end.

(* find position by state name *)
Fixpoint pos (s : sname) (ln : list sname) (n : nat) : option nat :=
  match ln with
  | nil => None 
  | s' :: tail => if sname_dec s s' then Some n else pos s tail (S n)
  end.

(* find position by statechart *)
Fixpoint sc_pos (s : sc) (lp : set sc) (n : nat) : option nat :=
  match lp with 
  | nil => None 
  | s' :: tail => if sc_dec s s' then Some n else sc_pos s tail (S n)
  end.

(* computes the next state after a transition *)
Fixpoint next (h : history) (ssn : set sname) (s : sc) {struct s} : sc :=
  match s with
  | basic_sc n ee => basic_sc n ee
  | or_sc n lsc l lt ee => 
      match (pos n ssn 0) with
      | None => next_stop h s
      | Some j => (or_sc n ((fix aux (ls : list sc) : list sc :=
                     match ls with
                     | nil => nil
                     | s' :: tail => if (sc_dec s' (nth j lsc s')) 
                                     then (next h ssn s') :: tail 
                                     else s' :: (aux tail)
                     end) lsc) j lt ee)
      end                         
  | and_sc n lsc ee => and_sc n ((fix aux (l : set sc){struct l} : (list sc) :=
                        match l with
                        | nil => nil
                        | p :: tail => (next h ssn p) :: aux tail
                        end) lsc) ee
  end.

(* get state name *)
Fixpoint name (s : sc) : sname :=
  match s with 
  | basic_sc n ee => n
  | or_sc n lsc l lt ee => n
  | and_sc n lsc ee => n
  end.

(* priority proposition *)
Inductive priority : event -> sc -> Prop :=
  | p_or : forall l lsc lt n tn i s e g a ee sr td h,
           set_In (tn, l, sr, e, g, a, td, i, h) lt -> 
           (forall st, set_In st sr -> set_In st (conf (nth l lsc s))) -> 
             priority e (or_sc n lsc l lt ee)
  | p_and : forall n lsc e ee, 
            (exists s, set_In s lsc -> priority e s) -> priority e (and_sc n lsc ee).

Inductive subst_and_r : set sc -> sc -> sc -> set sc -> Prop :=
  | r_subst : forall lsc lsc' sj sj' n ee pos, sc_pos sj lsc 0 = Some pos -> 
              (nth pos lsc' (basic_sc n ee)) = sj' ->
              subst_and_r lsc sj sj' lsc'.

(* substitute sc with sc' *)
Fixpoint subst_lsc (lsc : set sc) (s : sc) (s' : sc) {struct lsc} : set sc :=
  match lsc with
  | nil => nil
  | t :: tail => if (sc_dec t s) then s' :: tail else t :: (subst_lsc tail s s')
  end.


(* ==========Operational Semantics==========*)
(* label (event * guard * seqact * bool) *)
Inductive sred (st : state) : sc -> label -> sc -> Prop :=
  | bas : forall e g n ee, beval st g = true ->
          sred st (basic_sc n ee) (e, g, nil, false) (basic_sc n ee) 
  | or1 : forall e g a n lsc l lt i tn s ee en ex tr sr td h s', 
          beval st g = true -> 
          set_In (tn, l, sr, e, g, a, td, i, h) lt ->
          (forall sta, set_In sta sr -> set_In sta (conf (nth l lsc s))) ->
          ~ priority e (nth l lsc s) -> exit (nth l lsc s) ex  -> 
          entry (nth i lsc s) en  -> tr = ex ++ a ++ en ->
          s' = subst_or (or_sc n lsc i lt ee) (nth i lsc s) (next h td (nth i lsc s)) ->
          sred st (or_sc n lsc l lt ee) (e, g, tr, true) s'
  | or2 : forall sl sl' e g l' lsc' lt' n' l lsc n lt tr ee, 
          beval st g = true -> 
          sred st sl (e, g, tr, true) sl' -> nth l lsc sl = sl ->
          nth l' lsc' sl' = sl' -> 
          or_sc n' lsc' l' lt' ee = subst_or (or_sc n lsc l lt ee) sl sl' ->
          sred st (or_sc n lsc l lt ee) (e, g, tr, true) (or_sc n' lsc' l' lt' ee)
  | or3 : forall sl e g n lsc l t ee, beval st g = true -> 
          sred st sl (e, g, nil, false) sl -> 
          sl = nth l lsc sl  -> ~ priority e (or_sc n lsc l t ee) ->
          sred st (or_sc n lsc l t ee) (e, g, nil, false) (or_sc n lsc l t ee) 
  | and : forall e g f lsc n ee  tr' tr lsc', beval st g = true ->   
          reconstruct_action st e lsc tr' lsc' f -> tr = turn_flat tr' ->
          sred st (and_sc n lsc ee) (e, g, tr, f) (and_sc n lsc' ee)  
with
reconstruct_action (st : state): event -> list sc -> list (list string) -> list sc -> bool -> Prop :=
  | r_action_true : 
      forall lsc ltr lsc' e g, 
      (exists sj, exists a, exists sj', set_In sj lsc /\ sred st sj (e, g, a, true) sj') ->
      (forall sj sj', set_In sj lsc -> subst_and_r lsc sj sj' lsc' -> 
        (exists tr', exists f, set_In tr' ltr /\ sred st sj (e, g, tr', f) sj')) ->
      (forall tr' sj', set_In tr' ltr -> 
        (exists sj, exists f, subst_and_r lsc sj sj' lsc' ->  
         set_In sj lsc /\ sred st sj (e, g, tr', f) sj')) -> 
      reconstruct_action st e lsc ltr lsc' true
  | r_action_false:
      forall lsc ltr e g, (forall sj, set_In sj lsc -> sred st sj (e, g, nil, false) sj) ->
        reconstruct_action st e lsc ltr lsc false.

Theorem sred_deterministic: forall st s1 s2 s3 l,  
   sred st s1 l s2 -> sred st s1 l s3 -> s2 = s3.
Proof.
  intros. (*unfinished*)

Admitted.

Inductive sstar (st : state) : sc -> trace -> sc -> trace -> Prop:=
  | sstar_self : forall s t, sstar st s t s t
  | sstar_trans : forall s t s' t' s'' t'' a b e g, sstar st s t s' t' -> 
                  sred st s' (hd e t', g, a, b) s'' -> 
                  t'' = (tl t') ++ a -> sstar st s t s'' t''.

(* all the states are basic states *)
Inductive all_basic : set sc -> Prop :=
  | onesc : forall n ee, all_basic ((basic_sc n ee) :: nil)
  | addsc : forall lsc n ee, all_basic lsc -> all_basic ((basic_sc n ee) :: lsc).

(* add an element to the end of a list of states *)
Fixpoint add_to_list (a : sc) (lsc : list sc) {struct lsc} : list sc :=
  match lsc with
  | nil => a :: nil
  | t :: tail => t :: add_to_list a tail
  end.

(* sublist of string*)
Inductive sub_seqact : list action -> list action -> Prop :=
  | subnil : forall l, sub_seqact nil l
  | subcons1 : forall l1 l2 x, sub_seqact l1 l2 -> sub_seqact l1 (x :: l2)
  | subcons2 : forall l1 l2 x, sub_seqact l1 l2 -> sub_seqact (x :: l1)(x :: l2).

(* get source statename from the transition *)
Definition sou (t : trans) : nat := snd (fst (fst (fst (fst (fst (fst (fst t))))))).

(* get source restriction set from the transition *)
Definition souRes (t : trans) : set sname := snd (fst (fst (fst (fst (fst (fst t)))))).

(* get target sname from the transition*)
Definition tar (t : trans) : nat := snd (fst t).

(* get target restriction set from the transition *)
Definition tarDet (t : trans) : set sname := snd (fst (fst t)).

(* get event from the transition *)
Definition ev (t : trans) : event := snd (fst (fst (fst (fst (fst t))))).

(* get sequence of action from the transition*)
Definition actSeq (t : trans) : seqact := snd (fst (fst (fst t))).

(* get sname name set*)
Fixpoint names (lsc : set sc) : set sname :=
  match lsc with
  | nil => nil
  | a :: tail => 
      match a with
      | basic_sc n ee => set_add sname_dec n (names tail)
      | or_sc n lsc l ltr ee => set_add sname_dec n (names tail)
      | and_sc n ssc ee => set_add sname_dec n (names tail)
      end
  end.

(* get transitions *)
Fixpoint get_trans (s : sc) : set trans :=
  match s with
  | basic_sc n ee => nil
  | or_sc n lsc l lt ee => 
     ((fix aux (l : list sc) : (set trans) :=
      match l with
        | nil => lt
        | p :: tail => set_union trans_dec (get_trans p) (aux tail)
      end) lsc)
  | and_sc n lsc ee => 
     ((fix aux (l : set sc) : (set trans) :=
     match l with
        | nil => nil
        | p :: tail => set_union trans_dec (get_trans p) (aux tail)
     end) lsc)
end.


Inductive wellformed_tran : list sc -> trans -> Prop :=
  | wellformed : forall lsc t a, 
                  set_In (name (nth (sou t) lsc a)) (names lsc) ->
                  set_In (name (nth (tar t) lsc a)) (names lsc) ->
                  ((souRes t = nil) \/
                     set_In (souRes t) (conf_all (nth (sou t) lsc a))) ->
                  ((tarDet t = nil ) \/
                     set_In (tarDet t) (conf_all (nth (tar t) lsc a))) ->
                  wellformed_tran lsc t.

(* one-step refine relation *)
Inductive refineone (st : state) : sc -> sc -> Prop :=
  | and_add1 : forall lsc ee n, all_basic lsc -> refineone st (basic_sc n ee) (and_sc n lsc ee) 
  | and_add2 : forall n lsc ee s', all_basic (s' :: nil) ->
               refineone st (and_sc n lsc ee) (and_sc n (set_add sc_dec s' lsc) ee)
  | and_subst : forall sc sc' n lsc ee, refineone st sc sc' -> 
                refineone st (and_sc n lsc ee) (and_sc n (subst_lsc lsc sc sc') ee)
  | or_add1 : forall n s' ee, all_basic (s' :: nil) -> 
                refineone st (basic_sc n ee) (or_sc n (s' :: nil) 0 nil (nil,nil))
  | or_add2 : forall n lsc l lt ee s', 
              refineone st (or_sc n lsc l lt ee) (or_sc n (add_to_list s' lsc) l lt ee)
  | or_subst : forall n sc sc' lsc l lt ee, refineone st sc sc' -> 
               refineone st (or_sc n lsc l lt ee) (or_sc n (subst_lsc lsc sc sc') l lt ee)
  | trans_add : forall n lsc l lt ee t', wellformed_tran lsc t' ->
                refineone st (or_sc n lsc l lt ee) (or_sc n lsc l (set_add trans_dec t' lt) ee)
  | trans_imp : forall  tn s1 sr e g a td s2 h g' lt n l lsc ee,
                set_In (tn, s1, sr, e, g, a, td, s2, h) lt -> 
                beval st (BImp g' g) = true ->
                refineone st (or_sc n lsc l lt ee)
                (or_sc n lsc l (set_add trans_dec (tn, s1, sr, e, g', a, td, s2, h) 
                (remove trans_dec (tn, s1, sr, e, g, a, td, s2, h) lt)) ee)
  | act_add : forall tn s1 sr e a a' g td s2 h lt ee lsc n l,
              set_In (tn, s1, sr, e, g, a, td, s2, h) lt -> sub_seqact a a' -> 
              refineone st (or_sc n lsc l lt ee) 
              (or_sc n lsc l (set_add trans_dec (tn, s1, sr, e, g, a', td, s2, h) 
                (remove trans_dec (tn, s1, sr, e, g, a, td, s2, h) lt)) ee)
  | en_add1 : forall ee en' n, sub_seqact (fst ee) en' ->
              refineone st (basic_sc n ee) (basic_sc n (en', (snd ee)))
  | en_add2 : forall lsc n l lt ee en', sub_seqact (fst ee) en' ->
              refineone st (or_sc n lsc l lt ee) (or_sc n lsc l lt (en', (snd ee)))
  | en_add3 : forall lsc n ee en', sub_seqact (fst ee) en' ->
              refineone st (and_sc n lsc ee) (and_sc n lsc (en', (snd ee)))
  | ex_add1 : forall ee ex' n, sub_seqact (snd ee) ex' ->
              refineone st (basic_sc n ee) (basic_sc n ((fst ee), ex'))
  | ex_add2 : forall lsc n l lt ee ex', sub_seqact (fst ee) ex' ->
              refineone st (or_sc n lsc l lt ee) (or_sc n lsc l lt ((fst ee), ex'))
  | ex_add3 : forall n lsc ee ex', sub_seqact (fst ee) ex' ->
              refineone st (and_sc n lsc ee) (and_sc n lsc ((fst ee), ex')).

(*unfinished*)
Theorem behavior_pre: forall st e s s' t g a,
 refineone st s t -> sred st s (e, g, a, true) s' -> 
 (exists t', refineone st s' t'  /\ sred st t (e, g, a, true) t').
Proof.
intros st e s s' t g a H0 H1.
induction H0.
(*1*)
inversion H1.
Admitted.



Inductive refine(st : state) : sc -> sc -> Prop :=
  | one : forall sc1 sc2, refineone st sc1 sc2 -> refine st sc1 sc2
  | self : forall sc, refine st sc sc
  | tran : forall sc1 sc0 sc2, refine st sc1 sc0 -> 
             refine st sc0 sc2 -> refine st sc1 sc2.

Require Import Relations.

Theorem refine_refl : forall st : state, reflexive _ (refine st).
Proof.
  intro st. unfold reflexive.
  intro x. apply self.
Qed.

Theorem refine_trans : forall st : state, transitive _ (refine st).
Proof.
  intro st. unfold transitive.
  intros x y z. apply tran.
Qed.



(*=================Examples================*)
(* Example1: conf_all *)
(* n1 is an and-state and has three substates n2 n3 *)
Definition n6 : sc := basic_sc "n6" (nil, nil).
Definition n7 : sc := basic_sc "n7" (nil, nil).
Definition n8 : sc := basic_sc "n8" (nil, nil).
Definition n9 : sc := basic_sc "n9" (nil, nil).
Definition n5 : sc := basic_sc "n5" ("s" :: nil, nil).


Definition tt3: trans := ("t3", 0, nil, "a", BTrue, "b" :: nil, nil, 1, none).
Definition n4 : sc := or_sc "n4" (n8 :: n9 :: nil) 0 (tt3 :: nil) (nil, "d" :: nil).
Definition tt1: trans := ("t1", 0, nil, "a", BTrue, "c" :: nil, nil, 1, none).
Definition tt2: trans := ("t2", 0, nil, "a", BTrue, "d" :: nil, nil, 1, none).
(* interlevel transition *)
Definition tt4: trans := ("t4", 0, ("n4" :: "n9" :: nil), "c", BTrue, "a" :: nil, nil, 1, none).
Definition tt5: trans := ("t5", 1, nil, "d", BTrue, nil, nil, 0, shallow).
Definition tt6: trans := ("t6", 0, nil, "e", BTrue, nil, nil, 1, none).

Definition n3 : sc := or_sc "n3" (n6 :: n7 :: nil) 0 (tt2 :: nil) (nil, nil).
Definition n2 : sc := or_sc "n2" (n4 :: n5 :: nil) 0 (tt1 :: tt4 :: tt5 :: nil) (nil, nil).
Definition n1 : sc := and_sc "n1" (n2 :: n3 :: nil) (nil, nil).

Eval compute in conf n6.
Eval compute in conf n3.
Eval compute in conf n4.

Eval compute in conf_all n8.
Eval compute in conf_all n9.
Eval compute in conf_all n4.
Eval compute in conf_all n2.
Eval compute in conf_all n1.

(* ============================ *)
(* Example2: from the ph.D paper  chapter 4*)


Definition g1 : guard := BTrue.
Definition g2 : guard := BTrue.
Definition g3 : guard := BTrue.
Definition tr1: trans := ("t1", 0, nil, "a", g1, ("m" :: nil), nil, 1, none).
Definition tr2: trans := ("t2", 0, nil, "b", g2, ("n" :: nil), nil, 1, none).
Definition tr3: trans := ("t3", 0, nil, "a", g3, ("l" :: nil), nil, 1, none).
Definition tr4: trans := ("t4", 0, ("n4" :: "n7" :: nil), "c", BTrue, nil, nil, 1, none).
Definition tr5: trans := ("t5", 1, nil, "d", BTrue, ("p" :: nil), nil, 0, shallow).
Definition tr6: trans := ("t6", 0, nil, "e", BTrue, nil, nil, 1, none).
Definition s5 : sc := basic_sc "n5" ("p" :: nil, "q" :: nil).
Definition s6 : sc := basic_sc "n6" (nil, nil).
Definition s7 : sc := basic_sc "n7" (nil, nil).
Definition s8 : sc := basic_sc "n8" (nil, "r" :: nil).
Definition s9 : sc := basic_sc "n9" (nil, nil).
Definition s10 : sc := basic_sc "n10" (nil, "s" :: nil).
Definition s4 : sc := or_sc "n4" (s6 :: s7 :: nil) 0 (tr3 :: nil) (nil, nil).
Definition s3 : sc := or_sc "n3" (s8 :: s9 :: nil) 0 (tr2 :: nil) (nil, nil).
Definition s2 : sc := or_sc "n2" (s4 :: s5 :: nil) 0 (tr1 :: tr4 :: tr5 :: nil) (nil, nil).
Definition s1 : sc := and_sc "n1" (s2 :: s3 :: nil) (nil, nil).
Definition s0 : sc := or_sc "n0" (s1 :: s10 :: nil) 0 (tr6 :: nil) (nil, nil).
Eval compute in conf s0.
Eval compute in subconf s0.
Eval compute in subconf s2.
Eval compute in conf_all s1.
Eval compute in conf_all s6.
Eval compute in conf_all s4.
Eval compute in conf_all s2.
(*================================================*)
(*Example 3: refine*)
Definition s3_0 : sc := basic_sc "n3" (nil,nil).
Definition s1_0 : sc := and_sc "n1" (s2 :: s3_0 :: nil) (nil, nil).
Definition s10_0 : sc := basic_sc "n10" (nil,  nil).
Definition s0_0 : sc := or_sc "n0" (s1_0 :: s10_0 :: nil) 0 (tr6 :: nil) (nil, nil).

Definition s3_1 : sc := or_sc "n3" (s8::nil) 0 nil (nil,nil).
Definition s1_1 : sc := and_sc "n1" (s2 :: s3_1 :: nil) (nil, nil).
Definition s0_1 : sc := or_sc "n0" (s1_1 :: s10_0 :: nil) 0 (tr6 :: nil) (nil, nil).

Definition s3_2 : sc := or_sc "n3" (s8::s9::nil) 0 nil (nil,nil).
Definition s1_2 : sc := and_sc "n1" (s2 :: s3_2 :: nil) (nil, nil).
Definition s0_2 : sc := or_sc "n0" (s1_2 :: s10_0 :: nil) 0 (tr6 :: nil) (nil, nil).

Definition s0_3 : sc := or_sc "n0" (s1 :: s10_0 :: nil) 0 (tr6 :: nil) (nil, nil).


(*step 1*)
Lemma refine_n3_add_n8: forall st, refineone st s3_0 s3_1.
Proof.
intro st.
apply or_add1. apply onesc.
Qed.

Lemma refine_s0_0_to_s0_1: forall st, refine st s0_0 s0_1.
Proof.
intro st.
apply one. unfold s0_0. unfold s0_1.
assert (subst_lsc (s1_0 :: s10_0 :: nil) s1_0 s1_1 = (s1_1 :: s10_0 :: nil) ).
simpl. auto.
rewrite <- H.
apply or_subst. unfold s1_0. unfold s1_1.
assert (subst_lsc (s2 :: s3_0 :: nil) s3_0 s3_1 = (s2 :: s3_1 :: nil)).
simpl. auto.
rewrite <-H0.
apply and_subst. 
apply refine_n3_add_n8.
Qed.

(*step 2*)
Lemma refine_n3_add_n9: forall st, refineone st s3_1 s3_2.
Proof.
intro st.
assert ((s8 :: s9 :: nil)= (add_to_list s9 (s8 :: nil))).
simpl. reflexivity. unfold s3_1. unfold s3_2.
rewrite  H.
apply or_add2.
Qed.

Lemma refine_s0_1_to_s0_2: forall st, refine st s0_1 s0_2.
Proof.
intro st.
apply one. unfold s0_1. unfold s0_2.
assert (subst_lsc (s1_1 :: s10_0 :: nil) s1_1 s1_2 = (s1_2 :: s10_0 :: nil) ).
simpl. auto.
rewrite <- H.
apply or_subst. unfold s1_1. unfold s1_2.
assert (subst_lsc (s2 :: s3_1 :: nil) s3_1 s3_2 = (s2 :: s3_2 :: nil)).
simpl. auto.
rewrite <-H0.
apply and_subst. 
apply refine_n3_add_n9.
Qed.

(*step 3*)
Lemma refine_n3_add_t2: forall st, refineone st s3_2 s3.
Proof.
intro st. unfold s3_2. unfold s3.
assert ((set_add trans_dec tr2 nil) = tr2 :: nil).
simpl. reflexivity.
rewrite <- H.
apply trans_add.
apply wellformed with (lsc:= (s8 :: s9 :: nil))(t:=tr2)(a:=basic_sc "none" (nil,nil)).
simpl.
right. left. auto.
simpl. left. auto.
left. auto. left. auto.
Qed.


Lemma refine_s0_2_to_s0_3: forall st, refine st s0_2 s0_3.
Proof.
intro st.
apply one. unfold s0_2. unfold s0_3.
assert (subst_lsc (s1_2 :: s10_0 :: nil) s1_2 s1 = (s1 :: s10_0 :: nil) ).
simpl. auto.
rewrite <- H.
apply or_subst. unfold s1_2. unfold s1.
assert (subst_lsc (s2 :: s3_2 :: nil) s3_2 s3 = (s2 :: s3 :: nil)).
simpl. auto.
rewrite <-H0.
apply and_subst. 
apply refine_n3_add_t2.
Qed.

(*step 4*)
Lemma refine_n10_add_exit: forall st, refineone st s10_0 s10.
Proof.
intro st.
unfold s10_0. unfold s10.
apply ex_add1.
simpl. apply subnil.
Qed.

Lemma refine_s0_3_to_s0: forall st, refine st s0_3 s0.
Proof.
intro st.
apply one. unfold s0_3. unfold s0.
assert (subst_lsc (s1 :: s10_0 :: nil) s10_0 s10 = (s1 :: s10 :: nil) ).
simpl. auto.
rewrite <- H.
apply or_subst. 
apply refine_n10_add_exit.
Qed.

(*all steps*)
Lemma refine_s0_0_to_s0: forall st, refine st s0_0 s0.
Proof.
intro st.
apply tran with (sc0:=s0_1).
apply refine_s0_0_to_s0_1.
apply tran with (sc0:=s0_2).
apply refine_s0_1_to_s0_2.
apply tran with (sc0:=s0_3).
apply refine_s0_2_to_s0_3.
apply  refine_s0_3_to_s0.
Qed.


(*
Definition s0' : sc := or_sc "n0" (s1 :: s10 :: nil) 1 (tr6 :: nil) (nil, nil).

Theorem conf_preserve: forall st s1 s2 n, refineone st s1 s2 -> 
 (set_In n (conf s1) -> set_In n (conf s2)).

Example tranexmp : forall st, sstar st s0 ("a"::"c"::"b"::"d"::"e"::nil) s0' nil.


Example t1false: ~ sred s0 s0''.
*)

(* Example3: reconstruct_enter 
Definition s2 : sc := basic_sc "s2" ("in2" :: nil, nil).
Definition s3 : sc := basic_sc "s3" ("in3" :: nil, nil).
Definition s4 : sc := basic_sc "s4" ("in4" :: nil, nil).
Definition s5 : sc := basic_sc "s5" ("in5" :: nil, nil).
Definition s6 : sc := and_sc "s6" (s3 :: s4 :: nil) (nil, nil).
Definition t : trans := ("t", 0, nil, "eid", BTrue, nil, nil, 1, none).
Definition s1 : sc := or_sc "s1" (s2 :: s6 :: nil) 1 (t :: nil) ("in1" :: nil, nil).
Definition s7 : sc := and_sc "s7" (s1 :: s5 :: nil) (nil, nil).

Example enterExamp: 
  reconstruct_enter (s1 :: s5 :: nil)
    (("in1" :: "in3" :: "in4" :: nil) :: ("in1" :: "in4" :: "in3" :: nil) :: ("in5" :: nil) :: nil).
Proof.
apply r1. 
(*1*)
intros. destruct H.
exists ("in1" :: "in3" :: "in4" :: nil).
simpl. split. auto. subst.
apply or_entry with (s := s2)(tr := "in3" :: "in4" :: nil).
simpl. apply and_entry with (lle := ("in3" :: nil) :: ("in4" :: nil) :: nil).
apply r1. intros. destruct H;subst. exists ("in3" :: nil). split;simpl;auto. apply base_entry.
destruct H;subst.  exists ("in4" :: nil). split;simpl;auto. apply base_entry. inversion H.
intros. destruct H; subst. exists s3. split; simpl; auto. apply base_entry. destruct H.
subst. exists s4. split;simpl;auto.  apply base_entry. inversion H.
simpl. auto. simpl. auto. 
destruct H; subst. exists ("in5" :: nil). simpl;auto. split. right; right; left. 
auto. apply base_entry. inversion H.
(*2*)
intros. destruct H; subst. exists s1. split. simpl;auto. 
apply or_entry with (s := s2)(tr := "in3" :: "in4" :: nil).
simpl. apply and_entry with (lle := ("in3" :: nil) :: ("in4" :: nil) :: nil).
apply r1. intros. destruct H;subst. exists ("in3" :: nil). split;simpl;auto. apply base_entry.
destruct H;subst.  exists ("in4" :: nil). split;simpl;auto. apply base_entry. inversion H.
intros. destruct H; subst. exists s3. split; simpl; auto. apply base_entry. destruct H.
subst. exists s4. split;simpl;auto.  apply base_entry. inversion H.
simpl. auto. simpl. auto. 
destruct H;subst. exists s1. simpl;auto. split. left;auto.
apply or_entry with (s := s2)(tr := "in4" :: "in3" :: nil).
simpl. apply and_entry with (lle := ("in4" :: nil) :: ("in3" :: nil) :: nil).
apply r1. intros. destruct H;subst. exists ("in3" :: nil). split;simpl;auto. apply base_entry.
destruct H;subst.  exists ("in4" :: nil). split;simpl;auto. apply base_entry. inversion H.
intros. destruct H; subst. exists s4; split; simpl; auto. apply base_entry.
destruct H;subst. exists s3; split; simpl; auto. apply base_entry. inversion H.
simpl. auto. simpl. auto.
destruct H;subst. exists s5; split; simpl; auto. apply base_entry. inversion H.
Qed.
*)
Definition SALwait : sc := basic_sc "Lwait" (nil, nil).
Definition SALwrite : sc := basic_sc "Lwrite" (nil, nil).
Definition SASid : sc := basic_sc "Sid" (nil, nil).
Definition SASpwd : sc := basic_sc "Spwd" (nil, nil).
Definition SAScmd : sc := basic_sc "Scmd" ("encmd" :: nil, nil).

Definition t1: trans :=("t1", 0, nil, "eid", BTrue, nil, nil, 1, none).
Definition t2: trans :=("t2", 1, nil, "ecmd", BTrue, nil, nil, 0, shallow).
Definition t3: trans :=("t3", 0, nil, "eid", BTrue, "eerror" :: nil, nil, 1, none).
(* interlevel transition *)
(*Definition t4: trans :=("t4", 0, ("Spwd"::nil), "epwd", BTrue, "eloginsucc" :: nil, nil, 1, none).*)
Definition t4: trans :=("t4", 0, ("Sident" :: "Spwd"::nil), "epwd", BTrue, "eloginsucc" :: nil, nil, 1, none).
Definition t5: trans :=("t5", 0, nil, "eid", BTrue, nil, nil, 1, none).

Definition SASident : sc := or_sc "Sident" (SASid :: SASpwd :: nil) 0 (t1 :: nil) (nil, "exlogin" :: nil).
Definition SASLog : sc := or_sc "SLog" (SALwait :: SALwrite :: nil) 0 (t5 :: nil) (nil, nil).
Definition SASexecute : sc := or_sc "Sexecute" (SASident :: SAScmd :: nil) 0 (t2 :: t3 :: t4 :: nil) (nil, nil).
Definition SASserver : sc := and_sc "Sserver" (SASexecute :: SASLog :: nil) (nil, nil).

Definition SASident1 : sc := or_sc "Sident" (SASid :: SASpwd :: nil) 1 (t1 :: nil) (nil, "exlogin" :: nil).
Definition SASexecute1 : sc := or_sc "Sexecute" (SASident1 :: SAScmd :: nil) 0 (t2 :: t3 :: t4 :: nil) (nil, nil).
Definition SASLog1 : sc := or_sc "SLog" (SALwait :: SALwrite :: nil) 1 (t5 :: nil) (nil, nil).
Definition SASserver1 : sc := and_sc "Sserver" (SASexecute1 :: SASLog1 :: nil) (nil, nil).
Definition SASexecute2 : sc := or_sc "Sexecute" (SASident1 :: SAScmd :: nil) 1 (t2 :: t3 :: t4 :: nil) (nil, nil).
Definition SASserver2 : sc := and_sc "Sserver" (SASexecute2 :: SASLog1 :: nil) (nil, nil).

Definition t6: trans := ("t6", 1, nil, "ecmd", BTrue, nil, nil, 0, none).
Definition SALwrite' : sc := basic_sc "Lwrite'" (nil,nil).
Definition t5': trans :=("t5", 0, nil, "eid", BTrue, nil, nil, 1, none).
Definition SASLog' : sc := or_sc "SLog" (SALwait :: SALwrite' :: nil) 0 (t5' :: t6 :: nil) (nil, nil).
Definition SASserver' : sc := and_sc "Sserver" (SASexecute :: SASLog' :: nil) (nil, nil).

Example examp : forall st, sstar st SASserver ("eid"::"epwd"::"ecmd"::nil) SASserver1 nil.
Proof.
 intro st.
 apply sstar_trans with (s':= SASserver1)(t' := "encmd" :: nil)(e := "encmd")
                        (a := nil)(b := false)(g := BTrue).
 apply sstar_trans with (s':= SASserver1)(t' := "eloginsucc" :: "encmd" :: nil)
                        (e := "eloginsucc")(a := nil)(b := false)(g := BTrue).
 apply sstar_trans with (s':= SASserver1)(t' := "exlogin" :: "eloginsucc" :: "encmd" :: nil)
                        (e := "exlogin")(a := nil)(b := false)(g := BTrue).
 apply sstar_trans with (s':= SASserver2) (t' := "ecmd" :: "exlogin" :: "eloginsucc" :: "encmd" :: nil)
                        (e := "ecmd")(a := nil)(b := true)(g := BTrue).
 apply sstar_trans with (s':= SASserver1) (t' := "epwd" :: "ecmd" :: nil)(e := "epwd")
                        (a := "exlogin" :: "eloginsucc" :: "encmd" :: nil)(b := true)(g := BTrue).
 apply sstar_trans with (s':= SASserver) (t' := "eid" :: "epwd" :: "ecmd" :: nil)
                        (e := "eid")(a := nil)(b := true)(g := BTrue).
 apply sstar_self.

(*Sserver -> Sserver1 /eid*)
 apply and with (tr' := nil :: nil). auto.
 apply r_action_true with (g := BTrue).
     (*true flag*)
    exists SASexecute. exists nil. exists SASexecute1. 
    split; simpl; auto.
     (* sred SASexecute ("eid", nil, true) SASexecute1 *)
     apply or2 with (sl := SASident)(sl' := SASident1). auto.
     apply or1 with (a := nil)(i := 1)(tn := "t1")(s := SASident)(en := nil)
                    (ex := nil)(sr := nil)(td := nil)(h := none). 
     auto. simpl. auto.
     intros sta H. inversion H.
     intuition. inversion H.
     constructor. constructor.
     simpl; auto.
     simpl; auto.
     simpl; auto.
     simpl; auto.
     simpl; auto.
    (*->*)
      intros sj sj' HsetIn Hsubst.
      inversion HsetIn; clear HsetIn; subst.
        (*SASexecute*)
        inversion Hsubst; clear Hsubst; subst.
        inversion H; clear H; subst.
        exists nil. exists true. 
        split; simpl; auto.
          (* sred SASexecute ("eid", nil, true) SASexecute1 *)
          apply or2 with (sl := SASident)(sl' := SASident1). auto.
          apply or1 with (a := nil)(i := 1)(tn := "t1")(s := SASident)
                (en := nil)(ex := nil)(sr := nil)(td := nil)(h := none)(g := BTrue).
          simpl. auto. simpl. auto.
          intros sta H. inversion H.
          intuition. inversion H.
          constructor. constructor.
          simpl; auto.
          simpl; auto.
          simpl; auto.
          simpl; auto.
          simpl; auto.
       (*SASLog*)
       inversion Hsubst. clear Hsubst. subst. destruct H. subst.
       inversion H0; clear H0; subst.
       exists nil. exists true. 
       split; simpl; auto.
          (* sred SASLog ("eid", nil, false) SASLog1*)
          apply or1 with (a := nil)(i := 1)(tn := "t5")(s := SASident)
                         (en := nil)(ex := nil)(sr := nil)(td := nil)(h := none).
          auto. simpl. auto.
          intros sta H. inversion H.
          intuition. inversion H.
          constructor. constructor.
          simpl; auto.
          simpl; auto.
       (*False*)
       inversion H.
     (*<-*)
     intros tr' sj' HsetIn.
     inversion HsetIn; clear HsetIn; subst.
       (*nil*)
        exists SAScmd.  exists true. 
        split; inversion H; clear H; subst; inversion H0.
       (*False*)
        inversion H.
  simpl. auto.
  (*--*)
  simpl; auto.

(*Sserver1 -> Sserver2 /epwd*)
 apply and with (tr' := ("exlogin" :: "eloginsucc" :: "encmd" :: nil) :: nil :: nil). auto.
(* AND *)
    apply r_action_true with (g := BTrue).
     (*true flag*)
    exists SASexecute1. exists ("exlogin" :: "eloginsucc" :: "encmd" :: nil). exists SASexecute2. 
    split; simpl; auto.
     (* sred SASexecute1 ("epwd", "eloginsucc" :: nil, true) SASexecute2 *)
     apply or1 with (a := "eloginsucc" :: nil)(i := 1)(tn := "t4")(s := SASident)
                    (en := "encmd" :: nil)(ex := "exlogin" :: nil)(sr :="Sident" :: "Spwd" :: nil)
                    (td := nil)(h := none).
     simpl. auto. simpl. right.  right. left. auto.
     intros sta H. inversion H; clear H; subst. simpl; auto. 
     inversion H0. simpl. left. auto. inversion H.
     (*~p*)
     intuition. inversion H; clear H; subst. destruct H3; inversion H.
     (*exit action*)
     apply or_exit with (s := SAScmd)(tr := nil). constructor. simpl; auto.
     (*entry action*) 
     constructor. simpl; auto.
     simpl; auto.
    (*->*)
      intros sj sj' HsetIn Hsubst.
      inversion HsetIn; clear HsetIn; subst.
        (*SASexecute1*)
        inversion Hsubst; clear Hsubst; subst.
        inversion H; clear H; subst.
        exists ("exlogin" :: "eloginsucc" :: "encmd" :: nil). exists true. 
        split; simpl; auto.
           (* sred SASexecute1 ("epwd", "eloginsucc" :: nil, true) SASexecute2 *)
           apply or1 with (a := "eloginsucc" :: nil)(i := 1)(tn := "t4")(s := SASident)
                          (en := "encmd" :: nil)(ex := "exlogin" :: nil)(sr := "Sident" :: "Spwd" :: nil)
                          (td := nil)(h := none).
           simpl. auto. simpl. right. right. left. auto. 
           intros sta H. inversion H; clear H; subst. simpl; auto. simpl. inversion H0.
           left. auto. inversion H.
           (*~p*)
           intuition. inversion H; clear H; subst. destruct H3; inversion H.
           (*exit action*)
           apply or_exit with (s := SAScmd)(tr := nil). constructor. simpl; auto.
           (*entry action*) 
           constructor. simpl; auto.
           simpl; auto.
       (*SASLog1*)
       inversion Hsubst; clear Hsubst; subst. destruct H. subst.
       inversion H0; clear H0; subst.
       exists nil. exists false. 
       split; simpl; auto.
         apply or3 with (sl := SALwrite). auto.
         apply bas. auto.
         simpl; auto.
         (*~p*)
         intuition. inversion H; clear H; subst.
         destruct H3. inversion H.
         inversion H.
       (*False*)
       inversion H.
     (*<-*)
     intros tr' sj' HsetIn.
     inversion HsetIn; clear HsetIn; subst.
       (*"exlogin" :: "eloginsucc" :: "encmd" :: nil*)
        exists SASexecute1. exists true.
        split; simpl; auto. 
        inversion H; clear H; subst.
        inversion H0; clear H0; subst.
          (* sred SASexecute1 ("epwd", "exlogin" :: "eloginsucc" :: "encmd" :: nil, true) SASexecute2 *)
           apply or1 with (a := "eloginsucc" :: nil)(i := 1)(tn := "t4")(s := SASident)
                          (en := "encmd" :: nil)(ex := "exlogin" :: nil)(sr := "Sident" :: "Spwd" :: nil)
                          (td := nil)(h := none).
           simpl. auto. simpl. right. right. left. auto.
           intros sta H. inversion H; clear H; subst. simpl; auto. inversion H0.
           simpl. left. auto. inversion H.
           (*~p*)
           intuition. inversion H; clear H; subst. destruct H3; inversion H.
           (*exit action*)
           apply or_exit with (s := SAScmd)(tr := nil). constructor. simpl; auto.
           (*entry action*) 
           constructor. simpl; auto.
           simpl; auto.
       (*nil*)
        destruct H; subst.
        exists SASLog.  exists false. 
        split; inversion H; clear H; subst; inversion H0.
       (*False*)
        inversion H.
 simpl; auto.
(*--*)
 simpl; auto.      

(*Sserver2 -> Sserver1 /ecmd*)
 apply and with (tr' := nil :: nil). auto.
  (* AND *)
    apply r_action_true with (g := BTrue).
     (*true flag*)
    exists SASexecute2. exists nil. exists SASexecute1. 
    split; simpl; auto.
     (* sred SASexecute2 ("ecmd", nil, true) SASexecute1 *)
     apply or1 with (a := nil)(i := 0)(tn := "t2")(s := SASident)(en := nil)
                    (ex := nil)(sr := nil)(td := nil)(h := shallow).
     auto. simpl. auto.
     intros sta H. inversion H.
     intuition. inversion H.
     constructor. simpl. apply or_entry with (s := SASident1)(tr := nil). constructor.
     simpl; auto.
     simpl; auto.
     simpl; auto.
    (*->*)
      intros sj sj' HsetIn Hsubst.
      inversion HsetIn; clear HsetIn; subst.
        (*SASexecute2*)
        inversion Hsubst; clear Hsubst; subst.
        inversion H; clear H; subst.
        exists nil. exists true. 
        split; simpl; auto.
          (* sred SASexecute2 ("ecmd", nil, true) SASexecute1 *)
          apply or1 with (a := nil)(i := 0)(tn := "t2")(s := SASident)(en := nil)
                         (ex := nil)(sr := nil)(td := nil)(h := shallow).
          auto. simpl. auto.
          intros sta H. inversion H.
          intuition. inversion H.
          constructor. simpl. apply or_entry with (s := SASident1)(tr := nil). constructor.
          simpl; auto.
          simpl; auto.
          simpl; auto.
       (*SASLog1*)
       inversion Hsubst; clear Hsubst; subst. destruct H. subst.
       inversion H0; clear H0; subst.
       exists nil. exists false. 
       split; simpl; auto.
         apply or3 with (sl := SALwrite). auto.
         apply bas. auto.
         simpl; auto.
         (*~p*)
         intuition. inversion H; clear H; subst.
         destruct H3. inversion H.
         inversion H.
       (*False*)
       inversion H.
     (*<-*)
     intros tr' sj' HsetIn.
     inversion HsetIn; clear HsetIn; subst.
       (*nil*)
        exists SAScmd.  exists true. 
        split; inversion H; clear H; subst; inversion H0.
       (*False*)
        inversion H.
  (*--*)
  simpl. auto.
(**)
  simpl. auto.
(*Sserver1 /exlogin*)
apply and with (tr' := nil :: nil). auto.
  apply r_action_false with (g := BTrue).
  intros sj HsetIn.
  inversion HsetIn; clear HsetIn; subst.
  (*Sexecute1*)
  apply or3 with (sl := SASident1). auto.
  apply or3 with (sl := SASpwd). auto.
  apply bas. auto.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3; inversion H.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3. inversion H.
  destruct H. inversion H. destruct H; inversion H.
  destruct H. subst.
 (*SASLog1*)
  apply or3 with (sl := SALwrite). auto.
  apply bas. auto.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3; inversion H.
  inversion H.
  simpl; auto.
  simpl; auto.

(*Sserver1 /eloginsucc*)
apply and with (tr' := nil :: nil). auto.
  apply r_action_false with (g := BTrue).
  intros sj HsetIn.
  inversion HsetIn; clear HsetIn; subst.
  (*Sexecute1*)
  apply or3 with (sl := SASident1). auto.
  apply or3 with (sl := SASpwd). auto.
  apply bas. auto.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3; inversion H.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3. inversion H.
  destruct H. inversion H. destruct H; inversion H.
  destruct H. subst.
 (*SASLog1*)
  apply or3 with (sl := SALwrite).  auto.
  apply bas. auto.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3; inversion H.
  inversion H.
  simpl; auto.
  simpl; auto.

(*Sserver1 /encmd*)
apply and with (tr' := nil :: nil). auto.
  apply r_action_false with (g := BTrue).
  intros sj HsetIn.
  inversion HsetIn; clear HsetIn; subst.
  (*Sexecute1*)
  apply or3 with (sl := SASident1). auto.
  apply or3 with (sl := SASpwd). auto.
  apply bas. auto.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3; inversion H.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3. inversion H.
  destruct H. inversion H. destruct H; inversion H.
  destruct H. subst.
 (*SASLog1*)
  apply or3 with (sl := SALwrite). auto.
  apply bas. auto.
  simpl; auto.
  intuition. inversion H; clear H; subst. destruct H3; inversion H.
  inversion H.
  simpl; auto.
  simpl; auto.
Qed.


