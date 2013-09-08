(*
   Quark is Copyright (C) 2012-2015, Quark Team.

   You can redistribute and modify it under the terms of the GNU GPL,
   version 2 or later, but it is made available WITHOUT ANY WARRANTY.

   For more information about Quark, see our web site at:
   http://goto.ucsd.edu/quark/
*)


Require Import Ynot.

Require Import Basis.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import RSep.
Require Import NArith.
Require Import Arith.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Fixpoint length_in_size_helper (l : list ascii) (res:positive) := 
  match l with 
  | nil => res
  | a :: ls => (length_in_size_helper ls (Psucc res))
  end.

Fixpoint length_in_size (l : list ascii) := 
  length_in_size_helper l 1%positive.

Lemma psucc_ge:
  forall p, (Psucc p >= p)%positive.
Proof.
  intros p.
  unfold Pge.
  rewrite ZC2; [discriminate | apply Pcompare_p_Sp].
Qed.

Lemma not_lt:
  forall a, a <> Lt <-> a = Gt \/ a = Eq.
Proof.
  unfold iff; split.
  intros a_not_Lt.
  destruct a. 
  right; auto. destruct a_not_Lt; auto.
  left; auto.

  intros a_Gt.
  destruct a_Gt; rewrite H; discriminate.
Qed.  

Lemma pos_ge_trans:
  forall p0 p1 p2, (p0 >= p1)%positive -> (p1 >= p2)%positive -> (p0 >= p2)%positive.
Proof.
  intros p0 p1 p2 H H0.

  unfold Pge in H,H0. unfold Pge.
  rewrite not_lt in H,H0. rewrite not_lt.
  destruct H. destruct H0.

  left; apply ZC2; eapply Plt_trans;
  unfold Plt; apply ZC1; eauto.

  left; apply Pcompare_Eq_eq in H0.
  rewrite<- H0. auto.

  destruct H0.
  left; apply Pcompare_Eq_eq in H.
  rewrite H. auto.

  right; apply Pcompare_Eq_eq in H.  
  rewrite H. auto.
Qed. 

Lemma lsi :
  forall l0 p0, ((length_in_size_helper l0 p0) >= p0)%positive.
Proof.
  induction l0.

  intros. simpl. 
  unfold Pge.
  rewrite Pcompare_refl.
  discriminate.

  intros.
  simpl.

  destruct l0.
  simpl. apply psucc_ge.

  simpl in IHl0.
  simpl.

  assert (length_in_size_helper l0 (Psucc (Psucc p0)) >= (Psucc p0))%positive.
  apply IHl0.
  assert ((Psucc p0) >= p0)%positive.
  apply psucc_ge.
  
  eapply pos_ge_trans.
  eauto. eauto.
Qed.

Definition size (s:positive ) := (1 + s)%positive.

Lemma psucc_plus_1 :
  forall a, Psucc a = (a + 1)%positive.
Proof.
  induction a; simpl; auto.
Qed.

Ltac inv H := inversion H; subst; clear H.

(* core structures and traces *)
Axiom file_desc : Set.
Axiom ichan     : Set.
Axiom ochan     : Set.

Variable stdin  : file_desc.
Variable stdout : file_desc.

(*
   the checking function called before a socket is created.

   arg0 : the host destination of THE SOCKET
   arg1 : the tab's domain

   returns true only if 

   the tab is allowed to create a socket to the host.
*)
Parameter is_safe_sock_dest_on : list ascii -> list ascii -> bool.


(* converts a file descriptor into an ascii representation. it returns an ascii list of length 4 *)
Parameter tab_id_to_la :  ichan -> list ascii.

(* Converts the file descriptor's ascii representation to the real fd representaion   the first 4 elements of the ascii list are converted. *)
Parameter get_tab_id : list ascii -> ichan.

(* extract the domain attr from the cookie and returns the domain's top domain.*)
Parameter get_topdomain_cookie : list ascii -> list ascii.

(* from a domain expression ...*.c.b.a  returns b.a (if it's just a, returns a *)
Parameter get_topdomain_tab : list ascii -> list ascii.

Fixpoint get_cookie_content_helper (la:list ascii) (cnt:nat) : list ascii :=
if beq_nat cnt 4 then la
else
  match la with
    | a :: la' => get_cookie_content_helper la' (S cnt)
    | nil => nil
  end.

(* cut the first 4 elements from the list and returns the rest part of the string *)
Definition get_cookie_content (la:list ascii) : list ascii :=
  get_cookie_content_helper la 0%nat.
Opaque get_cookie_content.

Axiom iceq:
  forall (ic1 ic2: ichan), {ic1 = ic2} + {ic1 <> ic2}.

Axiom file_desc_eq:
  forall (f1 f2: file_desc), {f1 = f2} + {f1 <> f2}.

Axiom oceq:
  forall (oc1 oc2: ochan), {oc1 = oc2} + {oc1 <> oc2}.

(* tabs *)

Definition tab := (prod (prod (prod (prod ichan ochan) (list ascii)) (list ascii)) (option ichan)).

(* kernel reads to recv from tab *)
Definition t2k (t: tab) : ichan :=
  fst (fst (fst (fst t))).

(*  tab_ichan t. *)

(* kernel writes to send to tab *)
Definition k2t (t: tab) : ochan :=
  snd (fst (fst (fst t))).

(* returns tab's init url *)
Definition tab_init_url (t: tab) : list ascii :=
  snd (fst (fst t)).

(* returns tab's origin *)
Definition tab_origin_url (t: tab) : list ascii :=
  snd (fst t).

Definition create_tab (ic:ichan) (oc:ochan) (initurl:list ascii) (torigin:list ascii) (parent:option ichan): tab :=
  (pair (pair (pair (pair ic oc) (initurl)) torigin) (parent)).

(* cookie process *)
Definition cproc := (prod (prod ichan ochan) (list ascii)).

(* kernel reads to recv from a cproc *)
Definition c2k (c: cproc) : ichan :=
  fst (fst c).

(* kernel writes to send to cproc *)
Definition k2c (c: cproc) : ochan :=
  snd (fst c).

(* returns tab's init url *)
Definition cproc_domain (c: cproc) : list ascii :=
  snd c.

Definition create_cproc (ic:ichan) (oc:ochan)  (origin:list ascii): cproc :=
  (pair (pair ic oc) (origin)).

Inductive Action : Set :=
  | MousePos : list ascii -> Action
  | ReadN : ichan -> positive -> list ascii -> Action
  | ReadFile : file_desc -> ascii -> Action
  | WriteStrFile : file_desc -> list ascii -> Action
  | WriteN : ochan -> positive -> list ascii -> Action
  | MkTab : tab -> Action
  | MkCProc : cproc -> Action
  | Endorse : bool -> Action
  | KillTab : tab -> Action
  | SendSocket : tab -> list ascii -> list ascii -> Action
  | Wget  : list ascii -> list ascii -> Action.

Definition laeq (l1 l2 : list ascii) :=
  list_eq_dec ascii_dec l1 l2.

Check laeq.
Definition positive_eq_dec : forall x y:positive, {x=y}+{x<>y}.
Proof.
  decide equality.
Qed.

Definition tabeq:
  forall (t1 t2: tab), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
  decide equality.
  apply iceq.
  repeat decide equality.
  apply oceq.
  apply iceq.
Qed.

Definition cproceq:
  forall (t1 t2: cproc), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
  decide equality.
  repeat decide equality.
  decide equality.
  repeat decide equality.
  apply oceq.
  apply iceq.
Qed.

Definition Trace : Set :=
  list Action.

Definition coqtab (initurl: list ascii) (rv: ichan * ochan * list ascii) (ptab: option tab) : tab :=
  let i := (fst (fst rv)) in
  let o := (snd (fst rv)) in
  let url := (snd rv) in
    create_tab i o initurl url 
      (
        match ptab with
          | Some pt => Some (t2k pt)
          | None => None
       end
      ).


Definition coqcproc (origin: list ascii) (rv: ichan * ochan) : cproc :=
  let i := (fst rv) in
  let o := (snd rv) in
    create_cproc i o origin.

Axiom gout    : ochan.
Axiom ihandle : ichan -> hprop.
Axiom ohandle : ochan -> hprop.
Axiom traced  : Trace -> hprop.
Axiom fhandle : file_desc -> hprop.


Definition thandle (t: tab) : hprop :=
  ihandle (t2k t) * ohandle (k2t t).

Definition chandle (c: cproc) : hprop :=
  ihandle (c2k c) * ohandle (k2c c).

(* actions *)
Axiom readn:
  forall (f: ichan) (s: positive) (tr: [Trace]),
  STsep (tr ~~ traced tr * ihandle f)
        (fun la => tr ~~ traced (ReadN f s la :: tr) * [ length_in_size la  = s] * ihandle f).

Axiom readfile:
  forall (f: file_desc) (tr: [Trace]),
  STsep (tr ~~ traced tr * fhandle f)
        (fun c:ascii => tr ~~ traced (ReadFile f c :: tr) * fhandle f).

Axiom writestrfile:
  forall (f: file_desc) (str: list ascii) (tr: [Trace]),
  STsep (tr ~~ traced tr * fhandle f)
        (fun _:unit => tr ~~ traced (WriteStrFile f str :: tr) * fhandle f).

Axiom mousepos: forall (tr: [Trace]), STsep (tr ~~ traced tr) (fun
  posstr => tr ~~ traced ((MousePos posstr) :: tr)).

Axiom writen:
  forall (f: ochan) (p: positive ) (s: list ascii) (tr: [Trace]),
  STsep (tr ~~ traced tr * ohandle f)
        (fun _:unit => tr ~~ traced (WriteN f p s :: tr) * ohandle f).

Axiom mktab:
  forall (url:list ascii) (avoid: list ichan) (oavoid: list ochan) (ptab: option tab) (tr: [Trace]),
  STsep (tr ~~ traced tr)
        (fun (rv: ichan * ochan * list ascii) =>
          let t := (coqtab url rv ptab) in 
          tr ~~ traced (MkTab t :: tr) * ihandle (t2k t) * ohandle (k2t t) * [~ In (t2k t) avoid]  * [~ In (k2t t) oavoid]).

Axiom mkcproc:
  forall (domain:list ascii) (avoid: list ichan) (oavoid: list ochan) (tr: [Trace]),
  STsep (tr ~~ traced tr)
        (fun (rv: ichan * ochan) =>
          let c := (coqcproc domain rv) in 
          tr ~~ traced (MkCProc c :: tr) * ihandle (c2k c) * ohandle (k2c c) * [~ In (c2k c) avoid] *  [~ In (k2c c) oavoid]).

Axiom killtab:
  forall (t: tab) (tr: [Trace]),
  STsep (tr ~~ traced tr)
        (fun _:unit => tr ~~ traced (KillTab t:: tr)).

(* later, desc should be disappered because a tab can connect only to it's origin *)
Axiom sendsocket:
  forall (t: tab) (host:list ascii) (sock_desc : list ascii) (tr: [Trace]),
  STsep (tr ~~ traced tr * thandle t)
        (fun _:unit => tr ~~ traced (SendSocket t host sock_desc :: tr) * thandle t).

Axiom wget:
  forall (url: list ascii) (tr: [Trace]),
  STsep (tr ~~ traced tr)
        (fun (html: list ascii) =>
          tr ~~ traced (Wget url html :: tr)).

Axiom endorse:
  forall (tr: [Trace]),
  STsep (tr ~~ traced tr)
        (fun (dec: bool) =>
          tr ~~ traced (Endorse dec :: tr)).

Axiom select:
  forall (stdin: file_desc) (ics: list ichan) (tr: [Trace]),
  STsep (tr ~~ traced tr)
        (fun ready:(option file_desc*(list ichan)) =>
          tr ~~ traced tr * [fst ready = (Some stdin) \/ snd ready <> nil] * 
          [forall ic, In ic (snd ready) -> In ic ics]).

(* aux defns *)

Definition WroteStr (f: ochan) (s: list ascii) : Action :=
  WriteN f (length_in_size s) s.


Lemma iceq_true:
  forall T (A B: T) f,
  (if iceq f f then A else B) = A.
Proof.
  intros. case (iceq f f); intros.
  auto. destruct n; auto.
Qed.

Lemma iceq_false:
  forall T (A B: T) f1 f2,
  f1 <> f2 ->
  (if iceq f1 f2 then A else B) = B.
Proof.
  intros. case (iceq f1 f2); intros.
  subst. destruct H; auto. auto.
Qed.


Lemma file_desc_eq_true:
  forall T (A B: T) f,
  (if file_desc_eq f f then A else B) = A.
Proof.
  intros.
  destruct (file_desc_eq f f); auto.
  destruct n; auto.
Qed.


Lemma file_desc_eq_false:
  forall T (A B: T) f1 f2,
  f1 <> f2 ->
  (if file_desc_eq f1 f2 then A else B) = B.
Proof.
  intros.
  destruct (file_desc_eq f1 f2); intros.
  subst. destruct H; auto. auto.
Qed.


Lemma oceq_true:
  forall T (A B: T) f,
  (if oceq f f then A else B) = A.
Proof.
  intros. case (oceq f f); intros.
  auto. destruct n; auto.
Qed.

Lemma oceq_false:
  forall T (A B: T) f1 f2,
  f1 <> f2 ->
  (if oceq  f1 f2 then A else B) = B.
Proof.
  intros. case (oceq f1 f2); intros.
  subst. destruct H; auto. auto.
Qed.

Lemma ascii_dec_true:
  forall T (A B: T) c,
  (if ascii_dec c c then A else B) = A.
Proof.
  intros. case (ascii_dec c c); auto.
  intros. destruct n; auto.
Qed.

Lemma ascii_dec_false:
  forall T (A B: T) c1 c2,
  c1 <> c2 ->
  (if ascii_dec c1 c2 then A else B) = B.
Proof.
  intros. case (ascii_dec c1 c2); auto.
  intros; subst; destruct H; auto.
Qed.

Lemma rev_nil_eq_nil:
  forall A (l: list A),
  rev l = nil ->
  l = nil.
Proof.
  intros. apply f_equal with (f := @rev A) in H.
  rewrite rev_involutive in H. auto.
Qed.

Lemma rev_inj:
  forall A (l1 l2: list A),
  rev l1 = rev l2 ->
  l1 = l2.
Proof.
  intros. apply f_equal with (f := @rev A) in H.
  repeat rewrite rev_involutive in H. auto.
Qed.

Definition in_tail {A} (a: A) (l: list A) : Prop :=
  match l with
  | h::t => In a t
  | nil  => False
  end.

Lemma in_tail_app_tail:
  forall A (l1 l2: list A) x,
  In x l2 ->
  l1 <> nil ->
  in_tail x (l1 ++ l2).
Proof.
  intros. destruct l1. destruct H0; auto.
  simpl. apply in_or_app. right; auto.
Qed.

Definition in_mod_last {A} (a: A) (l: list A) : Prop :=
  match rev l with
  | h::t => In a t
  | nil  => False
  end.

Lemma in_mod_last_or:
  forall A (t: list A) (x h: A),
  in_mod_last x (h::t) ->
  x = h \/ in_mod_last x t.
Proof.
  unfold in_mod_last.
  destruct t using rev_ind; simpl. auto.
  rewrite rev_app; simpl; intros.
  apply in_app_or in H.
  destruct H; simpl in H; auto.
  destruct H; auto. contradiction.
Qed.


Inductive uniq {A} : list A -> Prop :=
  | uniq_nil:
      uniq nil
  | uniq_cons:
      forall l a,
      uniq l ->
      ~ In a l ->
      uniq (a :: l).


Lemma uniq_app:
  forall A (l1 l2: list A),
  uniq (l1 ++ l2) -> uniq l1 /\ uniq l2.
Proof.
  induction l1; simpl; intros.
  split. constructor. auto.

  split.
  apply uniq_cons.
  inversion H. apply IHl1 in H2. destruct H2. auto.
  inversion H. unfold not. intros. destruct H3.
  apply in_or_app. left. auto.

  inversion H.
  apply IHl1 in H2. destruct H2. auto.
Qed.

Lemma uniq_end:
  forall A (l: list A) a,
  uniq l ->
  ~ In a l ->
  uniq (l ++ a :: nil).
Proof.
  induction l; simpl; intros.
  constructor; auto.
  constructor; auto.
  apply IHl; auto. inv H; auto.
  unfold not; intros. destruct H0.
  apply in_app_or in H1. simpl in H1.
  destruct H1. inv H. contradiction.
  destruct H0; auto. contradiction.
Qed.

Lemma uniq_app_comm_helper:
  forall A (a : A) (l1 l2: list A),
  ~ In a (l1 ++ l2) -> uniq (l1 ++ l2) -> uniq (l1 ++ a:: l2).
Proof.
  intros A a l1.
  induction l1.

  intros. simpl. apply uniq_cons; auto.

  intros. simpl. 
  apply uniq_cons.
   (* use IH *)
  simpl in H0. inv H0. 
  assert ( ~ In a (l1 ++ l2)).
  unfold not; intros. destruct H.
  replace ((a0 :: l1) ++ l2) with (a0 :: (l1 ++ l2)).
  apply in_cons; auto. reflexivity.
  apply IHl1; auto.

   (* use the given hypothesis *)
  unfold not; intros. destruct H.
  assert (a = a0).

  apply in_app_or in H1.
  destruct H1. simpl in H0. inv H0. destruct H4.
  apply in_app_iff. left; auto.

  simpl in H. destruct H. auto.
  simpl in H0. inv H0. destruct H4. 
  apply in_app_iff. right.  auto.

  rewrite H. simpl. left; auto.
Qed.


Lemma uniq_app_comm:
  forall A (l1 l2: list A),
  uniq (l1 ++ l2) -> uniq (l2 ++ l1).
Proof.
  induction l1.
  intros. rewrite app_nil_r. auto.

  intros.
  simpl in H.
  inversion H.

  eapply uniq_app_comm_helper; eauto. 
  unfold not; intros. destruct H3.
  apply in_app_or in H4. 
  apply in_app_iff.
  apply or_comm. auto.
Qed.


Lemma map_in_uniq_inv:
  forall A B (f: A -> B) (l: list A) x y,
  f x = f y ->
  uniq (map f l) ->
  In x l ->
  In y l ->
  x = y.
Proof.
  induction l; simpl; intros. contradiction.
  destruct H1; destruct H2; subst. auto.
  inv H0. destruct H5. rewrite H. apply in_map; auto.
  inv H0. destruct H5. rewrite <- H. apply in_map; auto.
  apply IHl; auto. inv H0; auto.
Qed.
