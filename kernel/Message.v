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
Require Import Arith.
Require Import List.
Require Import RSep.
Require Import VCRIO.
Require Import NArith.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Fixpoint str_la (s: string) : list ascii :=
  match s with
  | EmptyString => nil
  | String a s' => a :: (str_la s')
  end.

Fixpoint la_str (la: list ascii) : string :=
  match la with
  | nil   => EmptyString
  | x::xs => String x (la_str xs)
  end.

Fixpoint str_nta (s: string) : list ascii :=
  match s with
  | EmptyString => nil
  | String a s' => a :: (str_nta s')
  end.

Fixpoint nta_str (la: list ascii) : string :=
  match la with
  | nil               => EmptyString
  | x::xs             => String x (nta_str xs)
  end.

Lemma nth_error_some_in:
  forall A (l: list A) i a,
  nth_error l i = Some a ->
  In a l.
Proof.
  induction l; destruct i; simpl; intros.
  discriminate. discriminate. inv H; auto.
  right. eapply IHl; eauto.
Qed.

Inductive la_eq: list ascii -> list ascii -> Prop :=
  | nil_la : la_eq nil nil
  | not_nil_la : forall la la' a, la_eq la la' -> la_eq (a::la) (a::la').

Inductive la_endswith : list ascii -> list ascii -> Prop :=
  | la_endswith_same : forall la la', la_eq la la' -> la_endswith la la'
  | la_endswith_strict : forall la la' a, la_endswith la la' -> la_endswith (a::la) la'.

Inductive la_startswith : list ascii -> list ascii -> Prop :=
  | la_startswith_same : forall la la', la_eq la la' -> la_startswith la la'
  | la_startswith_strict : forall la la' a, la_startswith la la' -> la_startswith (la ++ a::nil) la'.

Inductive la_notcontaining : list ascii -> ascii -> Prop :=
  | la_notcontaining_nil : forall a, la_notcontaining nil a
  | la_notcontaining_cons : forall la a sep, a <> sep -> la_notcontaining la sep -> 
                              la_notcontaining (a::la) sep.

Definition la_firstelem (elem:list ascii) (str:list ascii) (sep:ascii) :=
  (la_startswith str (elem ++ (sep :: nil))) /\ (la_notcontaining elem sep).

Lemma same_la_eq : 
  forall la, la_eq la la.
Proof.
  induction la.
  apply nil_la.
  
  apply not_nil_la. apply IHla.
Qed.

Definition tabeq_true:
  forall T (A B: T) t,
  (if tabeq t t then A else B) = A.
Proof.
  intros. case (tabeq t t); intros.
  auto. destruct n; auto.
Qed.

Definition tabeq_false:
  forall T (A B: T) t1 t2,
  t1 <> t2 ->
  (if tabeq t1 t2 then A else B) = B.
Proof.
  intros. case (tabeq t1 t2); intros.
  subst. destruct H; auto. auto.
Qed.

Fixpoint thandles (tabs: list tab) : hprop :=
  match tabs with
  | t::ts => thandle t * thandles ts
  | nil   => __
  end.

(* drop first thandle to x *)
Fixpoint thandles_drop (tabs: list tab) (x: tab) : hprop :=
  match tabs with
  | t::ts =>
      if tabeq t x
      then thandles ts
      else thandle t * thandles_drop ts x
  | nil => __
  end.

Lemma unpack_thandles:
  forall ts t,
  In t ts ->
  thandles ts ==> thandle t * thandles_drop ts t.
Proof.
  induction ts; simpl; intros. contradiction.
  destruct H; subst. rewrite tabeq_true. apply himp_refl.
  case (tabeq a t); intros. subst. apply himp_refl.
  apply himp_comm_conc. apply himp_assoc_conc1.
  apply himp_split. apply himp_refl.
  apply himp_comm_conc; auto.
Qed.

Lemma repack_thandles:
  forall ts t,
  In t ts ->
  thandle t * thandles_drop ts t ==> thandles ts.
Proof.
  induction ts; simpl; intros. contradiction.
  destruct H; subst. rewrite tabeq_true. apply himp_refl.
  case (tabeq a t); intros. subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Lemma repack_io_t_handles:
  forall ts t,
  In t ts ->
  thandle t * thandles_drop ts t ==> thandles ts.
Proof.
  induction ts; simpl; intros. contradiction.
  destruct H; subst. rewrite tabeq_true. apply himp_refl.
  case (tabeq a t); intros. subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Lemma unpack_thandles_last:
  forall ts t,
  thandles (ts ++ t :: nil) ==> thandles ts * thandle t.
Proof.
  induction ts; simpl; intros.
  apply himp_comm_prem. apply himp_empty_prem.
  apply himp_empty_conc. apply himp_refl.
  apply himp_assoc_conc1. apply himp_split.
  apply himp_refl. auto.
Qed.

Lemma repack_thandles_last:
  forall ts t,
  thandles ts * thandle t ==> thandles (ts ++ t :: nil).
Proof.
  induction ts; simpl; intros.
  apply himp_comm_conc. apply himp_empty_conc.
  apply himp_empty_prem. apply himp_refl.
  apply himp_assoc_prem1. apply himp_split.
  apply himp_refl. auto.
Qed.


Definition cproceq_true:
  forall T (A B: T) t,
  (if cproceq t t then A else B) = A.
Proof.
  intros. case (cproceq t t); intros.
  auto. destruct n; auto.
Qed.

Definition cproceq_false:
  forall T (A B: T) t1 t2,
  t1 <> t2 ->
  (if cproceq t1 t2 then A else B) = B.
Proof.
  intros. case (cproceq t1 t2); intros.
  subst. destruct H; auto. auto.
Qed.


Fixpoint chandles (cprocs: list cproc) : hprop :=
  match cprocs with
  | t::ts => chandle t * chandles ts
  | nil   => __
  end.

(* drop first chandle to x *)
Fixpoint chandles_drop (cprocs: list cproc) (x: cproc) : hprop :=
  match cprocs with
  | t::ts =>
      if cproceq t x
      then chandles ts
      else chandle t * chandles_drop ts x
  | nil => __
  end.

Lemma unpack_chandles:
  forall ts t,
  In t ts ->
  chandles ts ==> chandle t * chandles_drop ts t.
Proof.
  induction ts; simpl; intros. contradiction.
  destruct H; subst. rewrite cproceq_true. apply himp_refl.
  case (cproceq a t); intros. subst. apply himp_refl.
  apply himp_comm_conc. apply himp_assoc_conc1.
  apply himp_split. apply himp_refl.
  apply himp_comm_conc; auto.
Qed.

Lemma repack_chandles:
  forall ts t,
  In t ts ->
  chandle t * chandles_drop ts t ==> chandles ts.
Proof.
  induction ts; simpl; intros. contradiction.
  destruct H; subst. rewrite cproceq_true. apply himp_refl.
  case (cproceq a t); intros. subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Lemma repack_io_t_chandles:
  forall ts t,
  In t ts ->
  chandle t * chandles_drop ts t ==> chandles ts.
Proof.
  induction ts; simpl; intros. contradiction.
  destruct H; subst. rewrite cproceq_true. apply himp_refl.
  case (cproceq a t); intros. subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Lemma unpack_chandles_last:
  forall ts t,
  chandles (ts ++ t :: nil) ==> chandles ts * chandle t.
Proof.
  induction ts; simpl; intros.
  apply himp_comm_prem. apply himp_empty_prem.
  apply himp_empty_conc. apply himp_refl.
  apply himp_assoc_conc1. apply himp_split.
  apply himp_refl. auto.
Qed.

Lemma repack_chandles_last:
  forall ts t,
  chandles ts * chandle t ==> chandles (ts ++ t :: nil).
Proof.
  induction ts; simpl; intros.
  apply himp_comm_conc. apply himp_empty_conc.
  apply himp_empty_prem. apply himp_refl.
  apply himp_assoc_prem1. apply himp_split.
  apply himp_refl. auto.
Qed.


(* messages from tab to kernel *)

Inductive t2k_msg : Set :=
  | Display : positive -> list ascii -> t2k_msg
  | ReqHtml : positive -> list ascii -> t2k_msg
  | RequestSocket : positive -> list ascii -> t2k_msg
  | Navigate : positive -> list ascii -> t2k_msg
  | GetCookie : positive -> list ascii -> t2k_msg
  | SetCookie : positive -> list ascii -> t2k_msg.


Definition t2k_msg_tag (m: t2k_msg) : ascii :=
  match m with
  | Display _ _ => "001"%char
  | ReqHtml _ _ => "002"%char
  | RequestSocket _ _ => "003"%char
  | Navigate _ _=> "009"%char
  | GetCookie _ _=> "010"%char
  | SetCookie _ _=> "011"%char
  end.

Definition t2k_msg_payload (m: t2k_msg) : list ascii :=
  match m with
  | Display _ s => s
  | ReqHtml _ s => s
  | RequestSocket _ s => s
  | Navigate _ s => s
  | GetCookie _ s  =>  s
  | SetCookie _ s => s
  end.

Definition t2k_msg_psize (m: t2k_msg) : positive :=
  match m with
  | Display s _ => s
  | ReqHtml s _ => s
  | RequestSocket s _  => s
  | Navigate s _ => s
  | GetCookie s _ =>  s
  | SetCookie s _ => s
  end.

Fixpoint byte_pos_to_ascii (pos:positive) (cnt:nat) : ascii :=
  if beq_nat cnt 7 then 
    match pos with
      | 1%positive => one%char
      | p~1%positive => one%char
      | p~0%positive => zero%char
    end
  else
    match pos with
      | 1%positive => one%char
      | p~1%positive => shift true (byte_pos_to_ascii p (S cnt))
      | p~0%positive => shift false (byte_pos_to_ascii p (S cnt))
    end.

Fixpoint next_byte_pos (pos:positive) (cnt:nat) : option positive :=
  if beq_nat cnt 7 then 
    match pos with
      | 1%positive => (Some 1%positive)
      | p~1%positive => (Some 1%positive)
      | p~0%positive => None
    end
  else
    match pos with
      | 1%positive => (Some 1%positive)
      | p~1%positive =>
         match (next_byte_pos p (S cnt)) with
           | (Some up) => (Some (xI up))
           | None => (Some xH)
         end
      | p~0%positive => 
         match (next_byte_pos p (S cnt)) with
           | (Some up) => (Some (xO up))
           | None => None
         end
    end.

Fixpoint shift_pos_byte (pos:positive) (cnt:nat) : positive :=
  if beq_nat cnt 8 then pos
  else
  match pos with 
    | 1%positive => 1%positive
    | p~0%positive => shift_pos_byte p (S cnt)
    | p~1%positive => shift_pos_byte p (S cnt)
  end.

Fixpoint pos2la4 (p0:positive) : list ascii :=
  let p1 := shift_pos_byte p0 0 in
  let p2 := shift_pos_byte p1 0 in
  let p3 := shift_pos_byte p2 0 in
  (if (leb 9 (Psize p2)) 
    then (let nbyte :=  (next_byte_pos p3 0) in 
      match nbyte with | None => "000"%char | Some p => (byte_pos_to_ascii p 0) end)
    else "000"%char ) ::
  (if (leb 9 (Psize p1)) 
    then (let nbyte :=  (next_byte_pos p2 0) in 
      match nbyte with | None => "000"%char | Some p => (byte_pos_to_ascii p 0) end)
    else "000"%char ) ::
  (if (leb 9 (Psize p0)) 
    then (let nbyte :=  (next_byte_pos p1 0) in 
      match nbyte with | None => "000"%char | Some p => (byte_pos_to_ascii p 0) end)
    else "000"%char ) ::
  (let nbyte :=  (next_byte_pos p0 0) in
    match nbyte with | None => "000"%char | Some p => (byte_pos_to_ascii p 0) end) :: nil.

(* Eval compute in (pos2la4 (256*256*256*3 + 256*256*3 + 256*3 + 3)%positive). *)
(* Fixpoint la2pos (la: list ascii) : positive := 1%positive. *)
(* Eval compute in (byte_pos_to_ascii 255%positive 0%nat). *)

Definition ReadMsg (t: tab) (m: t2k_msg) : Trace :=
  ReadN (t2k t) (t2k_msg_psize m) (t2k_msg_payload m) :: 
  ReadN (t2k t) (size 4%positive)  (pos2la4 (t2k_msg_psize m)) :: 
  ReadN (t2k t) (size 1%positive) ((t2k_msg_tag m)::nil ) :: nil.

Definition not_msg (s: list ascii) : Prop :=
  forall t1 t2 s p s' p' s'' p'' m,
    ReadN (t2k t1) s p :: ReadN (t2k t1) s' p' :: ReadN (t2k t1) s'' p'' :: nil <> ReadMsg t2 m.

Inductive maybe_t2k_msg : Set :=
  | T2Kmsg : t2k_msg -> maybe_t2k_msg
  | BadTag : list ascii -> maybe_t2k_msg.

Definition hd_a (ls:list ascii) : ascii := 
  hd "000"%char ls.

Definition isnil (ls: list ascii) : bool :=
  match ls with 
  | nil => true
  | _ => false
  end.

Axiom readmsg:
  forall (t: tab) (tr: [Trace]),
  STsep (tr ~~ traced tr * thandle t)
        (fun mm =>
          match mm with
          | T2Kmsg m => tr ~~ traced (ReadMsg t m ++ tr) * thandle t
          | BadTag garbage => tr ~~ traced (ReadN (t2k t) (size 1%positive) garbage :: tr) * thandle t * [not_msg garbage]
          end).

(* messages from kernel to tab *)
Inductive k2t_msg : Set :=
  | Render   : positive -> list ascii -> k2t_msg
  | KeyPress : positive -> list ascii -> k2t_msg
  | MouseClick: positive -> list ascii -> k2t_msg
  | RspHtml  : positive -> list ascii -> k2t_msg
  | ResultSocket : positive -> list ascii -> k2t_msg
  | ResultCookie : positive -> list ascii -> k2t_msg
  | K2TSetCookie : positive -> list ascii -> k2t_msg.

Definition k2t_msg_tag (m: k2t_msg) : ascii :=
  match m with
  | Render _ _    => "004"%char
  | KeyPress _ _ => "005"%char
  | MouseClick _ _=> "006"%char
  | RspHtml _ _ => "007"%char
  | ResultSocket _ _=> "008"%char
  | ResultCookie _ _=> "012"%char
  | K2TSetCookie _ _ => "016"%char
  end.

Definition k2t_msg_psize (m: k2t_msg) : positive :=
  match m with
  | Render p _    => p
  | KeyPress p _ => p
  | MouseClick p _ => p
  | RspHtml p _  => p
  | ResultSocket p _  => p
  | ResultCookie p _  => p
  | K2TSetCookie p _ => p
  end.

Definition k2t_msg_payload (m: k2t_msg) : list ascii :=
  match m with
  | Render _ s    => s
  | KeyPress _ s => s
  | MouseClick _ s => s
  | RspHtml _ s  => s
  | ResultSocket _ s  => s
  | ResultCookie _ s  => s
  | K2TSetCookie _ s => s
  end.

Definition WroteMsg (t: tab) (m: k2t_msg) : Trace :=
  let ic := (k2t t) in
    WriteN ic (k2t_msg_psize m) (k2t_msg_payload m) :: WriteN ic (size 4%positive) (pos2la4 (k2t_msg_psize m)) ::  WriteN ic (size 1%positive) ((k2t_msg_tag m) :: nil) :: nil.

Axiom writemsg:
  forall (t: tab) (m: k2t_msg) (tr: [Trace]),
  STsep (tr ~~ traced tr * thandle t)
        (fun _:unit => tr ~~ traced (WroteMsg t m ++ tr) * thandle t).


(* message from kernel to graphics *)
Inductive k2g_msg : Set :=
  | K2GDisplay : positive -> list ascii -> k2g_msg.

Definition k2g_msg_tag (m: k2g_msg) : ascii :=
  match m with
  | K2GDisplay _ _ => "000"%char
  end.

Definition K2GDisplayTag := k2g_msg_tag (K2GDisplay 1%positive nil).

Definition k2g_msg_payload (m: k2g_msg) : list ascii :=
  match m with
  | K2GDisplay _ s => s
  end.

Definition k2g_msg_psize (m: k2g_msg) : positive :=
  match m with
  | K2GDisplay p _ => p
  end.

Definition WroteGMsg (m: k2g_msg) : Trace :=
    WriteN gout (k2g_msg_psize m) (k2g_msg_payload m) :: WriteN gout 4%positive (pos2la4 (k2g_msg_psize m)) ::  WriteN gout 1%positive ((k2g_msg_tag m) :: nil) :: nil.

Axiom writegmsg:
  forall (m: k2g_msg) (tr: [Trace]),
  STsep (tr ~~ traced tr * ohandle gout)
        (fun _:unit => tr ~~ traced (WroteGMsg m ++ tr) * ohandle gout).


(* message from kernel to cookie processes *)
Inductive k2c_msg : Set :=
  | K2CSetCookie : positive -> list ascii -> k2c_msg
  | K2CGetCookie : positive -> list ascii -> k2c_msg.

Definition k2c_msg_tag (m: k2c_msg) : ascii :=
  match m with
  | K2CSetCookie _ _ => "013"%char
  | K2CGetCookie _ _ => "014"%char
  end.

Definition K2CSetCookieTag := k2c_msg_tag (K2CSetCookie 1%positive nil).
Definition K2CGetCookieTag := k2c_msg_tag (K2CGetCookie 1%positive nil).

Definition k2c_msg_payload (m: k2c_msg) : list ascii :=
  match m with
  | K2CSetCookie _ s => s
  | K2CGetCookie _ s => s
  end.

Definition k2c_msg_psize (m: k2c_msg) : positive :=
  match m with
  | K2CSetCookie s _ => s
  | K2CGetCookie s _ => s
  end.

Definition WroteCMsg (c: cproc) (m: k2c_msg) : Trace :=
  let oc := (k2c c) in
    WriteN oc (k2c_msg_psize m) (k2c_msg_payload m) :: WriteN oc (size 4%positive) (pos2la4 (k2c_msg_psize m)) ::  WriteN oc (size 1%positive) ((k2c_msg_tag m) :: nil) :: nil.

Axiom writecmsg:
  forall (c: cproc) (m: k2c_msg) (tr: [Trace]),
  STsep (tr ~~ traced tr * chandle c)
        (fun _:unit => tr ~~ traced (WroteCMsg c m ++ tr) * chandle c).


(* c2k *)
Inductive c2k_msg : Set :=
  | C2KSetCookie : positive -> list ascii -> c2k_msg
  | C2KResultCookie : positive -> list ascii -> c2k_msg.

Definition c2k_msg_tag (m: c2k_msg) : ascii :=
  match m with
  | C2KSetCookie _ _ => "017"%char
  | C2KResultCookie _ _ => "015"%char
  end.

Definition C2KResultCookieTag := c2k_msg_tag (C2KResultCookie 1%positive nil).

Definition c2k_msg_payload (m: c2k_msg) : list ascii :=
  match m with
  | C2KSetCookie _ s => s
  | C2KResultCookie _ s => s
  end.

Definition c2k_msg_psize (m: c2k_msg) : positive :=
  match m with
  | C2KSetCookie s _ => s
  | C2KResultCookie s _ => s
  end.

Definition ReadCMsg (c: cproc) (m: c2k_msg) : Trace :=
  ReadN (c2k c) (c2k_msg_psize m) (c2k_msg_payload m) :: 
  ReadN (c2k c) (size 4%positive)  (pos2la4 (c2k_msg_psize m)) :: 
  ReadN (c2k c) (size 1%positive) ((c2k_msg_tag m)::nil ) :: nil.

Axiom readcmsg:
  forall (c: cproc) (tr: [Trace]),
  STsep (tr ~~ traced tr * chandle c)
        (fun m => tr ~~ traced (ReadCMsg c m ++ tr) * chandle c).

Definition endorsemsg := (str_la " The current tab navigates to :  ").

Definition WroteEndorseMsg (initurl: list ascii): Action :=
  WriteStrFile stdout (endorsemsg ++ initurl).

Definition writeendorsemsg:
  forall (initurl: list ascii) (tr: [Trace]),
  STsep (tr ~~ traced tr * fhandle stdout)
        (fun _:unit => tr ~~ traced (WroteEndorseMsg initurl :: tr) * fhandle stdout).
Proof.  
  intros; refine (
    {{ 
      writestrfile stdout (endorsemsg ++ initurl) tr 
    }}
  );
  sep fail auto.
Qed.

Definition escape := "027"%char.

(* Definition clear_a  := escape :: str_la "[2J" ++ escape :: str_la "[;H".*)
Definition clear_a  := escape :: str_la "[1m" ++ escape :: str_la "[32m".
Definition chrome_a := escape :: str_la "[1m" ++ escape :: str_la "[32m".
Definition curtab_a := escape :: str_la "[1m" ++ escape :: str_la "[31m".
Definition reset_a  := escape :: str_la "[0m".

Definition clear_s  := la_str clear_a.
Definition chrome_s := la_str chrome_a.
Definition curtab_s := la_str curtab_a.
Definition reset_s  := la_str reset_a.

Definition Clear : Action :=
  WriteStrFile stdout clear_a.

Definition clear:
  forall (_: unit) (tr: [Trace]),
  STsep (tr ~~ traced tr * fhandle stdout)
        (fun _:unit => tr ~~ traced (Clear :: tr) * fhandle stdout).
Proof.
  intros; refine (
    {{ writestrfile stdout clear_a tr }}
  );
  sep fail auto.
Qed.

(* WARNING : coq hangs if you destruct an ascii value *)

Definition tab_idx_select (t: tab) : string :=
  la_str (tab_origin_url t).

Definition select_tab_idx (c: ascii) : option nat :=
  match c with
  | "001"%char => Some 0
  | "002"%char => Some 1
  | "003"%char => Some 2
  | "004"%char => Some 3
  | "005"%char => Some 4
  | "006"%char => Some 5
  | "007"%char => Some 6
  | "014"%char => Some 7
  | "015"%char => Some 8
  | "016"%char => Some 9
  | _   => None
  end%char.

Fixpoint str_concat (sep: string) (strs: list string) : string :=
  match strs with
  | nil    => ""
  | s::nil => s
  | s::ss  => s ++ sep ++ str_concat sep ss
  end%string.

Fixpoint title (focus t: tab) (i: nat) : string :=
  (if tabeq focus t then
    curtab_s ++ (tab_idx_select t) ++ chrome_s
  else
    tab_idx_select t)%string.

Fixpoint titles_aux (tabs: list tab) (focus: tab) (i: nat) : list string :=
  match tabs with
  | t :: ts =>
      title focus t i :: titles_aux ts focus (S i)
  | nil =>
      nil
  end.
  

Definition titles (tabs: list tab) (focus: tab) : string :=
  ("| " ++ (str_concat " | " (titles_aux tabs focus 0)) ++ " |")%string.

Definition newline := "010"%char.

Definition nl := String newline EmptyString.

Definition screen_aux (tabs: list tab) (focus: tab) (disp: string) : string :=
  (        chrome_s
  ++ nl ++ "-------------------------------------------------------------------------------------------------------------"
  ++ nl ++ titles tabs focus
  ++ nl ++ "-------------------------------------------------------------------------------------------------------------"
  ++ nl 
        ++ reset_s
  )%string.

Definition screen (tabs: list tab) (focus: tab) (disp: list ascii) : list ascii :=
  str_la (screen_aux tabs focus (nta_str disp)).
Opaque screen.

Definition Paint (tabs: list tab) (focus: tab) : Trace :=
  WriteStrFile stdout (screen tabs focus nil) ::
  WriteStrFile stdout ("@"%char :: tab_origin_url focus  ++ newline :: nil) ::
  Clear :: nil.

Definition paint:
  forall (tabs: list tab) (focus: tab) (tr: [Trace]),
  STsep (tr ~~ traced tr * fhandle stdout)
        (fun _:unit => tr ~~ traced (Paint tabs focus ++ tr) * fhandle stdout).
Proof.
  intros; refine (
    clear tt
      tr;;
    writestrfile stdout ("@"%char :: tab_origin_url focus ++ newline :: nil)
      (tr ~~~ Clear :: tr);;
    writestrfile stdout (screen tabs focus nil)
      (tr ~~~ WriteStrFile stdout ("@"%char :: tab_origin_url focus ++ newline :: nil) :: Clear :: tr);;
    {{ Return tt }}
  );
  sep fail auto.
Qed.
