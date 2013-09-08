(*
   Quark is Copyright (C) 2012-2015, Quark Team.

   You can redistribute and modify it under the terms of the GNU GPL,
   version 2 or later, but it is made available WITHOUT ANY WARRANTY.

   For more information about Quark, see our web site at:
   http://goto.ucsd.edu/quark/
*)

external sendfd: int -> int -> unit = "_sendfd"
external int_of_file_descr: Unix.file_descr -> int = "_int_of_file_descr"
external file_descr_of_int: int -> Unix.file_descr = "_file_descr_of_int"

let (|>) x f = f x

let print  = Printf.printf
let eprint = Printf.eprintf
let mkstr  = Printf.sprintf
let null_file_descr = (Unix.openfile "/dev/null" [Unix.O_RDWR]  0)

(* read evrything out of a file descriptor *)
let drain_file_desc fd pid =
  let cap = 1024 in
  let buf = Buffer.create cap in
  let tmp = String.create cap in
  Unix.set_nonblock fd;
  let rec aux () =
    try 
      let n = Unix.read fd tmp 0 cap in
      if n > 0 then 
      begin
        Buffer.add_substring buf tmp 0 n;
        aux ();
      end
    with _ ->
      let (got_pid, status) = Unix.waitpid [Unix.WNOHANG] pid in
      if got_pid = 0 then begin
        aux (); 
      end
  in
  aux ();
  Buffer.contents buf

let drain_ichan ic =
  let cap = 1 lsl 12 in
  let buf = Buffer.create cap in
  let tmp = String.create cap in
  let rec aux () =
    let n = input ic tmp 0 cap in
    if n > 0 then begin
      Buffer.add_substring buf tmp 0 n;
      aux ()
    end
  in
  aux ();
  Buffer.contents buf

(* run command in shell, return its output *)
let shell_out cmd =
  (* D:BEGIN    ((eprint "BEGIN] shell_out : %s\n" cmd); flush stderr);     D:END *)  
  let c = Unix.open_process_in cmd in
  let o = drain_ichan c in
  (* D:BEGIN    ((eprint "END] shell_out : drain ichan ended"); flush stderr);     D:END *)  
  close_in c; 
  (* D:BEGIN    ((eprint "END] shell_out : close "); flush stderr);    D:END *)    o

(* run command in shell, return its output *)
let exec_out cmd args =
  let (r,w) = Unix.pipe () in  
  let pid = (Unix.create_process cmd (Array.of_list (cmd::args)) Unix.stdin w Unix.stderr) in 
  let output = (drain_file_desc r pid) in
  ignore (Unix.close w);
  ignore (Unix.close r); output

let quote str = 
  (String.concat "" ("\"" :: str :: "\"" :: []))

let vcr_open_process_args cmd args =
  let (p,c) = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  let escaped_args = (List.map quote args) in
  let cmd_str = (String.concat " " (List.append [ cmd ; (string_of_int (int_of_file_descr c)) ] escaped_args)) in
  (* D:BEGIN *)   ((eprint "BEGIN] vcr_open_process_args : %s\n" cmd_str); flush stderr);  (* D:END *)  
  (ignore (Unix.open_process cmd_str));
  (p,p)

(* fst - in/snd - out *)
(*
let vcr_open_process_args cmd args =
  let (p,c) = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  eprint "BEGIN] open_process:%s, %d, %d, %s, %s\n" (Unix.getenv("PWD")) (Unix.getpid ()) (int_of_file_descr c) cmd (String.concat " " args); flush stderr; 
  let pid = (Unix.create_process cmd (Array.of_list (cmd::(string_of_int (int_of_file_descr c))::args)) null_file_descr null_file_descr Unix.stderr) in 
  (eprint "pid:%d\n" pid); flush stderr;
  eprint "END] open_process!\n"; flush stderr; 
  (p,p)
*)
let vcr_open_process cmd =
  vcr_open_process_args cmd []

type ('a, 'b) prod =
  | Pair of 'a * 'b

let fst = function
  | Pair (x, y) -> x

let snd = function
  | Pair (x, y) -> y

let to_pair (a, b) =
  Pair (a, b)

let ctoa x =
  let n = Char.code x in
  MlCoq.Ascii ( n lsr 0 land 1 = 1
              , n lsr 1 land 1 = 1
              , n lsr 2 land 1 = 1
              , n lsr 3 land 1 = 1
              , n lsr 4 land 1 = 1
              , n lsr 5 land 1 = 1
              , n lsr 6 land 1 = 1
              , n lsr 7 land 1 = 1
              )

let atoc (MlCoq.Ascii (a0, a1, a2, a3, a4, a5, a6, a7)) =
  Char.chr (   (if a0 then 1 lsl 0 else 0)
           lor (if a1 then 1 lsl 1 else 0)
           lor (if a2 then 1 lsl 2 else 0)
           lor (if a3 then 1 lsl 3 else 0)
           lor (if a4 then 1 lsl 4 else 0)
           lor (if a5 then 1 lsl 5 else 0)
           lor (if a6 then 1 lsl 6 else 0)
           lor (if a7 then 1 lsl 7 else 0)
             )

let la_str la =
 let s = String.create (List.length la) in
 let rec fill i = function
   | x :: xs ->
      s.[i] <- atoc x;
      fill (i + 1) xs
   | [] -> s
 in
 fill 0 la

let str_la s =
  (* D:BEGIN    eprint "BEGIN] str_la\n"; flush stderr;     D:END *)  
  let n = String.length s in
  let rec fill i res =
    if i >= 0 then
      fill (i-1) ((ctoa (String.get s i)) :: res)
    else
      res
  in
  fill (n-1) []

(* channels *)

type file_desc = Unix.file_descr
type ichan = Unix.file_descr
type ochan = Unix.file_descr

type tab =
    ((((ichan, ochan) prod, MlCoq.ascii list) prod, MlCoq.ascii list) prod, ichan option) prod

type cproc =
    ((ichan, ochan) prod, MlCoq.ascii list) prod

let stdin  = Unix.stdin
let stdout = Unix.stdout
let gout = snd (to_pair (vcr_open_process_args "../python-browser-8/output.py" ([]) )) 
(* let gout = snd (to_pair (vcr_open_process_args "../python-browser-8/output_exec" ([]) )) *)

let iceq ic1 ic2 =
  ic1 = ic2

let oceq oc1 oc2 =
  oc1 = oc2

let file_desc_eq f1 f2 =
  f1 = f2

let origineq origin1 origin2 =
  origin1 = origin2


(* I/O wrappers to log to stderr *)

let input_char ic =
  let buf = String.create 1 in
  ignore (Unix.read ic buf 0 1);
  let c = String.get buf 0 in
  (* eprint "K << %c\n%!" c; *) c

let output_char oc c =
  (* eprint "K >> %c\n%!" c; *)
  ignore (Unix.write oc (String.make 1 c) 0 1); ()

(* I/O actions *)
let read ic =
  try
    (Some (ctoa (input_char ic)))
  with End_of_file -> 
    None

let readfile f _ =
  try
    (ctoa (input_char f))
  with End_of_file -> 
    (ctoa (Char.chr 0))

let rec readn_worker ic cnt = 
  if cnt > 0 then
    let asc = (read ic) in
    match asc with 
    | Some value -> 
	value :: readn_worker ic (cnt-1)
    | None -> 
	[]
  else
    []

let rec get_empty_la cnt =
  if cnt > 0 then
    (ctoa (Char.chr 0)) :: get_empty_la (cnt-1)
  else
    []

let rec truncate la cnt =
  if cnt > 0 then
    match la with
    | a :: sla -> (truncate sla (cnt-1))
    | nil -> nil
  else la

let readn ic pos _ =
  (* D:BEGIN    eprint "K << BEGIN] readn\n"; flush stderr;    D:END *)  
  let cnt = (VCRCommon.pos2int pos) - 1 in
  let la = readn_worker ic cnt in
  (* D:BEGIN     eprint "K << END] readn\n"; flush stderr;    D:END *)  
  flush stderr;
  let len_la = List.length la in
  if len_la == cnt then la
  else if len_la < cnt then (List.append 
			       la (get_empty_la (cnt - len_la)))
  else truncate la (len_la - cnt)


let readn_with_int ic size_int =
  (* D:BEGIN     eprint "K << BEGIN] readn_with_int:%d\n" size_int; flush stderr;    D:END *)  
  let cnt = size_int in
  let la = readn_worker ic cnt in
  (* D:BEGIN     eprint "K << END] readn_with_int\n"; flush stderr;    D:END *)  
  let len_la = List.length la in
  if len_la == cnt then la
  else if len_la < cnt then (List.append 
			       la (get_empty_la (cnt - len_la)))
  else truncate la (len_la - cnt)

(*
  ReadN (t2k t) (t2k_msg_psize m) (t2k_msg_payload m) :: 
  ReadN (t2k t) (size 4%positive)  (pos2la4 (t2k_msg_psize m)) :: 
  ReadN (t2k t) (size 1%positive) ((t2k_msg_tag m)::nil ) :: nil.
*)

let la4_to_int la = 
  match la with 
  | a3 :: a2 :: a1 :: a0 :: nil -> 
      (  ((Char.code (atoc a3)) lsl 24) lor
	 ((Char.code (atoc a2)) lsl 16) lor
	 ((Char.code (atoc a1)) lsl 8 ) lor
	 (Char.code (atoc a0)))
  | _ -> 0

let int_to_la4 v64 = 
  let v = v64 in
  let la = 
  (ctoa (Char.chr ((v64 lsr 24) land 0x000000FF))) ::
  (ctoa (Char.chr ((v64 lsr 16) land 0x000000FF))) ::
  (ctoa (Char.chr ((v64 lsr 8) land 0x000000FF))) ::
  (ctoa (Char.chr (v64 land 0x000000FF))) :: [] in
  (* D:BEGIN    (eprint "K: int_to_la4 %d %d \n" (la4_to_int la) v64);    D:END *)   la

let readmsg t _ = 
  (* D:BEGIN    eprint "K << BEGIN] readmsg\n";    D:END *)  
  try  
    let ic = fst (fst (fst (fst t))) in
    let tag = input_char ic in
    let size_buf = readn_with_int ic 4 in
    let size_int = la4_to_int size_buf in
    let payload = readn_with_int ic size_int in
    (* D:BEGIN     (eprint "K << MIDL] readmsg - tag : %d, size: %d\n" (Char.code tag) size_int);    D:END *)  
    (* D:BEGIN     eprint "K << MIDL] readmsg - payload is read\n";    D:END *)  
    let tmsg = 
      (if tag = (Char.chr 1) then 
	VCRCommon.T2Kmsg(VCRCommon.Display((VCRCommon.int2pos (size_int+1)), payload))
    else if tag = (Char.chr 2) then VCRCommon.T2Kmsg (VCRCommon.ReqHtml ((VCRCommon.int2pos (size_int+1)), payload))
    else if tag = (Char.chr 3) then 
      VCRCommon.T2Kmsg (VCRCommon.RequestSocket ((VCRCommon.int2pos (size_int+1)), payload))
    else if tag = (Char.chr 9) then VCRCommon.T2Kmsg (VCRCommon.Navigate ((VCRCommon.int2pos (size_int+1)), payload))
    else if tag = (Char.chr 10) then VCRCommon.T2Kmsg (VCRCommon.GetCookie ((VCRCommon.int2pos (size_int+1)), payload))
    else if tag = (Char.chr 11) then VCRCommon.T2Kmsg (VCRCommon.SetCookie ((VCRCommon.int2pos (size_int+1)), payload))
    else 
	(eprint "BADTAG\n"; VCRCommon.BadTag ((ctoa (Char.chr 0))::[]))) in
    (* D:BEGIN     eprint "K << END] readmsg\n";    D:END *)  
    flush stderr;
    tmsg  
  with _ -> 
    (* D:BEGIN    eprint "K << ERROR-END] readmsg - bad tag\n";    D:END *)  
    VCRCommon.BadTag ((ctoa (Char.chr 0))::[])


let readcmsg (c:cproc) _ = 
  (* D:BEGIN    eprint "K << BEGIN] readcmsg\n";    D:END *)  
  try  
    let ic = fst (fst c) in
    let tag = input_char ic in
    let size_buf = readn_with_int ic 4 in
    let size_int = la4_to_int size_buf in
    let payload = readn_with_int ic size_int in
    (* D:BEGIN     (eprint "K << MIDL] readcmsg - tag : %d, size: %d\n" (Char.code tag) size_int);    D:END *)  
    (* D:BEGIN     eprint "K << MIDL] readcmsg - payload is read\n";    D:END *)  
    let cmsg = 
      (if tag = (Char.chr 17) then 
	VCRCommon.C2KSetCookie((VCRCommon.int2pos (size_int+1)), payload)
      else (* tag must be 15 *) 
	VCRCommon.C2KResultCookie((VCRCommon.int2pos (size_int+1)), payload)) in
    (* D:BEGIN     eprint "K << END] readcmsg\n";    D:END *)  
    flush stderr;
    cmsg  
  with _ -> 
    (* D:BEGIN    eprint "K << ERROR-END] readcmsg - bad tag\n";    D:END *)  
    let cmsg = VCRCommon.C2KResultCookie((VCRCommon.int2pos (1+1)), (str_la "\0")) in
    flush stderr;
    cmsg  

(* write messages *)

let write oc a =
  output_char oc (atoc a)

let rec writen_worker oc la =
  match la with
  | a :: ls -> ignore (write oc a); writen_worker oc ls
  | nil -> () 

let rec writestrfile f la _ =
  match la with
  | a :: ls -> ignore (write f a); writestrfile f ls ()
  | nil -> () 

let rec send_to_sock_worker oc str =
  let len = String.length str in
  let sent_data = Unix.send oc str 0 len [] in 
  if sent_data < len then
    let remain = (len - sent_data) in
    (send_to_sock_worker oc (String.sub str sent_data remain))
  else ()
  
let rec send_to_sock oc la =
  let str = (la_str la) in
  (send_to_sock_worker oc str); ()
  
let writen oc la _ = 
  (* D:BEGIN    eprint "K >> BEGIN] writen\n";    D:END *)  
  (writen_worker oc la);
  (* D:BEGIN    eprint "K >> END] writen\n";   D:END *)   ()

let endorse a _ =
  print_endline "\n Will you confirm this action? (y/n)\n";
  let c = input_char stdin in
  c = 'y'

let writemsg (t:tab) k2t_msg _ = 
  (* D:BEGIN    eprint "K >> BEGIN] writemsg\n"; flush stderr;    D:END *)  
  let oc = snd (fst (fst (fst t))) in
  let value = 
    (match k2t_msg with 
    | VCRCommon.Render (s,p) -> (4,s,p)
    | VCRCommon.KeyPress (s,p) -> (5,s,p)
    | VCRCommon.MouseClick (s,p) -> (6,s,p)
    | VCRCommon.RspHtml (s,p) -> (7,s,p)
    | VCRCommon.ResultSocket (s,p) -> (8,s,p)
    | VCRCommon.ResultCookie (s,p) -> (12,s,p) 
    | VCRCommon.InvalidateCookie (s,p) -> (16,s,p)) in
  match value with 
  | (tag,size,payload) ->
     (* D:BEGIN    (eprint "K >> MIDL] writemsg's tag:%d\n" tag);    D:END *)  
     (* D:BEGIN    (eprint "K >> MIDL] writemsg's size:%d\n " (List.length payload)); flush stderr;    D:END *)  
      write oc (ctoa (Char.chr tag));
     (* D:BEGIN    (eprint "K >> MIDL] writemsg : tag is written\n "; flush stderr);    D:END *)  
      send_to_sock oc (int_to_la4 (List.length payload));
      (* writen oc  VCRCommon.XH  (int_to_la4 (List.length payload)) (); *)
     (* D:BEGIN    (eprint "K >> MIDL] writemsg : size is written\n "; flush stderr);    D:END *)  
      send_to_sock oc payload;
      (* writen oc VCRCommon.XH payload ();  *)
     (* D:BEGIN    (eprint "K >> MIDL] writemsg : payload is written\n "; flush stderr);    D:END *)  
      (* D:BEGIN    eprint "K >> END] writemsg\n"; flush stderr;    D:END *)  
      ()


let writegmsg k2g_msg _ = 
  (* D:BEGIN    eprint "K >> BEGIN] writeGmsg\n";    D:END *)  
  let oc = gout in
  let value = 
    (match k2g_msg with 
    | VCRCommon.K2GDisplay (s,p) -> (0,s,p)) in
  match value with 
  | (tag,size,payload) ->
     (* D:BEGIN     (eprint "K >> MIDL] writeGmsg's tag:%d\n" tag);    D:END *)  
     (* D:BEGIN     (eprint "K >> MIDL] writeGmsg's size:%d\n " (List.length payload));    D:END *)  
      write oc (ctoa (Char.chr tag));
      send_to_sock oc (int_to_la4 (List.length payload));
      send_to_sock oc payload;
      (*
      writen oc VCRCommon.XH (int_to_la4 (List.length payload)) ();
      writen oc VCRCommon.XH payload (); 
	*)
      (* D:BEGIN    eprint "K >> END] writeGmsg\n";    D:END *)  
      ()

let writecmsg (c:cproc) k2c_msg _ = 
  (* D:BEGIN    eprint "K >> BEGIN] writecmsg\n"; flush stderr;    D:END *)  
  let oc = snd (fst c) in
  let value = 
    (match k2c_msg with 
    | VCRCommon.K2CSetCookie (s,p) -> (13,s,p)
    | VCRCommon.K2CGetCookie (s,p) -> (14,s,p)) in
  match value with 
  | (tag,size,payload) ->
     (* D:BEGIN    (eprint "K >> MIDL] writecmsg's tag:%d\n" tag);    D:END *)  
     (* D:BEGIN    (eprint "K >> MIDL] writecmsg's size:%d\n " (List.length payload)); flush stderr;    D:END *)  
      write oc (ctoa (Char.chr tag));
     (* D:BEGIN    (eprint "K >> MIDL] writecmsg : tag is written\n "; flush stderr);    D:END *)  
      send_to_sock oc (int_to_la4 (List.length payload));
      (* writen oc  VCRCommon.XH  (int_to_la4 (List.length payload)) (); *)
     (* D:BEGIN    (eprint "K >> MIDL] writecmsg : size is written\n "; flush stderr);    D:END *)  
      send_to_sock oc payload;
      (* writen oc VCRCommon.XH payload ();  *)
     (* D:BEGIN    (eprint "K >> MIDL] writecmsg : payload is written\n "; flush stderr);    D:END *)  
      (* D:BEGIN    eprint "K >> END] writecmsg\n"; flush stderr;    D:END *)  
      ()

(*
external sendfd: int -> int -> unit = "_sendfd"
external int_of_file_descr: Unix.file_descr -> int = "_int_of_file_descr"
*)
(* forall (t: tab) (desc: list ascii) (tr: [Trace]), *)
(* sprintf(buf, "%s:%d:%d:%d:%d", hostname, port, family(AF_INET), type(SOCK_STREAM), protocol); *)
let sendsocket t host desc _ = 
  (* D:BEGIN    eprint "K >> BEGIN] sendsocket\n"; flush stderr;    D:END *)  
  let oc = snd (fst (fst (fst t))) in
  let tab_fd_int = int_of_file_descr oc in

  try 
    let desc_str = la_str desc in
    let ls = Str.split (Str.regexp ":") desc_str in
    (* let hostname = List.nth ls 0 in *)
    let hostname = la_str host in
    let port = int_of_string (List.nth ls 1) in
    let family = int_of_string (List.nth ls 2) in
    let stype = int_of_string (List.nth ls 3) in
    (* let protocol = int_of_string (List.nth ls 4) in *)
    let sock = Unix.socket 
	(if family = 2 then Unix.PF_INET
         else if family = 10 then Unix.PF_INET6
         else Unix.PF_UNIX)
         (if stype = 1 then Unix.SOCK_STREAM
         else if stype = 2 then Unix.SOCK_DGRAM
         else if stype = 3 then Unix.SOCK_RAW
         else Unix.SOCK_SEQPACKET)
	0 in
    (* D:BEGIN     eprint "K >> MIDL0] sendsocket\n"; flush stderr;     D:END *) 
    let ipaddr = (Unix.gethostbyname hostname).Unix.h_addr_list.(0) in    
    (* D:BEGIN    eprint "K >> MIDL1] sendsocket\n"; flush stderr;     D:END *) 
    let portaddr = Unix.ADDR_INET (ipaddr, port) in
    (* D:BEGIN   (eprint "K >> END] sendsocket host:%s port:%d family:%d type:%d\n" hostname port family stype); flush stderr;   D:END *)      
    Unix.connect sock portaddr;
    let sock_fd_int = (int_of_file_descr sock) in    
    sendfd tab_fd_int sock_fd_int;
   (* D:BEGIN   eprint "K >> END] sendsocket\n"; flush stderr;   D:END *)  
    ()
  with 
    _ -> 
      (* D:BEGIN *)  eprint "K >> ERROR] sendsocket\n"; flush stderr;    (* D:END *)  
      try 
	sendfd tab_fd_int 1
      with
	_ -> ()

(*
let flush oc _ =
  flush (Unix.out_channel_of_descr oc)
*)

(*
let get_wellformedorigin _ =
  print_endline "Enter a URL to visit (scheme://host(:port)(/resource)):\n";
  let str = read_line () in
    print_string str;
    try 
      if (Str.string_match (Str.regexp "\\(http[s]?://\\)\\([^:/]+\\)\\(:[0-9]+\\)?") str 0 ) then (Some str) else None 
    with _ -> None
*)

let get_tab_origin_helper _ =
  print_endline "Enter a trusted origin suffix for the opening tab (e.g, a.com):";
  let str = read_line () in
  str

let rec get_tab_origin initurl =
  let line = get_tab_origin_helper () in
  match initurl with
  | [] -> line
  | _ ->
      print_endline "initurl is checked against the entered origin";
      if (Str.string_match 
	    (Str.regexp (String.concat "" ("http[s]?://[^/]*"::line::[])))
	       (la_str initurl) 0)
      then line 
      else (
	print_endline "The origin suffix you entered is inconsistent with the visiting url. Please do it again\n";
	(get_tab_origin initurl)
       )

let strip str = 
  let str = Str.replace_first (Str.regexp "^[ \n]+") "" str in
  Str.replace_first (Str.regexp "[ \n]+$") "" str;;  

let mktab initurl avoid oavoid ptab _  = 
  let next_tab_no = List.length avoid in
  let tab_uid = shell_out (Printf.sprintf "id -u tab%d" next_tab_no) in
  let tab_uid = strip tab_uid in
  let origin = get_tab_origin initurl in 
  let initurl_str = (match initurl with | [] -> "None" | _ -> la_str initurl) in
  let (i,o) = (vcr_open_process_args "../python-browser-8/tab_exec " (tab_uid :: origin :: [])) in 
  to_pair (to_pair (i,o), str_la origin)

let mkcproc domain avoid oavoid _  = 
  let (i,o) = (vcr_open_process_args "../python-browser-8/cookie.py " ([la_str domain])) in
  to_pair (i,o)

(*
let wget url _ =
  (* D:BEGIN    eprint "BEGIN] wget"; flush stderr;   D:END *)  
  eprint "BEGIN] wget\n"; flush stderr;
  let html = (url |> la_str
      |> mkstr "../python-browser-8/pywget.py '%s'"
      |> shell_out
      |> str_la) in
  (eprint "END] wget\n"; flush stderr); 
  html
*)

let wget url _ =
  (* D:BEGIN *)  eprint "BEGIN] wget"; flush stderr;   (* D:END *)
  (* let result = str_la (exec_out "../python-browser-8/pywget.py" [(la_str url)]) in *)
  let user_agent = "Mozilla/5.0 (X11; Linux i686) AppleWebKit/534.30 (KHTML, like Gecko) Ubuntu/11.04 Chromium/12.0.742.112 Chrome/12.0.742.112 Safari/534.30" in
  ignore (exec_out "/usr/bin/wget" [
		   "-q"; 
		   "-O"; 
		   "webfile"; 
		   "--tries=1";
		   "--timeout=1.0";
		   "--convert-links"; 
		   "-U"; 
		   user_agent; 
		   (la_str url)]);
  let ic = (open_in "webfile") in
  let result = drain_ichan ic in
  close_in ic; str_la result

let mousepos a _ =
  str_la (shell_out "../python-browser-8/mousepos.py")

(*
let ic_descr = Unix.descr_of_in_channel
let descr_ic = Unix.in_channel_of_descr
*)

(* descr_ic is NOT the inverse of ic_descr *)

let select f ics _ =
  let ics = (f :: ics) in
  (* D:BEGIN    (eprint "BEGIN] select\n"; flush stderr);    D:END *)  
  let ready, _, _ =
    (* -1.0 means no timeout *)
    Unix.select ics [] [] (-1.0)
  in
  (* D:BEGIN    (eprint "END] select\n"; flush stderr);     D:END *)  
  if ready = [] then 
  begin
    failwith "select returned nil after no timeout"
  end;
  try 
    List.find (fun ic -> ic = f) ready;
    to_pair ((Some f),[])
  with _ ->
    to_pair (None, (List.map (fun h -> List.find (fun ic -> ic = h) ics) ready))


let whitelist_hash = Hashtbl.create 10;;

Hashtbl.add whitelist_hash "google.com" ["gstatic.com"];;
Hashtbl.add whitelist_hash "facebook.com" ["fbcdn.net"];;
Hashtbl.add whitelist_hash "youtube.com" ["ytimg.com"];;
Hashtbl.add whitelist_hash "yahoo.com" ["yimg.com"];;
Hashtbl.add whitelist_hash "wikipedia.org" ["wikimedia.org"];;
Hashtbl.add whitelist_hash "twitter.com" ["twimg.com"];;
Hashtbl.add whitelist_hash "blogger.com" ("google.com"::"blogspot.com"::"gstatic.com"::"googleusercontent.com"::[]);;
Hashtbl.add whitelist_hash "ebay.com" ("ebaystatic.com"::"ebayimg.com"::"ebayrtm.com"::"ebay-stories.com"::"ad.doubleclick.net"::"s0.2mdn.net"::[]);;

let endswith s0 s1 =
  try 
    if (Str.string_match (Str.regexp (String.concat "" (".*"::s1::[]))) s0 0) 
    then true
    else false
  with _ ->
      false

let rec is_str_endswith_in_list str list =
  match list with
  | a :: list' ->
      if (endswith str a) then true
      else is_str_endswith_in_list str list'
  | nil -> false

(* library functions called by the coq kernel *)
let is_safe_sock_dest_on la_sock_host la_tab_domain = 
  let sock_host = (la_str la_sock_host) in
  let tab_domain = (la_str la_tab_domain) in
  (* D:BEGIN    (eprint "BEGIN] is_safe_sock_dest_on:%s on %s\n" sock_host tab_domain; flush stderr); D:END *)    
  if (endswith sock_host tab_domain) then true
  else
    try 
      let whitelist = Hashtbl.find whitelist_hash tab_domain in
      let res = is_str_endswith_in_list sock_host whitelist in
      (* D:BEGIN    (eprint "END] is_safe_sock_dest_on:%s on %s: %b\n" sock_host tab_domain res; flush stderr); D:END *)    
      res
    with _ ->
      (* D:BEGIN    (eprint "END] is_safe_sock_dest_on is failed\n"; flush stderr); D:END *)    
      false

(* Unix.file_descr -> list ascii *)
let tab_id_to_la sock = 
  let int_sock = int_of_file_descr sock in
  int_to_la4 int_sock

(*  list ascii -> Unix.file_descr*)
let get_tab_id la = 
  let int_sock = la4_to_int la in
  (file_descr_of_int int_sock)

let rec get_topdomain_tab_helper (la:MlCoq.ascii list) (cnt:int) :MlCoq.ascii list =
  match la with
  | a :: la' -> 
      let c = atoc a in
      (if c = '.' 
      then 
	(if cnt >= 1 then []
	else (ctoa c) :: (get_topdomain_tab_helper la' (cnt+1)))
      else
	(ctoa c) :: (get_topdomain_tab_helper la' cnt))
  | [] -> []

(* list ascii -> list ascii *)
let get_topdomain_tab (la_tabdomain:MlCoq.ascii list ) =
  try 

  let la_tabdomain_rev = List.rev la_tabdomain in
  let rev_result = get_topdomain_tab_helper la_tabdomain_rev 0 in
  List.rev rev_result

  with _ -> []

let get_topdomain_cookie (la_cookie:MlCoq.ascii list ) =
  try 

  let cookie = (la_str la_cookie) in
  (* D:BEGIN    (eprint "BEGIN] get_topdomain_cookie\n"; flush stderr);    D:END *)    
  (* D:BEGIN    (eprint "MIDL] cookie %s \n" cookie; flush stderr);    D:END *)    
  if (Str.search_forward (Str.regexp "\\(; \\)?domain=\\([^;]+\\)") cookie 0) > 0
  then (
    let topdomain_tab = get_topdomain_tab (str_la (Str.matched_group 2 cookie)) in
    let topdomain_tab_str = la_str topdomain_tab in
    topdomain_tab
   )
  else 
    (
    (* D:BEGIN    (eprint "MIDL] get_topdomain_cookie failed\n"; flush stderr); D:END *)    
    []
    )

  with _ -> []
