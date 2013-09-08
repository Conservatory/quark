
let null =
  Char.chr 0

let send s =
  print_string s;
  print_char null;
  flush stdout;
  prerr_endline ("RENDERER: send " ^ s)

let recv () =
  let buf = Buffer.create 128 in
  let rec aux () =
    let c = input_char stdin in
    if c != null then begin
      Buffer.add_char buf c;
      aux ()
    end
  in
  aux ();
  prerr_endline ("RENDERER: recv " ^ Buffer.contents buf);
  Buffer.contents buf

let rec main () =
  begin match recv () with
  | "KeyPress" ->
      ignore (recv ());
      send "Display";
      send "Hello Kernel!";
  | "Render" ->
      ()
  | "RspHtml" ->
      ignore (recv ())
  | _ ->
      prerr_endline ">>> bogus message from kernel <<<"
  end;
  main ()

let _ =
  main ()

