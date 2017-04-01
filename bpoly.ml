open Format
open Store
open Cycle

let limit = ref 65535
type howshow =
  | Sum | Length | Height | Depth | BarChart
  (* | NumKind | BaseTwo | BaseTwoS | ShrinkL | ShrinkM | ShrinkF *)
type mode = Naive | Floyd | Brent
type store = Map | Hashtbl
type display = Quiet | Verbose | Every of int | Show of howshow list

let restart_file : string option ref = ref None
let mode = ref Naive
let store = ref Hashtbl
let display = ref Verbose
let blist = ref []
let wid = ref 1

(* list representation in string *)
(* n-th character denotes the number of 'n' in the list representation *)
(* "\001\002\002\000\000\001" for 5.2.2.1.1.0 *)
type expr = Bytes.t
(* unsafe_get *)
external ($!!) : expr -> int -> int = "%string_unsafe_get"
external ($<-) : expr -> int -> int -> unit = "%string_unsafe_set"

let pp_expr prf expr =
  let i = Bytes.length expr-1 in
  fprintf prf "%*d" !wid i;
  for j = 2 to expr $!! i do
    fprintf prf ".%*d" !wid i
  done;
  for i = Bytes.length expr-2 downto 0 do
    for j = 1 to expr $!! i do
      fprintf prf ".%*d" !wid i
    done
  done

let list_of_expr (expr:expr) =
  let rec multi_add i num acc =
    if num <= 0 then acc else multi_add i (num-1) (i::acc) in
  let rec loop i acc =
    if i >= Bytes.length expr then acc
    else loop (i+1) (multi_add i (Char.code (Bytes.get expr i)) acc) in
  loop 0 []

let rec non_increasing = function
  | [] | [_] -> true
  | x::y::l -> x >= y && non_increasing (y::l)

let expr_of_list list =
  if non_increasing list then match list with
  | [] -> invalid_arg "expr_of_list"
  | n::l -> let expr = Bytes.make (n+1) '\000' in
            List.iter (fun n -> (expr $<- n) (1+(expr $!! n))) list;
            expr
  else invalid_arg "expr_of_list"

let expr_inc (expr:expr) i num =
  let len = Bytes.length expr in
  if i < len then begin
    (expr $<- i) (num + (expr $!! i));
    expr
  end else
    let newe = Bytes.make (i+1) '\000' in
    Bytes.blit expr 0 newe 0 len;
    (newe $<- i) num;
    newe

(* insert height i bar into expr[1..-1] and decrement all *)
let insert_left (expr:expr) i num =
  let len = Bytes.length expr in
  let rec loop j i =
    if j >= len then
      let newe : expr = Bytes.make i '\000' in
      Bytes.blit expr 1 newe 0 (len-1);
      (newe $<- (i-1)) num;
      newe
    else if j >= i then
      let newe : expr = Bytes.make (len-1) '\000' in
      Bytes.blit expr 1 newe 0 (len-1);
      (newe $<- (i-1)) (num + (newe $!! (i-1)));
      newe
    else
      loop (j+1) (i + (expr $!! j)) in
  loop 1 i

(* insert height i bar into expr (after the most left bar is inserted) *)
let insert_one expr i num =
  let rec loop j i =
    if j >= i then
      (expr $<- i) (num + (expr $!! i))
    else
      loop (j+1) (i + (expr $!! j)) in
  if num > 0 then loop 0 i

let apply (expr1:expr) (expr2:expr) =
  let zero1 = expr1 $!! 0 in
  let len2 = Bytes.length expr2 in
  (* first insert only the largest bar of expr2 to expr1 *)
  let left2 = expr2 $!! (len2-1) in
  let expr1 = insert_left expr1 (len2+zero1) left2 in
  let rec insert_rest j =
    if j >= 0 then begin
      insert_one expr1 (zero1 + j) (expr2 $!! j);
      insert_rest (j-1)
    end in
  insert_rest (len2-2);
  expr1

let repeat f n x =
  let rec loop i acc = if i <= 0 then acc else loop (i-1) (f acc) in
  loop n x

(* fold expr lower to higher *)
(* f 5 (f 2 (f 2 (f 1 (f 1 (f 0 e)))))  for 5.2.2.1.1.0 *)
let expr_fold_up f e expr =
  let len = Bytes.length expr in
  let rec loop idx acc =
    if idx < len then
      loop (idx+1) (repeat (f idx) (expr $!! idx) acc)
    else acc in
  loop 0 e

(* fold expr lower to higher *)
(* f 0 (f 1 (f 1 (f 2 (f 2 (f 5 e)))))  for 5.2.2.1.1.0 *)
let expr_fold_down f e expr =
  let len = Bytes.length expr in
  let rec loop idx acc =
    if idx < 0 then acc
    else loop (idx-1) (repeat (f idx) (expr $!! idx) acc) in
  loop (len-1) e

let expr_sum expr = expr_fold_up (+) 0 expr
let expr_length expr = expr_fold_up (fun _->succ) 0 expr
let expr_height expr = Bytes.length expr
let expr_depth expr =
  fst (expr_fold_down (fun h (d,i) -> (max (i+h) d, i+1)) (0,0) expr)

let pp_bar_chart prf expr =
  fprintf prf "@[";
  ignore (expr_fold_down (fun h b ->
                          if b then fprintf prf "@\n";
                          for i = 1 to h do fprintf prf "#" done;
                          true) false expr);
  fprintf prf "@]"

let pp_howshow expr prf = function
  | Sum -> fprintf prf "S=%3d" (expr_sum expr)
  | Length -> fprintf prf "L=%3d" (expr_length expr)
  | Height -> fprintf prf "H=%3d" (expr_height expr)
  | Depth -> fprintf prf "D=%3d" (expr_depth expr)
  | BarChart -> pp_bar_chart prf expr

let pp_howshow_list expr prf = function
  | [] -> invalid_arg "pp_howshow_list"
  | hs::rest ->
    fprintf prf "@[%a" (pp_howshow expr) hs;
    List.iter (fprintf prf ",@;%a" (pp_howshow expr)) rest;
    fprintf prf "@]"
  
(* fold expr up to down *)

let show_status disp = match disp with
  | Quiet -> (fun i exp -> ())
  | Every cycle ->
     (fun i exp -> if i mod cycle = 0 then eprintf "\r%d... %!" i)
  | Verbose ->
     (fun i exp -> printf "%3d => %a@." i pp_expr exp)
  | Show hss ->
     (fun i exp -> 
      printf "%d => [%a] %a@." i 
             (pp_howshow_list exp) (List.rev hss) pp_expr exp)

module type EStoreType = StoreType with type t = expr

let rho_check stmod expr =
  let module N = (Naive (struct
                           type t = expr
                           let limit = !limit
                           let next e = apply e expr
                           let equal = (=)
                           let display = show_status !display
                         end) ((val stmod : EStoreType))) in
  N.find_cycle expr

let rho_check_floyd expr =
  let module R = (Floyd (struct
                           type t = expr
                           let limit = !limit
                           let next e = apply e expr
                           let equal = (=)
                           let display = show_status !display
                         end)) in
  R.find_cycle expr

let rho_check_brent expr =
  let module R = (Brent (struct
                           type t = expr
                           let limit = !limit
                           let next e = apply e expr
                           let equal = (=)
                           let display = show_status !display
                         end)) in
  R.find_cycle expr

let rho_check_restart_floyd expr fname =
  let module R = (RestartableFloyd (struct
                                     type t = expr
                                     let limit = !limit
                                     let next e = apply e expr
                                     let equal = (=)
                                     let display = show_status !display
                                   end)) in
  R.find_cycle_restart expr fname

let rho_check_restart_brent expr fname =
  let module R = (RestartableBrent (struct
                                     type t = expr
                                     let limit = !limit
                                     let next e = apply e expr
                                     let equal = (=)
                                     let display = show_status !display
                                   end)) in
  R.find_cycle_restart expr fname

let rec add_spec keys spec doc speclist = match keys with
  | [] -> speclist
  | key::keys' -> add_spec keys' spec doc ((key,spec,doc)::speclist)
let rec add_speclist ks_spcl spcl = match ks_spcl with
  | [] -> Arg.align spcl
  | (keys,spec,doc)::rest -> add_speclist rest (add_spec keys spec (" "^doc) spcl)
let make_speclist ks_spcl = add_speclist ks_spcl []

let add_display hs = match !display with
  | Show l -> display := Show (hs::l)
  | _ -> display := Show [hs]

let speclist = make_speclist [
  ["-n"], Arg.Set_int limit,
  "Limit number of self applications (default = "^string_of_int !limit^")";
  ["-u";"-unbound"], Arg.Unit(fun () -> limit := Pervasives.max_int-1),
  "Keep on trying self applications unless the rho-property is found";

  ["-q";"-quiet"], Arg.Unit(fun () -> display := Quiet),
  "Quiet mode";
  ["-e";"-every"], Arg.Int(fun i -> display := Every i),
  "Display only status every n";

  ["-mm";"-map"], Arg.Unit(fun () -> store := Map),
  "Use the Map module to store the history (in naive cycle detection)";

  ["-f";"-floyd"], Arg.Unit(fun () -> mode := Floyd),
  "Use Floyd's cycle-finding algorithm";
  ["-b";"-brent"], Arg.Unit(fun () -> mode := Brent),
  "Use Brent's cycle-finding algorithm";
  ["-r";"-restart"], Arg.String(fun s ->
                                if !mode = Naive then mode := Floyd;
                                restart_file := Some s),
  "Use Floyd's cycle-finding algorithm with restartable mode";
  ["-R";"-restart-auto"], Arg.Unit(fun () ->
                                   if !mode = Naive then mode := Floyd;
                                   restart_file := Some ""),
  "Similar to '-r' but with specifying no filename";
 
  ["-w";"-width"], Arg.Set_int wid,
  "Display each digit in the width";
  ["-S";"-sum"], Arg.Unit(fun () -> add_display Sum),
  "Display its sum";
  ["-L";"-length"], Arg.Unit(fun () -> add_display Length),
  "Display its length";
  ["-H";"-height"], Arg.Unit(fun () -> add_display Height),
  "Display its height";
  ["-D";"-depth"], Arg.Unit(fun () -> add_display Depth),
  "Display its depth";
  ["-B";"-bar-chart"], Arg.Unit(fun () -> add_display BarChart),
  "Display as bar chart like histogram the further step of shrink potential";

]

let usage_msg = "Usage: "^Sys.argv.(0)
let usage () = Arg.usage speclist usage_msg; exit 1
let anon_fun str = 
  try blist := int_of_string str :: !blist with _ -> usage ()

module MapStore = MakeMapStore(Bytes)

module HashedBytes = struct
  include Bytes
  let hash (s:Bytes.t) = Hashtbl.hash s
end

module HashtblStore = MakeHashtblStore(HashedBytes)

let make_stmod = function
  | Map -> (module MapStore : EStoreType)
  | Hashtbl -> (module HashtblStore : EStoreType)      
       
let () =
  Arg.parse speclist anon_fun usage_msg;
  let expr = expr_of_list (List.rev !blist) in
  let show_mode mode_str =
    printf "Cycle detection mode: %s@." mode_str in
  if !display = Quiet then printf "%3d => %a@." 1 pp_expr expr;
  let stime = Unix.gettimeofday() in
  let start, cycle = match !mode with
    | Naive ->
       let stmod = make_stmod !store in
       show_mode "Naive";
       rho_check stmod expr
    | Floyd ->
       begin match !restart_file with
             | None ->
                show_mode "Floyd";
                rho_check_floyd expr
             | Some fname ->
                show_mode "Restartable (Floyd)";
                rho_check_restart_floyd expr fname end
    | Brent ->
       begin match !restart_file with
             | None ->
                show_mode "Brent";
                rho_check_brent expr
             | Some fname ->
                show_mode "Restartable (Brent)";
                rho_check_restart_brent expr fname end in
  printf "Found! (%d = %d [%d])@." (start+cycle) start cycle;
  if !restart_file = None then
   printf "Elapsed time: %.3f sec.@." (Unix.gettimeofday()-.stime)
