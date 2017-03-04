open Format

let check_max = ref 65535
type howshow =
  | BaseTwo | BaseTwoS | Sum | SumS | Length
  | ShrinkL | ShrinkM | ShrinkF | BarChart | NumKind
type mode = Naive | Floyd | FloydExt
type equality = Exact | ExactArray of int | ExactHash
                | Digest of int | HashPair | HashPairArray of int
                | PartStore of int * int * int * int
                | HashRecomp of int | UseFS of string
type display = Quiet | Verbose | Show of howshow list | Every of int
let mode = ref FloydExt
let gc_mask = ref (-1)
let equality = ref Exact
let display = ref Verbose
let num = ref 0
let wid = ref 1

let pp_expr fmtr expr =
  let len = Bytes.length expr in
  if len > 0 then begin
    fprintf fmtr "%*d" !wid (Char.code expr.[0]);
    for i = 1 to len - 1 do
(*       if i = updated + 1 then *)
(*         fprintf fmtr "*%*d" !wid (Char.code expr.[i]) *)
(*       else *)
        fprintf fmtr ".%*d" !wid (Char.code expr.[i])
    done
  end

(* a,b,c,d,0,0,0 => a-1,b-1,c-1,d-1,4 *)
(* a,b,c,d => a-1,b-1,c-1,d-1,1 *)

external succ_char : char -> char = "%succint"
external pred_char : char -> char = "%predint"
external (>$) : char -> int -> bool = "%greaterthan"

let rec pred_rest idx src dst =
  if 0 <= idx then begin
    Bytes.set dst idx (pred_char src.[idx]);
    pred_rest (idx-1) src dst
  end else dst

let rec move_larger zc s_idx src dst =
  if 0 <= s_idx then
    let c = pred_char src.[s_idx] in
    if c < zc then begin
      Bytes.set dst (s_idx+1) c;
      move_larger (succ_char zc) (s_idx-1) src dst
    end else begin
      if zc >$ 255 then invalid_arg("move_larger: exceeds 8 bit integer.");
      Bytes.set dst (s_idx+1) zc;
      Bytes.set dst (s_idx) c;
      (* s_idx+1, *)
      pred_rest (s_idx-1) src dst
    end
  else begin
    if zc >$ 255 then invalid_arg("move_larger: exceeds 8 bit integer.");
    Bytes.set dst 0 zc;
    (* 0, *)
    dst
  end

let rec app_nBB z idx src =
  if idx < 0 then (* 0, *) Bytes.make 1 z
  else if src.[idx] = '\000' then
    app_nBB (succ_char z) (idx-1) src
  else
    let c = pred_char src.[idx] in
    let dst = Bytes.create (idx+2) in
    if c < z then begin
      Bytes.set dst (idx+1) c;
      move_larger (succ_char z) (idx-1) src dst;
    end else begin
      Bytes.set dst (idx+1) z;
      Bytes.set dst idx c;
      (* idx+1, *)
      pred_rest (idx-1) src dst
    end

let app_nBB n exp = app_nBB n (Bytes.length exp-1) exp

let expr_length = Bytes.length

let rec expr_value_fold f e idx expr =
  if 0 <= idx then
    expr_value_fold f (f (Char.code expr.[idx]) e) (idx-1) expr
  else e
let expr_value_fold f e expr = expr_value_fold f e (Bytes.length expr-1) expr

let expr_value_base2_0 expr = expr_value_fold (fun k x -> x*2+k) 0 expr
let expr_value_base2_1 expr = expr_value_fold (fun k x -> x*2+k+1) 0 expr
let expr_value_sum_0 expr = expr_value_fold (fun k x -> x+k) 0 expr
let expr_value_sum_1 expr = expr_value_fold (fun k x -> x+k+1) 0 expr
  
(* let expr_value_shrink_least expr = *)
(*   fst (expr_value_fold *)
(*          (fun k (m, right) -> min m (right-k,k+1), right+1) ((max_int,0),0) expr) *)

let expr_value_shrink_further expr =
  fst (expr_value_fold
         (fun k ((md,mk), right) ->
           let d = right-k in
           let mdk = 
             if d > 0 then
               let k, d = max (k+1,d) (mk,md) in d, k
             else max (d,k+1) (md,mk) in
           mdk, right+1) ((min_int,0),0) expr)

let expr_value_shrink_least expr =
  fst (expr_value_fold
         (fun k (m, right) -> min m (right-k,k+1), right+1) ((max_int,0),0) expr)

let expr_value_shrink_most expr =
  fst (expr_value_fold
         (fun k (m, right) -> max m (right-k,k+1), right+1) ((min_int,0),0) expr)

let expr_value expr = expr_value_base2_0 expr + expr_length expr

let expr_kind expr =
  let rec loop acc last_c i =
    if i < 0 then acc
    else
      let c = expr.[i] in
      if c = last_c then
        loop acc last_c (i-1)
      else
        loop (acc+1) c (i-1) in
  let len = Bytes.length expr in
  loop 1 expr.[len-1] (len-2)

let pp_bar_chart fmtr expr =
  fprintf fmtr "@[";
  if Bytes.length expr > 0 then
    for j = 1 to Char.code expr.[0] do
      fprintf fmtr "#"
    done;
  for i = 1 to Bytes.length expr-1 do
    fprintf fmtr "@\n";
    for j = 1 to Char.code expr.[i] do
      fprintf fmtr "#"
    done
  done;
  fprintf fmtr "@]"

let pp_howshow expr fmtr = function
  | BaseTwo -> fprintf fmtr "%8d" (expr_value_base2_0 expr)
  | BaseTwoS -> fprintf fmtr "%8d" (expr_value_base2_1 expr)
  | Sum -> fprintf fmtr "%4d" (expr_value_sum_0 expr)
  | SumS -> fprintf fmtr "%4d" (expr_value_sum_1 expr)
  | Length -> fprintf fmtr "%2d" (expr_length expr)
  | NumKind -> fprintf fmtr "%2d" (expr_kind expr)
  | ShrinkL -> let shrink, step = expr_value_shrink_least expr in
               fprintf fmtr "%2d:%2d" step shrink
  | ShrinkM -> let shrink, step = expr_value_shrink_most expr in
               fprintf fmtr "%2d:%2d" step shrink
  | ShrinkF -> let shrink, step = expr_value_shrink_most expr in
               fprintf fmtr "%2d:%2d" step shrink
  | BarChart -> pp_bar_chart fmtr expr

let pp_howshow_list expr fmtr = function
  | [] -> invalid_arg "pp_howshow_list"
  | hs::rest ->
    fprintf fmtr "@[%a" (pp_howshow expr) hs;
    List.iter (fprintf fmtr ",@;%a" (pp_howshow expr)) rest;
    fprintf fmtr "@]"

module type StoreType = sig
  type t
  val find	: string -> t -> int		(* corresponding number of expressions *)
  val add	: string -> int -> t -> t
  val singleton	: string -> int -> t
end

let show_status i exp = match !display with
  | Quiet -> ()
  | Every cycle -> if i mod cycle = 0 then eprintf "\r%d... %!" i
  | Verbose -> printf "%3d => %a@." i pp_expr exp
  | Show hss ->
    printf "%3d => [%a] %a@." i
      (pp_howshow_list exp) (List.rev hss) pp_expr exp

let nBB_rho_check stmod n =
  let module Store = (val stmod : StoreType) in
  let rec loop last i hist =
    if i > !check_max then begin
      if !check_max > 1 then printf "%d terms are all different.@." !check_max
    end else
      let (* updated, *) next = app_nBB n last in
      try
        let prev = Store.find next hist in
        printf "Found! (%d = %d [%d])@." i prev (i-prev)
      with Not_found ->
        show_status i next;
        if i land !gc_mask = 0 then Gc.minor ();
        loop next (i+1) (Store.add next i hist) in
  let init_e = Bytes.make 1 n in
  printf "%3d => %a@." 1 pp_expr init_e;
  loop init_e 2 (Store.singleton init_e 1)

let nBB_rho_check_floyd n =
  let rec find_loop last1 last2 i =
    if i > !check_max then begin
      if !check_max > 1 then 
        printf "%d terms are all different.@." (2 * !check_max);
      exit 0
    end else
      let next1 = app_nBB n last1 in
      let next2 = app_nBB n (app_nBB n last2) in
      if next1 = next2 then (i, next1)
      else begin
        show_status i next1;
        find_loop next1 next2 (i+1)
      end in
  let init1 = Bytes.make 1 n in
  printf "%3d => %a@." 1 pp_expr init1;
  let init2 = app_nBB n init1 in
  let i, exp = find_loop init1 init2 2 in
  printf "Loop detected! (%d = %d [%d])@." (2*i) i i;
  if !display = Verbose then display := Every 1;
  let rec find_loop_entry i last1 last2 =
    let next1 = app_nBB n last1 in
    let next2 = app_nBB n last2 in
    if next1 = next2 then i, next1
    else begin
      show_status i next1;
      find_loop_entry (i+1) next1 next2
    end in
  let start, exp = find_loop_entry 2 init1 (app_nBB n exp) in
  if !display <> Quiet then printf "%3d => %a@." start pp_expr exp;
  printf "Loop entry found at %d!@." start;
  let rec find_cycle cyc last =
    let next = app_nBB n last in
    if next = exp then cyc
    else begin
      show_status (start+cyc) next;
      find_cycle (cyc+1) next
    end in
  let cyc = find_cycle 1 exp in
  printf "Found! (%d = %d [%d])@." (start+cyc) start cyc

let nBB_rho_check_floyd_ext n =
  let rec find_loop last1 last2 i =
    if i > !check_max then begin
      if !check_max > 1 then 
        printf "%d terms are all different.@." (2 * !check_max);
      exit 0
    end else
      let next1 = app_nBB n last1 in
      let next2 = app_nBB n (app_nBB n last2) in
      if next1 = next2 then (i, next1)
      else begin
        show_status i next1;
        find_loop next1 next2 (i+1)
      end in
  let init1 = String.make 1 n in
  printf "%3d => %a@." 1 pp_expr init1;
  let init2 = app_nBB n init1 in
  let point, exp = find_loop init1 init2 2 in
  printf "Loop detected! (%d = %d [%d])@." (2*point) point point;
  if !display = Verbose then display := Every 1;
  let rec find_loop_entry i cnt last1 last2 =
    let next1 = app_nBB n last1 in
    let next2 = app_nBB n last2 in
    if next1 = next2 then i, cnt
    else
      let cnt = if next2 = exp then cnt + 1 else cnt in
      show_status i next1;
      find_loop_entry (i+1) cnt next1 next2 in
  let entry, cnt = find_loop_entry 2 1 init1 (app_nBB n exp) in
  let cyc = point / cnt in
  if !display <> Quiet then printf "%3d => %a@." entry pp_expr exp;
  printf "Found! (%d = %d [%d])@." (entry+cyc) entry cyc

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
  ["-n"], Arg.Set_int check_max,
  "Limit number of self applications (default = "^string_of_int !check_max^")";
  ["-m";"-max"], Arg.Unit(fun () -> check_max := Pervasives.max_int),
  "Keep on trying self applications unless the rho-property is found";
  ["-q";"-quiet"], Arg.Unit(fun () -> display := Quiet),
  "Quiet mode";
  ["-e";"-every"], Arg.Int(fun i -> display := Every i),
  "Display only status every n";
  ["-ps";"-part-store"],
  Arg.String(fun s ->
    Scanf.sscanf s"%d/%d/%d/%d"(fun p q m1 m2 -> equality := PartStore(p,q,m1,m2))),
  "(e.g., p/q/m1/m2) Store history only when n % q = p and m1 < n < m2";
  ["-d";"-digest"], Arg.Int(fun i -> equality := Digest i),
  "Use first n digits of MD5 digest to check equality";
  ["-ea";"-exact-array"], Arg.Int(fun i -> equality := ExactArray i),
  "Use exact values to check equality and store them in an array with length 2**n";
  ["-eh";"-hash-pair"], Arg.Unit(fun () -> equality := ExactHash),
  "Use exact values to check equality and store them in a hash table";
  ["-hp";"-hash-pair"], Arg.Unit(fun () -> equality := HashPair),
  "Use hash values of itself and its digest to check equality";
  ["-ha";"-hash-pair-array"], Arg.Int(fun i -> equality := HashPairArray i),
  "Use hash values of itself and its digest to check equality using an array with length 2**n ";
  ["-hr";"-hash-recomp"], Arg.Int(fun n -> equality := HashRecomp n),
  "Use its hash value for equality and recomputing for further checking from a storage containing only every n value";
  ["-fc";"-floyd-cycle"], Arg.Unit(fun () -> mode := Floyd),
  "Use Floyd's cycle-finding algorithm";
  ["-fx";"-floyd-ext"], Arg.Unit(fun () -> mode := FloydExt),
  "Use Floyd's cycle-finding algorithm with optimization";
  ["-fs";"-file-system"], Arg.String(fun str -> equality := UseFS str),
  "Use file system for store in the directory";
  ["-b0";"-basetwo0"], Arg.Unit(fun () -> add_display BaseTwo),
  "Display its value as base 2";
  ["-b1";"-basetwo1"], Arg.Unit(fun () -> add_display BaseTwoS),
  "Display its value as base 2 after each digit incrementation";
  ["-s0";"-sum0"], Arg.Unit(fun () -> add_display Sum),
  "Display its sum";
  ["-s1";"-sum1"], Arg.Unit(fun () -> add_display SumS),
  "Display its sum after each digit incrementation";
  ["-l";"-length"], Arg.Unit(fun () -> add_display Length),
  "Display its length";
  ["-k";"-kind"], Arg.Unit(fun () -> add_display NumKind),
  "Display the number of its kinds";
  ["-sl";"-shrink-least"], Arg.Unit(fun () -> add_display ShrinkL),
  "Display the minimum nubmer of shrink potential";
  ["-sm";"-shrink-most"], Arg.Unit(fun () -> add_display ShrinkM),
  "Display the maximum nubmer of shrink potential";
  ["-sf";"-shrink-further"], Arg.Unit(fun () -> add_display ShrinkF),
  "Display the further step of shrink potential";
  ["-b";"-bar-chart"], Arg.Unit(fun () -> add_display BarChart),
  "Display as bar chart like histogram the further step of shrink potential";
  ["-w";"-width"], Arg.Set_int wid,
  "Display each digit in the width";
  ["-gc"], Arg.Int(fun i -> gc_mask := 1 lsl i - 1),
  "Run GC every (2**n) time";
]

let usage_msg = "Usage: "^Sys.argv.(0)
let usage () = Arg.usage speclist usage_msg; exit 1
let anon_fun str = try num := int_of_string str with _ -> usage ()

let compare_int (x:int) (y:int) = compare x y
module Int = struct type t = int let compare = compare_int end
module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)

let make_stmod = function
  | Exact ->
    (module struct
      type t = int StringMap.t
      let find = StringMap.find
      let add = StringMap.add
      let singleton = StringMap.singleton
    end : StoreType)
  | ExactHash ->
    (module struct
      type t = (string, int) Hashtbl.t
      let find k t = Hashtbl.find t k
      let add k v t = Hashtbl.add t k v; t
      let singleton k v = Hashtbl.create (1 lsl 20 + 1)
    end : StoreType)      
  | ExactArray q ->
    (module struct
      type t = (string * int) list array
      let mask = 1 lsl q - 1
      let idx k = Hashtbl.hash k land mask
      let find k t =
        let i = idx k in
        List.assoc k t.(i) 
      let add k v t =
        let i = idx k in
        t.(i) <- (k, v) :: t.(i);
        t
      let singleton k v =
        let a = Array.make (1 lsl q) [] in
        eprintf "Array created.@.";
        a
    end : StoreType)
  | PartStore(p,q,m1,m2) ->
    (module struct
      type t = (string, int) Hashtbl.t
      let find k t = Hashtbl.find t k
      let add k v t =
        if v < m2 && m1 < v && v mod q = p then Hashtbl.add t k v;
        t
      let singleton k v = Hashtbl.create (1 lsl 20 + 1)
    end : StoreType)
  | Digest n ->
    let len = min (max n 1) 16 in
    (module struct
      type t = (string,int) Hashtbl.t
      let f k = String.sub (Digest.string k) 0 len
      let find k t = Hashtbl.find t (f k)
      let add k v t = Hashtbl.add t (f k) v; t
      let singleton k v =
        let h = Hashtbl.create (1 lsl 20 + 1) in
        eprintf "Hashtbl created.@."; h
    end : StoreType)
  | HashPair -> 
    (module struct
      type t = (int,int) Hashtbl.t
      let f k = Hashtbl.hash k lsl 32 lor Hashtbl.hash (Digest.string k)
      let find k t = Hashtbl.find t (f k)
      let add k v t = Hashtbl.add t (f k) v; t
      let singleton k v =
        let h = Hashtbl.create (1 lsl 20 + 1) in
        eprintf "Hashtbl created.@."; h
    end : StoreType)
  | HashPairArray q ->
    (module struct
      type t = (int * int) list array
      let mask = 1 lsl q - 1
      let idx k = Hashtbl.hash k land mask
      let hsd k = Hashtbl.hash (Digest.string k)
      let find k t =
        let i = idx k in
        List.assoc (hsd k) t.(i) 
      let add k v t =
        let i = idx k in
        t.(i) <- (hsd k, v) :: t.(i);
        t
      let singleton k v =
        let a = Array.make (1 lsl q) [] in
        eprintf "Array created.@.";
        a
    end : StoreType)
  | HashRecomp q ->
    (* let rec app_nBB_ntimes tmp m =
      if m < 1 then tmp
      else app_nBB_ntimes (app_nBB (Char.chr !num) tmp) (m-1) in *)
    (module struct
      type t = int IntMap.t * string IntMap.t
      let find k (it,st) =
        let h = Hashtbl.hash k in
        let x = IntMap.find h it in
        assert (ignore h; false);
        x
      let add k v (it,st) =
        IntMap.add (Hashtbl.hash k) v it,
        if v mod q = 1 then IntMap.add v k st else st
      let singleton k v = assert (v = 1);
        IntMap.singleton (Hashtbl.hash k) v,
        IntMap.singleton v k
    end : StoreType)
  | UseFS dir ->
    let dir_name = Filename.concat "/tmp" dir in
    let () = Unix.mkdir dir_name 0o700 in
    eprintf "Directory %s created.@." dir_name;
    (module struct
      type t = unit
      let get_fname k = 
        let len = String.length k in
        let hex = Bytes.create (len*2) in
        for i = 0 to len-1 do
          Bytes.blit (sprintf "%02x" (Char.code k.[i])) 0 hex (i*2) 2
        done;
        Filename.concat dir_name hex
        (*           Filename.concat dir_name (Digest.to_hex (Digest.string k)) *)
      let find k () =
        try input_value (open_in (get_fname k))
        with _ -> raise Not_found
      let singleton k v = 
        let oc = open_out (get_fname k) in
        output_value oc v;
        close_out oc
      let add k v () = singleton k v
      end : StoreType)      

let () =
  Arg.parse speclist anon_fun usage_msg;
  match !mode with
    | Naive -> 
      let stmod = make_stmod !equality in
      nBB_rho_check stmod (Char.chr !num)
    | Floyd ->
      nBB_rho_check_floyd (Char.chr !num)
    | FloydExt ->
      nBB_rho_check_floyd_ext (Char.chr !num)
