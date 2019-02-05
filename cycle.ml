(* Finding cycles *)
open Format
open Store

module type ExprType = sig
  type t
  val limit : int
  val next : t -> t        (* Its input must be preserved. *)
  val next_impure : t -> t (* Its input may be broken.     *)
  val copy : t -> t        (* Deep copy *)
  val equal : t -> t -> bool
  val display : int -> t -> unit
end

(* (\* stores with numbers *\) *)
(* module type StoreType = sig *)
(*   type t *)
(*   type store *)
(*   (\* Return the correponding number if a given expression is found *\) *)
(*   val find      : t -> store -> int *)
(*   (\* Add a given expression to the store *\)                                     *)
(*   val add	: t -> int -> store -> store *)
(*   val singleton	: t -> int -> store *)
(* end *)

type restart = RBrent | RFloyd | RGosper

module Naive (E:ExprType) (S:StoreType with type t = E.t) = struct
  type t = E.t
  let find_cycle init =
    let rec loop last i hist =
      if i > E.limit then begin
        if E.limit > 1 then printf "%d terms are all different.@." E.limit;
        exit 0
      end else
        let next = E.next_impure last in
        try let prev = S.find next hist in
            (prev, i-prev, next)
        with Not_found ->
          E.display i next;
          loop next (i+1) (S.add (E.copy next) i hist) in
    E.display 1 init;
    loop init 2 (S.singleton (E.copy init) 1)
end

module Floyd (E:ExprType) = struct
  type t = E.t

  (* Find loop by Floyd's tortoise-and-hare cycle-finding algorithm *)
  (* to return i and e such that e = A(i) = A(2i)                   *)
  let rec find_loop last1 last2 i =
    if i > E.limit then begin
      if E.limit > 1 then
        eprintf "%d terms are all different.@." (2 * E.limit);
      exit 0
    end else
      let next1 = E.next_impure last1 in
      let next2 = E.next_impure (E.next_impure last2) in
      E.display i next1;
      (* E.display (2*i) next2; *)
      if E.equal next1 next2 then (i, next1)
      else find_loop next1 next2 (succ i)

  (* Find the entry of loop by starting with i such that e=A(i)=A(2i) *)
  (* and searching the smallest k with x = A(k) = A(i+k)              *)
  (* to return k and x                                                *)
  let rec find_loop_entry last1 last2 i e cyc_op =
    let next1 = E.next_impure last1 in
    let next2 = E.next_impure last2 in
    if E.equal next1 next2 then (i, cyc_op, next1)
    else
      let cyc_op = match cyc_op with
        | None when E.equal e next2 -> Some i
        | _ -> cyc_op in
      E.display (succ i) next2;
      find_loop_entry next1 next2 (succ i) e cyc_op

  let find_cycle init =
    E.display 1 init;
    (* Find (the smallest) i and e s.t. e = A(i) = A(2i) *)
    let i, e = find_loop (E.copy init) (E.next init) 2 in
    printf "Loop detected! (%d = %d [%d])@." (2*i) i i;
    (* Find (the smallest) k, c and x s.t. x = A(k) = A(i+k) 
       where c is A(c) = A(i) and i < c < 2i *)
    let k, co, x =
      find_loop_entry (E.copy init) (E.next e) (succ i) e None in
    let loop_size = match co with None -> i | Some c -> c-i+1 in
    printf "Loop entry found at %d!@." (k-i+1);
    (* E.display (k-i+1) x; *)
    k-i+1, loop_size, x
end

(* Restartable Floyd's cycle detection *) 
(* limit is unabled. *)
module RestartableFloyd (E:ExprType) = struct
  type t = E.t

  type funcall =
    | Init
    | FindLoop of { last1: t; last2: t; i: int }
    (* | FindLoopEntry of { last1: t; last2: t; i: int; e: t; cnt: int } *)
    | FindLoopEntry of { last1: t; last2: t; i: int; e: t; cyc_op: int option }
  type state = { mutable init: t option;
                 mutable i_e: (int * t) option; (* (i, A(i)) s.t. A(i)=A(2i) *)
                 mutable funcall: funcall;
                 mutable elapsed: float;
               }

  let state = { init = None; i_e = None; funcall = Init; elapsed = 0. }
  let stime = ref (Unix.gettimeofday()) (* start time *)
  let rfile = ref ""      (* the file name for restarting *)

  let save_current_state state =
    let elapsed = state.elapsed +. Unix.gettimeofday()-. !stime in
    state.elapsed <- elapsed;
    let oc = open_out !rfile in
    output_value oc (RFloyd, state);
    close_out oc

  exception Interrupted of state

  (* Find loop by Floyd's tortoise-and-hare cycle-finding algorithm *)
  (* to return i and e such that e = A(i) = A(2i)                   *)
  let rec find_loop last1 last2 i =
    state.funcall <- FindLoop{ last1; last2; i };
    let next1 = E.next last1 in
    let next2 = E.next (E.next last2) in
    E.display i next1;
    (* E.display (2*i) next2; *)
    if i land 0xffffff = 0 then save_current_state state;
    if E.equal next1 next2 then (i, next1)
    else find_loop next1 next2 (succ i)

  (* Find the entry of loop by starting with i such that e=A(i)=A(2i) *)
  (* and searching the smallest k with x = A(k) = A(i+k)              *)
  (* to return k and x                                                *)
  let rec find_loop_entry last1 last2 i e cyc_op =
    state.funcall <- FindLoopEntry{ last1; last2; i; e; cyc_op };
    let next1 = E.next last1 in
    let next2 = E.next last2 in
    if E.equal next1 next2 then (i, cyc_op, next1)
    else
      let cyc_op = match cyc_op with
        | None when E.equal e next2 -> Some i
        | _ -> cyc_op in
      E.display i next1;
      if i land 0xffffff = 0 then save_current_state state;
      find_loop_entry next1 next2 (succ i) e cyc_op

  let find_cycle_with_state init =
    E.display 1 init;
    (* Find (the smallest) i and e s.t. e = A(i) = A(2i) *)
    let i, e = match state.funcall with
      | Init -> find_loop init (E.next init) 2 
      | FindLoop { last1; last2; i } -> find_loop last1 last2 i
      | FindLoopEntry _ -> match state.i_e with
                           | None -> failwith "impossible state."
                           | Some i_e -> i_e in
    state.i_e <- Some(i,e);
    printf "Loop detected! (%d = %d [%d])@." (2*i) i i;
    (* Find (the smallest) k, c and x s.t. x = A(k) = A(i+k) 
       where c is A(c) = A(i) and i < c < 2i *)
    let k, co, x = match state.funcall with
      | Init | FindLoop _ ->
         find_loop_entry init (E.next e) (succ i) e None
      | FindLoopEntry { last1; last2; i; e; cyc_op } ->
         find_loop_entry last1 last2 i e cyc_op in
    let loop_size = match co with None -> i | Some c -> c-i+1 in
    printf "Loop entry found at %d!@." (k-i+1);
    k-i+1, loop_size, x

  let find_cycle_restart expr fname =
    let auto, fname =
      if fname = "" then true, sprintf ".bfloyd%d" (Hashtbl.hash expr)
      else false, fname in
    rfile := fname;
    stime := Unix.gettimeofday();
    Sys.(set_signal sigint
           (Signal_handle(fun _signum -> raise (Interrupted state))));
    (* Load a state from a given file *)
    let restart, {init; i_e; funcall; elapsed} =
      try input_value (open_in fname)
      with _ -> RFloyd, { init = Some expr; i_e = None; funcall = Init;
                          elapsed = 0. } in
    if restart <> RFloyd then
      begin eprintf"Inconsistent cycle detection mode.@."; exit 1 end;
    state.init <- init; state.i_e <- i_e; state.funcall <- funcall;
    state.elapsed <- elapsed;
    if state.init <> Some expr then
      begin eprintf"inconsistent initial expression."; exit 1 end;
    let init = match state.init with None -> expr | Some e -> e in
    try
      let res = find_cycle_with_state init in
      let elapsed = state.elapsed +. Unix.gettimeofday()-. !stime in
      begin try Unix.unlink fname with _ -> () end;
      eprintf "Elapsed time: %.3f sec@." elapsed;
      res
    with Interrupted state ->
      save_current_state state;
         let funcall = match state.funcall with
           | Init -> "init"
           | FindLoop { i } -> sprintf "find_loop _ _ %d" i
           | FindLoopEntry { i } -> sprintf "find_loop_entry _ _ %d _ _" i in
         let opt_r = if auto then "-R" else sprintf "-r %s" !rfile in
         eprintf ("Interrupted at '%s' (%.2f sec).@."
                  ^^"You can run again with '%s'.@.")
                 funcall state.elapsed opt_r;
         exit 0

end

(* Sample

  module E = struct 
    type t = int
    let limit = 100
    let next i = if i > 26 then 23 else i+1
    let equal = (=)
    let display i e = printf "%d => %d; " i e
  end

  module R = Rho(E)

  let start, cycle = R.find_cycle 6

*)

(* Brent's algorithm *)
module SimpleBrent (E:ExprType) = struct
  type t = E.t

  (* Find loop by Brent's cycle-finding algorithm                    *)
  (* to return k and pow such that A(pow=2**n) = A(pow+k) (1<=k<pow) *)
  let rec find_loop last1 last2 i pow =
    if pow > E.limit then begin
      if E.limit > 1 then
        eprintf "%d terms are all different.@." (pow+i);
      exit 0
    end else
      if E.equal last1 last2 then (i,pow)
      else
        if i = pow then
          let next2 = E.next last2 in
          E.display (pow+i+1) next2;
          find_loop last2 next2 1 (pow lsl 1)
        else
          let next2 = E.next_impure last2 in
          E.display (pow+i+1) next2;
          find_loop last1 next2 (succ i) pow
        (* let next2 = E.next last2 in
         * E.display (pow+i+1) next2;
         * if i = pow then
         *   find_loop last2 next2 1 (pow lsl 1)
         * else
         *   find_loop last1 next2 (succ i) pow *)
                    
  let rec find_kth x1 k =
    if k <= 1 then x1 else find_kth (E.next_impure x1) (k-1)

  (* Find the entry of loop by starting with i=1 s.t. e=A(i)=A(i+c) *)
  (* to return i                                                    *)
  let rec find_loop_entry last1 last2 i =
    if E.equal last1 last2 then (i, last1)
    else
      let next1 = E.next_impure last1 in
      let next2 = E.next_impure last2 in
      E.display (succ i) next1;
      find_loop_entry next1 next2 (succ i)

  let find_cycle init =
    E.display 1 init;
    let next = E.next init in
    E.display 2 next;
    (* Find (the smallest) c and e s.t. e = A(i) = A(i+c) with i=2**j-1
       with smallest j  *)
    let loop_size, pow = find_loop (E.copy init) next 1 1 in
    printf "Loop detected! (%d = %d [%d])@." (pow+loop_size) pow loop_size;
    (* Compute A(c) *)
    let e = find_kth (E.copy init) loop_size in
    E.display 1 init;
    (* Find (the smallest) k and x s.t. x = A(k) = A(k+c) *)
    let k, x = find_loop_entry init (E.next_impure e) 1 in
    printf "Loop entry found at %d!@." k;
    k, loop_size, x
end

(* Restartable Brent's algorithm *)
module RestartableBrent (E:ExprType) = struct
  type t = E.t

  type funcall =
    | Init
    | FindLoop of { last1: t; last2: t; i: int; pow: int }
    | FindKth of { x1: t; k: int }
    | FindLoopEntry of { last1: t; last2: t; i: int }

  type state = { mutable init: t option;
                 mutable find_loop: (int * int) option;
                 mutable find_kth: t option;
                 mutable funcall: funcall;
                 mutable elapsed: float; }

  exception Interrupted of state

  let state = { init = None;
                find_loop = None;
                find_kth = None;
                funcall = Init;
                elapsed = 0.  }
  let stime = ref (Unix.gettimeofday()) (* start time *)
  let rfile = ref ""      (* the file name for restarting *)

  let save_current_state state =
    let elapsed = state.elapsed +. Unix.gettimeofday() -. !stime in
    state.elapsed <- elapsed;
    let oc = open_out !rfile in
    output_value oc (RBrent, state);
    close_out oc

  (* Find loop by Brent's cycle-finding algorithm                    *)
  (* to return k and pow such that A(pow=2**n) = A(pow+k) (1<=k<pow) *)
  let rec find_loop last1 last2 i pow =
    state.funcall <- FindLoop { last1; last2; i; pow };
    if pow > E.limit then begin
      if E.limit > 1 then
        eprintf "%d terms are all different.@." (pow+i);
      exit 0
    end else
      if E.equal last1 last2 then (i,pow)
      else 
        let next2 = E.next last2 in
        E.display (pow+i+1) next2;
        if i land 0xffffff = 0 then save_current_state state;
        if i = pow then
          find_loop last2 next2 1 (pow lsl 1)
        else
          find_loop last1 next2 (succ i) pow
                    
  let rec find_kth x1 k =
    state.funcall <- FindKth { x1; k };
    if k <= 1 then x1 else find_kth (E.next x1) (k-1)

  (* Find the entry of loop by starting with i=1 s.t. e=A(i)=A(i+c) *)
  (* to return i                                                    *)
  let rec find_loop_entry last1 last2 i =
    state.funcall <- FindLoopEntry { last1; last2; i };
    if E.equal last1 last2 then (i, last1)
    else
      let next1 = E.next last1 in
      let next2 = E.next last2 in
      E.display i next1;
      if i land 0xffffff = 0 then save_current_state state;
      find_loop_entry next1 next2 (succ i)

  let find_cycle_with_funcall init =
    E.display 1 init;
    begin match state.init with
          | Some e -> 
              if e <> init then
                begin eprintf"inconsistent initial expression."; exit 1 end
          | None -> state.init <- Some init end;
    let next = E.next init in
    E.display 2 next;
    (* Find (the smallest) c and e s.t. e = A(i) = A(i+c) with i=2**j-1 
       with smallest j *)
    let loop_size, pow = match state.funcall with
      | Init -> find_loop init next 1 1
      | FindLoop{last1;last2;i;pow} -> find_loop last1 last2 i pow
      | _ -> match state.find_loop with
             | None -> invalid_arg "wrong state (find_loop)"
             | Some ls_p -> ls_p in
    state.find_loop <- Some(loop_size, pow);
    printf "Loop detected! (%d = %d [%d])@." (pow+loop_size) pow loop_size;
    (* Compute A(c) *)
    let e = match state.funcall with
      | Init | FindLoop _ -> find_kth init loop_size
      | FindKth{x1;k} -> find_kth x1 k
      | _ -> match state.find_kth with
             | None -> invalid_arg "wrong state (find_kth)"
             | Some e -> e in
    state.find_kth <- Some e;
    (* Find (the smallest) k and x s.t. x = A(k) = A(k+c) *)
    let k, x = match state.funcall with
      | Init | FindLoop _ | FindKth _ -> find_loop_entry init (E.next e) 1
      | FindLoopEntry{last1;last2;i} -> find_loop_entry last1 last2 i in
    printf "Loop entry found at %d!@." k;
    k, loop_size, x

  let find_cycle_restart init fname =
    (* generate a filename if specifying no fileneme *)
    let auto, fname =
      if fname = "" then true, sprintf ".bbrent%d" (Hashtbl.hash init)
      else false, fname in
    rfile := fname;
    stime := Unix.gettimeofday();
    Sys.(set_signal sigint
           (Signal_handle(fun _signum -> raise (Interrupted state))));
    (* Load a state from a given file *)
    let restart, s =
      try input_value (open_in !rfile) with _ -> RBrent, state in
    state.init <- s.init; state.find_loop <- s.find_loop;
    state.find_kth <- s.find_kth; state.funcall <- s.funcall;
    state.elapsed <- s.elapsed;
    if restart <> RBrent then
      begin eprintf"Inconsistent cycle detection mode.@."; exit 1 end;
    try 
      let res = find_cycle_with_funcall init in
      let elapsed = state.elapsed+.Unix.gettimeofday()-. !stime in
      begin try Unix.unlink !rfile with _ -> () end;
      eprintf "Elapsed time: %.3f sec@." elapsed;
      res
    with Interrupted state ->
      save_current_state state;
      let funcall = match state.funcall with
        | Init -> "init"
        | FindLoop { i; pow } -> sprintf "find_loop _ _ %d %d" i pow
        | FindKth { k } -> sprintf "find_kth _ %d" k
        | FindLoopEntry { i } -> sprintf "find_loop_entry _ _ %d" i in
      let opt_r = if auto then "-R" else sprintf "-r %s" !rfile in
      eprintf ("Interrupted at '%s' (%.2f sec).@."
               ^^"You can run again with '%s'.@.")
              funcall state.elapsed opt_r;
      exit 0
end

(* Improved Brent's algorithm *)
(* Storing the expression at the previous power
   for finding the entry point of the cycler earlier *)
module Brent (E:ExprType) = struct

  (* Find loop by Brent's cycle-finding algorithm                    *)
  (* to return k and pow such that A(pow=2**n) = A(pow+k) (1<=k<pow),*)
  (* and A(pow/2)                                                    *)
  let rec find_loop last1 last2 i pow ppow_exp =
    if pow > E.limit then begin
      if E.limit > 1 then
        eprintf "%d terms are all different.@." (pow+i);
      exit 0
    end else
      if E.equal last1 last2 then (i,pow,ppow_exp)
      else 
        if i = pow then
          let next2 = E.next last2 in
          E.display (pow+i+1) next2;
          find_loop last2 next2 1 (pow lsl 1) last1
        else
          let next2 = E.next_impure last2 in
          E.display (pow+i+1) next2;
          find_loop last1 next2 (succ i) pow ppow_exp
                    
  let rec find_kth x1 k =
    if k <= 1 then x1 else find_kth (E.next_impure x1) (k-1)

  (* Find the entry of loop by starting with i=1 s.t. e=A(i)=A(i+c) *)
  (* to return i                                                    *)
  let rec find_loop_entry last1 last2 i =
    if E.equal last1 last2 then (i, last1)
    else
      let next1 = E.next_impure last1 in
      let next2 = E.next_impure last2 in
      E.display (succ i) next1;
      find_loop_entry next1 next2 (succ i)

  let find_cycle init =
    E.display 1 init;
    let next = E.next init in
    E.display 2 next;
    (* Find (the smallest) c and 2**i e s.t. e = A(2**i) = A(2**i+c)
       with smallest i *)
    let loop_size, pow, ppow_exp =
      find_loop (E.copy init) next 1 1 (E.copy init) in
    printf "Loop detected! (%d = %d [%d])@." (pow+loop_size) pow loop_size;
    (* Compute A(2**j+c) with maximum j s.t. 2**j+c < 2**i *)
    let ppow = pow lsr 1 in
    let k, x =
      if loop_size < ppow then
        find_loop_entry ppow_exp
          (find_kth (E.copy ppow_exp) (succ loop_size)) ppow
      else
        find_loop_entry init
          (find_kth (E.next_impure ppow_exp) (loop_size-ppow+1)) 1 in
    (* Find (the smallest) k(>=i/2) and x s.t. x = A(k) = A(k+c) *)
    (* let k, x = find_loop_entry exp_prev e ppow in *)
    printf "Loop entry found at %d!@." k;
    k, loop_size, x

end


module Gosper(E:ExprType) = struct
  type t = E.t
  (* To find A(n) = A(r) with n <> r *) 

  (* Nu2(r) = k such that r = d * 2^k with some odd d. *)
  (* M(n) = { u < n | u = max { r | Nu2(r+1) = k } for some k < log_2 n } *)
  (* E.g., M(15) = { 7, 11, 13, 14 }     *)
  (*       M(16) = { 7, 11, 13, 14, 15 } *)
  (*       M(17) = { 7, 11, 13, 15, 16 } *)
  (* The set { A(m) | m in M(n) } for each n is maintained. *)

  (* counting trailing zeros *)
  let ctz x =
    let n = 0 in
    let n, x = if x land 0xffffffff = 0 then n + 32, x lsr 32 else n, x in
    let n, x = if x land 0xffff = 0 then n + 16, x lsr 16 else n, x in
    let n, x = if x land 0xff = 0 then n + 8, x lsr 8 else n, x in
    let n, x = if x land 0xf = 0 then n + 4, x lsr 4 else n, x in
    let n, x = if x land 0x3 = 0 then n + 2, x lsr 2 else n, x in
    if x land 0x1 = 0 then n + 1 else n
  
  let rec find_loop aset last i k =
    if i > E.limit then begin
      if E.limit > 1 then
        eprintf "%d terms are all different.@." (2 * E.limit);
      exit 0
    end else
      let next = E.next_impure last in
      E.display i last;
      let rec loop j =
        if k <= j then None
        else if E.equal next aset.(j) then Some j
        else loop (succ j) in
      match loop 0 with
      | None ->
         let r = ctz i in
         aset.(r) <- E.copy next;
         find_loop aset next (succ i) (if r = k then succ k else k)
      | Some j ->
         let j1 = 1 lsl j in
         let i1 = i - 1 in
         let n = i1 land (lnot (j1 - 1)) - (lnot i1) land  j1 in
         i - n, n

  let rec move_until_loop_size i e =
    if i < 1 then e else move_until_loop_size (i-1) (E.next e)
  
  let rec find_loop_entry last1 last2 i =
    E.display i last1;
    if E.equal last1 last2 then i, last1
    else find_loop_entry
           (E.next_impure last1) (E.next_impure last2) (succ i)

  let find_cycle init =
    let aset = Array.make 64 init in
    let loop_size, i = find_loop aset (E.copy init) 1 1 in
    printf "Loop detected! (%d = %d [%d])@." (i+loop_size) i loop_size;
    let e = move_until_loop_size loop_size (E.copy init) in
    let k, x = find_loop_entry init e 1 in
    printf "Loop entry found at %d!@." k;
    k, loop_size, x

end

module RestartableGosper(E:ExprType) = struct
  type t = E.t

  type funcall =
    | Init
    | FindLoop of { last1: t; last2: t; i: int; pow: int }
    | FindKth of { x1: t; k: int }
    | FindLoopEntry of { last1: t; last2: t; i: int }

  type state = { mutable init: t option;
                 mutable find_loop: (int * int) option;
                 mutable find_kth: t option;
                 mutable funcall: funcall;
                 mutable elapsed: float; }

  exception Interrupted of state

  let state = { init = None;
                find_loop = None;
                find_kth = None;
                funcall = Init;
                elapsed = 0.  }
  let stime = ref (Unix.gettimeofday()) (* start time *)
  let rfile = ref ""      (* the file name for restarting *)

  let save_current_state state =
    let elapsed = state.elapsed +. Unix.gettimeofday() -. !stime in
    state.elapsed <- elapsed;
    let oc = open_out !rfile in
    output_value oc (RBrent, state);
    close_out oc

  (* Find loop by Brent's cycle-finding algorithm                    *)
  (* to return k and pow such that A(pow=2**n) = A(pow+k) (1<=k<pow) *)
  let rec find_loop a set last =
    failwith"RestartableGosper.find_loop"

  (* Find the entry of loop by starting with i such that e=A(i)=A(2i) *)
  (* and searching the smallest k with x = A(k) = A(i+k)              *)
  (* to return k and x                                                *)
  let rec find_loop_entry last1 last2 i =
    failwith"RestartableGosper.find_loop_entry"

  let find_cycle_restart init fname =
    failwith"RestartableGosper.find_loop_restart"
    (* generate a filename if specifying no fileneme *)
         
end

    
