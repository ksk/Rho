open Format

module type Expr = sig
  type t
  val pp_expr: int -> formatter -> t -> unit
  val compare: t -> t -> int
  val equal: t -> t -> bool
  val hash: t -> int
  val copy: t -> t
  val list_of_expr: t -> int list
  val expr_of_list: int list -> t
  val apply: t -> t -> t
  val apply_mono: t -> int -> t
  val expr_fold_up: (int -> 'a -> 'a) -> 'a -> t -> 'a
  val expr_fold_down: (int -> 'a -> 'a) -> 'a -> t -> 'a
end

(* unsafe_get *)
external ($!!) : Bytes.t -> int -> int = "%string_unsafe_get"
external ($<-) : Bytes.t -> int -> int -> unit = "%string_unsafe_set"

(* list representation in string *)
(* n-th character denotes the number of 'n' in the list representation *)
(* "\001\002\002\000\000\001" for 5.2.2.1.1.0 *)
module PureBytes: Expr = struct
  type t = Bytes.t

  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
  let copy x = x

  let pp_expr wid prf expr =
    let i = Bytes.length expr-1 in
    fprintf prf "%*d" wid i;
    for j = 2 to expr $!! i do
      fprintf prf ".%*d" wid i
    done;
    for i = Bytes.length expr-2 downto 0 do
      for j = 1 to expr $!! i do
        fprintf prf ".%*d" wid i
      done
    done
    
  let list_of_expr expr =
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
    if non_increasing list then
      match list with
      | [] -> invalid_arg "expr_of_list"
      | n::l ->
         let expr = Bytes.make (n+1) '\000' in
         List.iter (fun n -> (expr $<- n) (1+(expr $!! n))) list;
         expr
    else invalid_arg "expr_of_list"
    
  let expr_inc expr i num =
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
  let insert_left expr i num =
    (* printf "expr=%a (%S); i=%d; num=%d@." (pp_expr 1) expr (Obj.magic expr) i num; *)
    let len = Bytes.length expr in
    let rec loop j i =
      (* printf "j=%d; i=%d@." j i; *)
      if j >= len then
        let newe = Bytes.make i '\000' in
        Bytes.blit expr 1 newe 0 (len-1);
        (newe $<- (i-1)) num;
        newe
      else if j >= i then
        let newe = Bytes.make (len-1) '\000' in
        Bytes.blit expr 1 newe 0 (len-1);
        (newe $<- (i-1)) (num + (newe $!! (i-1)));
        newe
      else
        loop (j+1) (i + (expr $!! j)) in
    loop 1 i
    
  (* insert height i bar into expr
     (after the most left bar is inserted) *)
  let insert_one expr i num =
    let rec loop j i =
      if j >= i then
        (expr $<- i) (num + (expr $!! i))
      else
        loop (j+1) (i + (expr $!! j)) in
    if num > 0 then loop 0 i
    
  let apply expr1 expr2 =
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

  let apply_mono expr h =
    (* printf "expr=%a (%S); h=%d@." (pp_expr 1) expr (Obj.magic expr) h; *)
    insert_left expr (succ h + (expr $!! 0)) 1

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
    
end

module ImpureBytes: Expr = struct
  type t = { bytes: Bytes.t; from: int; upto: int }

  let pp_expr wid prf {bytes;from;upto} =
    fprintf prf "%*d" wid (upto-from);
    for j = 2 to bytes $!! upto do
      fprintf prf ".%*d" wid (upto-from)
    done;
    for i = upto-1 downto from do
      for j = 1 to bytes $!! i do
        fprintf prf ".%*d" wid (i-from)
      done
    done

  let b_max = 256

  let copy {bytes;from;upto} =
    {bytes=Bytes.copy bytes;from;upto}

  let bytes_of_expr {bytes;from;upto} e =
    let len = upto-from+1 in
    let b = Bytes.make len '\000' in
    Bytes.blit bytes from b 0 len;
    b
    
  let list_of_expr {bytes;from;upto} =
    let rec multi_add i num acc =
      if num <= 0 then acc else multi_add i (num-1) (i::acc) in
    let rec loop i acc =
      if i > upto then acc
      else loop (i+1) (multi_add (i-from)
                         (Char.code (Bytes.get bytes i)) acc) in
    loop from []
    
  let rec non_increasing = function
    | [] | [_] -> true
    | x::y::l -> x >= y && non_increasing (y::l)
               
  let expr_of_list list =
    if non_increasing list then
      match list with
      | [] -> invalid_arg "expr_of_list"
      | n::l ->
         let bytes = Bytes.make (max b_max (n+1)) '\000' in
         List.iter (fun n -> (bytes $<- n) (1+(bytes $!! n))) list;
         {bytes; from=0; upto=n}
    else invalid_arg "expr_of_list"
    
  let repeat f n x =
    let rec loop i acc = if i <= 0 then acc else loop (i-1) (f acc) in
    loop n x

  let expr_fold_up f e {bytes;from;upto} =
    let rec loop i acc =
      if upto < i then acc
      else loop (succ i) (repeat (f (i-from)) (bytes $!! i) acc) in
    loop from e
    
  let expr_fold_down f e {bytes;from;upto} =
    let rec loop i acc =
      if i < from then acc
      else loop (i-1) (repeat (f (i-from)) (bytes $!! i) acc) in
    loop upto e

  let hash e = expr_fold_down (fun i x -> (x lsl 3) + i + 1) 0 e

  let insert_one ({bytes;from;upto} as expr) b num =
    let rec loop i b =
      (* printf "b=%d; (from,upto)=(%d,%d); i=%d; e=%a@."
       *   b from upto i (pp_expr 1) expr; *)
      if upto < i then
        let b_max = Bytes.length bytes in
        if b < b_max then begin
            for j = upto+1 to b-1 do (bytes $<- j) 0 done;
            (bytes $<- b) num;
            { expr with from; upto = b }
        end else if b_max lsr 1 < from then
          let b = b - from in
          (* printf "%S@." (Obj.magic bytes);
           * printf "2:b=%d, from=%d, upto=%d@." b from upto; *)
          (* printf "-%S[%d..%d] (%a)"
           *   (Obj.magic expr.bytes) expr.from expr.upto (pp_expr 1) expr;
           * printf " %d %d %d@." from 0 (upto-from+1); *)
          Bytes.blit bytes from bytes 0 (upto-from+1);
          for j = upto-from+1 to b-1 do (bytes $<- j) 0 done;
          (bytes $<- b) num;
          (* printf "%S@." (Obj.magic bytes); *)
          { expr with from = 0; upto = b }
        else
          let b = b - from in
          (* printf "3:b=%d, from=%d, upto=%d@." b from upto; *)
          let bs = Bytes.make (b_max lsl 1) '\000' in
          let upto = upto - from in
          (* printf "bytes=%S@.bs=%S@." (Obj.magic bytes) (Obj.magic bs); *)
          Bytes.blit bytes from bs 0 (upto+1);
          (bs $<- b) num;
          (* printf "bytes=%S@.bs=%S@." (Obj.magic bytes) (Obj.magic bs); *)
          { bytes=bs; from = 0; upto=b }
      else if b = i then begin
        (bytes $<- i) (num + (bytes $!! i));
        { expr with from }
      end else
        loop (succ i) (b + (bytes $!! i)) in
    if num > 0 then loop from (b+from) else expr

  let apply {bytes=b1;from=f1;upto=u1} {bytes=b2;from=f2;upto=u2} =
    (* printf "---@."; *)
    let base = b1 $!! f1 in
    let f1 = succ f1 in
    let rec loop e1 u2 =
      (* printf "e1=%a; f2=%d, u2=%d@." (pp_expr 1) e1 f2 u2;
       * printf "%S[%d..%d] %a@."
       *   (Obj.magic e1.bytes) e1.from e1.upto (pp_expr 1) e1; *)
      if u2 < f2 then e1
      else loop (insert_one e1 (base+u2-f2) (b2 $!! u2)) (u2-1) in
    loop {bytes=b1;from=f1;upto=u1} u2

  let apply_mono {bytes;from;upto} h =
    (* printf "e=%a; h=%d; q=%d@." (pp_expr 1) {bytes;from;upto} h (h+(bytes$!! from));
     * printf "  %S[%d..%d]@." (Obj.magic bytes) from upto; *)
    insert_one {bytes; from = succ from; upto} (h+(bytes$!! from)) 1

  (* to count the maximum number of zeros *)
  (* let apply_mono =
    let nz = ref 0 in
    fun {bytes;from;upto} h ->
      let res = apply_mono {bytes;from;upto} h in
      let z = res.bytes $!! res.from in
      if !nz < z then begin
        printf "            nz <= %d@." z;
        nz := z;
      end;
      res *)

  let compare {bytes=b1;from=f1;upto=u1} {bytes=b2;from=f2;upto=u2} =
    (* printf "e1=%a; e2=%a@."
     *   (pp_expr 1) {bytes=b1;from=f1;upto=u1} 
     *   (pp_expr 1) {bytes=b2;from=f2;upto=u2};
     * printf "h1=%d; h2=%d@."
     *   (hash {bytes=b1;from=f1;upto=u1})
     *   (hash {bytes=b2;from=f2;upto=u2});
     * printf " b1=%S[%d..%d]@. b2=%S[%d..%d]@."
     *   (Obj.magic b1) f1 u1 (Obj.magic b2) f2 u2; *)
    match compare (u1-f1) (u2-f2) with
    | 0 ->
       let rec loop i1 i2 =
         if u1 < i1 then 0 
         else match compare (b1 $!! i1) (b2 $!! i2) with
              | 0 -> loop (succ i1) (succ i2)
              | neq -> neq in
       loop f1 f2
    | neq -> neq

  (* let compare e1 e2 =
   *   let s1 = Format.asprintf "%a" (pp_expr 1) e1 in
   *   let s2 = Format.asprintf "%a" (pp_expr 1) e2 in
   *   let ce = compare e1 e2 in
   *   let cs = String.compare s1 s2 in
   *   if  ce * ce <> cs * cs then begin
   *       printf "e1=%a; e2=%a@." (pp_expr 1) e1 (pp_expr 1) e2;
   *       printf " b1=%S[%d..%d]@. b2=%S[%d..%d]@."
   *         (Obj.magic e1.bytes) e1.from e1.upto
   *         (Obj.magic e2.bytes) e2.from e2.upto
   *     end;
   *   compare e1 e2 *)

  let equal e1 e2 = compare e1 e2 = 0

end 
