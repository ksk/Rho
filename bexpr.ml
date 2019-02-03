open Format

module type Expr = sig
  type t
  val compare: t -> t -> int
  val equal: t -> t -> bool
  val hash: t -> int
  val copy: t -> t
  val rev_list_of_expr: t -> int list
  val list_of_expr: t -> int list
  val expr_of_list: int list -> t
  val apply: t -> t -> t
  val apply_mono: t -> int -> t
end

(* n-iteration of f *)
let repeat f n x =
  let rec loop i acc = if i <= 0 then acc else loop (i-1) (f acc) in
  loop n x

(* unsafe_get *)
external ($!!) : Bytes.t -> int -> int = "%string_unsafe_get"
external ($<-) : Bytes.t -> int -> int -> unit = "%string_unsafe_set"
external ($|) : Bytes.t -> int -> int -> unit = "%string_unsafe_set"
let (|<-) (x: int -> unit) = x [@@inline]


(* decreasing polynomial representation in string *)
(* n-th character denotes the number of 'n' in the list representation *)
(* "\001\002\002\000\000\001" for 5.2.2.1.1.0 *)
module PureBytes: Expr = struct
  type t = Bytes.t

  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
  let copy x = x

  let list_of_expr expr =
    let rec multi_add i num acc =
      if num <= 0 then acc else multi_add i (num-1) (i::acc) in
    let rec loop i acc =
      if i >= Bytes.length expr then acc
      else loop (i+1) (multi_add i (Char.code (Bytes.get expr i)) acc) in
    loop 0 []

  let rev_list_of_expr expr = List.rev(list_of_expr expr)
    
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
         (* List.iter (fun n -> expr $|n|<- succ(expr $!! n)) list; *)
         expr
    else invalid_arg "expr_of_list"
    
  let expr_inc expr i num =
    let len = Bytes.length expr in
    if i < len then begin
      (expr $<- i) (num + (expr $!! i));
      (* expr $|i|<- num + (expr $!! i); *)
      expr
    end else
      let newe = Bytes.make (i+1) '\000' in
      Bytes.blit expr 0 newe 0 len;
      (newe $<- i) num;
      (* newe $|i|<- num; *)
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
        (* newe $|i-1|<- num; *)
        newe
      else if j >= i then
        let newe = Bytes.make (len-1) '\000' in
        Bytes.blit expr 1 newe 0 (len-1);
        (newe $<- (i-1)) (num + (newe $!! (i-1)));
        (* newe $|i-1|<- (num + (newe $!! (i-1))); *)
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
        (* expr $|i|<- (num + (expr $!! i)) *)
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
    (* printf "expr=%a (%S); h=%d@." (pp_expr 1) expr (Bytes.to_string expr) h; *)
    insert_left expr (succ h + (expr $!! 0)) 1

end

module PureBytes2: Expr = struct
  type t = Bytes.t

  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
  let copy x = x

  let list_of_expr expr =
    let rec multi_add i num acc =
      if num <= 0 then acc else multi_add i (num-1) (i::acc) in
    let rec loop i acc =
      if i >= Bytes.length expr then acc
      else loop (i+1) (multi_add i (Char.code (Bytes.get expr i)) acc) in
    loop 0 []

  let rev_list_of_expr expr = List.rev(list_of_expr expr)
    
  let rec non_increasing = function
    | [] | [_] -> true
    | x::y::l -> x >= y && non_increasing (y::l)
               
  let expr_of_list list =
    if non_increasing list then
      match list with
      | [] -> invalid_arg "expr_of_list"
      | n::l ->
         let expr = Bytes.make (n+1) '\000' in
         (* List.iter (fun n -> (expr $<- n) (1+(expr $!! n))) list; *)
         List.iter (fun n -> expr $|n|<- succ(expr $!! n)) list;
         expr
    else invalid_arg "expr_of_list"
    
  let expr_inc expr i num =
    let len = Bytes.length expr in
    if i < len then begin
      (* (expr $<- i) (num + (expr $!! i)); *)
      expr $|i|<- num + (expr $!! i);
      expr
    end else
      let newe = Bytes.make (i+1) '\000' in
      Bytes.blit expr 0 newe 0 len;
      (* (newe $<- i) num; *)
      newe $|i|<- num;
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
        (* (newe $<- (i-1)) num; *)
        newe $|i-1|<- num;
        newe
      else if j >= i then
        let newe = Bytes.make (len-1) '\000' in
        Bytes.blit expr 1 newe 0 (len-1);
        (* (newe $<- (i-1)) (num + (newe $!! (i-1))); *)
        newe $|i-1|<- (num + (newe $!! (i-1)));
        newe
      else
        loop (j+1) (i + (expr $!! j)) in
    loop 1 i
    
  (* insert height i bar into expr
     (after the most left bar is inserted) *)
  let insert_one expr i num =
    let rec loop j i =
      if j >= i then
        (* (expr $<- i) (num + (expr $!! i)) *)
        expr $|i|<- (num + (expr $!! i))
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
    (* printf "expr=%a (%S); h=%d@." (pp_expr 1) expr (Bytes.to_string expr) h; *)
    insert_left expr (succ h + (expr $!! 0)) 1


end

(* another decreasing polynomial representation in string *)
(* (n-from)-th character denotes the number of 'n' in the list representation *)
(* "\000\000\000\001\002\002\000\000\001\000\000"
   for 5.2.2.1.1.0 when from = 3 (offset) *)
(* from and upto are maintained for updates *)
module ImpureBytes: Expr = struct
  type t = { bytes: Bytes.t; from: int; upto: int }

  (* let pp_expr wid prf {bytes;from;upto} =
   *   pp_expr wid prf {bytes;from;upto};
   *   fprintf prf " %S[%d..%d]" (Bytes.to_string bytes) from upto *)

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

  let rev_list_of_expr expr = List.rev(list_of_expr expr)

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
         (* List.iter (fun n -> bytes $|n|<- succ(bytes $!! n)) list; *)
         {bytes; from=0; upto=n}
    else invalid_arg "expr_of_list"
    
  let hash e = Hashtbl.hash (list_of_expr e)

  let insert_one ({bytes;from;upto} as expr) b num =
    let rec loop i b =
      if upto < i then
        let b_max = Bytes.length bytes in
        if b < b_max then begin
          (bytes $<- b) num;
          (* bytes $|b|<- num; *)
          { expr with from; upto = b }
        end else if b_max lsr 1 < from then
          let b = b - from in
          Bytes.blit bytes from bytes 0 (upto-from+1);
          (* cleaning for the future use *) 
          for j = from to b_max-1 do (bytes $<- j) 0 done;
          (* for j = from to b_max-1 do bytes $|j|<- 0 done; *)
          (bytes $<- b) num;
          (* bytes $|b|<- num; *)
          { expr with from = 0; upto = b }
        else
          let b = b - from in
          let bs = Bytes.make (b_max lsl 1) '\000' in
          let upto = upto - from in
          Bytes.blit bytes from bs 0 (upto+1);
          (bs $<- b) num;
          (* bs $|b|<- num; *)
          { bytes=bs; from = 0; upto=b }
      else if b = i then begin
        (bytes $<- i) (num + (bytes $!! i));
        (* bytes $|i|<- num + (bytes $!! i); *)
        { expr with from }
      end else
        loop (succ i) (b + (bytes $!! i)) in
    if num > 0 then loop from (b+from) else expr

  let apply {bytes=b1;from=f1;upto=u1} {bytes=b2;from=f2;upto=u2} =
    let base = b1 $!! f1 in
    (b1 $<- f1) 0 ; (* clear after checking base *)
    (* b1 $|f1|<- 0; (\* clear after checking base *\) *)
    let f1 = succ f1 in
    let rec loop e1 u2 =
      if u2 < f2 then e1
      else loop (insert_one e1 (base+u2-f2) (b2 $!! u2)) (u2-1) in
    loop {bytes=b1;from=f1;upto=u1} u2

  let apply_mono {bytes;from;upto} h =
    let base = bytes$!! from in
    (bytes$<-from) 0;
    (* bytes $|from|<- 0; *)
    insert_one {bytes; from = succ from; upto} (h+base) 1

  let compare {bytes=b1;from=f1;upto=u1} {bytes=b2;from=f2;upto=u2} =
    match compare (u1-f1) (u2-f2) with
    | 0 ->
       let rec loop i1 i2 =
         if u1 < i1 then 0 
         else match compare (b1 $!! i1) (b2 $!! i2) with
              | 0 -> loop (succ i1) (succ i2)
              | neq -> neq in
       loop f1 f2
    | neq -> neq

  let equal e1 e2 = compare e1 e2 = 0

end 

module ImpureBytes2: Expr = struct
  type t = { bytes: Bytes.t; from: int; upto: int }

  (* let pp_expr wid prf {bytes;from;upto} =
   *   pp_expr wid prf {bytes;from;upto};
   *   fprintf prf " %S[%d..%d]" (Bytes.to_string bytes) from upto *)

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

  let rev_list_of_expr expr = List.rev(list_of_expr expr)
    
  let rec non_increasing = function
    | [] | [_] -> true
    | x::y::l -> x >= y && non_increasing (y::l)
               
  let expr_of_list list =
    if non_increasing list then
      match list with
      | [] -> invalid_arg "expr_of_list"
      | n::l ->
         let bytes = Bytes.make (max b_max (n+1)) '\000' in
         (* List.iter (fun n -> (bytes $<- n) (1+(bytes $!! n))) list; *)
         List.iter (fun n -> bytes $|n|<- succ(bytes $!! n)) list;
         {bytes; from=0; upto=n}
    else invalid_arg "expr_of_list"
    
  let hash e = Hashtbl.hash (list_of_expr e)

  let insert_one ({bytes;from;upto} as expr) b num =
    let rec loop i b =
      if upto < i then
        let b_max = Bytes.length bytes in
        if b < b_max then begin
          (* (bytes $<- b) num; *)
          bytes $|b|<- num;
          { expr with from; upto = b }
        end else if b_max lsr 1 < from then
          let b = b - from in
          Bytes.blit bytes from bytes 0 (upto-from+1);
          (* cleaning for the future use *) 
          (* for j = from to b_max-1 do (bytes $<- j) 0 done; *)
          for j = from to b_max-1 do bytes $|j|<- 0 done;
          (* (bytes $<- b) num; *)
          bytes $|b|<- num;
          { expr with from = 0; upto = b }
        else
          let b = b - from in
          let bs = Bytes.make (b_max lsl 1) '\000' in
          let upto = upto - from in
          Bytes.blit bytes from bs 0 (upto+1);
          (* (bs $<- b) num; *)
          bs $|b|<- num;
          { bytes=bs; from = 0; upto=b }
      else if b = i then begin
        (* (bytes $<- i) (num + (bytes $!! i)); *)
        bytes $|i|<- num + (bytes $!! i);
        { expr with from }
      end else
        loop (succ i) (b + (bytes $!! i)) in
    if num > 0 then loop from (b+from) else expr

  let apply {bytes=b1;from=f1;upto=u1} {bytes=b2;from=f2;upto=u2} =
    let base = b1 $!! f1 in
    (* (b1 $<- f1) 0 ; (\* clear after checking base *\) *)
    b1 $|f1|<- 0; (* clear after checking base *)
    let f1 = succ f1 in
    let rec loop e1 u2 =
      if u2 < f2 then e1
      else loop (insert_one e1 (base+u2-f2) (b2 $!! u2)) (u2-1) in
    loop {bytes=b1;from=f1;upto=u1} u2

  let apply_mono {bytes;from;upto} h =
    let base = bytes$!! from in
    (* (bytes$<-from) 0; *)
    bytes $|from|<- 0;
    insert_one {bytes; from = succ from; upto} (h+base) 1

  let compare {bytes=b1;from=f1;upto=u1} {bytes=b2;from=f2;upto=u2} =
    match compare (u1-f1) (u2-f2) with
    | 0 ->
       let rec loop i1 i2 =
         if u1 < i1 then 0 
         else match compare (b1 $!! i1) (b2 $!! i2) with
              | 0 -> loop (succ i1) (succ i2)
              | neq -> neq in
       loop f1 f2
    | neq -> neq

  let equal e1 e2 = compare e1 e2 = 0

end 

module ZBytes = struct
  type t = Z.t

  let isucc = succ
  let (+/) = (+)
  let (-/) = (-)
  let (<=/) (x:int) = (<=) x
  let log2span = 3
  let span = 1 lsl log2span (* 8-bit span *)
  let n_span n = n lsl log2span

  open Z
  let (!/) = to_int 
  let mask = one lsl span - one

  let repeat f n x =
    let rec loop i acc =
      if i = zero then acc else loop (pred i) (f acc) in
    loop n x

  let list_of_expr exp =
    let rec loop i e acc =
      if e = zero then acc
      else loop (isucc i) (e asr span)
             (repeat (fun l->i::l) (e land mask) acc) in
    loop 0 exp []

  let rev_list_of_expr exp = List.rev(list_of_expr exp)

  let expr_of_list l =
    let rec loop l acc = match l with
      | [] -> acc
      | h::l -> loop l (acc + one lsl n_span h) in
    loop l zero

  let compare = compare
  let equal = (=)
  let hash = hash
  let copy x = x

  let insert_bar exp h num =
    let rec loop e cur i h =
      if cur = zero then e lor (num lsl n_span h)
      else if h <=/ i then e + num lsl n_span h
      else loop e (cur asr span) (isucc i) (h +/ !/(cur land mask)) in
    loop exp exp 0 h

  let apply_nums exp nums h =
    let zeros = !/ (exp land mask) in
    let rec loop e ns h = match ns with
      | [] -> e 
      | n::ns -> loop (insert_bar e (h+/zeros) n) ns (h-/1) in
    loop (exp asr span) nums (h-/1)

  let apply exp1 exp2 =
    let rec loop e2 ns h =
      if e2 = zero then apply_nums exp1 ns h
      else loop (e2 asr span) (e2 land mask :: ns) (isucc h) in
    loop exp2 [] 0

  let ($$) l1 l2 =
    list_of_expr(apply(expr_of_list l1)(expr_of_list l2))

  let apply_mono exp h =
    let zeros = !/ (exp land mask) in
    insert_bar (exp asr span) (h+/zeros) one

end

module type Bits = sig
  type t
  val zero: t
  val one: t
  val (>>%): t -> int -> t
  val (<<%): t -> int -> t
  val (|%): t -> t -> t
  val is_even: t -> bool
  val is_one: t -> bool
end

(* Using bits for the sequence of 0 (B x) and 1 (x o B) *)
module MakeBitSeq(B:Bits) = struct
  type t = B.t 
  open B
  (* 1:B; x0: B x; x1: B x B *)
  let rev_list_of_expr (expr:t) =
    let rec to_revpoly e =
      if is_even e then
        List.map succ (to_revpoly (e >>% 1))
      else if is_one e then
        [0]
      else
        0 :: to_revpoly (e >>% 1) in
    to_revpoly expr

  let list_of_expr expr =
    List.rev (rev_list_of_expr expr)

  let compare (x:t) = compare x
  let equal (x:t) = (=) x
  let hash (x:t) = Hashtbl.hash x

  let copy (x:t) = x

  let expr_of_list l: t =
    let rec loop l =
      match l with
      | [x] -> one <<% x
      | x::xs -> ((loop (List.map (fun y->y-x) xs) <<% 1) |% one) <<% x
      | [] -> invalid_arg "BitSeq.expr_of_list" in
    loop (List.rev l)

  let apply1 (exp1:t) (exp2:t) =
    let rec loop e1 e2 =
      if is_even e1 then loop0 (e1 >>% 1) e2
      else if is_one e1 then e2 <<% 1
      else loop (e1 >>% 1) (e2 <<% 1)
    and loop0 e1 e2 =
      if is_even e2 then
        if is_even e1 then loop0 (e1 >>% 1) (e2 >>% 1) <<% 1
        else if is_one e1 then (e2 <<% 2) |% one
        else (loop0 (e1 >>% 1) (e2 <<% 1) <<% 1) |% one
      else if is_one e2 then (e1 <<% 1) |% one
      else (loop0 e1 (e2 >>% 1) <<% 1) |% one in
    loop exp1 exp2

  (* tail recursive *)
  let apply2 (exp1:t) (exp2:t): t =
    let rec loop e1 e2 ofs acc =
      if is_even e1 then loop0 (e1 >>% 1) e2 ofs acc
      else if is_one e1 then (e2 <<% succ ofs) |% acc
      else loop (e1 >>% 1) (e2 <<% 1) ofs acc
    and loop0 e1 e2 ofs acc =
      if is_even e2 then
        if is_even e1 then
          loop0 (e1 >>% 1) (e2 <<% 1) (succ ofs) acc
        else if is_one e1 then (((e2 <<% 2) |% one) <<% ofs) |% acc
        else loop0 (e1 >>% 1) (e2 <<% 1)
               (succ ofs) ((one <<% ofs) |% acc)
      else if is_one e2 then (((e1 <<% 1) |% one) <<% ofs) |% acc
      else loop0 e1 (e2 >>% 1) (succ ofs) ((one <<% ofs) |% acc) in
    loop exp1 exp2 0 zero
  
  (* let ($$) l1 l2 =
   *   list_of_expr(apply (expr_of_list l1) (expr_of_list l2));; *)

  let apply = apply2

  let apply_mono (exp:t) h: t =
    let rec loop e h ofs acc =
      if is_even e then loop0 (e >>% 1) h ofs acc
      else if is_one e then (one <<% succ(h+ofs)) |% acc
      else loop (e >>% 1) (succ h) ofs acc 
    and loop0 e h ofs acc =
      if h = 0 then (((e <<% 1) |% one) <<% ofs) |% acc
      else if is_even e then loop0 (e >>% 1) (h-1) (succ ofs) acc
      else if is_one e then (((one <<% (h+2)) |% one) <<% ofs) |% acc
      else loop0_h (e >>% 1) h (succ ofs) ((one <<% ofs) |% acc)
    and loop0_h e h ofs acc =
      if is_even e then loop0 (e >>% 1) h (succ ofs) acc
      else if is_one e then (((one <<% (h+3)) |% one) <<% ofs) |% acc
      else loop0_h (e >>% 1) (succ h) (succ ofs) ((one <<% ofs) |% acc) in
    loop exp h 0 zero

end [@@inline]

module IntBits: Bits = struct
  (* double int *)
  type t = int
  let zero = 0
  let one = 1
  let (>>%) = (lsr)
  let (<<%) = (lsl)
  let (|%) = (lor)
  let is_even x = x land 1 = 0
  let is_one x = x = 1
end

module DIntBits: Bits = struct
  (* double int *)
  type t = int * int (* 63 bit * 63 bit *)
  let zero = (0,0)
  let one = (0,1)
  let (>>%) ((x1,x2):t) i: t =
    (x1 lsr i, (x1 lsl (63-i)) lor (x2 lsr i))
  let (<<%) ((x1,x2):t) i: t = 
    ((x1 lsl i) lor (x2 lsr (63-i)), x2 lsl i)
  let (|%) ((x1,x2):t) ((y1,y2):t) = (x1 lor y1, x2 lor y2)
  let is_even ((_,x2):t) = x2 land 1 = 0
  let is_one ((x1,x2):t) = x1 = 0 && x2 = 1
end

module ZBits: Bits = struct
  type t = Z.t
  let zero = Z.zero
  let one = Z.one
  let (>>%) = Z.(asr)
  let (<<%) = Z.(lsl)
  let (|%) = Z.(lor)
  let is_even = Z.is_even
  let is_one = Z.equal Z.one
end


module DIntBitSeq = MakeBitSeq(DIntBits)
module IntBitSeq = MakeBitSeq(IntBits)
module ZBitSeq = MakeBitSeq(ZBits)
