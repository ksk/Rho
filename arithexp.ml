
open Genlex

let lexer = make_lexer [ "(";")";"+";"-";"*" ]

let rec parse_exp env = parser
| [< e1 = parse_atom env; e2 = parse_rem1 env e1 >] -> e2

and parse_atom env = parser
| [< 'Ident x >] -> env x
| [< 'Int n >] -> n
| [< 'Kwd "("; e = parse_exp env; 'Kwd ")" >] -> e
| [< >] -> invalid_arg "Parsing failure (atom)"

and parse_rem1 env acc = parser
| [< 'Kwd "*"; e1 = parse_atom env;
     e2 = parse_rem1 env (acc*e1) >] -> e2
| [< 'Kwd "+"; e1 = parse_atom env;
     e2 = parse_rem2 env acc e1 >] -> e2
| [< >] -> acc

and parse_rem2 env acc1 acc2 = parser
| [< 'Kwd "*"; e1 = parse_atom env; 
      e2 = parse_rem1 env (acc2*e1) >] -> acc1 + e2
| [< 'Kwd "+"; e1 = parse_atom env; 
      e2 = parse_rem2 env (acc1+acc2) e1 >] -> e2
| [< >] -> acc1+acc2

let parse env s = parse_exp env (lexer (Stream.of_string s))
