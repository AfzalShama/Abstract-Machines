type ident = string ;;

type exp = 	
		| Int of int
		| Bool of bool
		| Var of ident 
		| Add of (exp * exp)
		| Sub of (exp * exp)
		| Mult of (exp * exp)
		| Divide of (exp * exp)
		| Mod of (exp * exp)
		| Equal of (exp * exp)
		| Great of (exp * exp)
		| GreatEq of (exp * exp)
		| LessEq of (exp * exp)
		| Exponent of (exp * exp)
		| Abs of exp
		| And of (exp * exp)
		| Or of (exp * exp)
		| Implies of (exp * exp)
		| Not of exp
		| Ifte of (exp * exp * exp) 
		| Proj of (exp * exp)
		| NTuple of (exp list)
		| Lambda of (ident * exp)
		| App of (exp * exp) 
		| Assign of (exp * exp)
		| Par of (exp list) 
		| Seq of (exp list) 
		| LetDE of (exp * exp);;

type instruction =  exp ;;

type opcode = 
| INT of int 
| BOOL of bool 
| VAR of ident
| ADD | SUB | MULT | DIVIDE | MOD | EQUAL | GREAT| LESS | GREATEQ | LESSEQ | EXPONENT | ABS
| AND | OR | IMPLIES | NOT
| CLOS of (ident * code) 
| APP of code
| IFTE of (code * code)
| NTUPLE of (code list)
| ASSIGN of (code * code)
and 
code = opcode list ;;



type value = AnsInt of int | AnsBool of bool | AnsVar of ident | AnsClos of (gamma * code) 
and 
gamma = (ident * value) list ;;

type stack = value list ;;

let rec compile = function
					| Int(n) -> [INT(n)]
					| Bool(b) -> [BOOL(b)]
					| Var(v) -> [VAR(v)]
					| Add(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [ADD]
					| Sub(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [SUB]
					| Mult(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [MULT]
					| Divide(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [DIVIDE]
					| Mod(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [MOD]
					| Equal(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [EQUAL]					
					| Mult(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [MULT]
					| GreatEq(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [GREATEQ]
					| LessEq(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [LESSEQ]
					| Exponent(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [EXPONENT]
					| Abs(exp1) -> (compile exp1) @ [ABS]
					| And(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [AND]
					| Or(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [OR]
					| Implies(exp1, exp2) -> (compile (Not(exp1))) @ (compile exp2) @ [OR]
					| Not(exp1) -> (compile exp1) @ [NOT]
					| NTuple(exps) -> [NTUPLE(List.map compile exps)]
					| Proj(exp1, exp2) -> (compile exp1) @ (compile exp2)
					| Ifte(exp1, exp2, exp3) -> compile(exp1) @ [IFTE((compile exp2), (compile exp3))]
					| Lambda(id, exp1) -> [CLOS(id, compile(exp1))]
					| App(exp1, exp2) -> [APP(compile exp2)] @ (compile exp1)
					| Assign(v,n) -> [ASSIGN((compile v), (compile n))]
					| Par([]) -> []
					| Par(d::dlist) -> (compile d) @ (compile (Par(dlist))) 
					| Seq([]) -> []
					| Seq(d::dlist) -> (compile d) @ (compile (Seq(dlist))) 
					| LetDE(def1, exp) ->  (compile def1) @ (compile exp) ;;


(* Checks if the Binary operator is Comparison or Computation *)
let type_of_bin op = match op with
	| EXPONENT -> -1
	| ADD -> 0
	| SUB -> 0
	| MULT -> 0
	| DIVIDE -> 0
	| MOD -> 0
	| EQUAL -> 1
	| GREAT -> 1
	| LESS -> 1
	| GREATEQ -> 1
	| LESSEQ -> 1 ;;

(* Operations performed by Integer Binary Operators *)
let eval_bin_op_int1 = function
	| ADD -> (+) 
	| SUB -> (-) 
	| MULT -> ( * )
	| DIVIDE -> (/)
	| MOD -> (mod) ;;

let eval_bin_op_int2 = function	
	| EQUAL -> (==)
	| GREAT -> (>)
	| LESS -> (<)
	| GREATEQ -> (>=)
	| LESSEQ -> (<=) ;;


(* Operations performed by Boolean Binary Operators *)
let eval_bin_op_bool = function
	| AND -> (&)
	| OR -> (||) ;;


let rec lookup id g = match g with
							| [] -> AnsVar(id)
							| (x,v)::gs -> if (String.equal id x) then v else (lookup id gs) ;;

let rec remove id l = match l with []-> l								
								| (x,y)::xs -> if (String.equal id x) then xs else (x,y)::(remove id xs) ;;


exception INVALID_SYNTAX of string ;;	

let rec krivine_bigStep ((st: stack), (ga: gamma), (co: code)) = match (st, ga, co) with 
		| ans::s1, g, [] -> ans
		| s, g, INT(n)::c -> krivine_bigStep ((AnsInt(n)::s), g, c)
		| s, g, BOOL(b)::c -> krivine_bigStep ((AnsBool(b)::s), g, c)
		| s, g, VAR(id)::c -> let temp = (match (lookup id g) with
											AnsClos(g1, c1) -> krivine_bigStep (s, g1, c1)
											| x -> x )
								in krivine_bigStep (temp::s, g, c) 
		| s, g, ASSIGN([VAR(id)], [v])::c -> (match v with INT(n) -> krivine_bigStep(s, (id, AnsInt(n))::g, c) 
																| BOOL(b) -> krivine_bigStep(s, (id, AnsBool(b))::g, c))
		| x::xs, g , IFTE(c1,c2)::c -> (match x with AnsBool(true) -> krivine_bigStep(xs, g, c1 @ c) 
													|_ -> krivine_bigStep(xs, g, c2 @ c))
		| AnsInt(n)::xs, g, NTUPLE(clist)::c -> krivine_bigStep(xs, g, (List.nth clist n) @ c)
		| s, g, APP(c2)::c -> krivine_bigStep (AnsClos(g, c2)::s, g, c)
		| s, g, CLOS(id, c1)::c -> let g = (remove id g) in 
									(match s with 
										  [] -> krivine_bigStep([], g, c1 @ c)
										| cl::xs -> krivine_bigStep (xs, (id, cl)::g, c1 @ c))
		| (s, g, op::cs) -> match s with 
					  AnsInt(n)::xs ->  (match op with 
											  ABS -> krivine_bigStep (AnsInt(abs(n))::xs, g, cs)
											| bin_op -> (match (type_of_bin bin_op) with 
															  -1 -> (match xs with 
														  				AnsInt(n2)::xxs -> krivine_bigStep (AnsInt(int_of_float ((float n2)**(float n)))::xxs, g, cs)
																		| _ -> raise(INVALID_SYNTAX "Invalid Arguments"))
															| 0 -> (match xs with 
																		AnsInt(n2)::xxs -> krivine_bigStep (AnsInt(eval_bin_op_int1 bin_op n2 n)::xxs, g, cs)
																		| _ -> raise(INVALID_SYNTAX "Invalid Arguments"))
															| 1 -> (match xs with 
																		AnsInt(n2)::xxs -> krivine_bigStep (AnsBool(eval_bin_op_int2 bin_op n2 n)::xxs, g, cs)))
																		| _ -> raise(INVALID_SYNTAX "Invalid Arguments"))
					| AnsBool(b)::xs -> (match op with
											  NOT -> krivine_bigStep (AnsBool(not(b))::xs, g, cs)
											| bin_op -> (match xs with AnsBool(b2)::xxs -> krivine_bigStep (AnsBool(eval_bin_op_bool bin_op b2 b)::xxs, g, cs)))

					| _ -> raise(INVALID_SYNTAX "Invalid Arguments")

 		| _ -> raise(INVALID_SYNTAX "Wrong Input") ;;


let krivine_machine ((e: exp), (g:gamma)) = krivine_bigStep ([], g, (compile e)) ;;

(* krivine_machine (Clos("y",(Divide(App(Clos("x",Mult(Var("x"), Int(2))), Add(Int(3),Int(4))), Int(1)))), []);; *)

krivine_machine(Var("z"),[("z",AnsClos([], compile(Int(3))))]);;

krivine_machine(Add(Add(Int(2),Int(3)),Add(Int(2),Int(3))), []);;

krivine_machine(Add(Int(2),Var("z")),[("z",AnsClos([], compile(Int(3))))]);;

krivine_machine(App(Lambda("x",Add(Var("x"),Int(1))),Int(2)), []);;

krivine_machine(App(Lambda("x",Mult(Var("x"),Add(Var("x"),Int(1)))),Int(2)), []);;

krivine_machine(App(Lambda("x",App(Lambda("d",Mult(Var("d"),Int(2))),Int(2))),Int(2)), []);;

krivine_machine(Ifte(GreatEq(Int(8),Int(2)),App(Lambda("x",Divide(Var("x"),Int(2))),Int(2)),App(Lambda("x",Mult(Var("x"),Add(Var("x"),Int(1)))),Int(2))), []);;

krivine_machine(Ifte(GreatEq(Int(1),Int(2)),App(Lambda("x",Divide(Var("x"),Int(2))),Int(2)),App(Lambda("x",Mult(Var("x"),Add(Var("x"),Int(1)))),Int(2))), []);;

krivine_machine(LetDE(Par[Assign(Var("a"),Int(2))],Add(Var("a"),Int(20))), []);;

krivine_machine(LetDE(Seq[Assign(Var("a"),Int(2))],Add(Var("a"),Int(20))), []);;

krivine_machine(Proj(Int(2), NTuple([Int(1); Int(2); Int(3)])), []);;

krivine_machine(App(Lambda("x",LetDE(Par[Assign(Var("a"),Int(2))],Add(Var("a"),Var("x")))),Int(2)), []);;

