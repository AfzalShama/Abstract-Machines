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
		| Clos of (ident * exp)
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
| RET | APP 
| IFTE of (code * code)
| NTUPLE of (code list)
| ASSIGN of (code * code)
and 
code = opcode list ;;



type value = AnsInt of int | AnsBool of bool | AnsVar of ident | AnsClos of (gamma * ident * code) 
and 
gamma = (ident * value) list ;;

type stack = value list ;;

type dump = (stack * gamma * code) list ;;

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
					| Clos(id, exp1) -> [CLOS(id, compile(exp1) @ [RET])]
					| App(exp1, exp2) -> (compile exp1) @ (compile exp2) @ [APP] 
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

exception INVALID_SYNTAX of string ;;						

let rec bigStep ((st: stack), (ga: gamma), (co: code), (du: dump)) = match (st, ga, co, du) with 
		| ans::s1, g, [], [] -> ans
		| s, g, [], (s1, g1, c1)::d -> bigStep (s1, g1, c1, d)
		| s, g, INT(n)::c, d -> bigStep ((AnsInt(n)::s), g, c, d)
		| s, g, BOOL(b)::c, d -> bigStep ((AnsBool(b)::s), g, c, d)
		| s, g, VAR(id)::c, d -> bigStep ((lookup id g)::s, g, c, d)
		| s, g, ASSIGN([VAR(id)], [v])::c, d -> (match v with INT(n) -> bigStep(s, (id, AnsInt(n))::g, c, d) 
																| BOOL(b) -> bigStep(s, (id, AnsBool(b))::g, c, d))
		| x::xs, g , IFTE(c1,c2)::c, d -> (match x with AnsBool(true) -> bigStep(xs, g, c1 @ c, d) 
													  | _ -> bigStep(xs, g, c2 @ c, d))
		| AnsInt(n)::xs, g, NTUPLE(clist)::c, d -> bigStep(xs, g, (List.nth clist n) @ c, d)
		| s, g, CLOS(id, c1)::c, d -> bigStep (AnsClos(g, id, c1)::s, g, c, d)
		| a::AnsClos(g1, id1, c1)::s, g, APP::c, d -> bigStep ([], (id1, a)::g1, c1, (s, g, c)::d)
		| a::s, g, RET::c, (s1, g1, c1)::d -> bigStep (a::s1, g1, c1, d)
		| (s, g, op::cs, d) -> match s with 
							  AnsInt(n)::xs ->  (match op with 
													  ABS -> bigStep (AnsInt(abs(n))::xs, g, cs, d)
													| bin_op -> (match (type_of_bin bin_op) with 
																	  -1 -> (match xs with 
																  				AnsInt(n2)::xxs -> bigStep (AnsInt(int_of_float ((float n2)**(float n)))::xxs, g, cs, d)
																				| _ -> raise(INVALID_SYNTAX "Invalid Arguments"))
																	| 0 -> (match xs with 
																				AnsInt(n2)::xxs -> bigStep (AnsInt(eval_bin_op_int1 bin_op n2 n)::xxs, g, cs, d)
																				| _ -> raise(INVALID_SYNTAX "Invalid Arguments"))
																	| 1 -> (match xs with 
																				AnsInt(n2)::xxs -> bigStep (AnsBool(eval_bin_op_int2 bin_op n2 n)::xxs, g, cs, d)))
																				| _ -> raise(INVALID_SYNTAX "Invalid Arguments"))
							| AnsBool(b)::xs -> (match op with
													  NOT -> bigStep (AnsBool(not(b))::xs, g, cs, d)
													| bin_op -> (match xs with AnsBool(b2)::xxs -> bigStep (AnsBool(eval_bin_op_bool bin_op b2 b)::xxs, g, cs, d)))	
			                | _ -> raise(INVALID_SYNTAX "Invalid Arguments")

 		| _ -> raise(INVALID_SYNTAX "Wrong Input") ;;


let secd_machine (e: exp) = bigStep ([], [], (compile e), []) ;;


(* secd_machine (App(Clos("y",(Divide(App(Clos("x",Mult(Var("x"), Int(2))), Add(Int(3),Int(4))), Var("y")))),Sub(Int(9), Int(2))));; *)

secd_machine(Proj(Int(2), NTuple([Int(12); Int(121); Int(33)])));;

secd_machine(LetDE(Par([Assign(Var("a"),Int(1)); Assign(Var("b"),Int(2)); Assign(Var("c"),Int(3))]),Add(Add(Var("a"),Var("b")),Mult(Var("c"),Int(2)))));;

secd_machine(Ifte(GreatEq(Int(4),Int(2)),Add(Int(1),Int(3)),Sub(Int(1),Int(3))));;

secd_machine(LetDE(Seq([Par([Assign(Var("f"),Bool(false))]); Seq([Assign(Var("a"),Int(1)); Assign(Var("b"),Int(2)); Assign(Var("c"),Int(3))])]),Add(Add(Var("a"),Var("b")),Mult(Var("c"),Int(2)))));;










