
module Solver = Z3.Solver
module Expr = Z3.Expr
module Boolean = Z3.Boolean
module Symbol = Z3.Symbol
module Sort = Z3.Sort
module FuncDecl = Z3.FuncDecl
module Arithmetic = Z3.Arithmetic
module BitVector = Z3.BitVector
module Quantifier = Z3.Quantifier
module Model = Z3.Model
module Z3Array = Z3.Z3Array
module Datatype = Z3.Datatype
module Constructor = Z3.Datatype.Constructor
module Seq = Z3.Seq
module FuncInterp = Z3.Model.FuncInterp

let print_check (solver: Solver.solver) (l: Expr.expr list): unit =
	Printf.printf "%s\n" (Solver.string_of_status (Solver.check solver l))

let print_model (solver: Solver.solver): unit = 
	match (Solver.get_model solver) with
	| Some m -> Printf.printf "%s\n" (Model.to_string m)
	| None -> Printf.printf "no model\n"		


let print_proof (solver: Solver.solver): unit = 
	try
		match (Solver.get_proof solver) with
		| Some p -> Printf.printf "%s\n" (Expr.to_string p)
		| None -> Printf.printf "no proof\n"		
	with
	| _ -> Printf.printf "no proof\n"
		


let solve (ctx: Z3.context) (assertions: Expr.expr list): unit =
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver assertions;
	print_check solver [];
	print_model solver

let prove (ctx: Z3.context) (assertions: Expr.expr list): unit =
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver assertions;
	print_check solver [];
	print_model solver;
	print_proof solver

(*
	from z3 import *
	Tie, Shirt = Bools('Tie Shirt')
	s = Solver()
	s.add(Or(Tie, Shirt), 
	    Or(Not(Tie), Shirt), 
	    Or(Not(Tie), Not(Shirt)))
	print(s.check())
	print(s.model())
*)
let test1 (ctx: Z3.context): unit = 
	let tie: Symbol.symbol = Symbol.mk_string ctx "Tie" in
	let shirt: Symbol.symbol = Symbol.mk_string ctx "Shirt" in
	let bool_sort: Sort.sort = Boolean.mk_sort ctx in
	let tie_expr: Expr.expr = Expr.mk_const ctx tie bool_sort in 
	let shirt_expr: Expr.expr = Expr.mk_const ctx shirt bool_sort in 
	solve ctx [
		Boolean.mk_or ctx [tie_expr; shirt_expr]; 
		(* Boolean.mk_or ctx [(Boolean.mk_not ctx shirt_expr); tie_expr]; unsatisfiable *)
		Boolean.mk_or ctx [(Boolean.mk_not ctx tie_expr); shirt_expr];
		Boolean.mk_or ctx [(Boolean.mk_not ctx tie_expr); (Boolean.mk_not ctx shirt_expr)]
	]

(*
	Z = IntSort()
	f = Function('f', Z, Z)
	x, y, z = Ints('x y z')
	A = Array('A', Z, Z)
	fml = Implies(x + 2 == y, f(Store(A, x, 3)[y - 2]) == f(y - x + 1))
	solve(Not(fml))
*)
let test2 (ctx: Z3.context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let f: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [int_sort] int_sort in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	(* unused variable z *)
	let z: Expr.expr = Arithmetic.Integer.mk_const_s ctx "z" in
	let arr: Expr.expr = Z3Array.mk_const_s ctx "arr" int_sort int_sort in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let two: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 2 in
	let three: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 3 in
	let implies_l: Expr.expr = Boolean.mk_eq ctx (Arithmetic.mk_add ctx [x; two]) y in
	(* f(Store(A, x, 3)[y - 2]) *)
	let temp1: Expr.expr = 
		FuncDecl.apply f [(Z3Array.mk_select ctx (Z3Array.mk_store ctx arr x three) (Arithmetic.mk_sub ctx [y; two]))] in
	(* f(y - x + 1) *)
	let temp2: Expr.expr = FuncDecl.apply f [Arithmetic.mk_add ctx [Arithmetic.mk_sub ctx [y; x]; one]] in
	let implies_r: Expr.expr = Boolean.mk_eq ctx temp1 temp2 in
	let fml: Expr.expr = Boolean.mk_implies ctx implies_l implies_r in
	solve ctx [Boolean.mk_not ctx fml]


(*
	from z3 import *
	x, y = Ints('x y')
	s = Solver()
	s.add((x % 4) + 3 * (y / 2) > x - y)
	print(s.sexpr())
*)
let test3 (ctx: Z3.context): unit =
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	let two: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 2 in
	let three: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 3 in
	let four: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 4 in
	(* x % 4 *)
	let temp1: Expr.expr = Arithmetic.Integer.mk_mod ctx x four in
	(* 3 * (y / 2) *)
	let temp2: Expr.expr = Arithmetic.mk_mul ctx [three; (Arithmetic.mk_div ctx y two)] in
	(* x - y *)
	let temp3: Expr.expr = Arithmetic.mk_sub ctx [x; y] in
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver [Arithmetic.mk_gt ctx (Arithmetic.mk_add ctx [temp1; temp2]) temp3];
	Printf.printf "%s\n" (Solver.to_string solver)

(*
	S = DeclareSort('S')
	s = Const('s', S)
	solve(ForAll(s, s != s))
*)
let test4 (ctx: Z3.context): unit =
	let s_sort: Sort.sort = Sort.mk_uninterpreted_s ctx "S" in
	let s: Expr.expr = Expr.mk_const_s ctx "s" s_sort in
	let q: Quantifier.quantifier = 
		Quantifier.mk_forall_const ctx [s] (Boolean.mk_not ctx (Boolean.mk_eq ctx s s)) 
		(Some 1) [] [] None None in
	solve ctx [Quantifier.expr_of_quantifier q]


(*
	Z = IntSort()
	B = BoolSort()
	f = Function('f', B, Z)
	g = Function('g', Z, B)
	a = Bool('a')
	solve(g(1+f(a)))
*)
let test5 (ctx: Z3.context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let bool_sort: Sort.sort = Boolean.mk_sort ctx in
	let f: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [bool_sort] int_sort in
	let g: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "g" [int_sort] bool_sort in
	let a: Expr.expr = Boolean.mk_const_s ctx "a" in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let fml: Expr.expr = FuncDecl.apply g [Arithmetic.mk_add ctx [one; (FuncDecl.apply f [a])]] in
	solve ctx [fml]

(*
	x = Int('x')
	y = Int('y')
	n = x + y >= 3
	print("num args: ", n.num_args())
	print("children: ", n.children())
	print("1st child:", n.arg(0))
	print("2nd child:", n.arg(1))
	print("operator: ", n.decl())
	print("op name:  ", n.decl().name())
*)
let test6 (ctx: Z3.context): unit =
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	let three: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 3 in
	let n: Expr.expr = Arithmetic.mk_ge ctx (Arithmetic.mk_add ctx [x; y]) three in
	Printf.printf "num args: %s\n" (string_of_int (Expr.get_num_args n));
	let str: string = List.fold_left (fun a b -> (a ^ (Expr.to_string b) ^ "; ")) "[" (Expr.get_args n) in
	Printf.printf "children: %s\n" ((String.sub str 0 ((String.length str) - 2)) ^ "]");
	Printf.printf "1st child: %s\n" (Expr.to_string (List.nth (Expr.get_args n) 0));
	Printf.printf "2nd child: %s\n" (Expr.to_string (List.nth (Expr.get_args n) 1));
	Printf.printf "operator: %s\n" (FuncDecl.to_string (Expr.get_func_decl n));
	Printf.printf "op name: %s\n" (Symbol.to_string (FuncDecl.get_name (Expr.get_func_decl n)))

(*
	solve([y == x + 1, ForAll([y], Implies(y <= 0, x < y))])
	<==> alpha conversion
	solve([y == x + 1, ForAll([z], Implies(z <= 0, x < z))])
	unsatisfiable
*)
let test7 (ctx: Z3.context): unit =
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in	
	let zero: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 0 in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let q: Quantifier.quantifier = 
		Quantifier.mk_forall_const ctx [y] 
		(Boolean.mk_implies ctx (Arithmetic.mk_le ctx y zero) (Arithmetic.mk_lt ctx x y)) 
		(Some 1) [] [] None None in
	solve ctx [
		Boolean.mk_eq ctx y (Arithmetic.mk_add ctx [x; one]); 
		Quantifier.expr_of_quantifier q
	]

(*
	solve([y == x + 1, ForAll([y], Implies(y <= 0, x > y))])
	<==> alpha conversion
	solve([y == x + 1, ForAll([z], Implies(z <= 0, x > z))])
	unsatisfiable
*)
let test8 (ctx: Z3.context): unit =
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in	
	let zero: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 0 in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let q: Quantifier.quantifier = 
		Quantifier.mk_forall_const ctx [y] 
		(Boolean.mk_implies ctx (Arithmetic.mk_le ctx y zero) (Arithmetic.mk_gt ctx x y)) 
		(Some 1) [] [] None None in
	solve ctx [
		Boolean.mk_eq ctx y (Arithmetic.mk_add ctx [x; one]); 
		Quantifier.expr_of_quantifier q
	]

(*
	m, m1 = Array('m', Z, Z), Array('m1', Z, Z)
	def memset(lo, hi, y, m):
		return Lambda([x], If(And(lo <= x, x <= hi), y, Select(m, x)))
	solve([m1 == memset(1, 700, z, m), Select(m1, 6) != z])
*)
let test9 (ctx: Z3.context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let z: Expr.expr = Arithmetic.Integer.mk_const_s ctx "z" in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let sevenhundred: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 700 in
	let six: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 6 in
	(* let eighthundred: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 800 in *)
	let m: Expr.expr = Z3Array.mk_const_s ctx "m" int_sort int_sort in
	let m1: Expr.expr = Z3Array.mk_const_s ctx "m1" int_sort int_sort in
	let memset (lo: Expr.expr) (hi: Expr.expr) (y: Expr.expr) (m: Expr.expr): Expr.expr = 
		let p: Expr.expr = Boolean.mk_and ctx [Arithmetic.mk_le ctx lo x; Arithmetic.mk_le ctx x hi] in
		let q = Quantifier.mk_lambda_const ctx [x] (Boolean.mk_ite ctx p y (Z3Array.mk_select ctx m x)) in
		Quantifier.expr_of_quantifier q
	in
	(* m1 == memset(1, 700, z, m) *)
	let temp1: Expr.expr = Boolean.mk_eq ctx m1 (memset one sevenhundred z m) in
	(* Select(m1, 6) != z *)
	let temp2: Expr.expr = Boolean.mk_not ctx (Boolean.mk_eq ctx (Z3Array.mk_select ctx m1 six) z) in
	(* if we change 6 to 800, then satisfiable *)
	(* let temp2: Expr.expr = Boolean.mk_not ctx (Boolean.mk_eq ctx (Z3Array.mk_select ctx m1 eighthundred) z) in *)
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver [temp1; temp2]; (* unsatifiable *)
	print_check solver [];
	print_model solver


(*
	Q = Array('Q', Z, B)
	prove(Implies(ForAll(Q, Implies(Select(Q, x), Select(Q, y))), x == y))
*)
let test10 (ctx: Z3.context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let bool_sort: Sort.sort = Boolean.mk_sort ctx in
	let q_arr: Expr.expr = Z3Array.mk_const_s ctx "Q" int_sort bool_sort in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	let imp: Expr.expr = Boolean.mk_implies ctx (Z3Array.mk_select ctx q_arr x) (Z3Array.mk_select ctx q_arr y) in
	let q: Quantifier.quantifier = Quantifier.mk_forall_const ctx [q_arr] imp (Some 1) [] [] None None in
	let to_prove: Expr.expr = Boolean.mk_implies ctx (Quantifier.expr_of_quantifier q) (Boolean.mk_eq ctx x y) in
	prove ctx [to_prove]

(*
	S = DeclareSort('S')
	f = Function('f', S, S)
	x = Const('x', S)
	solve(f(f(x)) == x, f(f(f(x))) == x)
	solve(f(f(x)) == x, f(f(f(x))) == x, f(x) != x)
*)
let test11 (ctx: Z3.context): unit =
	let s_sort: Sort.sort = Sort.mk_uninterpreted_s ctx "S" in
	let f_func: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [s_sort] s_sort in
	let x: Expr.expr = Expr.mk_const_s ctx "x" s_sort in
	let f (x: Expr.expr): Expr.expr = (FuncDecl.apply f_func [x]) in
	solve ctx [
		Boolean.mk_eq ctx (f (f x)) x; 
		Boolean.mk_eq ctx (f (f (f x))) x
	];
	solve ctx [
		Boolean.mk_eq ctx (f (f x)) x; 
		Boolean.mk_eq ctx (f (f (f x))) x; 
		Boolean.mk_not ctx (Boolean.mk_eq ctx (f x) x)
	]


let mk_neq (ctx: Z3.context) (a: Expr.expr) (b: Expr.expr): Expr.expr = 
	Boolean.mk_not ctx (Boolean.mk_eq ctx a b)

let reals (ctx: Z3.context) (s_li: string list): Expr.expr list = 
	List.map (fun a -> Arithmetic.Real.mk_const_s ctx a) s_li

(*
	S = DeclareSort('S')
	a, b, c, d, e, s, t = Consts('a b c d e s t', S)
	f = Function('f', S, S, S)
	g = Function('g', S, S)
	solve([a == b, b == c, d == e, b == s, d == t, f(a, g(d)) != f(g(e), b)])
*)
let test12 (ctx: Z3.context): unit =
	let s_sort: Sort.sort = Sort.mk_uninterpreted_s ctx "S" in
	let a: Expr.expr = Expr.mk_const_s ctx "a" s_sort in
	let b: Expr.expr = Expr.mk_const_s ctx "b" s_sort in
	let c: Expr.expr = Expr.mk_const_s ctx "c" s_sort in
	let d: Expr.expr = Expr.mk_const_s ctx "d" s_sort in
	let e: Expr.expr = Expr.mk_const_s ctx "e" s_sort in
	let s: Expr.expr = Expr.mk_const_s ctx "s" s_sort in
	let t: Expr.expr = Expr.mk_const_s ctx "t" s_sort in
	let f_func: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [s_sort; s_sort] s_sort in
	let g_func: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "g" [s_sort] s_sort in
	let f (x: Expr.expr) (y: Expr.expr): Expr.expr = (FuncDecl.apply f_func [x; y]) in
	let g (x: Expr.expr): Expr.expr = (FuncDecl.apply g_func [x]) in
	solve ctx [
		Boolean.mk_eq ctx a b; Boolean.mk_eq ctx b c;
		Boolean.mk_eq ctx d e; 
		Boolean.mk_eq ctx b s; 
		Boolean.mk_eq ctx d t;
		mk_neq ctx (f a (g d)) (f (g e) b)
	]


(*
	x, y = Reals('x y')
	solve([x >= 0, Or(x + y <= 2, x + 2*y >= 6), Or(x + y >= 2, x + 2*y > 4)])
*)
let test13 (ctx: Z3.context): unit =
	let zero: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 0 in
	let two: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 2 in
	let four: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 4 in
	let six: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 6 in
	let x: Expr.expr = Arithmetic.Real.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Real.mk_const_s ctx "y" in
	let temp1: Expr.expr = Arithmetic.mk_add ctx [x; y] in
	let temp2: Expr.expr = Arithmetic.mk_add ctx [x; Arithmetic.mk_mul ctx [two; y]] in
	solve ctx [
		Arithmetic.mk_ge ctx x zero; 
		Boolean.mk_or ctx [(Arithmetic.mk_le ctx temp1 two); (Arithmetic.mk_ge ctx temp2 six)];
		Boolean.mk_or ctx [(Arithmetic.mk_ge ctx temp1 two); (Arithmetic.mk_gt ctx temp2 four)]
	]


(*
	A = Array('A', IntSort(), IntSort())
	solve(A[x] == x, Store(A, x, y) == A)
*)
let test14 (ctx: Z3.context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	let a_arr: Expr.expr = Z3Array.mk_const_s ctx "A" int_sort int_sort in
	solve ctx [
		Boolean.mk_eq ctx (Z3Array.mk_select ctx a_arr x) x;
		Boolean.mk_eq ctx (Z3Array.mk_store ctx a_arr x y) a_arr
	]
	
(*
	check:

	store:
	s.add(Store(a, i, v)[j] == If(i == j, v, a[j]))
	s.add(Store(a, i, v)[i] == v)

	extensionality:
	s.add(Implies(ForAll(i, a[i] == b[i]), a == b))
	s.add(Implies(a[Ext(a, b)] == b[Ext(a, b)], a == b))
*)
let test15 (ctx: Z3.context): unit = 
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let i: Expr.expr = Arithmetic.Integer.mk_const_s ctx "i" in
	let j: Expr.expr = Arithmetic.Integer.mk_const_s ctx "j" in
	let v: Expr.expr = Arithmetic.Integer.mk_const_s ctx "v" in
	let a: Expr.expr = Z3Array.mk_const_s ctx "a" int_sort int_sort in
	let b: Expr.expr = Z3Array.mk_const_s ctx "b" int_sort int_sort in
	(* Store(a, i, v)[j] *)
	let temp1: Expr.expr = Z3Array.mk_select ctx (Z3Array.mk_store ctx a i v) j in 
	(* If(i == j, v, a[j]) *)
	let temp2: Expr.expr = Boolean.mk_ite ctx (Boolean.mk_eq ctx i j) v (Z3Array.mk_select ctx a j) in
	(* Store(a, i, v)[i] *)
	let temp3: Expr.expr = Z3Array.mk_select ctx (Z3Array.mk_store ctx a i v) i in
	(* ForAll(i, a[i] == b[i]) *)
	let q: Quantifier.quantifier = 
		Quantifier.mk_forall_const ctx [i] 
		(Boolean.mk_eq ctx (Z3Array.mk_select ctx a i) (Z3Array.mk_select ctx b i)) 
		(Some 1) [] [] None None in
	(* a == b *)
	let temp4: Expr.expr = Boolean.mk_eq ctx a b in
	(* Ext(a, b) *)
	let ext: Expr.expr = Z3Array.mk_array_ext ctx a b  in
	(* a[Ext(a, b)] == b[Ext(a, b)] *)
	let temp5: Expr.expr = Boolean.mk_eq ctx (Z3Array.mk_select ctx a ext) (Z3Array.mk_select ctx b ext) in
	(* unsatisfiable, because these four axioms should all be true *)
	solve ctx [
		Boolean.mk_not ctx (Boolean.mk_and ctx [
			Boolean.mk_eq ctx temp1 temp2;
			Boolean.mk_eq ctx temp3 v;
			Boolean.mk_implies ctx (Quantifier.expr_of_quantifier q) temp4;
			Boolean.mk_implies ctx temp5 temp4
		])
	]	

(*
	def is_power_of_two(x):
		return And(x != 0, 0 == (x & (x - 1)))
	x = BitVec('x', 4)
	prove(is_power_of_two(x) == Or([x == 2**i for i in range(4)]))
*)
let test16 (ctx: Z3.context): unit =
	let zero: Expr.expr = Expr.mk_numeral_int ctx 0 (BitVector.mk_sort ctx 4) in
	let one: Expr.expr = Expr.mk_numeral_int ctx 1 (BitVector.mk_sort ctx 4) in
	let two: Expr.expr = Expr.mk_numeral_int ctx 2 (BitVector.mk_sort ctx 4) in
	let four: Expr.expr = Expr.mk_numeral_int ctx 4 (BitVector.mk_sort ctx 4) in
	let eight: Expr.expr = Expr.mk_numeral_int ctx 8 (BitVector.mk_sort ctx 4) in
	let is_power_of_two (x: Expr.expr): Expr.expr = 
		Boolean.mk_and ctx [
			mk_neq ctx x zero;
			Boolean.mk_eq ctx zero (BitVector.mk_and ctx x (BitVector.mk_sub ctx x one))
		]
	in
	let x: Expr.expr = BitVector.mk_const_s ctx "x" 4 in 
	prove ctx [
		Boolean.mk_not ctx (Boolean.mk_eq ctx (is_power_of_two x) (Boolean.mk_or ctx [
																				Boolean.mk_eq ctx x one;
																				Boolean.mk_eq ctx x two;
																				Boolean.mk_eq ctx x four;
																				Boolean.mk_eq ctx x eight
																			]))
	]

(*
	v = BitVec('v',32)
	mask = v >> 31
	prove(If(v > 0, v, -v) == (v + mask) ^ mask)
*)
let test17 (ctx: Z3.context): unit =
	let zero: Expr.expr = Expr.mk_numeral_int ctx 0 (BitVector.mk_sort ctx 32) in
	let thirtyone: Expr.expr = Expr.mk_numeral_int ctx 31 (BitVector.mk_sort ctx 32) in
	let v: Expr.expr = BitVector.mk_const_s ctx "v" 32 in
	let mask: Expr.expr = BitVector.mk_ashr ctx v thirtyone in
	(* If(v > 0, v, -v) *)
	let temp1: Expr.expr = Boolean.mk_ite ctx (BitVector.mk_sgt ctx v zero) v (BitVector.mk_neg ctx v) in
	(* (v + mask) ^ mask <==> v ^ mask ^ mask *)
	let temp2: Expr.expr = BitVector.mk_xor ctx (BitVector.mk_add ctx v mask) mask in
	prove ctx [Boolean.mk_eq ctx temp1 temp2]

(*
	x = FP('x', FPSort(3, 4))
	print(10 + x)
*)
let test18 (ctx: Z3.context): unit = ()(*
	let fp_sort: Sort.sort = FloatingPoint.mk_sort ctx 3 4 in
	let x: Expr.expr = FloatingPoint.mk_const_s ctx "x" fp_sort in
	let ten: Expr.expr = FloatingPoint.mk_numeral_f ctx 10. fp_sort in
	let temp: Expr.expr = FloatingPoint.mk_add ctx (FloatingPoint.RoundingMode.mk_rtz ctx) x ten in
	Printf.printf "%s\n" (FloatingPoint.numeral_to_string temp)*)

(*
	Tree = Datatype('Tree')
	Tree.declare('Empty')
	Tree.declare('Node', ('left', Tree), ('data', Z), ('right', Tree))
	Tree = Tree.create()
	t = Const('t', Tree)
	solve(t != Tree.Empty)

	prove(t != Tree.Node(t, 0, t))
*)
(*
	let create (ctx:context) 
		(name:Symbol.symbol) 
		(recognizer:Symbol.symbol) 
		(field_names:Symbol.symbol list) 
		(sorts:Sort.sort option list) 
		(sort_refs:int list)
	https://github.com/Z3Prover/z3/issues/4264
*)
let test19 (ctx: Z3.context): unit = 
	let zero: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 0 in
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let tree_sym: Symbol.symbol = Symbol.mk_string ctx "Tree" in
	let left_sym: Symbol.symbol = Symbol.mk_string ctx "left" in
	let right_sym: Symbol.symbol = Symbol.mk_string ctx "right" in
	let data_sym: Symbol.symbol = Symbol.mk_string ctx "data" in
	let empty: Constructor.constructor = 
	Datatype.mk_constructor ctx tree_sym (Symbol.mk_string ctx "is-empty") [] [] [] and
	node: Constructor.constructor = 
	Datatype.mk_constructor ctx tree_sym (Symbol.mk_string ctx "is-node") 
	[left_sym; data_sym; right_sym] [None; Some int_sort; None] [0; -1; 0] 
	in
	let tree_sort: Sort.sort = Datatype.mk_sort_s ctx "tree_sort" [empty; node] in
	let t: Expr.expr = Expr.mk_const_s ctx "t" tree_sort in
	let cons: FuncDecl.func_decl list = Datatype.get_constructors tree_sort in
	let empty_cons: FuncDecl.func_decl = List.nth cons 0 in
	let node_cons: FuncDecl.func_decl = List.nth cons 1 in
	List.iter (fun a -> Printf.printf "%s\n" (FuncDecl.to_string a)) (Datatype.get_constructors tree_sort);
	solve ctx [mk_neq ctx t (FuncDecl.apply empty_cons [])];
	prove ctx [mk_neq ctx t (FuncDecl.apply node_cons [t; zero; t])]
	(* prove ctx [Boolean.mk_eq ctx t (FuncDecl.apply node_cons [t; zero; t])] unsatisfiable *)


(*
	s, t, u = Strings('s t u')
	prove(Implies(And(PrefixOf(s, t), SuffixOf(u, t), 
								Length(t) == Length(s) + Length(u)), 
								t == Concat(s, u)))
*)
let test20 (ctx: Z3.context): unit = 
	let string_sort: Sort.sort = Seq.mk_string_sort ctx in
	let s: Expr.expr = Expr.mk_const_s ctx "s" string_sort in
	let t: Expr.expr = Expr.mk_const_s ctx "t" string_sort in
	let u: Expr.expr = Expr.mk_const_s ctx "u" string_sort in
	let s_len: Expr.expr = Seq.mk_seq_length ctx s in
	let t_len: Expr.expr = Seq.mk_seq_length ctx t in
	let u_len: Expr.expr = Seq.mk_seq_length ctx u in
	(* And(PrefixOf(s, t), SuffixOf(u, t), Length(t) == Length(s) + Length(u)) *)
	let implies_l: Expr.expr = Boolean.mk_and ctx [
		Seq.mk_seq_prefix ctx s t;
		Seq.mk_seq_suffix ctx u t;
		Boolean.mk_eq ctx t_len (Arithmetic.mk_add ctx [s_len; u_len])
	] in
	(* t == Concat(s, u) *)
	let implies_r: Expr.expr = Boolean.mk_eq ctx t (Seq.mk_seq_concat ctx [s; u]) in
	(*
	this is unsatisfiable:
	proof ctx [Boolean.mk_not ctx (Boolean.mk_iff ctx implies_l implies_r)];
	*)
	prove ctx [Boolean.mk_implies ctx implies_l implies_r]

(*
	s, t = Consts('s t', SeqSort(IntSort()))
	solve(Concat(s, Unit(IntVal(2))) == Concat(Unit(IntVal(1)), t))
	prove(Concat(s, Unit(IntVal(2))) != Concat(Unit(IntVal(1)), s))
*)
let test21 (ctx: Z3.context): unit =
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in 
	let element_sort: Sort.sort = Seq.mk_seq_sort ctx int_sort in
	let s: Expr.expr = Expr.mk_const_s ctx "s" element_sort in
	let t: Expr.expr = Expr.mk_const_s ctx "t" element_sort in
	let one: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 1 in
	let two: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 2 in
	(* Concat(s, Unit(IntVal(2))) *)
	let temp1: Expr.expr = Seq.mk_seq_concat ctx [s; Seq.mk_seq_unit ctx two] in
	(* Concat(Unit(IntVal(1)), t) *)
	let temp2: Expr.expr = Seq.mk_seq_concat ctx [Seq.mk_seq_unit ctx one; t] in
	(* Concat(Unit(IntVal(1)), s) *)
	let temp3: Expr.expr = Seq.mk_seq_concat ctx [Seq.mk_seq_unit ctx one; s] in
	solve ctx [Boolean.mk_eq ctx temp1 temp2];
	prove ctx [mk_neq ctx temp1 temp3]

(*
	s = Solver()
	A = DeclareSort()
	R = Function('R', A, A, B)
	x, y, z = Consts('x y z', A)

	# R = PartialOrder(A, 0)
	s.Add(ForAll([x], R(x, x)))  
	s.Add(ForAll([x,y], Implies(And(R(x, y), R(y, x)), x == y)))
	s.Add(ForAll([x,y,z], Implies(And(R(x, y), R(y, z)), R(x, z))))
	
	# R = TotalLinearOrder(A, 0)
	s.Add(ForAll([x], R(x, x)))  
	s.Add(ForAll([x,y], Implies(And(R(x, y), R(y, x)), x == y)))
	s.Add(ForAll([x,y,z], Implies(And(R(x, y), R(y, z)), R(x, z))))
	s.Add(ForAll([x,y], Or(R(x, y), R(y, x))))

	# R = TreeOrder(A, 0)
	s.Add(ForAll([x], R(x, x)))  
	s.Add(ForAll([x,y], Implies(And(R(x, y), R(y, x)), x == y)))
	s.Add(ForAll([x,y,z], Implies(And(R(x, y), R(y, z)), R(x, z))))
	s.Add(ForAll([x,y,z], Implies(And(R(x, y), R(x, z)), Or(R(y, z), R(z, y)))))

	# R = PiecewiseLinearOrder(A, 0)
	s.Add(ForAll([x], R(x, x)))  
	s.Add(ForAll([x,y], Implies(And(R(x, y), R(y, x)), x == y)))
	s.Add(ForAll([x,y,z], Implies(And(R(x, y), R(y, z)), R(x, z))))
	s.Add(ForAll([x,y,z], Implies(And(R(x, y), R(x, z)), Or(R(y, z), R(z, y)))))
	s.Add(ForAll([x,y,z], Implies(And(R(y, x), R(z, x)), Or(R(y, z), R(z, y)))))

	# No same support in OCaml bindings
*)
let test22 (ctx: Z3.context): unit = ()

(*
	R = Function('R', A, A, B)
	TC_R = TransitiveClosure(R)
	TRC_R = TransitiveReflexiveClosure(R)
	s = Solver()
	a, b, c = Consts('a b c', A)
	s.add(R(a, b))
	s.add(R(b, c))
	s.add(Not(TC_R(a, c)))
	print(s.check())   # produces unsat

	# No same support in OCaml bindings
*)
let test23 (ctx: Z3.context): unit = ()

(*
	p, q, r = Bools('p q r')
	s = Solver()
	s.add(Implies(p, q))
	s.add(Not(q))
	print(s.check())
	s.push()
	s.add(p)
	print(s.check())
	s.pop()
	print(s.check())
*)
let test24 (ctx: Z3.context): unit = 
	let p: Expr.expr = Boolean.mk_const_s ctx "p" in
	let q: Expr.expr = Boolean.mk_const_s ctx "q" in
	let r: Expr.expr = Boolean.mk_const_s ctx "r" in
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver [Boolean.mk_implies ctx p q];
	(* inside the solver: [p->q] *)
	Solver.add solver [Boolean.mk_not ctx q];
	(* inside the solver: [p->q; q] *)
	print_check solver []; (* satisfiable *)
	Solver.push solver;
	(* inside the solver: [p->q; q; ()] *)
	Solver.add solver [p];
	(* inside the solver: [p->q; q; (); p] *)
	print_check solver []; (* unsatisfiable *)
	(*
	Solver.push solver;
	(* inside the solver: [p->q; q; (); p; ()] *)
	Solver.add solver [p];
	(* inside the solver: [p->q; q; (); p; (); p] *)
	print_check solver []; (* unsatisfiable *)
	Solver.pop solver 1; (* Backtracks one backtracking point. *)
	(* only pop one, inside the solver: [p->q; q; (); p] *)
	(* if pop two, inside the solver: [p->q; q] *)
	print_check solver []; (* unsatisfiable *)
	*)
	Solver.pop solver 1; (* Backtracks one backtracking point. *)
	(* inside the solver: [p->q; q] *)
	print_check solver [] (* satisfiable *)


(*
	p, q = Bools('p q')
	s = Solver()

	s.add(Implies(p, q))
	s.add(Not(q))
	print(s.check(p))

	s.add(Not(q))
	s.assert_and_track(q, p) # p -> q; p
	print(s.check())
*)
let test25 (ctx: Z3.context): unit = 
	let p: Expr.expr = Boolean.mk_const_s ctx "p" in
	let q: Expr.expr = Boolean.mk_const_s ctx "q" in
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver [Boolean.mk_implies ctx p q];
	Solver.add solver [Boolean.mk_not ctx q];
	print_check solver [p]; (* unsatisfiable *)
	Solver.reset solver;
	Solver.add solver [Boolean.mk_not ctx q];
	Solver.assert_and_track solver q p;
	print_check solver [] (* unsatisfiable *)

(*
	p, q, r, v = Bools('p q r v')
	s = Solver()
	s.add(Not(q))
	s.assert_and_track(q, p)
	s.assert_and_track(r, v)
	print(s.check())
	print(s.unsat_core()) # the core is only available after check
*)
let test26 (ctx: Z3.context): unit =
	let p: Expr.expr = Boolean.mk_const_s ctx "p" in
	let q: Expr.expr = Boolean.mk_const_s ctx "q" in
	let r: Expr.expr = Boolean.mk_const_s ctx "r" in
	let v: Expr.expr = Boolean.mk_const_s ctx "v" in
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver [Boolean.mk_not ctx q];
	Solver.assert_and_track solver q p;
	Solver.assert_and_track solver r v;
	print_check solver []; (* unsatisfiable *)
	List.iter (fun a -> Printf.printf "%s\n" (Expr.to_string a)) (Solver.get_unsat_core solver)	(* only p *)

(*
	By default solvers do not return minimal cores.
	def set_core_minimize(s):
		s.set("sat.core.minimize","true")  # For Bit-vector theories
		s.set("smt.core.minimize","true")  # For general SMT
*)
let set_core_minimize (solver: Solver.solver): unit = ()

(*
	f = Function('f', Z, Z)
	x, y = Ints('x y')
	s.add(f(x) > y, f(f(y)) == y)
	print(s.check())
	print(s.model())

	m = s.model()
	for d in m:
	    print(d, m[d])

	num_entries = m[f].num_entries()
	for i in range(num_entries):
	    print(m[f].entry(i))
	print("else", m[f].else_value())

	print(m.eval(x), m.eval(f(3)), m.eval(f(4)))
*)
let test27 (ctx: Z3.context): unit =
	let three: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 3 in
	let four: Expr.expr = Arithmetic.Integer.mk_numeral_i ctx 4 in
	let int_sort: Sort.sort = Arithmetic.Integer.mk_sort ctx in
	let f: FuncDecl.func_decl = FuncDecl.mk_func_decl_s ctx "f" [int_sort] int_sort in
	let x: Expr.expr = Arithmetic.Integer.mk_const_s ctx "x" in
	let y: Expr.expr = Arithmetic.Integer.mk_const_s ctx "y" in
	(* f(x) > y *)
	let temp1: Expr.expr = Arithmetic.mk_gt ctx (FuncDecl.apply f [x]) y in
	(* f(f(y)) == y *)
	let temp2: Expr.expr = Boolean.mk_eq ctx (FuncDecl.apply f [(FuncDecl.apply f [y])]) y in
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver [temp1; temp2];
	print_check solver []; (* satisfiable *)
	print_model solver;

	let model_completion: bool = false in

	let m: Model.model = 
	(match (Solver.get_model solver) with
	| Some m -> m
	| None -> raise (Failure "no model")) in

	List.iter (fun a -> Printf.printf "decl: %s\n" (FuncDecl.to_string a)) (Model.get_decls m);
	List.iter (fun a -> Printf.printf "const_decl: %s\n" (FuncDecl.to_string a)) (Model.get_const_decls m);
	List.iter (fun a -> Printf.printf "func_decl: %s\n" (FuncDecl.to_string a)) (Model.get_func_decls m);

	let f_itp: FuncInterp.func_interp = 
	(match (Model.get_func_interp m f) with
	| Some itp -> itp
	| None -> raise (Failure "no model")) in
	List.iter 
	(fun a -> Printf.printf "entry: %s\n" (Model.FuncInterp.FuncEntry.to_string a)) 
	(Model.FuncInterp.get_entries f_itp);
	Printf.printf "else: %s\n" (Expr.to_string (Model.FuncInterp.get_else f_itp));

	(* m.eval(x), m.eval(f(3)), m.eval(f(4)) *)
	let e1: Expr.expr = 
	(match Model.eval m x model_completion with
	| Some e -> e
	| _ -> raise (Failure "cannot eval")) in
	Printf.printf "m.eval(x): %s\n" (Expr.to_string e1);

	let e2: Expr.expr = 
	(match Model.eval m (FuncDecl.apply f [three]) model_completion with
	| Some e -> e
	| _ -> raise (Failure "cannot eval")) in
	Printf.printf "m.eval(f(3)): %s\n" (Expr.to_string e2);

	let e3: Expr.expr = 
	(match Model.eval m (FuncDecl.apply f [four]) model_completion with
	| Some e -> e
	| _ -> raise (Failure "cannot eval")) in
	Printf.printf "m.eval(f(4)): %s\n" (Expr.to_string e3)

(*
	4.6.1. Statistics
	print(s.statistics())
	Printf.printf "%s\n" (Statistics.to_string (Solver.get_statistics solver))

	4.6.2. Proofs
	print(s.proof())
	print_proof solver

	4.6.3. Retrieving Solver State
	s.assertions()
	Solver.get_assertions : solver -> Expr.expr list
	Solver.get_assertions solver

	s.units()
	No same support in OCaml bindings 

	s.non_units()
	No same support in OCaml bindings

	s.sexpr()
	Solver.to_string solver

	4.6.4. Cloning Solver State
	s.translate(ctx)
	Solver.translate : solver -> context -> solver
	Solver.translate solver ctx

	4.6.5. Loading formulas
	s.from_string() and s.from_file() 

	First, use
	SMT.parse_smtlib2_string : context ->
	       string ->
	       Symbol.symbol list ->
	       Sort.sort list ->
	       Symbol.symbol list ->
	       FuncDecl.func_decl list -> AST.ASTVector.ast_vector
	Parse the given string using the SMT-LIB2 parser.
	Returns A conjunction of assertions in the scope (up to push/pop) at the end of the string.

	or

	SMT.parse_smtlib2_file : context ->
	       string ->
	       Symbol.symbol list ->
	       Sort.sort list ->
	       Symbol.symbol list ->
	       FuncDecl.func_decl list -> AST.ASTVector.ast_vector

	and then use

	AST.ASTVector.to_expr_list : ast_vector -> Expr.expr list

	and then

	Solver.add : solver -> Expr.expr list -> unit

*)
let test27 (ctx: Z3.context): unit = ()

(*
	a, b, c, d = Bools('a b c d')

	s = Solver()
	s.add(Implies(a, b), Implies(c, d))   # background formula
	print(s.consequences([a, c],          # assumptions
	                     [b, c, d]))      # what is implied?
	
	No same support in OCaml bindings
*)
let test28 (ctx: Z3.context): unit = ()

(*
	s = SolverFor("QF_FD")
	s.add()
	s.set("sat.restart.max", 100)
	def cube_and_conquer(s):
	    for cube in s.cube():
	       if len(cube) == 0:
	          return unknown
	       if is_true(cube[0]):
	          return sat     
	       is_sat = s.check(cube):
	       if is_sat == unknown:
	          s1 = s.translate(s.ctx)
	          s1.add(cube)
	          is_sat = cube_and_conquer(s1)
	       if is_sat != unsat:
	          return is_sat
	    return unsat

	No same support in OCaml bindings
*)
let test29 (ctx: Z3.context): unit = ()

(*
	TODO
	def block_model(s):
	    m = s.model()
	    s.add(Or([ f() != m[f] for f in m.decls() if f.arity() == 0]))  
*)
let test30 (ctx: Z3.context): unit = ()

(*
	def tt(s, f): 
	    return is_true(s.model().eval(f))

	def get_mss_base(s, ps):
	    if sat != s.check():
	       return []
	    mss = { q for q in ps if tt(s, q) }
	    return get_mss(s, mss, ps)

	def get_mss(s, mss, ps):
	    ps = ps - mss
	    backbones = set([])
	    while len(ps) > 0:
	       p = ps.pop()
	       if sat == s.check(mss | backbones | { p }):
	          mss = mss | { p } | { q for q in ps if tt(s, q) }
	          ps  = ps - mss
	       else:
	          backbones = backbones | { Not(p) }
	    return mss
*)
module Ex = struct 
	type t = Expr.expr 
	let compare a b: int = Z3.Expr.compare a b 
end
module ES = Set.Make(Ex)
let test31 (ctx: Z3.context): unit = 
	let tt (s: Solver.solver) (f: Expr.expr): bool = 
		(match (Solver.get_model s) with
		| Some m -> 
			(match (Model.eval m f false) with
			| Some ex -> Boolean.is_true ex
			| None -> raise (Failure "no expr"))
		| None -> raise (Failure "no model")) in
	let get_mss (s: Solver.solver) (mss: ES.t) (ps: ES.t): ES.t = 
		let ps_ref: ES.t ref = ref (ES.diff ps mss) in
		let mss_ref: ES.t ref = ref mss in
		let backbones_ref: ES.t ref = ref ES.empty in
		while (ES.cardinal !ps_ref) > 0 do
			let p: Expr.expr = ES.choose !ps_ref in
			if Solver.SATISFIABLE = Solver.check s ES.(empty |> add p |> union !mss_ref |> union !backbones_ref |> elements) then
			begin
				mss_ref := ES.(empty |> add p |> union !mss_ref |> union (ES.filter (fun q -> tt s q) !ps_ref));
				ps_ref := (ES.diff !ps_ref !mss_ref)
			end
			else backbones_ref := ES.(empty |> add (Boolean.mk_not ctx p) |> union !backbones_ref)
		done;
		!mss_ref
	in
	let get_mss_base (s: Solver.solver) (ps: ES.t): ES.t = 
		if Solver.SATISFIABLE <> Solver.check s [] then 
			ES.empty
		else
			let mss: ES.t = ES.filter (fun q -> tt s q) ps in
			get_mss s mss ps
	in ()

(*
	def ff(s, p): 
	    return is_false(s.model().eval(p))

	def marco(s, ps):
	    map = Solver()
	    set_core_minimize(s)
	    while map.check() == sat:
	        seed = {p for p in ps if not ff(map, p)}
	        if s.check(seed) == sat:
	           mss = get_mss(s, seed, ps)
	           map.add(Or(ps - mss))
	           yield "MSS", mss
	        else:
	           mus = s.unsat_core()
	           map.add(Not(And(mus)))
	           yield "MUS", mus
	TODO: What is set_core_minimize?
*)
let test32 (ctx: Z3.context): unit = ()

let _ = 
	let cfg = [("model", "true"); ("proof", "true")] in
	let ctx = (Z3.mk_context cfg) in
	test31 ctx
;;
