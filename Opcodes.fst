module Opcodes

open StackBC
open FStar.Seq

module Stack = StackBC
module Seq = FStar.Seq
module List = FStar.List.Tot

(* 76 A9 14 ... 88 AC *)


assume val hash_sha256: input : seq nat  -> Tot(r: seq nat{Seq.length r = 32} )
assume val hash_ripemd160: input : seq nat -> Tot(r: seq nat{Seq.length r = 20} )

(* 118 *)
val op_dup :  st_before: stackBC (seq nat){Stack.length st_before > 0 /\ Stack.capacity st_before > 0}  -> 
				line_before: seq nat{Seq.length line_before > 0 /\ (Seq.head line_before = 118)} 
				-> result_before : bool{result_before = true}
				-> Tot (st: stackBC (seq nat)
								{Stack.length st > 1 /\ 
								(Stack.index st 0) = (Stack.index st 1) /\ 
								Stack.length st = Stack.length st_before + 1}	* 
						line : seq nat {Seq.length line = Seq.length line_before - 1 } * result: bool) 

let op_dup  st_before line_before result_before = 
	let pop = Stack.pop st_before in 
	let element = fst pop in 
	let stack_after_pop = snd pop in 
	let stack_push1 = Stack.push stack_after_pop element in 
	let stack_push2 = Stack.push stack_push1 element in 
	let line = Seq.tail line_before in (stack_push2, line, result_before)

val op_hash160 : st_before : stackBC (seq nat){Stack.length st_before > 0} -> 
				line_before : seq nat {Seq.length line_before > 0 /\ (Seq.head line_before = 169)}
				-> result_before : bool {result_before = true}
				-> Tot(st: stackBC (seq nat)
						{Stack.length st > 0  /\
						Stack.index st 0 = (hash_ripemd160(hash_sha256 (Stack.index st_before 0))) /\
						Stack.length st = Stack.length st_before} * 
					line : seq nat {Seq.length line = Seq.length line_before - 1} * result: bool)

let op_hash160 st_before line_before result_before = 
		let pop = Stack.pop st_before in 
		let element = fst pop in 
		let stack_after_pop = snd pop in 
		let element = hash_ripemd160(hash_sha256 element) in 
		let stack_push1 = Stack.push stack_after_pop element in 
		let line = Seq.tail line_before in (stack_push1, line, result_before)

(* 1 - 75*)

(*val split: #a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Tot (seq a * seq a) *)
val op_push : st_before: stackBC (seq nat){ capacity st_before > 0}
				-> line_before : seq nat {Seq.length line_before > 0 /\ 
											Seq.length line_before > 1 + (Seq.head line_before)} ->
				result_before: bool{result_before = true}
				-> Tot(st: stackBC (seq nat) {Stack.length st > 0 /\ 
		Seq.length (Stack.index st 0) = Seq.head line_before} *  
		line : seq nat {Seq.length line = Seq.length line_before -1 - (Seq.head line_before)}
		* result: bool
	)

let op_push st_before line_before result_before = 
		let number_of_bytes = Seq.head line_before in 
		let line_before = Seq.split line_before 1 in 
		let line = snd line_before in 
		let line = Seq.split line number_of_bytes in 
		let element = fst line in 
		let stack_push1 = Stack.push st_before element  in 
		(stack_push1, snd line, result_before)
