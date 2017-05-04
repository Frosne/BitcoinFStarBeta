module Opcodes

open StackBC
open FStar.Seq

module Stack = StackBC
module Seq = FStar.Seq
module List = FStar.List.Tot

(* 76 A9 14 ... 88 AC *)


(* 118 *)


val op_dup : #a: eqtype -> st_before: stackBC a{Stack.length st_before > 0 /\ Stack.capacity st_before > 0}  -> 
				line_before: seq nat{Seq.length line_before > 0 /\ (Seq.head line_before = 118)}
				-> Tot (st: stackBC a 
								{Stack.length st > 1 /\ 
								(Stack.index st 0) = (Stack.index st 1) /\ 
								Stack.length st = Stack.length st_before + 1}	* 
						line : seq nat {Seq.length line = Seq.length line_before - 1 }) 

let op_dup #a st_before line_before = 
	let pop = Stack.pop st_before in 
	let element = fst pop in 
	let stack_after_pop = snd pop in 
	let stack_push1 = Stack.push stack_after_pop element in 
	let stack_push2 = Stack.push stack_push1 element in 
	let line = Seq.tail line_before in (stack_push2, line)

