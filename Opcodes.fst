module Opcodes

open StackBC
open FStar.Seq

module Stack = StackBC
module Seq = FStar.Seq
module List = FStar.List.Tot

(* 76 A9 14 ... 88 AC *)

assume val equ: f : 'a -> s: 'a -> Tot (bool)


(* 118 *)
val op_dup :	st_before: stackBC 'a{Stack.length st_before > 0}  -> 
				line_before: seq nat{Seq.length line_before > 0 /\ (Seq.head line_before = 118)}
				-> Tot (st: stackBC 'a 
								{Stack.length st > 1 /\ 
								equ Stack.index st 0 Stack.index st 1 /\ 
								Stack.length st = Stack.length st_before + 1} * 
				line : seq nat {Seq.length line = Seq.length line_before - 1 } )
