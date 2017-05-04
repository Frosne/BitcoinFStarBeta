module StackBC

open FStar.Seq

module Seq = FStar.Seq

type stackBC (a:eqtype) = 
| Mk : elem: seq a -> cap: nat -> len : nat{len = Seq.length elem} -> stackBC a


val elements:  #a:eqtype ->  st : stackBC a -> Tot(seq a)
let elements #a st = 
	match st with 
	| Mk el _ _ -> el

val capacity:  #a:eqtype->  st : stackBC a  -> Tot(nat)
let capacity #a st = 
	match st with 
	| Mk _ capacity _ -> capacity

val length: #a:eqtype ->  st : stackBC a -> Tot(nat)
let length #a st = 
	match st with 
	| Mk _ _ length -> length


val index : #a:eqtype ->  st: stackBC a -> counter:nat {length st > counter}  -> Tot(a)
let index #a st counter = 
	let elements = elements st in 
	index elements counter 

val head: #a: eqtype -> st: stackBC a {length st > 0}-> Tot (a)
let head #a st = 
	index st 0


val push: #a:eqtype ->  st: stackBC a{capacity st > 0} -> element : a  -> 
	Tot(st_new: stackBC a{
		length  st_new = length st + 1   /\ 
		head st_new = element /\ 
		capacity st_new = capacity st -1 } )

let push #a st element = 
	let elem = elements st in 
	let cap = capacity st in 
	let len = length st in 
	let elements_new = Seq.cons element elem in 
	let cap_new = cap  - 1 in 
	let len_new = len + 1 in 
	Mk elements_new cap_new len_new

val pop_elem:#a : eqtype ->  st: stackBC a {length st > 0} -> Tot(a)
let pop_elem #a st  = 
	index st 0	

val pop_stack: #a : eqtype -> st: stackBC a {length st >0} -> Tot (st_new: stackBC a{length st_new = length st - 1 })
let pop_stack #a st  = 
	let elem = elements st in 
	let cap = capacity st in 
	let len = length st in 
	let elements_new = Seq.tail elem in 
	let cap_new = cap + 1 in 
	let len_new = len - 1 in
	Mk elements_new cap_new len_new

val pop: #a : eqtype -> st: stackBC a {length st > 0} -> Tot(a * (st_new : stackBC a{length st_new = length st -1}))
let pop #a st = 
	let elem = pop_elem #a st in 
	let stack = pop_stack #a st in 
	(elem,stack)
