module StackBC

open FStar.List.Tot

module L = FStar.List.Tot

type stackBC 'a = 
| Mk : elements: list 'a -> capacity: nat -> length : nat{length = L.length elements} -> stackBC 'a


val elements: st : stackBC 'a -> Tot(list 'a)
let elements st = 
	match st with 
	| Mk el _ _ -> el

val capacity: st : stackBC 'a  -> Tot(nat)
let capacity st = 
	match st with 
	| Mk _ capacity _ -> capacity

val length: st : stackBC 'a -> Tot(nat)
let length st = 
	match st with 
	| Mk _ _ length -> length


val index : st: stackBC 'a -> counter:nat {length st > counter}  -> 'a
let index st counter = 
	let elements = elements st in 
	L.index elements counter 

