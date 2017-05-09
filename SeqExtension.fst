module SeqExtension

open FStar.Seq
open FStar.Option

module Seq = FStar.Seq


val _search: #a: eqtype -> s: seq a {Seq.length s > 0} -> element: a {Seq.mem element s}->  i: nat {i < Seq.length s} -> 
			Tot(r: nat{r < Seq.length s})
			(decreases (Seq.length s - i))			

let rec _search #a  s element i= 
	if (i = Seq.length s -1) then i else
	if Seq.index s i = element then i 
	else 
		_search #a s element  (i + 1)

val search: #a : eqtype ->s: seq a{Seq.length s > 0} -> element: a {Seq.mem element s}->  
			Tot(r: nat{r < Seq.length s})

let search #a  s element = 
	_search #a  s element 0			