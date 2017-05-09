module Opcodes

open StackBC
open FStar.Seq
open Prims 

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
                                Stack.length st = Stack.length st_before + 1}    * 
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
                                            Seq.length line_before > 1 + (Seq.head line_before) /\
                                            ((Seq.head line_before > 0) && (Seq.head line_before < 76))
                                            } ->
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

val op_equalverify: st_before : stackBC (seq nat){Stack.length st_before > 1} -> 
            line_before : seq nat {Seq.length line_before > 0 /\ Seq.head line_before = 136} ->
            result_before : bool{result_before = true} -> 
            Tot(st: stackBC (seq nat) {Stack.length st_before >= 0} * 
        line : seq nat{Seq.length line = Seq.length line_before -1} * result: bool)

let op_equalverify st_before line_before result_before = 
    let pop = Stack.pop st_before in 
    let elem1 = fst pop in 
    let pop2 = Stack.pop (snd pop) in 
    let elem2 = fst pop2 in 
    let result = (elem1 = elem2) in 
    let line = Seq.tail line_before in  
    (snd pop2, line, result)

val op_false: st_before: stackBC (seq nat) {Stack.capacity st_before > 0}-> 
                line_before : seq nat {Seq.length line_before > 0 /\ Seq.head line_before = 0}-> 
                result_before : bool{result_before = true} ->
                Tot(st: stackBC (seq nat){Stack.length st = Stack.length st_before + 1} * 
                line : seq nat {Seq.length line = Seq.length line_before -1} * result: bool)

let op_false st_before line_before result_before = 
    let element = Seq.createEmpty  in 
    let stack_push1 = Stack.push st_before element in 
    let line = Seq.tail line_before in 
    (stack_push1, line, result_before)

val get_bytes_push: number: nat{number = 1 || number = 2 || number = 4} ->  
                    line_before : seq nat{Seq.length line_before > number} -> 
                    Tot (nat * line: seq nat{Seq.length line = Seq.length line_before - number})
let get_bytes_push number line_before = 
    (*  I dont wanna have a recursion call while the standart is given only 1/2/4*)
    let r = 0 in
    if (number  = 1 ) then 
        let r = Seq.head line_before in (r, Seq.tail line_before)
    else if (number = 2) then 
        let r = Seq.head line_before in 
        let line_temp = Seq.tail line_before in 
        let r = op_Multiply r 256 + (Seq.head line_temp) in 
        let line_temp = Seq.tail line_temp in (r, line_temp)
    else 
        let r = Seq.head line_before in 
        let line_temp = Seq.tail line_before in 
        let r = op_Multiply r 256  + Seq.head line_temp in 
        let line_temp = Seq.tail line_temp in 
        let r = op_Multiply r 256  + Seq.head line_temp in 
        let line_temp = Seq.tail line_temp in 
        let r = op_Multiply r 256  + Seq.head line_temp in 
        let line_temp = Seq.tail line_temp in (r, line_temp)

val op_push1: st_before : stackBC (seq nat) {Stack.capacity st_before > 0} ->
                line_before : seq nat {
                    Seq.length line_before > 0 /\ Seq.head line_before = 76 /\ 
                    Seq.length line_before > 1 /\
                    Seq.length line_before >= 1+ (fst (get_bytes_push 1 line_before))} ->
                result_before : bool {result_before = true} -> 
                Tot(st:stackBC (seq nat) {Stack.length st = Stack.length st_before + 1} * 
                line: seq nat {Seq.length line = Seq.length line_before -1 - fst(get_bytes_push 1 line_before)} * result:bool)

let op_push1 st_before line_before result_before = 
    let bytes = get_bytes_push 1 line_before in 
    let length = fst bytes in 
    let line_new = snd bytes in 
    let element = Seq.split line_new length in 
    let stack_push1 = Stack.push st_before (fst element) in 
    (stack_push1, snd element, result_before)

val op_push2: st_before : stackBC (seq nat) {Stack.capacity st_before > 0} ->
                line_before : seq nat {
                    Seq.length line_before > 0 /\ Seq.head line_before = 77 /\ 
                    Seq.length line_before > 2 /\
                    Seq.length line_before >= 2 + (fst (get_bytes_push 2 line_before))} ->
                result_before : bool {result_before = true} -> 
                Tot(st:stackBC (seq nat) {Stack.length st = Stack.length st_before + 1} * 
                line: seq nat {Seq.length line = Seq.length line_before -2  - fst(get_bytes_push 2 line_before)} * result:bool)

let op_push2 st_before line_before result_before = 
    let bytes = get_bytes_push 2 line_before in 
    let length = fst bytes in 
    let line_new = snd bytes in 
    let element = Seq.split line_new length in 
    let stack_push1 = Stack.push st_before (fst element) in 
    (stack_push1, snd element, result_before)

val op_push4: st_before : stackBC (seq nat) {Stack.capacity st_before > 0} ->
                line_before : seq nat {
                    Seq.length line_before > 0 /\ Seq.head line_before = 78 /\ 
                    Seq.length line_before > 4 /\
                    Seq.length line_before >= 4+ (fst (get_bytes_push 4 line_before))} ->
                result_before : bool {result_before = true} -> 
                Tot(st:stackBC (seq nat) {Stack.length st = Stack.length st_before + 1} * 
                line: seq nat {Seq.length line = Seq.length line_before -4  - fst(get_bytes_push 4 line_before)} * result:bool)

let op_push4 st_before line_before result_before = 
    let bytes = get_bytes_push 4 line_before in 
    let length = fst bytes in 
    let line_new = snd bytes in 
    let element = Seq.split line_new length in 
    let stack_push1 = Stack.push st_before (fst element) in 
    (stack_push1, snd element, result_before)
