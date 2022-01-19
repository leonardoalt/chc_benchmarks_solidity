(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_State_17_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_State_17_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_State_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_State_17_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_1 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_State_17_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 _x_2_0 state_2 _x_2_1 _5_1))) (nondet_interface_1_State_17_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_5_C_37_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_6_C_37_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_7_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_5_1 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (s_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int))
(=> (= error_1 0) (nondet_interface_6_C_37_0 error_1 this_0 abi_0 crypto_0 state_0 s_20_0 z_26_0 state_0 s_20_0 z_26_0))))


(declare-fun |summary_8_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_9_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_1 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (nondet_interface_6_C_37_0 error_1 this_0 abi_0 crypto_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) true) (and (= error_1 0) (summary_9_function_f__36_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 s_20_1 z_26_1 state_2 s_20_2 z_26_2))) (nondet_interface_6_C_37_0 error_2 this_0 abi_0 crypto_0 state_0 s_20_0 z_26_0 state_2 s_20_2 z_26_2))))


(declare-fun |block_10_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_11_f_15_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(block_10_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1)))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (block_10_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _x_2_1 _x_2_0))) true)) true) (block_11_f_15_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1))))


(declare-fun |block_12_return_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_13_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (block_11_f_15_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1) (and (= expr_10_1 (< expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 100) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 _x_2_1) (and (= _5_1 0) (and (and (>= _x_2_1 0) (<= _x_2_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))) (and (not expr_10_1) (= error_1 1))) (block_13_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (block_13_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1) (summary_3_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (block_11_f_15_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1) (and (= _5_2 expr_13_0) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 _x_2_1) (and (= error_1 error_0) (and (= expr_10_1 (< expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 100) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 _x_2_1) (and (= _5_1 0) (and (and (>= _x_2_1 0) (<= _x_2_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))) true) (block_12_return_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_2))))


(declare-fun |block_14_return_ghost_f_14_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (block_14_return_ghost_f_14_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_2) (and (= _5_2 expr_13_0) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 _x_2_1) (and (= error_1 error_0) (and (= expr_10_1 (< expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 100) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 _x_2_1) (and (= _5_1 0) (and (and (>= _x_2_1 0) (<= _x_2_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))) true) (block_12_return_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_2))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (block_12_return_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1) true) true) (summary_3_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1))))


(declare-fun |block_15_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(block_15_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1)))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (block_15_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1) (and (summary_3_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 _x_2_1 state_3 _x_2_2 _5_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3017696395)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 179)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 222)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 100)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 139)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _x_2_1 _x_2_0))) true))))))) true) (summary_4_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_3 _x_2_2 _5_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (interface_0_State_17_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1) (= error_0 0))) (interface_0_State_17_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_16_State_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_17_State_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_17_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_18_State_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (contract_initializer_entry_17_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_18_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (contract_initializer_after_init_18_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_16_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_19_State_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_19_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (implicit_constructor_entry_19_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_16_State_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_State_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (implicit_constructor_entry_19_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_16_State_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_State_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int))
(=> (and (and (summary_constructor_2_State_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_State_17_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_20_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_21_f_35_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(block_20_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1)))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (block_20_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= s_20_1 s_20_0)) (= z_26_1 z_26_0))) true) true)) true) (block_21_f_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1))))


(declare-fun |block_22_return_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_23_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (block_21_f_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 2) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 z_26_1) true)))))) (and (not expr_32_1) (= error_1 3))) (block_23_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (block_23_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) (summary_8_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (block_21_f_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) (and (= error_1 error_0) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 2) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 z_26_1) true))))))) true) (block_22_return_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (block_22_return_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) true) true) (summary_8_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1))))


(declare-fun |block_24_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(block_24_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1)))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (block_24_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) (and (summary_8_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 s_20_1 z_26_1 state_3 s_20_2 z_26_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= s_20_1 s_20_0)) (= z_26_1 z_26_0))) true) true))))))) true) (summary_9_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_3 s_20_2 z_26_2))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (interface_5_C_37_0 this_0 abi_0 crypto_0 state_0 s_20_0 z_26_0) true) (and (summary_9_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) (= error_0 0))) (interface_5_C_37_0 this_0 abi_0 crypto_0 state_1 s_20_1 z_26_1))))


(declare-fun |contract_initializer_25_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_26_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= s_20_1 s_20_0)) (= z_26_1 z_26_0))) (contract_initializer_entry_26_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_1))))


(declare-fun |contract_initializer_after_init_27_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (contract_initializer_entry_26_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_1) (and (= z_26_2 expr_25_1) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_25_1 _5_4) (and (=> true true) (and (= expr_24_0 2) (and (=> true true) (and (= expr_22_0 s_20_1) true)))))))) true) (contract_initializer_after_init_27_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_2))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (contract_initializer_after_init_27_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_1) true) true) (contract_initializer_25_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_1))))


(declare-fun |implicit_constructor_entry_28_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= s_20_1 s_20_0)) (= z_26_1 z_26_0))) (and (and true (= s_20_1 0)) (= z_26_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_28_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_1))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (implicit_constructor_entry_28_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_1) (and (contract_initializer_25_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 s_20_1 z_26_1 s_20_2 z_26_2) true)) (> error_1 0)) (summary_constructor_7_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 s_20_0 z_26_0 s_20_2 z_26_2))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (implicit_constructor_entry_28_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_1) (and (= error_1 0) (and (contract_initializer_25_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 s_20_1 z_26_1 s_20_2 z_26_2) true))) true) (summary_constructor_7_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 s_20_0 z_26_0 s_20_2 z_26_2))))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (summary_constructor_7_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_20_0 z_26_0 s_20_1 z_26_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_C_37_0 this_0 abi_0 crypto_0 state_1 s_20_1 z_26_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (_x_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (interface_0_State_17_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _x_2_0 state_1 _x_2_1 _5_1) (= error_0 1))) error_target_5_0)))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (_x_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> (and (and (interface_5_C_37_0 this_0 abi_0 crypto_0 state_0 s_20_0 z_26_0) true) (and (summary_9_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_20_0 z_26_0 state_1 s_20_1 z_26_1) (= error_0 3))) error_target_6_0)))


(assert
(forall ( (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (_x_2_0 Int) (_x_2_1 Int) (_x_2_2 Int) (_x_2_3 Int) (_x_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_22_0 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_2_0 Int) (funds_4_0 Int) (s_20_0 Int) (s_20_1 Int) (s_20_2 Int) (s_20_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (z_26_0 Int) (z_26_1 Int) (z_26_2 Int) (z_26_3 Int))
(=> error_target_6_0 false)))
(check-sat)