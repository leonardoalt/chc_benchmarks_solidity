(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_9_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_9_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_9_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_c__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_4_function_c__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_9_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_c__8_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 _3_1))) (nondet_interface_1_C_9_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_5_B_21_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_6_B_21_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_7_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_6_B_21_0 error_1 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_8_function_c__8_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_9_function_c__8_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_6_B_21_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_9_function_c__8_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2 _3_1))) (nondet_interface_6_B_21_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_10_function_b__20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_11_function_b__20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_6_B_21_0 error_2 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_2 0) (summary_11_function_b__20_21_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_2 _14_1))) (nondet_interface_6_B_21_0 error_3 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_12_A_41_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_13_A_41_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_14_A_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int))
(=> (= error_3 0) (nondet_interface_13_A_41_0 error_3 this_0 abi_0 crypto_0 state_0 x_25_0 state_0 x_25_0))))


(declare-fun |summary_15_function_c__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_16_function_c__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (nondet_interface_13_A_41_0 error_3 this_0 abi_0 crypto_0 state_0 x_25_0 state_1 x_25_1) true) (and (= error_3 0) (summary_16_function_c__8_41_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_2 x_25_2 _3_1))) (nondet_interface_13_A_41_0 error_4 this_0 abi_0 crypto_0 state_0 x_25_0 state_2 x_25_2))))


(declare-fun |summary_17_function_b__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_18_function_b__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (nondet_interface_13_A_41_0 error_4 this_0 abi_0 crypto_0 state_0 x_25_0 state_1 x_25_1) true) (and (= error_4 0) (summary_18_function_b__20_41_0 error_5 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_2 x_25_2 _14_1))) (nondet_interface_13_A_41_0 error_5 this_0 abi_0 crypto_0 state_0 x_25_0 state_2 x_25_2))))


(declare-fun |summary_19_function_a__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_20_function_a__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (nondet_interface_13_A_41_0 error_5 this_0 abi_0 crypto_0 state_0 x_25_0 state_1 x_25_1) true) (and (= error_5 0) (summary_20_function_a__40_41_0 error_6 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_2 x_25_2))) (nondet_interface_13_A_41_0 error_6 this_0 abi_0 crypto_0 state_0 x_25_0 state_2 x_25_2))))


(declare-fun |block_21_function_c__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_22_c_7_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(block_21_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1)))


(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (block_21_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_22_c_7_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1))))


(declare-fun |block_23_return_function_c__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (block_22_c_7_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 42) (and (= _3_1 0) true))))) true) (block_23_return_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(declare-fun |block_24_return_ghost_c_6_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (block_24_return_ghost_c_6_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 42) (and (= _3_1 0) true))))) true) (block_23_return_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (block_23_return_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) true) true) (summary_3_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1))))


(declare-fun |block_25_function_c__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(block_25_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1)))


(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (block_25_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (summary_3_function_c__8_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 _3_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3285861048)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 195)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 218)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 66)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 184)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_c__8_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 _3_1))))


(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (interface_0_C_9_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_c__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (= error_0 0))) (interface_0_C_9_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_26_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_27_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_27_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_28_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (contract_initializer_entry_27_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_28_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (contract_initializer_after_init_28_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_26_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_29_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_29_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (implicit_constructor_entry_29_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_26_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (implicit_constructor_entry_29_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_26_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_14_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int))
(=> (and (and (summary_constructor_2_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_9_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_30_function_c__8_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_31_c_7_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(block_30_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1)))


(assert
(forall ( (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_30_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_31_c_7_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1))))


(declare-fun |block_32_return_function_c__8_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_31_c_7_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 42) (and (= _3_1 0) true))))) true) (block_32_return_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(declare-fun |block_33_return_ghost_c_6_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_33_return_ghost_c_6_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 42) (and (= _3_1 0) true))))) true) (block_32_return_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(assert
(forall ( (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_32_return_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) true) true) (summary_8_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1))))


(declare-fun |block_34_function_c__8_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(block_34_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1)))


(assert
(forall ( (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_34_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (summary_8_function_c__8_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 _3_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_1_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_1_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_1_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_1_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3285861048)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 195)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 218)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 66)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 184)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_9_function_c__8_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 _3_1))))


(assert
(forall ( (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (interface_5_B_21_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_9_function_c__8_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (= error_0 0))) (interface_5_B_21_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_35_function_b__20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_36_b_19_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(block_35_function_b__20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_35_function_b__20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_36_b_19_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1))))


(declare-fun |block_37_return_function_b__20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_38_function_c__8_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (summary_8_function_c__8_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2) (summary_38_function_c__8_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_36_b_19_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1) (and (summary_38_function_c__8_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _3_2) (and true (and (= _14_1 0) true)))) (> error_1 0)) (summary_10_function_b__20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_36_b_19_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1) (and (= _14_2 expr_17_0) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_0 _3_2) (and (= error_1 0) (and (summary_38_function_c__8_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _3_2) (and true (and (= _14_1 0) true)))))))) true) (block_37_return_function_b__20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_2))))


(declare-fun |block_39_return_ghost_b_18_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_39_return_ghost_b_18_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_2) (and (= _14_2 expr_17_0) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_0 _3_2) (and (= error_1 0) (and (summary_38_function_c__8_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _3_2) (and true (and (= _14_1 0) true)))))))) true) (block_37_return_function_b__20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_37_return_function_b__20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1) true) true) (summary_10_function_b__20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1))))


(declare-fun |block_40_function_b__20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(block_40_function_b__20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (block_40_function_b__20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1) (and (summary_10_function_b__20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 _14_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 1308091344)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 77)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 247)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 227)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 208)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_11_function_b__20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 _14_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (interface_5_B_21_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_11_function_b__20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _14_1) (= error_0 0))) (interface_5_B_21_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_41_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_42_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_42_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_43_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (contract_initializer_entry_42_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_43_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (contract_initializer_after_init_43_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_41_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_44_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_45_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_45_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_46_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (contract_initializer_entry_45_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_46_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (contract_initializer_after_init_46_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_44_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_47_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_47_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (implicit_constructor_entry_47_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_44_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_7_B_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (implicit_constructor_entry_47_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_41_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_44_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))) (> error_2 0)) (summary_constructor_7_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (implicit_constructor_entry_47_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_2 0) (and (contract_initializer_41_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_44_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))))) true) (summary_constructor_7_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int))
(=> (and (and (summary_constructor_7_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_B_21_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_48_function_c__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_49_c_7_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(block_48_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_48_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_25_1 x_25_0))) true) true)) true) (block_49_c_7_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1))))


(declare-fun |block_50_return_function_c__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_49_c_7_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 42) (and (= _3_1 0) true))))) true) (block_50_return_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_2))))


(declare-fun |block_51_return_ghost_c_6_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_51_return_ghost_c_6_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_2) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 42) (and (= _3_1 0) true))))) true) (block_50_return_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_50_return_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1) true) true) (summary_15_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1))))


(declare-fun |block_52_function_c__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(block_52_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_52_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1) (and (summary_15_function_c__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_25_1 state_3 x_25_2 _3_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3285861048)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 195)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 218)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 66)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 184)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_25_1 x_25_0))) true) true))))))) true) (summary_16_function_c__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_3 x_25_2 _3_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (interface_12_A_41_0 this_0 abi_0 crypto_0 state_0 x_25_0) true) (and (summary_16_function_c__8_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_1) (= error_0 0))) (interface_12_A_41_0 this_0 abi_0 crypto_0 state_1 x_25_1))))


(declare-fun |block_53_function_b__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_54_b_19_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(block_53_function_b__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_53_function_b__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_25_1 x_25_0))) true) true)) true) (block_54_b_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1))))


(declare-fun |block_55_return_function_b__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_56_function_c__8_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (summary_15_function_c__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_2) (summary_56_function_c__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _3_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_54_b_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1) (and (summary_56_function_c__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_1 x_25_1 _3_2) (and true (and (= _14_1 0) true)))) (> error_1 0)) (summary_17_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_54_b_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1) (and (= _14_2 expr_17_0) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_0 _3_2) (and (= error_1 0) (and (summary_56_function_c__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_1 x_25_1 _3_2) (and true (and (= _14_1 0) true)))))))) true) (block_55_return_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_2))))


(declare-fun |block_57_return_ghost_b_18_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_57_return_ghost_b_18_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_2) (and (= _14_2 expr_17_0) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_0 _3_2) (and (= error_1 0) (and (summary_56_function_c__8_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_1 x_25_1 _3_2) (and true (and (= _14_1 0) true)))))))) true) (block_55_return_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_55_return_function_b__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1) true) true) (summary_17_function_b__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1))))


(declare-fun |block_58_function_b__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(block_58_function_b__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_58_function_b__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1) (and (summary_17_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_25_1 state_3 x_25_2 _14_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 1308091344)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 77)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 247)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 227)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 208)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_25_1 x_25_0))) true) true))))))) true) (summary_18_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_3 x_25_2 _14_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (interface_12_A_41_0 this_0 abi_0 crypto_0 state_0 x_25_0) true) (and (summary_18_function_b__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_1) (= error_0 0))) (interface_12_A_41_0 this_0 abi_0 crypto_0 state_1 x_25_1))))


(declare-fun |block_59_function_a__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_60_a_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(block_59_function_a__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_59_function_a__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_25_1 x_25_0))) true) true)) true) (block_60_a_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1))))


(declare-fun |block_61_return_function_a__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_62_function_b__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (summary_17_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_2) (summary_62_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1 _14_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_60_a_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1) (and (summary_62_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_1 x_25_1 _14_2) true)) (> error_1 0)) (summary_19_function_a__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1))))


(declare-fun |block_63_function_a__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_60_a_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1) (and (= expr_36_1 (< expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 40) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_25_2) (and (= x_25_2 expr_31_1) (and (=> true (and (>= expr_31_1 0) (<= expr_31_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_1 expr_30_0) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_25_1) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 _14_2) (and (= error_1 0) (and (summary_62_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_1 x_25_1 _14_2) true))))))))))))))) (and (not expr_36_1) (= error_2 5))) (block_63_function_a__40_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (block_63_function_a__40_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_2) (summary_19_function_a__40_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_60_a_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1) (and (= error_2 error_1) (and (= expr_36_1 (< expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 40) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_25_2) (and (= x_25_2 expr_31_1) (and (=> true (and (>= expr_31_1 0) (<= expr_31_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_1 expr_30_0) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_25_1) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 _14_2) (and (= error_1 0) (and (summary_62_function_b__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_25_1 state_1 x_25_1 _14_2) true)))))))))))))))) true) (block_61_return_function_a__40_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_61_return_function_a__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1) true) true) (summary_19_function_a__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1))))


(declare-fun |block_64_function_a__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(block_64_function_a__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (block_64_function_a__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1) (and (summary_19_function_a__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_25_1 state_3 x_25_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_6_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_6_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_6_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_6_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 230582047)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 13)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 190)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 103)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 31)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_25_1 x_25_0))) true) true))))))) true) (summary_20_function_a__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_3 x_25_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (interface_12_A_41_0 this_0 abi_0 crypto_0 state_0 x_25_0) true) (and (summary_20_function_a__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1) (= error_0 0))) (interface_12_A_41_0 this_0 abi_0 crypto_0 state_1 x_25_1))))


(declare-fun |contract_initializer_65_A_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_66_A_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_25_1 x_25_0))) (contract_initializer_entry_66_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1))))


(declare-fun |contract_initializer_after_init_67_A_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (contract_initializer_entry_66_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1) true) true) (contract_initializer_after_init_67_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (contract_initializer_after_init_67_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1) true) true) (contract_initializer_65_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1))))


(declare-fun |contract_initializer_68_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_69_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_69_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_70_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (contract_initializer_entry_69_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_70_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (contract_initializer_after_init_70_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_68_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_71_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_72_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_72_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_73_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (contract_initializer_entry_72_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_73_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (contract_initializer_after_init_73_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_71_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_74_A_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_25_1 x_25_0))) (and true (= x_25_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_74_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (implicit_constructor_entry_74_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1) (and (contract_initializer_71_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_14_A_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_25_0 x_25_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (implicit_constructor_entry_74_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1) (and (contract_initializer_68_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_71_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))) (> error_2 0)) (summary_constructor_14_A_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_25_0 x_25_1))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (implicit_constructor_entry_74_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1) (and (contract_initializer_65_A_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_25_1 x_25_2) (and (= error_2 0) (and (contract_initializer_68_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_71_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)))))) (> error_3 0)) (summary_constructor_14_A_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_25_0 x_25_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (implicit_constructor_entry_74_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1) (and (= error_3 0) (and (contract_initializer_65_A_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_25_1 x_25_2) (and (= error_2 0) (and (contract_initializer_68_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_71_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))))))) true) (summary_constructor_14_A_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_25_0 x_25_2))))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (summary_constructor_14_A_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_25_0 x_25_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_12_A_41_0 this_0 abi_0 crypto_0 state_1 x_25_1))))


(declare-fun |error_target_7_0| () Bool)
(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> (and (and (interface_12_A_41_0 this_0 abi_0 crypto_0 state_0 x_25_0) true) (and (summary_20_function_a__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_25_0 state_1 x_25_1) (= error_0 5))) error_target_7_0)))


(assert
(forall ( (_14_0 Int) (_14_1 Int) (_14_2 Int) (_14_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_17_0 Int) (expr_28_0 Int) (expr_30_0 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_5_0 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_3_0 Int) (funds_4_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_25_0 Int) (x_25_1 Int) (x_25_2 Int) (x_25_3 Int) (x_25_4 Int) (x_25_5 Int))
(=> error_target_7_0 false)))
(check-sat)